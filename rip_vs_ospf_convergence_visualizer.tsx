import React, { useState, useEffect, useRef, useMemo } from 'react';
import {
  Play,
  Pause,
  SkipForward,
  SkipBack,
  FastForward,
  RotateCcw,
  Plus,
  Trash2,
  Link as LinkIcon,
  Zap,
  ShieldAlert,
  Activity,
  BookOpen,
  BarChart3,
  Network,
  Sun,
  Moon,
  Info,
  CheckCircle2,
  AlertTriangle,
  XCircle,
  Sliders,
  Eye,
  GraduationCap,
  Users,
  ArrowRight,
  Layers,
  Terminal
} from 'lucide-react';

// ============================================================================
// CONSTANTS & TOPOLOGY PRESETS (RFC 2453 RIP & RFC 2328 OSPF)
// ============================================================================
const INF = 16; // RFC 2453 RIP infinity metric = 16 hops/cost

const TOPOLOGY_PRESETS = {
  mesh6: {
    name: '6-Node Mesh (Default)',
    description: 'Redundant multi-path topology with alternative high-cost backup paths.',
    nodes: ['A', 'B', 'C', 'D', 'E', 'F'],
    positions: {
      A: [65, 155],
      B: [155, 60],
      C: [295, 60],
      D: [385, 155],
      E: [155, 250],
      F: [295, 250]
    },
    links: [
      { a: 'A', b: 'B', w: 1 },
      { a: 'B', b: 'C', w: 1 },
      { a: 'C', b: 'D', w: 1 },
      { a: 'A', b: 'E', w: 2 },
      { a: 'E', b: 'F', w: 1 },
      { a: 'F', b: 'D', w: 2 },
      { a: 'C', b: 'F', w: 4 }
    ]
  },
  linear4: {
    name: 'Linear Chain (A–B–C–D)',
    description: 'Textbook topology to observe pure 2-node/3-node Count-to-Infinity.',
    nodes: ['A', 'B', 'C', 'D'],
    positions: {
      A: [60, 155],
      B: [170, 155],
      C: [280, 155],
      D: [390, 155]
    },
    links: [
      { a: 'A', b: 'B', w: 1 },
      { a: 'B', b: 'C', w: 1 },
      { a: 'C', b: 'D', w: 1 }
    ]
  },
  ring6: {
    name: '6-Node Ring Topology',
    description: 'Symmetric ring demonstrating bi-directional LSA flooding & backup path switchover.',
    nodes: ['A', 'B', 'C', 'D', 'E', 'F'],
    positions: {
      A: [75, 155],
      B: [155, 55],
      C: [295, 55],
      D: [375, 155],
      E: [295, 255],
      F: [155, 255]
    },
    links: [
      { a: 'A', b: 'B', w: 1 },
      { a: 'B', b: 'C', w: 1 },
      { a: 'C', b: 'D', w: 1 },
      { a: 'D', b: 'E', w: 2 },
      { a: 'E', b: 'F', w: 2 },
      { a: 'F', b: 'A', w: 2 }
    ]
  },
  diamond5: {
    name: 'Dual-Homed Tail (Count-to-Infinity + Loop)',
    description: 'Diamond core (A-B-C) attached to tail link (C-D) where loops form when D fails.',
    nodes: ['A', 'B', 'C', 'D', 'E'],
    positions: {
      A: [65, 155],
      B: [185, 70],
      E: [185, 240],
      C: [295, 155],
      D: [400, 155]
    },
    links: [
      { a: 'A', b: 'B', w: 1 },
      { a: 'A', b: 'E', w: 1 },
      { a: 'B', b: 'C', w: 1 },
      { a: 'E', b: 'C', w: 2 },
      { a: 'B', b: 'E', w: 1 },
      { a: 'C', b: 'D', w: 1 }
    ]
  }
};

// ============================================================================
// CORE ALGORITHMS: DIJKSTRA (OSPF) & BELLMAN-FORD (RIP)
// ============================================================================

const deepClone = (obj) => JSON.parse(JSON.stringify(obj));

// Helper: Check if link `i` is operational
function isLinkOperational(links, i, failedLinks, failedNodes) {
  const l = links[i];
  if (!l) return false;
  return !failedLinks.has(i) && !failedNodes.has(l.a) && !failedNodes.has(l.b);
}

// Helper: Get active neighbors of node `n`
function getNeighbors(nodes, links, n, failedLinks, failedNodes) {
  if (failedNodes.has(n)) return [];
  const res = [];
  links.forEach((l, i) => {
    if (!isLinkOperational(links, i, failedLinks, failedNodes)) return;
    if (l.a === n) res.push({ v: l.b, w: l.w, linkIdx: i });
    else if (l.b === n) res.push({ v: l.a, w: l.w, linkIdx: i });
  });
  return res;
}

// OSPF: Dijkstra's Shortest Path First (RFC 2328) on node's current LSDB snapshot
function runDijkstra(source, nodes, links, lsdbSnap) {
  const fl = new Set(lsdbSnap.fl);
  const fn = new Set(lsdbSnap.fn);
  const D = {};
  nodes.forEach((x) => {
    D[x] = { c: Infinity, n: null };
  });
  if (fn.has(source)) {
    nodes.forEach((x) => {
      D[x] = { c: x === source ? 0 : INF, n: null };
    });
    return D;
  }
  D[source] = { c: 0, n: null };
  const vis = new Set();

  while (true) {
    let u = null;
    nodes.forEach((x) => {
      if (!vis.has(x) && D[x].c < Infinity && (u === null || D[x].c < D[u].c)) {
        u = x;
      }
    });
    if (u === null) break;
    vis.add(u);

    links.forEach((l, i) => {
      if (fl.has(i) || fn.has(l.a) || fn.has(l.b)) return;
      const v = l.a === u ? l.b : l.b === u ? l.a : null;
      if (!v || vis.has(v)) return;
      const newCost = D[u].c + l.w;
      if (newCost < D[v].c) {
        D[v] = { c: newCost, n: u === source ? v : D[u].n };
      }
    });
  }

  nodes.forEach((x) => {
    if (D[x].c === Infinity) {
      D[x] = { c: INF, n: null };
    }
  });
  return D;
}

// RIP: Synchronous Distance-Vector Bellman-Ford Update Round (RFC 2453)
function runRipRound(prevTable, nodes, links, failedLinks, failedNodes, rmode, costClimbTracker) {
  const old = deepClone(prevTable);
  const nextTable = deepClone(prevTable);
  const changedNodes = new Set();
  const packetEvents = [];
  let ctiDetected = false;

  nodes.forEach((n) => {
    if (failedNodes.has(n)) return;
    const activeNbrs = getNeighbors(nodes, links, n, failedLinks, failedNodes);

    nodes.forEach((d) => {
      if (d === n) return;
      const cur = old[n][d] || { c: INF, n: null };
      let best = INF;
      let nh = null;

      activeNbrs.forEach(({ v, w }) => {
        const nbrEntry = old[v][d] || { c: INF, n: null };
        let advertisedCost = nbrEntry.c;

        // Loop prevention mechanisms
        if (nbrEntry.n === n) {
          if (rmode === 'split') return; // Split Horizon: do not advertise back to next-hop
          if (rmode === 'poison') advertisedCost = INF; // Poison Reverse: advertise infinity (16)
        }

        const candidateCost = Math.min(INF, w + advertisedCost);
        if (
          candidateCost < best ||
          (candidateCost === best && candidateCost < INF && v === cur.n && nh !== cur.n)
        ) {
          best = candidateCost;
          nh = v;
        }
      });

      if (best >= INF) {
        best = INF;
        nh = null;
      }

      if (best !== cur.c || nh !== cur.n) {
        nextTable[n][d] = { c: best, n: nh };
        changedNodes.add(n);
        packetEvents.push({
          protocol: 'RIP',
          from: nh || 'Local',
          to: n,
          dest: d,
          oldCost: cur.c,
          newCost: best,
          nextHop: nh
        });

        const key = `${n}->${d}`;
        if (best > cur.c && cur.c < INF) {
          costClimbTracker[key] = (costClimbTracker[key] || 0) + 1;
          if (costClimbTracker[key] >= 2) ctiDetected = true;
        } else {
          costClimbTracker[key] = 0;
        }
      }
    });
  });

  return { nextTable, changedNodes, packetEvents, ctiDetected };
}

// Trace actual forwarding path from `src` to `dst` in table `tb`
function traceForwardingPath(tb, nodes, links, failedLinks, failedNodes, src, dst) {
  const path = [src];
  if (!nodes.includes(src) || !nodes.includes(dst)) return { path, st: 'invalid node' };
  if (failedNodes.has(src)) return { path, st: 'source node is down' };
  if (src === dst) return { path, st: 'ok' };

  let cur = src;
  while (cur !== dst) {
    const e = tb[cur]?.[dst];
    if (!e || e.n == null || e.c >= INF) {
      return { path, st: `unreachable at ${cur}` };
    }
    const activeNbrs = getNeighbors(nodes, links, cur, failedLinks, failedNodes);
    const linkOk = activeNbrs.some((x) => x.v === e.n);
    if (!linkOk) {
      return { path, st: `blackhole at ${cur}` };
    }
    if (path.includes(e.n)) {
      path.push(e.n);
      return { path, st: `routing loop (${path.slice(path.indexOf(e.n)).join('→')})` };
    }
    path.push(e.n);
    cur = e.n;
    if (path.length > nodes.length + 2) {
      return { path, st: 'routing loop' };
    }
  }
  return { path, st: 'ok' };
}

// Format seconds cleanly
const formatTime = (s) => {
  if (s >= 60) {
    const mins = Math.floor(s / 60);
    const secs = Math.round(s % 60);
    return `${mins}m ${secs}s`;
  }
  return `${s < 10 ? s.toFixed(1) : Math.round(s)}s`;
};

const formatCost = (c) => (c >= INF ? '∞ (16)' : c);

// ============================================================================
// STANDALONE BENCHMARK RUNNER (FOR 3-WAY COMPARISON LAB)
// ============================================================================
function runFullBenchmark(nodes, links, initialFailL, initialFailN, eventFailL, eventFailN) {
  const modes = [
    { key: 'none', name: 'RIP (No Loop Prevention)', type: 'rip' },
    { key: 'split', name: 'RIP + Split Horizon', type: 'rip' },
    { key: 'poison', name: 'RIP + Poison Reverse', type: 'rip' },
    { key: 'ospf', name: 'OSPF (Dijkstra Link-State)', type: 'ospf' }
  ];

  // Settle initial state before failure injection
  const baseRipTable = {};
  nodes.forEach((n) => {
    baseRipTable[n] = {};
    nodes.forEach((d) => {
      baseRipTable[n][d] = { c: d === n ? 0 : INF, n: null };
    });
  });

  let settledRip = deepClone(baseRipTable);
  for (let i = 0; i < 60; i++) {
    const { nextTable, changedNodes } = runRipRound(
      settledRip,
      nodes,
      links,
      initialFailL,
      initialFailN,
      'none',
      {}
    );
    settledRip = nextTable;
    if (changedNodes.size === 0) break;
  }

  // Determine affected originators for the event
  const affectedLinks = [];
  links.forEach((l, idx) => {
    const wasUp = isLinkOperational(links, idx, initialFailL, initialFailN);
    const nowUp = isLinkOperational(links, idx, eventFailL, eventFailN);
    if (wasUp !== nowUp) affectedLinks.push(idx);
  });

  const originators = new Set();
  affectedLinks.forEach((i) => {
    [links[i].a, links[i].b].forEach((x) => {
      if (!eventFailN.has(x)) originators.add(x);
    });
  });

  const results = {};

  modes.forEach((m) => {
    if (m.type === 'rip') {
      let T = deepClone(settledRip);
      // Drop direct dead neighbor routes
      nodes.forEach((n) => {
        if (eventFailN.has(n)) {
          nodes.forEach((d) => {
            T[n][d] = { c: d === n ? 0 : INF, n: null };
          });
          return;
        }
        const nbrs = getNeighbors(nodes, links, n, eventFailL, eventFailN);
        nodes.forEach((d) => {
          const e = T[n][d];
          if (e.n && !nbrs.some((x) => x.v === e.n)) {
            T[n][d] = { c: INF, n: null };
          }
        });
      });

      let rounds = 0;
      let totalUpdates = 0;
      let hadCti = false;
      const tracker = {};
      const costSeries = [deepClone(T)];

      for (let step = 0; step < 65; step++) {
        const { nextTable, changedNodes, packetEvents, ctiDetected } = runRipRound(
          T,
          nodes,
          links,
          eventFailL,
          eventFailN,
          m.key,
          tracker
        );
        if (ctiDetected) hadCti = true;
        if (changedNodes.size > 0) {
          rounds++;
          totalUpdates += packetEvents.length;
          T = nextTable;
          costSeries.push(deepClone(T));
        } else {
          break;
        }
      }

      results[m.key] = {
        name: m.name,
        steps: rounds,
        timeSec: rounds * 30,
        messages: totalUpdates,
        hadCti,
        costSeries
      };
    } else {
      // OSPF simulation
      const snap = { fl: [...eventFailL], fn: [...eventFailN] };
      const informed = new Set(originators);
      let hops = 0;
      let lsaFloodCount = originators.size;

      while (true) {
        const nextWave = new Set();
        nodes.forEach((n) => {
          if (informed.has(n) && !eventFailN.has(n)) {
            getNeighbors(nodes, links, n, eventFailL, eventFailN).forEach(({ v }) => {
              if (!informed.has(v)) nextWave.add(v);
            });
          }
        });
        if (nextWave.size > 0) {
          hops++;
          lsaFloodCount += nextWave.size;
          nextWave.forEach((v) => informed.add(v));
        } else {
          break;
        }
      }

      const timeSec = hops * 0.1 + (originators.size > 0 ? 0.2 : 0);
      results.ospf = {
        name: m.name,
        steps: hops,
        timeSec: Number(timeSec.toFixed(2)),
        messages: lsaFloodCount,
        hadCti: false
      };
    }
  });

  return results;
}

// ============================================================================
// MAIN APPLICATION COMPONENT
// ============================================================================
export default function App() {
  // Theme state
  const [darkMode, setDarkMode] = useState(true);
  // Navigation Tab: 'simulator' | 'benchmark' | 'reference'
  const [activeTab, setActiveTab] = useState('simulator');

  // Topology State
  const [presetKey, setPresetKey] = useState('mesh6');
  const [nodes, setNodes] = useState(TOPOLOGY_PRESETS.mesh6.nodes);
  const [positions, setPositions] = useState(TOPOLOGY_PRESETS.mesh6.positions);
  const [links, setLinks] = useState(TOPOLOGY_PRESETS.mesh6.links);

  // Interaction & Builder Mode
  // 'link' | 'node' | 'weight' | 'drag' | 'addNode' | 'addLink' | 'delete'
  const [clickMode, setClickMode] = useState('link');
  const [rmode, setRmode] = useState('none'); // 'none' | 'split' | 'poison'
  const [srcNode, setSrcNode] = useState('B');
  const [dstNode, setDstNode] = useState('D');
  const [inspectAllNodes, setInspectAllNodes] = useState(false);

  // Builder helper states
  const [linkStartNode, setLinkStartNode] = useState(null);
  const [newLinkWeight, setNewLinkWeight] = useState(1);
  const [draggingNode, setDraggingNode] = useState(null);

  // Simulation State
  const [failedLinks, setFailedLinks] = useState(new Set());
  const [failedNodes, setFailedNodes] = useState(new Set());
  const [history, setHistory] = useState([]); // Array of full tick snapshots
  const [cursor, setCursor] = useState(0); // Current history index
  const [isPlaying, setIsPlaying] = useState(false);
  const [playSpeedMs, setPlaySpeedMs] = useState(850);
  const [lastScenarioName, setLastScenarioName] = useState('Stable Initial Topology');

  // Refs for SVG dragging
  const svgRefRip = useRef(null);
  const svgRefOspf = useRef(null);

  // Compute settled baseline and reset simulation
  const initializeSimulation = (
    customNodes = nodes,
    customLinks = links,
    initFailL = new Set(),
    initFailN = new Set(),
    scenarioLabel = 'Network Stable'
  ) => {
    setIsPlaying(false);
    setFailedLinks(new Set(initFailL));
    setFailedNodes(new Set(initFailN));
    setLastScenarioName(scenarioLabel);

    // Initialize RIP tables
    let T = {};
    customNodes.forEach((n) => {
      T[n] = {};
      customNodes.forEach((d) => {
        T[n][d] = { c: d === n ? 0 : INF, n: null };
      });
    });

    for (let i = 0; i < 60; i++) {
      const { nextTable, changedNodes } = runRipRound(
        T,
        customNodes,
        customLinks,
        initFailL,
        initFailN,
        rmode,
        {}
      );
      T = nextTable;
      if (changedNodes.size === 0) break;
    }

    const s0 = { fl: [...initFailL], fn: [...initFailN] };
    const O = {};
    const seq = {};
    customNodes.forEach((n) => {
      seq[n] = 0;
      O[n] = runDijkstra(n, customNodes, customLinks, s0);
    });

    const initialTick = {
      tick: 0,
      ripTable: T,
      ospfTable: O,
      snaps: [s0],
      seq,
      rSteps: 0,
      oSteps: 0,
      rDone: true,
      oDone: true,
      rCh: [],
      oCh: [],
      cti: false,
      costClimbTracker: {},
      events: [
        {
          tick: 0,
          type: 'INFO',
          text: `${scenarioLabel}. Both RIP and OSPF routing tables are converged.`
        }
      ],
      ripPackets: 0,
      ospfPackets: 0
    };

    setHistory([initialTick]);
    setCursor(0);
  };

  // Run initial setup on mount
  useEffect(() => {
    initializeSimulation(nodes, links, new Set(), new Set(), 'Initial Topology Converged');
  }, []);

  // Re-settle when RIP loop-prevention mode changes
  const handleRmodeChange = (newMode) => {
    setRmode(newMode);
    setIsPlaying(false);
    // If a failure is currently active, re-trigger the failure from settled baseline under the new RIP mode
    if (failedLinks.size > 0 || failedNodes.size > 0) {
      triggerFailureFromBaseline(nodes, links, failedLinks, failedNodes, newMode, lastScenarioName);
    } else {
      initializeSimulation(nodes, links, new Set(), new Set(), 'Network Stable');
    }
  };

  // Inject failure from clean baseline so user can compare fairly
  const triggerFailureFromBaseline = (
    cNodes,
    cLinks,
    targetFailL,
    targetFailN,
    activeRmode,
    label
  ) => {
    setIsPlaying(false);
    setFailedLinks(new Set(targetFailL));
    setFailedNodes(new Set(targetFailN));
    setLastScenarioName(label);

    // 1. Settle healthy network first
    let T = {};
    cNodes.forEach((n) => {
      T[n] = {};
      cNodes.forEach((d) => {
        T[n][d] = { c: d === n ? 0 : INF, n: null };
      });
    });
    for (let i = 0; i < 60; i++) {
      const { nextTable, changedNodes } = runRipRound(
        T,
        cNodes,
        cLinks,
        new Set(),
        new Set(),
        activeRmode,
        {}
      );
      T = nextTable;
      if (changedNodes.size === 0) break;
    }

    const s0 = { fl: [], fn: [] };
    const O = {};
    const seq = {};
    cNodes.forEach((n) => {
      seq[n] = 0;
      O[n] = runDijkstra(n, cNodes, cLinks, s0);
    });

    // 2. Apply failure event to settled tables
    const affectedIndices = [];
    cLinks.forEach((l, i) => {
      if (targetFailL.has(i) || targetFailN.has(l.a) || targetFailN.has(l.b)) {
        affectedIndices.push(i);
      }
    });

    const originators = new Set();
    affectedIndices.forEach((i) => {
      [cLinks[i].a, cLinks[i].b].forEach((x) => {
        if (!targetFailN.has(x)) originators.add(x);
      });
    });

    // RIP immediate neighbor drop
    cNodes.forEach((n) => {
      if (targetFailN.has(n)) {
        cNodes.forEach((d) => {
          T[n][d] = { c: d === n ? 0 : INF, n: null };
        });
        return;
      }
      const activeNbrs = getNeighbors(cNodes, cLinks, n, targetFailL, targetFailN);
      cNodes.forEach((d) => {
        const e = T[n][d];
        if (e.n && !activeNbrs.some((x) => x.v === e.n)) {
          T[n][d] = { c: INF, n: null };
        }
      });
    });

    // OSPF LSA origination
    const s1 = { fl: [...targetFailL], fn: [...targetFailN] };
    const snaps = [s0, s1];
    originators.forEach((o) => {
      seq[o] = 1;
      O[o] = runDijkstra(o, cNodes, cLinks, s1);
    });

    const eventLogs = [
      {
        tick: 0,
        type: 'ALERT',
        text: `${label} — Originator routers [${[...originators].join(', ')}] detected local topology change.`
      }
    ];

    const firstSnap = {
      tick: 0,
      ripTable: T,
      ospfTable: O,
      snaps,
      seq,
      rSteps: 0,
      oSteps: 0,
      rDone: originators.size === 0,
      oDone: originators.size === 0,
      rCh: [...originators],
      oCh: [...originators],
      cti: false,
      costClimbTracker: {},
      events: eventLogs,
      ripPackets: 0,
      ospfPackets: originators.size
    };

    setHistory([firstSnap]);
    setCursor(0);
  };

  // Interactive Incremental Toggle Link or Node on current state
  const applyInteractiveEvent = (newFailL, newFailN, affectedLinkIndices, revivedNode, label) => {
    setIsPlaying(false);
    const curSnap = history[cursor];
    let T = deepClone(curSnap.ripTable);
    let O = deepClone(curSnap.ospfTable);
    let snaps = deepClone(curSnap.snaps);
    let seq = deepClone(curSnap.seq);

    const originators = new Set();
    affectedLinkIndices.forEach((i) => {
      [links[i].a, links[i].b].forEach((x) => {
        if (!newFailN.has(x)) originators.add(x);
      });
    });
    if (revivedNode && !newFailN.has(revivedNode)) {
      originators.add(revivedNode);
    }

    // RIP: drop routes using dead next hops
    nodes.forEach((n) => {
      if (newFailN.has(n)) {
        nodes.forEach((d) => {
          T[n][d] = { c: d === n ? 0 : INF, n: null };
        });
        return;
      }
      const activeNbrs = getNeighbors(nodes, links, n, newFailL, newFailN);
      nodes.forEach((d) => {
        const e = T[n][d];
        if (e.n && !activeNbrs.some((x) => x.v === e.n)) {
          T[n][d] = { c: INF, n: null };
        }
      });
    });

    if (revivedNode) {
      nodes.forEach((d) => {
        T[revivedNode][d] = { c: d === revivedNode ? 0 : INF, n: null };
      });
    }

    // OSPF: originate new LSA
    snaps.push({ fl: [...newFailL], fn: [...newFailN] });
    const k = snaps.length - 1;
    originators.forEach((o) => {
      seq[o] = k;
      O[o] = runDijkstra(o, nodes, links, snaps[k]);
    });

    setFailedLinks(new Set(newFailL));
    setFailedNodes(new Set(newFailN));
    setLastScenarioName(label);

    const resetSnap = {
      tick: 0,
      ripTable: T,
      ospfTable: O,
      snaps,
      seq,
      rSteps: 0,
      oSteps: 0,
      rDone: originators.size === 0,
      oDone: originators.size === 0,
      rCh: [...originators],
      oCh: [...originators],
      cti: false,
      costClimbTracker: {},
      events: [
        {
          tick: 0,
          type: 'ALERT',
          text: `${label} — Affected neighbor routers [${[...originators].join(', ') || 'None'}] triggered.`
        }
      ],
      ripPackets: 0,
      ospfPackets: originators.size
    };

    setHistory([resetSnap]);
    setCursor(0);
  };

  const toggleLinkFailure = (i) => {
    const nextFL = new Set(failedLinks);
    const wasDown = nextFL.has(i);
    if (wasDown) nextFL.delete(i);
    else nextFL.add(i);
    const l = links[i];
    applyInteractiveEvent(
      nextFL,
      failedNodes,
      [i],
      null,
      `${wasDown ? 'Restored' : 'Failed'} Link ${l.a}–${l.b}`
    );
  };

  const toggleNodeFailure = (nodeId) => {
    const nextFN = new Set(failedNodes);
    const wasDown = nextFN.has(nodeId);
    if (wasDown) nextFN.delete(nodeId);
    else nextFN.add(nodeId);

    const aff = [];
    links.forEach((l, i) => {
      if ((l.a === nodeId || l.b === nodeId) && !failedLinks.has(i)) {
        aff.push(i);
      }
    });
    applyInteractiveEvent(
      failedLinks,
      nextFN,
      aff,
      wasDown ? nodeId : null,
      `${wasDown ? 'Restored' : 'Failed'} Router Node ${nodeId}`
    );
  };

  // Compute next simulation tick from a snapshot
  const computeNextSnap = (prevSnap) => {
    if (prevSnap.rDone && prevSnap.oDone) return null;

    const nextTickNum = prevSnap.tick + 1;
    let T = deepClone(prevSnap.ripTable);
    let O = deepClone(prevSnap.ospfTable);
    const snaps = deepClone(prevSnap.snaps);
    const seq = deepClone(prevSnap.seq);
    const tracker = deepClone(prevSnap.costClimbTracker);

    let rSteps = prevSnap.rSteps;
    let oSteps = prevSnap.oSteps;
    let rDone = prevSnap.rDone;
    let oDone = prevSnap.oDone;
    let rCh = [];
    let oCh = [];
    let cti = prevSnap.cti;
    let ripPackets = prevSnap.ripPackets;
    let ospfPackets = prevSnap.ospfPackets;
    const newEvents = [];

    // 1. Advance RIP one Bellman-Ford round
    if (!rDone) {
      const { nextTable, changedNodes, packetEvents, ctiDetected } = runRipRound(
        T,
        nodes,
        links,
        failedLinks,
        failedNodes,
        rmode,
        tracker
      );
      T = nextTable;
      if (ctiDetected) cti = true;
      if (changedNodes.size > 0) {
        rSteps++;
        rCh = [...changedNodes];
        ripPackets += packetEvents.length;
        const summary = packetEvents
          .slice(0, 4)
          .map((p) => `${p.to}[${p.dest}]=${p.newCost >= INF ? '∞' : p.newCost} via ${p.nextHop || '–'}`)
          .join(', ');
        newEvents.push({
          tick: nextTickNum,
          type: 'RIP',
          text: `RIP Round ${rSteps}: Routers [${rCh.join(', ')}] updated tables (${packetEvents.length} route entries changed: ${summary}${packetEvents.length > 4 ? '…' : ''}).`
        });
      } else {
        rDone = true;
        rCh = [];
        newEvents.push({
          tick: nextTickNum,
          type: 'RIP_OK',
          text: `RIP converged after ${rSteps} update round(s) (${formatTime(rSteps * 30)}).`
        });
      }
    }

    // 2. Advance OSPF one LSA flood hop
    if (!oDone) {
      const k = snaps.length - 1;
      const nx = new Set();
      nodes.forEach((n) => {
        if (seq[n] === k && !failedNodes.has(n)) {
          getNeighbors(nodes, links, n, failedLinks, failedNodes).forEach(({ v }) => {
            if (seq[v] < k) nx.add(v);
          });
        }
      });

      if (nx.size > 0) {
        oSteps++;
        oCh = [...nx];
        ospfPackets += nx.size;
        nx.forEach((v) => {
          seq[v] = k;
          O[v] = runDijkstra(v, nodes, links, snaps[k]);
        });
        newEvents.push({
          tick: nextTickNum,
          type: 'OSPF',
          text: `OSPF Hop ${oSteps}: LSA flooded to [${oCh.join(', ')}]; each executed Dijkstra SPF immediately.`
        });
      } else {
        oDone = true;
        oCh = [];
        newEvents.push({
          tick: nextTickNum,
          type: 'OSPF_OK',
          text: `OSPF LSDB synchronized across all reachable routers in ${oSteps} flood hop(s).`
        });
      }
    }

    return {
      tick: nextTickNum,
      ripTable: T,
      ospfTable: O,
      snaps,
      seq,
      rSteps,
      oSteps,
      rDone,
      oDone,
      rCh,
      oCh,
      cti,
      costClimbTracker: tracker,
      events: [...prevSnap.events, ...newEvents],
      ripPackets,
      ospfPackets
    };
  };

  // Step Forward
  const handleStepForward = () => {
    if (cursor < history.length - 1) {
      setCursor(cursor + 1);
      return true;
    }
    const curSnap = history[cursor];
    const nextSnap = computeNextSnap(curSnap);
    if (!nextSnap) {
      setIsPlaying(false);
      return false;
    }
    const updated = [...history, nextSnap];
    setHistory(updated);
    setCursor(updated.length - 1);
    if (nextSnap.rDone && nextSnap.oDone) {
      setIsPlaying(false);
      return false;
    }
    return true;
  };

  // Step Backward
  const handleStepBack = () => {
    setIsPlaying(false);
    if (cursor > 0) setCursor(cursor - 1);
  };

  // Run to Convergence
  const handleRunToConvergence = () => {
    setIsPlaying(false);
    let tempHist = [...history];
    let cur = tempHist[tempHist.length - 1];
    let guard = 0;
    while (!(cur.rDone && cur.oDone) && guard < 80) {
      const nx = computeNextSnap(cur);
      if (!nx) break;
      tempHist.push(nx);
      cur = nx;
      guard++;
    }
    setHistory(tempHist);
    setCursor(tempHist.length - 1);
  };

  // Auto-play timer effect
  useEffect(() => {
    if (!isPlaying) return;
    const timer = setInterval(() => {
      setHistory((prevHist) => {
        const curSnap = prevHist[prevHist.length - 1];
        if (curSnap.rDone && curSnap.oDone) {
          setIsPlaying(false);
          return prevHist;
        }
        const nextSnap = computeNextSnap(curSnap);
        if (!nextSnap) {
          setIsPlaying(false);
          return prevHist;
        }
        setCursor(prevHist.length);
        if (nextSnap.rDone && nextSnap.oDone) {
          setIsPlaying(false);
        }
        return [...prevHist, nextSnap];
      });
    }, playSpeedMs);
    return () => clearInterval(timer);
  }, [isPlaying, playSpeedMs, failedLinks, failedNodes, rmode, nodes, links]);

  // Load Topology Preset
  const handleLoadTopology = (key) => {
    const p = TOPOLOGY_PRESETS[key];
    if (!p) return;
    setPresetKey(key);
    const newNodes = [...p.nodes];
    const newPos = deepClone(p.positions);
    const newLinks = deepClone(p.links);
    setNodes(newNodes);
    setPositions(newPos);
    setLinks(newLinks);
    if (!newNodes.includes(srcNode)) setSrcNode(newNodes[0]);
    if (!newNodes.includes(dstNode)) setDstNode(newNodes[newNodes.length - 1]);
    initializeSimulation(newNodes, newLinks, new Set(), new Set(), `Loaded ${p.name}`);
  };

  // Preset Failure Scenarios
  const runPresetFailNodeD = () => {
    const p = TOPOLOGY_PRESETS.mesh6;
    setPresetKey('mesh6');
    setNodes([...p.nodes]);
    setPositions(deepClone(p.positions));
    setLinks(deepClone(p.links));
    setSrcNode('B');
    setDstNode('D');
    triggerFailureFromBaseline(
      p.nodes,
      p.links,
      new Set(),
      new Set(['D']),
      rmode,
      'Preset: Node D Crash (Count-to-Infinity Scenario)'
    );
  };

  const runPresetFailLinkCD = () => {
    const p = TOPOLOGY_PRESETS.mesh6;
    setPresetKey('mesh6');
    setNodes([...p.nodes]);
    setPositions(deepClone(p.positions));
    setLinks(deepClone(p.links));
    setSrcNode('B');
    setDstNode('D');
    triggerFailureFromBaseline(
      p.nodes,
      p.links,
      new Set([2]), // Link C-D
      new Set(),
      rmode,
      'Preset: Link C–D Cut (Fast Reroute vs Bellman-Ford Hunt)'
    );
  };

  const runPresetLinearCountToInfinity = () => {
    const p = TOPOLOGY_PRESETS.linear4;
    setPresetKey('linear4');
    setNodes([...p.nodes]);
    setPositions(deepClone(p.positions));
    setLinks(deepClone(p.links));
    setSrcNode('A');
    setDstNode('D');
    triggerFailureFromBaseline(
      p.nodes,
      p.links,
      new Set([2]), // Link C-D in A-B-C-D chain
      new Set(),
      rmode,
      'Preset: Linear Chain Link C–D Cut (Pure 2-Hop Ping-Pong Loop)'
    );
  };

  // Custom Topology Builder Handlers on SVG Canvas
  const handleSvgClick = (e, svgRef) => {
    if (clickMode !== 'addNode') return;
    if (e.target.closest('[data-node]') || e.target.closest('[data-link]')) return;
    if (nodes.length >= 10) return;

    const svg = svgRef.current;
    if (!svg) return;
    const pt = svg.createSVGPoint();
    pt.x = e.clientX;
    pt.y = e.clientY;
    const svgP = pt.matrixTransform(svg.getScreenCTM().inverse());
    const x = Math.max(30, Math.min(420, Math.round(svgP.x)));
    const y = Math.max(30, Math.min(280, Math.round(svgP.y)));

    const alphabet = 'ABCDEFGHIJ'.split('');
    const nextLetter = alphabet.find((ch) => !nodes.includes(ch));
    if (!nextLetter) return;

    const nextNodes = [...nodes, nextLetter];
    const nextPos = { ...positions, [nextLetter]: [x, y] };
    setNodes(nextNodes);
    setPositions(nextPos);
    initializeSimulation(nextNodes, links, new Set(), new Set(), `Added Router ${nextLetter}`);
  };

  const handleNodeInteraction = (nodeId) => {
    if (clickMode === 'node') {
      toggleNodeFailure(nodeId);
    } else if (clickMode === 'addLink') {
      if (!linkStartNode) {
        setLinkStartNode(nodeId);
      } else if (linkStartNode === nodeId) {
        setLinkStartNode(null);
      } else {
        const exists = links.some(
          (l) =>
            (l.a === linkStartNode && l.b === nodeId) ||
            (l.a === nodeId && l.b === linkStartNode)
        );
        if (!exists) {
          const nextLinks = [
            ...links,
            { a: linkStartNode, b: nodeId, w: Number(newLinkWeight) || 1 }
          ];
          setLinks(nextLinks);
          initializeSimulation(
            nodes,
            nextLinks,
            new Set(),
            new Set(),
            `Added Link ${linkStartNode}–${nodeId} (weight ${newLinkWeight})`
          );
        }
        setLinkStartNode(null);
      }
    } else if (clickMode === 'delete') {
      if (nodes.length <= 2) return;
      const nextNodes = nodes.filter((n) => n !== nodeId);
      const nextLinks = links.filter((l) => l.a !== nodeId && l.b !== nodeId);
      const nextPos = { ...positions };
      delete nextPos[nodeId];
      setNodes(nextNodes);
      setLinks(nextLinks);
      setPositions(nextPos);
      if (srcNode === nodeId) setSrcNode(nextNodes[0]);
      if (dstNode === nodeId) setDstNode(nextNodes[nextNodes.length - 1]);
      initializeSimulation(nextNodes, nextLinks, new Set(), new Set(), `Removed Router ${nodeId}`);
    } else {
      setSrcNode(nodeId);
    }
  };

  const handleLinkInteraction = (linkIdx) => {
    if (clickMode === 'link') {
      toggleLinkFailure(linkIdx);
    } else if (clickMode === 'weight') {
      const nextLinks = deepClone(links);
      nextLinks[linkIdx].w = (nextLinks[linkIdx].w % 5) + 1;
      setLinks(nextLinks);
      initializeSimulation(
        nodes,
        nextLinks,
        failedLinks,
        failedNodes,
        `Updated Link ${nextLinks[linkIdx].a}–${nextLinks[linkIdx].b} weight to ${nextLinks[linkIdx].w}`
      );
    } else if (clickMode === 'delete') {
      const l = links[linkIdx];
      const nextLinks = links.filter((_, idx) => idx !== linkIdx);
      setLinks(nextLinks);
      initializeSimulation(nodes, nextLinks, new Set(), new Set(), `Deleted Link ${l.a}–${l.b}`);
    }
  };

  // Dragging nodes on SVG
  const handleMouseMoveSvg = (e, svgRef) => {
    if (!draggingNode || clickMode !== 'drag') return;
    const svg = svgRef.current;
    if (!svg) return;
    const pt = svg.createSVGPoint();
    pt.x = e.clientX;
    pt.y = e.clientY;
    const svgP = pt.matrixTransform(svg.getScreenCTM().inverse());
    const x = Math.max(25, Math.min(425, Math.round(svgP.x)));
    const y = Math.max(25, Math.min(285, Math.round(svgP.y)));
    setPositions((prev) => ({ ...prev, [draggingNode]: [x, y] }));
  };

  // Current active snapshot from history
  const curSnap = history[cursor] || history[0];

  // Derived metrics for current snapshot
  const ripTrace = useMemo(() => {
    if (!curSnap) return { path: [], st: 'initializing' };
    return traceForwardingPath(
      curSnap.ripTable,
      nodes,
      links,
      failedLinks,
      failedNodes,
      srcNode,
      dstNode
    );
  }, [curSnap, nodes, links, failedLinks, failedNodes, srcNode, dstNode]);

  const ospfTrace = useMemo(() => {
    if (!curSnap) return { path: [], st: 'initializing' };
    return traceForwardingPath(
      curSnap.ospfTable,
      nodes,
      links,
      failedLinks,
      failedNodes,
      srcNode,
      dstNode
    );
  }, [curSnap, nodes, links, failedLinks, failedNodes, srcNode, dstNode]);

  const rTimeSec = (curSnap?.rSteps || 0) * 30;
  const oTimeSec =
    (curSnap?.oSteps || 0) * 0.1 +
    ((curSnap?.oSteps || 0) > 0 || !curSnap?.oDone || (curSnap?.snaps?.length || 1) > 1 ? 0.2 : 0);

  // Benchmark results for the 3-Way Comparison Lab tab
  const benchmarkData = useMemo(() => {
    const targetFL = failedLinks.size > 0 || failedNodes.size > 0 ? failedLinks : new Set();
    const targetFN =
      failedLinks.size > 0 || failedNodes.size > 0 ? failedNodes : new Set([nodes[nodes.length - 1]]);
    return runFullBenchmark(nodes, links, new Set(), new Set(), targetFL, targetFN);
  }, [nodes, links, failedLinks, failedNodes]);

  // Render SVG Topology Graph for a protocol
  const renderTopologySvg = (protocol, table, changedList, traceObj, svgRef) => {
    if (!curSnap) return null;
    const changedSet = new Set(changedList);
    const pathEdges = new Set();
    for (let i = 0; i < traceObj.path.length - 1; i++) {
      pathEdges.add([traceObj.path[i], traceObj.path[i + 1]].sort().join('-'));
    }
    const latestSnapIdx = curSnap.snaps.length - 1;

    return (
      <svg
        ref={svgRef}
        viewBox="0 0 450 310"
        className={`w-full h-auto rounded-xl border select-none transition-colors ${
          darkMode ? 'bg-slate-950/70 border-slate-800' : 'bg-slate-50 border-slate-200'
        }`}
        onClick={(e) => handleSvgClick(e, svgRef)}
        onMouseMove={(e) => handleMouseMoveSvg(e, svgRef)}
        onMouseUp={() => setDraggingNode(null)}
        onMouseLeave={() => setDraggingNode(null)}
      >
        <defs>
          <filter id={`glow-${protocol}`} x="-20%" y="-20%" width="140%" height="140%">
            <feGaussianBlur stdDeviation="3" result="blur" />
            <feComposite in="SourceGraphic" in2="blur" operator="over" />
          </filter>
        </defs>

        {/* Grid lines for visual precision */}
        <g stroke={darkMode ? '#1e293b' : '#e2e8f0'} strokeWidth="0.5">
          {[60, 120, 180, 240].map((y) => (
            <line key={`gy-${y}`} x1="0" y1={y} x2="450" y2={y} />
          ))}
          {[90, 180, 270, 360].map((x) => (
            <line key={`gx-${x}`} x1={x} y1="0" x2={x} y2="310" />
          ))}
        </g>

        {/* Network Links */}
        {links.map((l, i) => {
          const posA = positions[l.a] || [50, 50];
          const posB = positions[l.b] || [100, 100];
          const dead = !isLinkOperational(links, i, failedLinks, failedNodes);
          const edgeKey = [l.a, l.b].sort().join('-');
          const onActivePath = !dead && pathEdges.has(edgeKey);
          const isLoopPath = onActivePath && traceObj.st.startsWith('routing loop');

          const strokeColor = dead
            ? '#ef4444'
            : isLoopPath
            ? '#f59e0b'
            : onActivePath
            ? protocol === 'RIP'
              ? '#8b5cf6'
              : '#10b981'
            : darkMode
            ? '#475569'
            : '#94a3b8';

          const midX = (posA[0] + posB[0]) / 2;
          const midY = (posA[1] + posB[1]) / 2;

          return (
            <g key={`link-${i}`} data-link={i}>
              <line
                x1={posA[0]}
                y1={posA[1]}
                x2={posB[0]}
                y2={posB[1]}
                stroke={strokeColor}
                strokeWidth={onActivePath ? 4.5 : 2.5}
                strokeDasharray={dead ? '6 5' : undefined}
              />
              {/* Animated pulse along active update edges */}
              {!dead && (changedSet.has(l.a) || changedSet.has(l.b)) && (
                <circle r="4" fill={protocol === 'RIP' ? '#f59e0b' : '#38bdf8'}>
                  <animateMotion
                    dur="0.9s"
                    repeatCount="indefinite"
                    path={`M${posA[0]},${posA[1]} L${posB[0]},${posB[1]}`}
                  />
                </circle>
              )}
              {/* Invisible thick click target */}
              <line
                x1={posA[0]}
                y1={posA[1]}
                x2={posB[0]}
                y2={posB[1]}
                stroke="transparent"
                strokeWidth="20"
                className="cursor-pointer"
                onClick={(e) => {
                  e.stopPropagation();
                  handleLinkInteraction(i);
                }}
              />
              {/* Link Weight Badge */}
              <g
                className="cursor-pointer"
                onClick={(e) => {
                  e.stopPropagation();
                  handleLinkInteraction(i);
                }}
              >
                <rect
                  x={midX - 10}
                  y={midY - 10}
                  width="20"
                  height="18"
                  rx="4"
                  fill={darkMode ? '#0f172a' : '#ffffff'}
                  stroke={dead ? '#ef4444' : darkMode ? '#334155' : '#cbd5e1'}
                  strokeWidth="1"
                />
                <text
                  x={midX}
                  y={midY + 3}
                  textAnchor="middle"
                  fontSize="11"
                  fontWeight="700"
                  fill={dead ? '#ef4444' : darkMode ? '#cbd5e1' : '#334155'}
                >
                  {l.w}
                </text>
              </g>
            </g>
          );
        })}

        {/* Router Nodes */}
        {nodes.map((n) => {
          const [x, y] = positions[n] || [50, 50];
          const dead = failedNodes.has(n);
          const changed = changedSet.has(n);
          const ospfInformed = protocol === 'OSPF' ? curSnap.seq[n] === latestSnapIdx : true;

          let fill = '#10b981'; // Healthy green
          if (dead) fill = '#ef4444'; // Dead red
          else if (changed) fill = '#f59e0b'; // Updating amber
          else if (protocol === 'OSPF' && !ospfInformed) fill = '#64748b'; // Uninformed grey

          const isSrc = n === srcNode;
          const isDst = n === dstNode;
          const isLinkOrigin = linkStartNode === n;

          const routeToDst = table[n]?.[dstNode];
          const costBadge = dead
            ? 'DOWN'
            : n === dstNode
            ? 'DST'
            : routeToDst
            ? routeToDst.c >= INF
              ? '∞'
              : `c:${routeToDst.c}`
            : '';

          return (
            <g
              key={`node-${n}`}
              data-node={n}
              className="cursor-pointer"
              onMouseDown={(e) => {
                if (clickMode === 'drag') {
                  e.stopPropagation();
                  setDraggingNode(n);
                }
              }}
              onClick={(e) => {
                e.stopPropagation();
                if (clickMode !== 'drag') handleNodeInteraction(n);
              }}
            >
              {/* Outer selection ring for Source or Destination */}
              {(isSrc || isDst || isLinkOrigin) && (
                <circle
                  cx={x}
                  cy={y}
                  r="23"
                  fill="none"
                  stroke={isLinkOrigin ? '#38bdf8' : isSrc ? '#a855f7' : '#3b82f6'}
                  strokeWidth="2.5"
                  strokeDasharray={isDst ? '4 2' : undefined}
                />
              )}

              <circle
                cx={x}
                cy={y}
                r="17"
                fill={fill}
                stroke={darkMode ? '#0f172a' : '#ffffff'}
                strokeWidth="2.5"
              />

              <text
                x={x}
                y={y + 5}
                textAnchor="middle"
                fontSize="13"
                fontWeight="800"
                fill="#ffffff"
              >
                {dead ? '✕' : n}
              </text>

              {/* Cost-to-Destination mini pill under router */}
              <rect
                x={x - 18}
                y={y + 20}
                width="36"
                height="14"
                rx="4"
                fill={darkMode ? '#1e293b' : '#f1f5f9'}
                stroke={darkMode ? '#334155' : '#cbd5e1'}
                strokeWidth="0.8"
              />
              <text
                x={x}
                y={y + 30}
                textAnchor="middle"
                fontSize="9.5"
                fontWeight="700"
                fill={
                  dead || (routeToDst && routeToDst.c >= INF)
                    ? '#ef4444'
                    : darkMode
                    ? '#e2e8f0'
                    : '#1e293b'
                }
              >
                {costBadge}
              </text>
            </g>
          );
        })}
      </svg>
    );
  };

  // Render Cost History Line Chart
  const renderCostChart = (protocolKey, colorHex) => {
    const W = 380;
    const H = 98;
    const P = 28;
    const visibleHistory = history.slice(0, cursor + 1);
    const values = visibleHistory.map((h) => {
      const tb = protocolKey === 'rip' ? h.ripTable : h.ospfTable;
      return tb[srcNode]?.[dstNode]?.c ?? INF;
    });

    const maxTicks = Math.max(8, values.length - 1);
    const X = (i) => P + ((W - P - 10) * i) / maxTicks;
    const Y = (c) => H - 16 - ((H - 28) * Math.min(c, INF)) / INF;

    return (
      <div className="mt-3">
        <div className="flex items-center justify-between text-xs mb-1">
          <span className={darkMode ? 'text-slate-400' : 'text-slate-500'}>
            Metric Cost ({srcNode} → {dstNode}) per Simulation Tick
          </span>
          <span className="font-mono font-semibold" style={{ color: colorHex }}>
            Current: {formatCost(values[values.length - 1])}
          </span>
        </div>
        <svg
          viewBox={`0 0 ${W} ${H}`}
          className={`w-full h-auto rounded-lg border ${
            darkMode ? 'bg-slate-950/60 border-slate-800' : 'bg-slate-50 border-slate-200'
          }`}
        >
          {/* Infinity ceiling dashed line */}
          <line
            x1={P}
            x2={W - 6}
            y1={Y(INF)}
            y2={Y(INF)}
            stroke="#ef4444"
            strokeDasharray="3 3"
            strokeWidth="1"
          />
          <text x="4" y={Y(INF) + 4} fontSize="9.5" fill="#ef4444" fontWeight="700">
            ∞(16)
          </text>
          <text x="8" y={H - 12} fontSize="9.5" fill={darkMode ? '#64748b' : '#94a3b8'}>
            0
          </text>

          {/* Cost Polyline */}
          <polyline
            fill="none"
            stroke={colorHex}
            strokeWidth="2.5"
            points={values.map((c, i) => `${X(i)},${Y(c)}`).join(' ')}
          />

          {/* Data Points */}
          {values.map((c, i) => (
            <g key={i}>
              <circle
                cx={X(i)}
                cy={Y(c)}
                r={i === values.length - 1 ? 4 : 2.8}
                fill={c >= INF ? '#ef4444' : colorHex}
              />
              {values.length <= 14 && (
                <text
                  x={X(i)}
                  y={Y(c) - 6}
                  textAnchor="middle"
                  fontSize="8.5"
                  fill={darkMode ? '#cbd5e1' : '#334155'}
                >
                  {c >= INF ? '∞' : c}
                </text>
              )}
            </g>
          ))}
        </svg>
      </div>
    );
  };

  // Render Routing Table for selected node (or all nodes)
  const renderRoutingTable = (protocolKey) => {
    if (!curSnap) return null;
    const tb = protocolKey === 'rip' ? curSnap.ripTable : curSnap.ospfTable;
    const prevTb =
      cursor > 0
        ? protocolKey === 'rip'
          ? history[cursor - 1].ripTable
          : history[cursor - 1].ospfTable
        : null;

    if (failedNodes.has(srcNode)) {
      return (
        <div className="my-3 p-3 rounded-lg bg-red-500/10 border border-red-500/30 text-red-400 text-xs flex items-center gap-2">
          <XCircle className="w-4 h-4 shrink-0" />
          <span>Router {srcNode} is currently disabled (powered off). All local routes flushed.</span>
        </div>
      );
    }

    return (
      <div className="mt-3 overflow-x-auto">
        <div className="flex items-center justify-between mb-1.5">
          <span className="text-xs font-semibold uppercase tracking-wider text-purple-400">
            Routing Table at Router {srcNode}
          </span>
          <span className="text-[11px] text-slate-400">Amber = changed this tick</span>
        </div>
        <table className="w-full text-xs border-collapse">
          <thead>
            <tr
              className={`border-b ${
                darkMode ? 'border-slate-800 text-slate-400' : 'border-slate-200 text-slate-500'
              }`}
            >
              <th className="py-1.5 px-2 text-left">Dest</th>
              <th className="py-1.5 px-2 text-left">Metric Cost</th>
              <th className="py-1.5 px-2 text-left">Next Hop</th>
              <th className="py-1.5 px-2 text-left">Route Status</th>
            </tr>
          </thead>
          <tbody>
            {nodes
              .filter((d) => d !== srcNode)
              .map((d) => {
                const entry = tb[srcNode]?.[d] || { c: INF, n: null };
                const prevEntry = prevTb?.[srcNode]?.[d];
                const changed =
                  prevEntry && (prevEntry.c !== entry.c || prevEntry.n !== entry.n);
                const costClimbed = prevEntry && entry.c > prevEntry.c && prevEntry.c < INF;

                return (
                  <tr
                    key={d}
                    className={`border-b transition-colors ${
                      d === dstNode
                        ? darkMode
                          ? 'bg-purple-500/10 border-slate-800'
                          : 'bg-purple-50 border-slate-200'
                        : darkMode
                        ? 'border-slate-800/70'
                        : 'border-slate-100'
                    }`}
                  >
                    <td className="py-1.5 px-2 font-bold">
                      {d} {d === dstNode && <span className="text-[10px] text-purple-400">(Target)</span>}
                    </td>
                    <td
                      className={`py-1.5 px-2 font-mono ${
                        changed
                          ? 'text-amber-400 font-bold'
                          : entry.c >= INF
                          ? 'text-red-400'
                          : ''
                      }`}
                    >
                      {formatCost(entry.c)}
                      {costClimbed && (
                        <span className="ml-1 text-[10px] px-1 py-0.5 rounded bg-red-500/20 text-red-400">
                          ↑ climbing
                        </span>
                      )}
                    </td>
                    <td
                      className={`py-1.5 px-2 font-mono ${
                        changed ? 'text-amber-400 font-bold' : ''
                      }`}
                    >
                      {entry.n || '–'}
                    </td>
                    <td className="py-1.5 px-2">
                      {entry.c >= INF ? (
                        <span className="text-[11px] text-red-400">Unreachable</span>
                      ) : changed ? (
                        <span className="text-[11px] text-amber-400">Updated</span>
                      ) : (
                        <span className="text-[11px] text-emerald-400">Active</span>
                      )}
                    </td>
                  </tr>
                );
              })}
          </tbody>
        </table>
      </div>
    );
  };

  return (
    <div
      className={`min-h-screen transition-colors ${
        darkMode ? 'bg-slate-950 text-slate-100' : 'bg-slate-100 text-slate-900'
      }`}
    >
      {/* =================================================================== */}
      {/* TOP ACADEMIC PROJECT HEADER                                         */}
      {/* =================================================================== */}
      <header
        className={`border-b sticky top-0 z-30 backdrop-blur-md ${
          darkMode ? 'bg-slate-900/90 border-slate-800' : 'bg-white/90 border-slate-200'
        }`}
      >
        <div className="max-w-7xl mx-auto px-4 py-3 flex flex-wrap items-center justify-between gap-3">
          <div className="flex items-center gap-3">
            <div className="w-10 h-10 rounded-xl bg-gradient-to-br from-purple-600 to-indigo-600 flex items-center justify-center text-white shadow-lg shadow-purple-600/20">
              <Network className="w-6 h-6" />
            </div>
            <div>
              <div className="flex items-center gap-2 flex-wrap">
                <h1 className="text-lg font-bold tracking-tight">
                  Visualizing RIP vs OSPF Convergence Under Network Failures
                </h1>
                <span className="text-[11px] font-semibold px-2 py-0.5 rounded-full bg-purple-500/15 text-purple-400 border border-purple-500/30">
                  VIT Computer Networks Project
                </span>
              </div>
              <div
                className={`text-xs flex flex-wrap items-center gap-x-4 gap-y-1 mt-0.5 ${
                  darkMode ? 'text-slate-400' : 'text-slate-600'
                }`}
              >
                <span className="flex items-center gap-1">
                  <Users className="w-3.5 h-3.5 text-purple-400" />
                  <b>Team:</b> Raamviyhash.R (24BYB0027), Sarvesh R (24BYB0081), Rahul Varshan S S (24BYB0084)
                </span>
                <span className="flex items-center gap-1">
                  <GraduationCap className="w-3.5 h-3.5 text-emerald-400" />
                  <b>Faculty Guide:</b> Prof. Aaseegha M D
                </span>
              </div>
            </div>
          </div>

          {/* Navigation Tabs & Theme Toggle */}
          <div className="flex items-center gap-2">
            <div
              className={`inline-flex rounded-xl p-1 border ${
                darkMode ? 'bg-slate-950 border-slate-800' : 'bg-slate-100 border-slate-200'
              }`}
            >
              <button
                onClick={() => setActiveTab('simulator')}
                className={`flex items-center gap-1.5 px-3 py-1.5 rounded-lg text-xs font-semibold transition-all ${
                  activeTab === 'simulator'
                    ? 'bg-purple-600 text-white shadow'
                    : darkMode
                    ? 'text-slate-400 hover:text-white'
                    : 'text-slate-600 hover:text-slate-900'
                }`}
              >
                <Activity className="w-3.5 h-3.5" />
                Interactive Simulator
              </button>
              <button
                onClick={() => setActiveTab('benchmark')}
                className={`flex items-center gap-1.5 px-3 py-1.5 rounded-lg text-xs font-semibold transition-all ${
                  activeTab === 'benchmark'
                    ? 'bg-purple-600 text-white shadow'
                    : darkMode
                    ? 'text-slate-400 hover:text-white'
                    : 'text-slate-600 hover:text-slate-900'
                }`}
              >
                <BarChart3 className="w-3.5 h-3.5" />
                4-Way Protocol Benchmark
              </button>
              <button
                onClick={() => setActiveTab('reference')}
                className={`flex items-center gap-1.5 px-3 py-1.5 rounded-lg text-xs font-semibold transition-all ${
                  activeTab === 'reference'
                    ? 'bg-purple-600 text-white shadow'
                    : darkMode
                    ? 'text-slate-400 hover:text-white'
                    : 'text-slate-600 hover:text-slate-900'
                }`}
              >
                <BookOpen className="w-3.5 h-3.5" />
                RFC & Theory Guide
              </button>
            </div>

            <button
              onClick={() => setDarkMode(!darkMode)}
              className={`p-2 rounded-xl border transition-colors ${
                darkMode
                  ? 'bg-slate-900 border-slate-800 text-amber-400 hover:bg-slate-800'
                  : 'bg-white border-slate-200 text-slate-700 hover:bg-slate-50'
              }`}
              title="Toggle Dark/Light Theme"
            >
              {darkMode ? <Sun className="w-4 h-4" /> : <Moon className="w-4 h-4" />}
            </button>
          </div>
        </div>
      </header>

      {/* =================================================================== */}
      {/* TAB 1: INTERACTIVE SIMULATOR                                        */}
      {/* =================================================================== */}
      {activeTab === 'simulator' && (
        <main className="max-w-7xl mx-auto px-4 py-4 space-y-4">
          {/* Top Control Bar: Topology Presets, Click Mode, RIP Mode, Playback */}
          <div
            className={`rounded-2xl border p-3.5 shadow-sm space-y-3 ${
              darkMode ? 'bg-slate-900/90 border-slate-800' : 'bg-white border-slate-200'
            }`}
          >
            <div className="flex flex-wrap items-end justify-between gap-3">
              {/* Selectors */}
              <div className="flex flex-wrap items-end gap-3">
                {/* Topology Selector */}
                <label className="flex flex-col gap-1 text-xs">
                  <span className={darkMode ? 'text-slate-400' : 'text-slate-500'}>
                    Topology Preset
                  </span>
                  <select
                    value={presetKey}
                    onChange={(e) => handleLoadTopology(e.target.value)}
                    className={`rounded-lg px-2.5 py-1.5 text-xs font-medium border outline-none ${
                      darkMode
                        ? 'bg-slate-950 border-slate-700 text-slate-100'
                        : 'bg-slate-50 border-slate-300 text-slate-900'
                    }`}
                  >
                    {Object.entries(TOPOLOGY_PRESETS).map(([k, v]) => (
                      <option key={k} value={k}>
                        {v.name}
                      </option>
                    ))}
                  </select>
                </label>

                {/* Graph Click Action */}
                <label className="flex flex-col gap-1 text-xs">
                  <span className={darkMode ? 'text-slate-400' : 'text-slate-500'}>
                    Canvas Click Action
                  </span>
                  <select
                    value={clickMode}
                    onChange={(e) => {
                      setClickMode(e.target.value);
                      setLinkStartNode(null);
                    }}
                    className={`rounded-lg px-2.5 py-1.5 text-xs font-medium border outline-none ${
                      darkMode
                        ? 'bg-slate-950 border-slate-700 text-slate-100'
                        : 'bg-slate-50 border-slate-300 text-slate-900'
                    }`}
                  >
                    <option value="link">⚡ Fail / Restore Link</option>
                    <option value="node">🛑 Fail / Restore Router Node</option>
                    <option value="weight">⚖️ Cycle Link Weight (1–5)</option>
                    <option value="drag">✋ Drag / Reposition Nodes</option>
                    <option value="addNode">➕ Add Router Node (Click Canvas)</option>
                    <option value="addLink">🔗 Add Link (Click 2 Nodes)</option>
                    <option value="delete">🗑️ Delete Node or Link</option>
                  </select>
                </label>

                {clickMode === 'addLink' && (
                  <label className="flex flex-col gap-1 text-xs">
                    <span className="text-sky-400">New Link Cost</span>
                    <input
                      type="number"
                      min="1"
                      max="15"
                      value={newLinkWeight}
                      onChange={(e) => setNewLinkWeight(e.target.value)}
                      className={`w-16 rounded-lg px-2 py-1.5 text-xs border ${
                        darkMode
                          ? 'bg-slate-950 border-slate-700 text-white'
                          : 'bg-slate-50 border-slate-300 text-slate-900'
                      }`}
                    />
                  </label>
                )}

                {/* RIP Loop Prevention */}
                <label className="flex flex-col gap-1 text-xs">
                  <span className={darkMode ? 'text-slate-400' : 'text-slate-500'}>
                    RIP Loop Prevention (RFC 2453)
                  </span>
                  <select
                    value={rmode}
                    onChange={(e) => handleRmodeChange(e.target.value)}
                    className={`rounded-lg px-2.5 py-1.5 text-xs font-semibold border outline-none ${
                      darkMode
                        ? 'bg-slate-950 border-purple-500/50 text-purple-300'
                        : 'bg-purple-50 border-purple-300 text-purple-900'
                    }`}
                  >
                    <option value="none">None (Count-to-Infinity Vulnerable)</option>
                    <option value="split">Split Horizon (Omit Reverse Route)</option>
                    <option value="poison">Poison Reverse (Advertise ∞ = 16)</option>
                  </select>
                </label>

                {/* Source & Destination */}
                <label className="flex flex-col gap-1 text-xs">
                  <span className={darkMode ? 'text-slate-400' : 'text-slate-500'}>
                    Source Router
                  </span>
                  <select
                    value={srcNode}
                    onChange={(e) => setSrcNode(e.target.value)}
                    className={`rounded-lg px-2.5 py-1.5 text-xs font-bold border outline-none ${
                      darkMode
                        ? 'bg-slate-950 border-slate-700 text-purple-400'
                        : 'bg-slate-50 border-slate-300 text-purple-700'
                    }`}
                  >
                    {nodes.map((n) => (
                      <option key={n} value={n}>
                        Router {n}
                      </option>
                    ))}
                  </select>
                </label>

                <label className="flex flex-col gap-1 text-xs">
                  <span className={darkMode ? 'text-slate-400' : 'text-slate-500'}>
                    Target Dest
                  </span>
                  <select
                    value={dstNode}
                    onChange={(e) => setDstNode(e.target.value)}
                    className={`rounded-lg px-2.5 py-1.5 text-xs font-bold border outline-none ${
                      darkMode
                        ? 'bg-slate-950 border-slate-700 text-sky-400'
                        : 'bg-slate-50 border-slate-300 text-sky-700'
                    }`}
                  >
                    {nodes.map((n) => (
                      <option key={n} value={n}>
                        Router {n}
                      </option>
                    ))}
                  </select>
                </label>
              </div>

              {/* Simulation Playback Controls */}
              <div className="flex flex-wrap items-center gap-1.5">
                <button
                  onClick={handleStepBack}
                  disabled={cursor === 0}
                  className={`flex items-center gap-1 px-2.5 py-1.5 rounded-lg text-xs font-medium border transition ${
                    cursor === 0
                      ? 'opacity-40 cursor-not-allowed'
                      : darkMode
                      ? 'bg-slate-800 border-slate-700 hover:bg-slate-700'
                      : 'bg-slate-100 border-slate-300 hover:bg-slate-200'
                  }`}
                  title="Step Back 1 Tick"
                >
                  <SkipBack className="w-3.5 h-3.5" />
                  Back
                </button>

                <button
                  onClick={handleStepForward}
                  disabled={curSnap?.rDone && curSnap?.oDone && cursor === history.length - 1}
                  className="flex items-center gap-1 px-3 py-1.5 rounded-lg text-xs font-semibold bg-purple-600 hover:bg-purple-500 text-white shadow transition disabled:opacity-40"
                >
                  <SkipForward className="w-3.5 h-3.5" />
                  Step Tick
                </button>

                <button
                  onClick={() => setIsPlaying(!isPlaying)}
                  disabled={curSnap?.rDone && curSnap?.oDone && cursor === history.length - 1}
                  className={`flex items-center gap-1 px-3 py-1.5 rounded-lg text-xs font-semibold border transition ${
                    isPlaying
                      ? 'bg-amber-500 text-slate-950 border-amber-400'
                      : darkMode
                      ? 'bg-slate-800 border-slate-700 hover:bg-slate-700'
                      : 'bg-slate-100 border-slate-300 hover:bg-slate-200'
                  } disabled:opacity-40`}
                >
                  {isPlaying ? <Pause className="w-3.5 h-3.5" /> : <Play className="w-3.5 h-3.5" />}
                  {isPlaying ? 'Pause' : 'Play'}
                </button>

                <button
                  onClick={handleRunToConvergence}
                  disabled={curSnap?.rDone && curSnap?.oDone}
                  className={`flex items-center gap-1 px-2.5 py-1.5 rounded-lg text-xs font-medium border transition ${
                    darkMode
                      ? 'bg-slate-800 border-slate-700 hover:bg-slate-700'
                      : 'bg-slate-100 border-slate-300 hover:bg-slate-200'
                  } disabled:opacity-40`}
                >
                  <FastForward className="w-3.5 h-3.5" />
                  Run to Convergence
                </button>

                <button
                  onClick={() => handleLoadTopology(presetKey)}
                  className={`flex items-center gap-1 px-2.5 py-1.5 rounded-lg text-xs font-medium border transition ${
                    darkMode
                      ? 'bg-slate-800 border-slate-700 hover:bg-slate-700 text-slate-300'
                      : 'bg-slate-100 border-slate-300 hover:bg-slate-200 text-slate-700'
                  }`}
                >
                  <RotateCcw className="w-3.5 h-3.5" />
                  Reset
                </button>
              </div>
            </div>

            {/* Quick Failure Scenario Presets Row */}
            <div
              className={`pt-2.5 border-t flex flex-wrap items-center justify-between gap-2 text-xs ${
                darkMode ? 'border-slate-800' : 'border-slate-200'
              }`}
            >
              <div className="flex flex-wrap items-center gap-2">
                <span className={`font-semibold ${darkMode ? 'text-slate-400' : 'text-slate-500'}`}>
                  One-Click Failure Demos:
                </span>
                <button
                  onClick={runPresetFailNodeD}
                  className="px-2.5 py-1 rounded-lg bg-red-500/15 text-red-400 border border-red-500/30 hover:bg-red-500/25 font-medium transition"
                >
                  🔥 Fail Node D (6-Node Count-to-Infinity)
                </button>
                <button
                  onClick={runPresetFailLinkCD}
                  className="px-2.5 py-1 rounded-lg bg-amber-500/15 text-amber-400 border border-amber-500/30 hover:bg-amber-500/25 font-medium transition"
                >
                  ✂️ Fail Link C–D (Backup Reroute Comparison)
                </button>
                <button
                  onClick={runPresetLinearCountToInfinity}
                  className="px-2.5 py-1 rounded-lg bg-purple-500/15 text-purple-400 border border-purple-500/30 hover:bg-purple-500/25 font-medium transition"
                >
                  ⛓️ Linear Chain A–B–C–D Tail Drop (Split Horizon Showcase)
                </button>
              </div>

              {/* Timeline scrubber */}
              <div className="flex items-center gap-2">
                <span className="text-slate-400">
                  Tick: <b className="text-purple-400">{curSnap?.tick || 0}</b> /{' '}
                  {history[history.length - 1]?.tick || 0}
                </span>
                <input
                  type="range"
                  min={0}
                  max={Math.max(0, history.length - 1)}
                  value={cursor}
                  onChange={(e) => {
                    setIsPlaying(false);
                    setCursor(Number(e.target.value));
                  }}
                  className="w-24 accent-purple-500 cursor-pointer"
                />
              </div>
            </div>
          </div>

          {/* Quantified Convergence Summary Banner */}
          <div
            className={`rounded-2xl border p-4 flex flex-wrap items-center justify-between gap-4 ${
              curSnap?.cti
                ? darkMode
                  ? 'bg-red-950/30 border-red-500/40'
                  : 'bg-red-50 border-red-300'
                : darkMode
                ? 'bg-slate-900/90 border-slate-800'
                : 'bg-white border-slate-200'
            }`}
          >
            <div className="space-y-1 max-w-3xl">
              <div className="flex items-center gap-2">
                <span className="text-xs font-bold uppercase tracking-wider px-2 py-0.5 rounded bg-purple-500/20 text-purple-400">
                  {lastScenarioName}
                </span>
                {curSnap?.cti && (
                  <span className="text-xs font-bold px-2 py-0.5 rounded bg-red-500/20 text-red-400 border border-red-500/30 flex items-center gap-1">
                    <AlertTriangle className="w-3.5 h-3.5" />
                    Count-to-Infinity Loop Detected in RIP!
                  </span>
                )}
              </div>
              <p className="text-sm leading-relaxed">
                {curSnap?.tick === 0 && (curSnap?.snaps?.length || 1) <= 1 ? (
                  <>
                    <b>Network is converged and stable.</b> Click any link or router node on either
                    topology below to inject a failure, or choose one of the{' '}
                    <b>One-Click Failure Demos</b> above, then press <b>Step Tick</b> or <b>Play</b>.
                  </>
                ) : curSnap?.rDone && curSnap?.oDone ? (
                  <>
                    <b>Convergence Complete:</b> OSPF converged in{' '}
                    <b className="text-emerald-400">
                      {curSnap.oSteps} flood hop{curSnap.oSteps === 1 ? '' : 's'} (~
                      {formatTime(oTimeSec)})
                    </b>{' '}
                    whereas RIP required{' '}
                    <b className="text-purple-400">
                      {curSnap.rSteps} Bellman-Ford round{curSnap.rSteps === 1 ? '' : 's'} (~
                      {formatTime(rTimeSec)})
                    </b>
                    {oTimeSec > 0 && rTimeSec > 0 && (
                      <>
                        {' '}
                        — making OSPF approximately{' '}
                        <b className="text-amber-400">
                          {Math.max(1, Math.round(rTimeSec / oTimeSec))}× faster
                        </b>
                        .
                      </>
                    )}
                  </>
                ) : (
                  <>
                    <b>Simulation in Progress (Tick {curSnap?.tick}):</b> RIP has executed{' '}
                    <b>{curSnap?.rSteps}</b> distance-vector round(s) ({formatTime(rTimeSec)}); OSPF
                    has flooded LSAs across <b>{curSnap?.oSteps}</b> hop(s) ({formatTime(oTimeSec)}).
                  </>
                )}
              </p>
            </div>

            {/* Key Speedup Metrics */}
            <div className="flex items-center gap-4">
              <div className="text-right">
                <div className="text-[11px] text-slate-400">RIP Simulated Time</div>
                <div className="text-lg font-extrabold text-purple-400">{formatTime(rTimeSec)}</div>
              </div>
              <div className="h-8 w-px bg-slate-700" />
              <div className="text-right">
                <div className="text-[11px] text-slate-400">OSPF Simulated Time</div>
                <div className="text-lg font-extrabold text-emerald-400">{formatTime(oTimeSec)}</div>
              </div>
              <div className="h-8 w-px bg-slate-700" />
              <div className="text-right">
                <div className="text-[11px] text-slate-400">OSPF Speed Advantage</div>
                <div className="text-lg font-extrabold text-amber-400">
                  {oTimeSec > 0 && rTimeSec > 0 ? `${Math.round(rTimeSec / oTimeSec)}×` : '—'}
                </div>
              </div>
            </div>
          </div>

          {/* ================================================================= */}
          {/* SIDE-BY-SIDE PROTOCOL CARDS: RIP vs OSPF                          */}
          {/* ================================================================= */}
          <div className="grid grid-cols-1 lg:grid-cols-2 gap-4">
            {/* LEFT CARD: RIP (Bellman-Ford Distance-Vector) */}
            <div
              className={`rounded-2xl border p-4 flex flex-col justify-between ${
                darkMode ? 'bg-slate-900/90 border-slate-800' : 'bg-white border-slate-200'
              }`}
            >
              <div>
                <div className="flex items-start justify-between gap-2 mb-1">
                  <div>
                    <div className="flex items-center gap-2">
                      <h2 className="text-base font-bold">
                        RIP v2 · Bellman-Ford (Distance-Vector)
                      </h2>
                      <span className="text-[11px] px-2 py-0.5 rounded bg-purple-500/15 text-purple-400 font-mono">
                        RFC 2453
                      </span>
                    </div>
                    <p className={`text-xs mt-0.5 ${darkMode ? 'text-slate-400' : 'text-slate-500'}`}>
                      Loop prevention:{' '}
                      <b className="text-purple-400">
                        {{
                          none: 'Disabled (None)',
                          split: 'Split Horizon',
                          poison: 'Poison Reverse'
                        }[rmode]}
                      </b>
                      . Periodic 30s update rounds, ∞ = 16.
                    </p>
                  </div>

                  {/* Status Pill */}
                  <div>
                    {curSnap?.rDone ? (
                      <span className="inline-flex items-center gap-1 px-2.5 py-1 rounded-full text-xs font-semibold bg-emerald-500/15 text-emerald-400 border border-emerald-500/30">
                        <CheckCircle2 className="w-3.5 h-3.5" />
                        {curSnap.tick > 0 || curSnap.rSteps > 0 ? 'Converged' : 'Stable'}
                      </span>
                    ) : (
                      <span className="inline-flex items-center gap-1 px-2.5 py-1 rounded-full text-xs font-semibold bg-amber-500/15 text-amber-400 border border-amber-500/30 animate-pulse">
                        <Activity className="w-3.5 h-3.5" />
                        Updating Vectors…
                      </span>
                    )}
                  </div>
                </div>

                {/* SVG Topology */}
                <div className="my-2">
                  {renderTopologySvg('RIP', curSnap?.ripTable || {}, curSnap?.rCh || [], ripTrace, svgRefRip)}
                </div>

                {/* Metrics Bar */}
                <div
                  className={`grid grid-cols-3 gap-2 p-2.5 rounded-xl border text-center my-2 ${
                    darkMode ? 'bg-slate-950/60 border-slate-800' : 'bg-slate-50 border-slate-200'
                  }`}
                >
                  <div>
                    <div className="text-[11px] text-slate-400">Update Rounds</div>
                    <div className="text-base font-extrabold text-purple-400">
                      {curSnap?.rSteps || 0}
                    </div>
                  </div>
                  <div>
                    <div className="text-[11px] text-slate-400">Est. Convergence Time</div>
                    <div className="text-base font-extrabold">{formatTime(rTimeSec)}</div>
                  </div>
                  <div>
                    <div className="text-[11px] text-slate-400">DV Table Updates</div>
                    <div className="text-base font-extrabold text-amber-400">
                      {curSnap?.ripPackets || 0}
                    </div>
                  </div>
                </div>

                {/* Active Forwarding Path Status */}
                <div className="flex flex-wrap items-center justify-between gap-2 my-2 text-xs">
                  <span className={darkMode ? 'text-slate-400' : 'text-slate-500'}>
                    Forwarding Path ({srcNode} → {dstNode}):
                  </span>
                  {ripTrace.st === 'ok' ? (
                    <span className="px-2.5 py-0.5 rounded-full bg-emerald-500/15 text-emerald-400 border border-emerald-500/30 font-mono font-semibold">
                      {ripTrace.path.join(' → ')}
                    </span>
                  ) : (
                    <span className="px-2.5 py-0.5 rounded-full bg-red-500/15 text-red-400 border border-red-500/30 font-semibold">
                      ⚠ {ripTrace.st}
                    </span>
                  )}
                </div>

                {/* Routing Table */}
                {renderRoutingTable('rip')}
              </div>

              {/* Cost Chart */}
              {renderCostChart('rip', '#a855f7')}
            </div>

            {/* RIGHT CARD: OSPF (Dijkstra Link-State) */}
            <div
              className={`rounded-2xl border p-4 flex flex-col justify-between ${
                darkMode ? 'bg-slate-900/90 border-slate-800' : 'bg-white border-slate-200'
              }`}
            >
              <div>
                <div className="flex items-start justify-between gap-2 mb-1">
                  <div>
                    <div className="flex items-center gap-2">
                      <h2 className="text-base font-bold">
                        OSPF v2 · Dijkstra SPF (Link-State)
                      </h2>
                      <span className="text-[11px] px-2 py-0.5 rounded bg-emerald-500/15 text-emerald-400 font-mono">
                        RFC 2328
                      </span>
                    </div>
                    <p className={`text-xs mt-0.5 ${darkMode ? 'text-slate-400' : 'text-slate-500'}`}>
                      Triggered LSA flooding (0.1s/hop + 0.2s SPF). Grey nodes await newest LSA.
                    </p>
                  </div>

                  {/* Status Pill */}
                  <div>
                    {curSnap?.oDone ? (
                      <span className="inline-flex items-center gap-1 px-2.5 py-1 rounded-full text-xs font-semibold bg-emerald-500/15 text-emerald-400 border border-emerald-500/30">
                        <CheckCircle2 className="w-3.5 h-3.5" />
                        {curSnap.tick > 0 || curSnap.oSteps > 0 || curSnap.snaps.length > 1
                          ? 'Converged'
                          : 'Stable'}
                      </span>
                    ) : (
                      <span className="inline-flex items-center gap-1 px-2.5 py-1 rounded-full text-xs font-semibold bg-sky-500/15 text-sky-400 border border-sky-500/30 animate-pulse">
                        <Zap className="w-3.5 h-3.5" />
                        Flooding LSAs…
                      </span>
                    )}
                  </div>
                </div>

                {/* SVG Topology */}
                <div className="my-2">
                  {renderTopologySvg(
                    'OSPF',
                    curSnap?.ospfTable || {},
                    curSnap?.oCh || [],
                    ospfTrace,
                    svgRefOspf
                  )}
                </div>

                {/* Metrics Bar */}
                <div
                  className={`grid grid-cols-3 gap-2 p-2.5 rounded-xl border text-center my-2 ${
                    darkMode ? 'bg-slate-950/60 border-slate-800' : 'bg-slate-50 border-slate-200'
                  }`}
                >
                  <div>
                    <div className="text-[11px] text-slate-400">LSA Flood Hops</div>
                    <div className="text-base font-extrabold text-emerald-400">
                      {curSnap?.oSteps || 0}
                    </div>
                  </div>
                  <div>
                    <div className="text-[11px] text-slate-400">Est. Convergence Time</div>
                    <div className="text-base font-extrabold">{formatTime(oTimeSec)}</div>
                  </div>
                  <div>
                    <div className="text-[11px] text-slate-400">LSDB Sync Events</div>
                    <div className="text-base font-extrabold text-sky-400">
                      {curSnap?.ospfPackets || 0}
                    </div>
                  </div>
                </div>

                {/* Active Forwarding Path Status */}
                <div className="flex flex-wrap items-center justify-between gap-2 my-2 text-xs">
                  <span className={darkMode ? 'text-slate-400' : 'text-slate-500'}>
                    Forwarding Path ({srcNode} → {dstNode}):
                  </span>
                  {ospfTrace.st === 'ok' ? (
                    <span className="px-2.5 py-0.5 rounded-full bg-emerald-500/15 text-emerald-400 border border-emerald-500/30 font-mono font-semibold">
                      {ospfTrace.path.join(' → ')}
                    </span>
                  ) : (
                    <span className="px-2.5 py-0.5 rounded-full bg-red-500/15 text-red-400 border border-red-500/30 font-semibold">
                      ⚠ {ospfTrace.st}
                    </span>
                  )}
                </div>

                {/* Routing Table */}
                {renderRoutingTable('ospf')}
              </div>

              {/* Cost Chart */}
              {renderCostChart('ospf', '#10b981')}
            </div>
          </div>

          {/* ================================================================= */}
          {/* HOP-BY-HOP PACKET & CONVERGENCE EVENT LOG + ALL-NODES INSPECTOR   */}
          {/* ================================================================= */}
          <div className="grid grid-cols-1 lg:grid-cols-3 gap-4">
            {/* Hop-by-Hop Event Log */}
            <div
              className={`lg:col-span-2 rounded-2xl border p-4 ${
                darkMode ? 'bg-slate-900/90 border-slate-800' : 'bg-white border-slate-200'
              }`}
            >
              <div className="flex items-center justify-between mb-2">
                <div className="flex items-center gap-2">
                  <Terminal className="w-4 h-4 text-purple-400" />
                  <h3 className="text-sm font-bold">
                    Synchronized Hop-by-Hop Convergence Event Log
                  </h3>
                </div>
                <span className="text-xs text-slate-400">
                  Showing {curSnap?.events?.length || 0} events up to Tick {curSnap?.tick || 0}
                </span>
              </div>
              <div
                className={`max-h-48 overflow-y-auto rounded-xl p-3 font-mono text-xs space-y-1.5 border ${
                  darkMode ? 'bg-slate-950 border-slate-800' : 'bg-slate-50 border-slate-200'
                }`}
              >
                {(curSnap?.events || []).map((ev, idx) => (
                  <div key={idx} className="flex items-start gap-2">
                    <span className="px-1.5 py-0.5 rounded bg-slate-800 text-slate-300 text-[10px] shrink-0">
                      T={ev.tick}
                    </span>
                    <span
                      className={
                        ev.type === 'ALERT'
                          ? 'text-red-400 font-semibold'
                          : ev.type === 'RIP'
                          ? 'text-purple-300'
                          : ev.type === 'OSPF'
                          ? 'text-sky-300'
                          : ev.type.endsWith('_OK')
                          ? 'text-emerald-400 font-semibold'
                          : 'text-slate-400'
                      }
                    >
                      {ev.text}
                    </span>
                  </div>
                ))}
              </div>
            </div>

            {/* Network-Wide Matrix Inspector */}
            <div
              className={`rounded-2xl border p-4 flex flex-col justify-between ${
                darkMode ? 'bg-slate-900/90 border-slate-800' : 'bg-white border-slate-200'
              }`}
            >
              <div>
                <div className="flex items-center justify-between mb-2">
                  <div className="flex items-center gap-2">
                    <Layers className="w-4 h-4 text-emerald-400" />
                    <h3 className="text-sm font-bold">All-Routers Cost Matrix (to {dstNode})</h3>
                  </div>
                  <span className="text-[11px] text-slate-400">Target: {dstNode}</span>
                </div>
                <p className="text-xs text-slate-400 mb-2">
                  Compare every router's current metric & next-hop toward destination{' '}
                  <b>Router {dstNode}</b> across both protocols:
                </p>
                <div className="overflow-x-auto">
                  <table className="w-full text-xs border-collapse">
                    <thead>
                      <tr
                        className={`border-b ${
                          darkMode ? 'border-slate-800 text-slate-400' : 'border-slate-200'
                        }`}
                      >
                        <th className="py-1 px-2 text-left">Router</th>
                        <th className="py-1 px-2 text-left text-purple-400">RIP (Cost / NH)</th>
                        <th className="py-1 px-2 text-left text-emerald-400">OSPF (Cost / NH)</th>
                      </tr>
                    </thead>
                    <tbody>
                      {nodes.map((n) => {
                        const rE = curSnap?.ripTable?.[n]?.[dstNode];
                        const oE = curSnap?.ospfTable?.[n]?.[dstNode];
                        const isDown = failedNodes.has(n);
                        return (
                          <tr
                            key={n}
                            onClick={() => setSrcNode(n)}
                            className={`border-b cursor-pointer ${
                              n === srcNode
                                ? darkMode
                                  ? 'bg-purple-500/10 border-slate-800'
                                  : 'bg-purple-50 border-slate-200'
                                : darkMode
                                ? 'border-slate-800/60 hover:bg-slate-800/40'
                                : 'border-slate-100 hover:bg-slate-50'
                            }`}
                          >
                            <td className="py-1 px-2 font-bold">
                              Router {n} {isDown && <span className="text-red-400">(DOWN)</span>}
                            </td>
                            <td className="py-1 px-2 font-mono">
                              {isDown
                                ? '—'
                                : n === dstNode
                                ? '0 (Self)'
                                : `${rE?.c >= INF ? '∞' : rE?.c} via ${rE?.n || '–'}`}
                            </td>
                            <td className="py-1 px-2 font-mono">
                              {isDown
                                ? '—'
                                : n === dstNode
                                ? '0 (Self)'
                                : `${oE?.c >= INF ? '∞' : oE?.c} via ${oE?.n || '–'}`}
                            </td>
                          </tr>
                        );
                      })}
                    </tbody>
                  </table>
                </div>
              </div>
              <div className="text-[11px] text-slate-400 mt-2">
                Tip: Click any row above to switch the active Source Router view.
              </div>
            </div>
          </div>
        </main>
      )}

      {/* =================================================================== */}
      {/* TAB 2: 4-WAY PROTOCOL BENCHMARK LAB (EXPECTED OUTCOMES VERIFICATION)*/}
      {/* =================================================================== */}
      {activeTab === 'benchmark' && (
        <main className="max-w-7xl mx-auto px-4 py-6 space-y-6">
          <div
            className={`rounded-2xl border p-6 ${
              darkMode ? 'bg-slate-900/90 border-slate-800' : 'bg-white border-slate-200'
            }`}
          >
            <div className="flex flex-wrap items-center justify-between gap-4 mb-6">
              <div>
                <span className="text-xs font-bold uppercase tracking-wider text-purple-400">
                  Expected Outcomes Verification Lab
                </span>
                <h2 className="text-xl font-bold mt-0.5">
                  Simultaneous 4-Way Convergence Benchmark
                </h2>
                <p className={`text-sm mt-1 ${darkMode ? 'text-slate-400' : 'text-slate-600'}`}>
                  Directly quantifying convergence speed, control overhead, and loop mitigation across{' '}
                  <b>RIP (No Prevention)</b>, <b>RIP (Split Horizon)</b>,{' '}
                  <b>RIP (Poison Reverse)</b>, and <b>OSPF (Dijkstra)</b> on the active topology.
                </p>
              </div>
              <div className="flex flex-wrap gap-2">
                <button
                  onClick={runPresetFailNodeD}
                  className="px-3 py-1.5 rounded-xl text-xs font-semibold bg-red-500/15 text-red-400 border border-red-500/30 hover:bg-red-500/25"
                >
                  Benchmark: Node D Failure (6-Node Mesh)
                </button>
                <button
                  onClick={runPresetLinearCountToInfinity}
                  className="px-3 py-1.5 rounded-xl text-xs font-semibold bg-purple-500/15 text-purple-400 border border-purple-500/30 hover:bg-purple-500/25"
                >
                  Benchmark: Linear Chain Link C–D Failure
                </button>
              </div>
            </div>

            {/* 4 Metric Summary Cards */}
            <div className="grid grid-cols-1 sm:grid-cols-2 lg:grid-cols-4 gap-4 mb-6">
              {Object.entries(benchmarkData).map(([k, item]) => {
                const isOspf = k === 'ospf';
                return (
                  <div
                    key={k}
                    className={`rounded-xl border p-4 ${
                      isOspf
                        ? darkMode
                          ? 'bg-emerald-950/20 border-emerald-500/40'
                          : 'bg-emerald-50 border-emerald-200'
                        : darkMode
                        ? 'bg-slate-950/70 border-slate-800'
                        : 'bg-slate-50 border-slate-200'
                    }`}
                  >
                    <div className="flex items-center justify-between mb-2">
                      <span className="text-xs font-bold">{item.name}</span>
                      {item.hadCti ? (
                        <span className="text-[10px] px-1.5 py-0.5 rounded bg-red-500/20 text-red-400 font-semibold">
                          Count-to-∞
                        </span>
                      ) : (
                        <span className="text-[10px] px-1.5 py-0.5 rounded bg-emerald-500/20 text-emerald-400 font-semibold">
                          Loop-Free
                        </span>
                      )}
                    </div>
                    <div className="text-2xl font-extrabold my-1">
                      {formatTime(item.timeSec)}
                    </div>
                    <div className="text-xs text-slate-400 flex items-center justify-between mt-2 pt-2 border-t border-slate-800/60">
                      <span>Steps: <b>{item.steps}</b></span>
                      <span>Updates: <b>{item.messages}</b></span>
                    </div>
                  </div>
                );
              })}
            </div>

            {/* Visual Bar Chart Comparison */}
            <div className="space-y-4">
              <h3 className="text-sm font-bold">
                Convergence Time Comparison (Log-Scaled Visual Bar & Exact Seconds)
              </h3>
              {Object.entries(benchmarkData).map(([k, item]) => {
                const maxTime = Math.max(
                  1,
                  ...Object.values(benchmarkData).map((d) => d.timeSec)
                );
                const pct = Math.max(4, Math.round((item.timeSec / maxTime) * 100));
                return (
                  <div key={k} className="space-y-1">
                    <div className="flex justify-between text-xs">
                      <span className="font-semibold">{item.name}</span>
                      <span className="font-mono">
                        {item.steps} {k === 'ospf' ? 'flood hops' : 'rounds'} ·{' '}
                        <b>{formatTime(item.timeSec)}</b> ({item.messages} table updates)
                      </span>
                    </div>
                    <div
                      className={`w-full h-3.5 rounded-full overflow-hidden ${
                        darkMode ? 'bg-slate-800' : 'bg-slate-200'
                      }`}
                    >
                      <div
                        className={`h-full rounded-full transition-all duration-500 ${
                          k === 'ospf'
                            ? 'bg-emerald-500'
                            : item.hadCti
                            ? 'bg-red-500'
                            : 'bg-purple-500'
                        }`}
                        style={{ width: `${pct}%` }}
                      />
                    </div>
                  </div>
                );
              })}
            </div>
          </div>
        </main>
      )}

      {/* =================================================================== */}
      {/* TAB 3: RFC 2453 & RFC 2328 REFERENCE & PROJECT DOCUMENTATION        */}
      {/* =================================================================== */}
      {activeTab === 'reference' && (
        <main className="max-w-7xl mx-auto px-4 py-6 space-y-6">
          <div className="grid grid-cols-1 md:grid-cols-2 gap-6">
            {/* RIP RFC 2453 Card */}
            <div
              className={`rounded-2xl border p-6 space-y-4 ${
                darkMode ? 'bg-slate-900/90 border-slate-800' : 'bg-white border-slate-200'
              }`}
            >
              <div className="flex items-center justify-between">
                <h2 className="text-lg font-bold text-purple-400">
                  RIP v2 · Distance-Vector (RFC 2453)
                </h2>
                <span className="text-xs font-mono px-2 py-1 rounded bg-purple-500/15 text-purple-300">
                  Bellman-Ford Algorithm
                </span>
              </div>
              <p className="text-sm leading-relaxed text-slate-300">
                Every RIP router maintains a vector of distances to all destinations and periodically
                broadcasts its entire routing table to immediate neighbors every <b>30 seconds</b>.
              </p>
              <div
                className={`p-3.5 rounded-xl font-mono text-xs border ${
                  darkMode ? 'bg-slate-950 border-slate-800' : 'bg-slate-50 border-slate-200'
                }`}
              >
                D_x(y) = min_v &#123; c(x, v) + D_v(y) &#125; &nbsp; (with ∞ = 16)
              </div>
              <ul className="text-xs space-y-2 text-slate-300 list-disc pl-4">
                <li>
                  <b>Count-to-Infinity Problem:</b> Good news travels fast, bad news travels slowly.
                  When a destination becomes unreachable, neighboring routers may mutually adopt
                  stale alternate routes through each other, incrementing cost by 1 or 2 each round
                  until hitting <b>16 (infinity)</b>.
                </li>
                <li>
                  <b>Split Horizon:</b> Never advertise a route back out the interface/neighbor from
                  which it was learned. Immediately eliminates 2-node routing loops.
                </li>
                <li>
                  <b>Poison Reverse:</b> Explicitly advertise a route learned from a neighbor back to
                  that neighbor with a metric of <b>16 (∞)</b>, immediately invalidating stale
                  mutual dependencies.
                </li>
              </ul>
            </div>

            {/* OSPF RFC 2328 Card */}
            <div
              className={`rounded-2xl border p-6 space-y-4 ${
                darkMode ? 'bg-slate-900/90 border-slate-800' : 'bg-white border-slate-200'
              }`}
            >
              <div className="flex items-center justify-between">
                <h2 className="text-lg font-bold text-emerald-400">
                  OSPF v2 · Link-State (RFC 2328)
                </h2>
                <span className="text-xs font-mono px-2 py-1 rounded bg-emerald-500/15 text-emerald-300">
                  Dijkstra SPF Algorithm
                </span>
              </div>
              <p className="text-sm leading-relaxed text-slate-300">
                Instead of exchanging rumor-based distance vectors, every OSPF router maintains an
                identical <b>Link-State Database (LSDB)</b> representing the complete network graph.
              </p>
              <div
                className={`p-3.5 rounded-xl font-mono text-xs border ${
                  darkMode ? 'bg-slate-950 border-slate-800' : 'bg-slate-50 border-slate-200'
                }`}
              >
                LSA Flood (0.1s/hop) → Full Topology Sync → Local Dijkstra SPF Tree (0.2s)
              </div>
              <ul className="text-xs space-y-2 text-slate-300 list-disc pl-4">
                <li>
                  <b>Event-Driven LSA Flooding:</b> As soon as a link or router fails, adjacent
                  routers originate a new Link-State Advertisement (LSA) and flood it hop-by-hop.
                </li>
                <li>
                  <b>Zero Count-to-Infinity:</b> Because every router computes shortest paths locally
                  from a complete topological map using Dijkstra’s algorithm, count-to-infinity cannot
                  occur.
                </li>
                <li>
                  <b>Sub-Second Convergence:</b> Convergence depends only on link propagation/flooding
                  delay plus SPF execution time, typically completing in under 1 second.
                </li>
              </ul>
            </div>
          </div>
        </main>
      )}
    </div>
  );
}