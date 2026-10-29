// Property-based laws for state-based replicated data types with a three-way
// merge, following the RA-linearizability criterion and the canonical join
// laws (VC1 to VC5).
//
// A datatype is `{ init, apply(state, op), merge3(l, a, b), read(state),
// equal?(a, b), serialise?(state), semanticCommutes?(op1, op2) }`.
// `semanticCommutes` is a trusted exact semantic oracle: true certifies
// commutation on every state, false certifies non-commutation, and undefined
// declines to decide. It is separate from instance.commutes, which declares
// the policy used to construct the linearization order.
// States are compared with `equal` when
// supplied, otherwise by `serialise`, otherwise structurally on `read`.
// `apply` and `merge3` are made total: a call that throws yields the
// distinguished state BOTTOM, and BOTTOM absorbs every later operation.
//
// An instance describes how to exercise a datatype:
//   genEvent(rnd, state, ctx) -> op | null
//       an op valid on `state` (the canonical state of the issuing replica's
//       event set). ctx = { replica, seq, fresh(), events } where fresh()
//       returns a globally increasing integer, usable as a tag or timestamp.
//   rc?(op1, op2)          the conflict-resolution relation on operations
//   commutes?(op1, op2)    declared commutativity; defaults to "not related
//                          by rc in either direction" (rc-non-comm)
//   label?(op)             the operation label (default: JSON of the op)
//   specCommutes?(op1, op2) commutativity in the sequential specification
//   spec?                  { init, step(phi, op) -> phi | undefined,
//                            observe(phi) } a deterministic sequential
//                          specification; `undefined` means "not admitted"
//   observe?(state)        the query compared against spec.observe
//   witnessOrder?(evA, evB) tie-break used to build the linear extension
//                          offered as the specification witness
//   replicas?, syncProbability?
//
// Events carry `{ id, replica, seq, op, vis }`, where `vis` is the set of
// event ids visible to the event when it was issued. Visibility is therefore
// explicit and transitive. Each property is a function
// `(datatype, instance, { seed, trials, maxSize, perTrial }) ->
//  { name, status, pass, runs, vacuous, inconclusive, inconclusiveExamples,
//    failures }`. `runs` counts only pass/fail checks; an inconclusive check
// is never a checked pass. A failure carries a counterexample
// shrunk by deleting events (together with every event that saw them, so the
// shrunk configuration is still an execution), set members and sequence
// entries while the same kind of failure persists.

export const BOTTOM = Symbol.for('ra-pbt.bottom');

/** The mulberry32 PRNG: a function returning floats in [0, 1). */
export function mulberry32(seed) {
  let a = seed >>> 0;
  return function next() {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

const randInt = (rnd, n) => Math.floor(rnd() * n);
const choose = (rnd, xs) => xs[randInt(rnd, xs.length)];
function shuffle(rnd, xs) {
  const ys = [...xs];
  for (let i = ys.length - 1; i > 0; i--) { const j = randInt(rnd, i + 1); [ys[i], ys[j]] = [ys[j], ys[i]]; }
  return ys;
}

// ---------------------------------------------------------------------------
// The kit: total operations, equality and the relations of the criterion.

function kit(datatype, instance) {
  const apply = (s, op) => {
    if (s === BOTTOM) return BOTTOM;
    try { const r = datatype.apply(s, op); return r === undefined ? BOTTOM : r; } catch { return BOTTOM; }
  };
  const merge = (l, a, b) => {
    if (l === BOTTOM || a === BOTTOM || b === BOTTOM) return BOTTOM;
    try { const r = datatype.merge3(l, a, b); return r === undefined ? BOTTOM : r; } catch { return BOTTOM; }
  };
  const key = (s) => {
    if (s === BOTTOM) return '⊥';
    if (datatype.serialise) return datatype.serialise(s);
    try { return JSON.stringify(datatype.read(s)); } catch (err) { return `unreadable: ${err.message}`; }
  };
  const eq = (a, b) => {
    if (a === BOTTOM || b === BOTTOM) return a === b;
    if (datatype.equal) return datatype.equal(a, b);
    return key(a) === key(b);
  };
  const show = (s) => {
    if (s === BOTTOM) return '⊥';
    let r;
    try { r = JSON.stringify(datatype.read(s)); } catch { r = 'unreadable'; }
    return datatype.serialise ? `${r} ${datatype.serialise(s)}` : r;
  };
  const rcOps = (a, b) => (instance.rc ? !!instance.rc(a, b) : false);
  const commOps = (a, b) => (instance.commutes ? !!instance.commutes(a, b) : !(rcOps(a, b) || rcOps(b, a)));
  const label = (op) => (instance.label ? instance.label(op) : JSON.stringify(op));
  return { datatype, instance, apply, merge, eq, show, rcOps, commOps, label, init: () => datatype.init() };
}

// ---------------------------------------------------------------------------
// Configurations: events with explicit visibility.

const memoOf = new WeakMap();
function memo(cfg) {
  let m = memoOf.get(cfg);
  if (!m) { m = { comm: new Map(), can: new Map(), pool: null }; memoOf.set(cfg, m); }
  return m;
}
const op = (cfg, id) => cfg.events.get(id).op;
const vis = (cfg, a, b) => cfg.events.get(b).vis.has(a);
const conc = (cfg, a, b) => a !== b && !vis(cfg, a, b) && !vis(cfg, b, a);
function commE(K, cfg, a, b) {
  const m = memo(cfg).comm, k = `${a}|${b}`;
  if (!m.has(k)) m.set(k, K.commOps(op(cfg, a), op(cfg, b)));
  return m.get(k);
}
const visNC = (K, cfg, a, b) => vis(cfg, a, b) && !commE(K, cfg, a, b);
const byIndex = (cfg) => (a, b) => cfg.events.get(a).index - cfg.events.get(b).index;
const sorted = (cfg, ids) => [...ids].sort(byIndex(cfg));
const setKey = (cfg, ids) => sorted(cfg, ids).join(',');

/** The linearization relation lo_E as successor lists: e1 lo e2 iff
 *  (e1 vis e2 and not e1 <-> e2) or (e1 || e2 and e1 rc e2 and no e3 in E
 *  with e2 vis e3 and not e2 <-> e3). */
function loOn(K, cfg, E) {
  const succ = new Map(E.map((x) => [x, []]));
  const absorbed = new Map(E.map((b) => [b, E.some((c) => c !== b && visNC(K, cfg, b, c))]));
  for (const a of E) for (const b of E) {
    if (a === b) continue;
    if (visNC(K, cfg, a, b)) succ.get(a).push(b);
    else if (conc(cfg, a, b) && K.rcOps(op(cfg, a), op(cfg, b)) && !absorbed.get(b)) succ.get(a).push(b);
  }
  return succ;
}

/** One topological order of (E, lo_E); `pickReady` chooses among ready
 *  events (sorted by generation index). Returns null on a cycle. */
function topo(K, cfg, E, pickReady) {
  const succ = loOn(K, cfg, E), indeg = new Map(E.map((x) => [x, 0]));
  for (const xs of succ.values()) for (const y of xs) indeg.set(y, indeg.get(y) + 1);
  let ready = sorted(cfg, E.filter((x) => indeg.get(x) === 0));
  const out = [];
  while (ready.length) {
    const i = pickReady(ready);
    const x = ready[i]; ready.splice(i, 1); out.push(x);
    for (const y of succ.get(x)) { indeg.set(y, indeg.get(y) - 1); if (indeg.get(y) === 0) ready.push(y); }
    ready = sorted(cfg, ready);
  }
  return out.length === E.length ? out : null;
}

/** All linear extensions of (E, lo_E), up to `cap`. */
function allExtensions(K, cfg, E, cap) {
  const succ = loOn(K, cfg, E), indeg = new Map(E.map((x) => [x, 0]));
  for (const xs of succ.values()) for (const y of xs) indeg.set(y, indeg.get(y) + 1);
  const out = [], cur = [], used = new Set();
  const go = () => {
    if (out.length >= cap) return;
    if (cur.length === E.length) { out.push([...cur]); return; }
    for (const x of sorted(cfg, E)) {
      if (used.has(x) || indeg.get(x) !== 0) continue;
      used.add(x); cur.push(x);
      for (const y of succ.get(x)) indeg.set(y, indeg.get(y) - 1);
      go();
      for (const y of succ.get(x)) indeg.set(y, indeg.get(y) + 1);
      used.delete(x); cur.pop();
      if (out.length >= cap) return;
    }
  };
  go();
  return out;
}

class CycleError extends Error {
  constructor(ids) { super(`lo_E is cyclic on {${ids.join(',')}}`); this.ids = ids; }
}

const fold = (K, cfg, seq) => seq.reduce((s, id) => K.apply(s, op(cfg, id)), K.init());

/** can(E): fold of the linear extension of (E, lo_E) that breaks ties by
 *  generation order. */
function can(K, cfg, ids) {
  const E = [...ids], k = setKey(cfg, E), m = memo(cfg).can;
  if (m.has(k)) return m.get(k);
  const pi = topo(K, cfg, E, () => 0);
  if (!pi) throw new CycleError(sorted(cfg, E));
  const s = fold(K, cfg, pi);
  m.set(k, s);
  return s;
}

/** The principal downset of e: e and every x with x vis_NC^+ e. */
function down(K, cfg, e) {
  const out = new Set([e]), stack = [e];
  while (stack.length) {
    const y = stack.pop();
    for (const x of cfg.order) if (!out.has(x) && visNC(K, cfg, x, y)) { out.add(x); stack.push(x); }
  }
  return out;
}
const weaklyClosed = (K, cfg, S) => {
  const set = new Set(S);
  for (const b of set) for (const x of cfg.order) if (visNC(K, cfg, x, b) && !set.has(x)) return false;
  return true;
};
const causallyClosed = (cfg, S) => {
  const set = new Set(S);
  for (const b of set) for (const x of cfg.events.get(b).vis) if (cfg.events.has(x) && !set.has(x)) return false;
  return true;
};
const maximal = (K, cfg, E, e) => E.includes(e) && loOn(K, cfg, E).get(e).length === 0;
const union = (a, b) => [...new Set([...a, ...b])];
const inter = (a, b) => { const s = new Set(b); return a.filter((x) => s.has(x)); };
const minus = (a, b) => { const s = new Set(b); return a.filter((x) => !s.has(x)); };

// ---------------------------------------------------------------------------
// Generation.

const REPLICA_NAMES = ['p', 'q', 'r', 's', 't', 'u'];

/** A random execution: replicas issue events on the canonical state of
 *  their event set and occasionally absorb another replica's event set.
 *  Every event set held by a replica is recorded as a version. */
export function generateConfiguration(datatype, instance, rnd, size, K = kit(datatype, instance)) {
  const R = Math.min(instance.replicas ?? 3, REPLICA_NAMES.length);
  const names = REPLICA_NAMES.slice(0, R);
  const cfg = { events: new Map(), order: [], versions: [] };
  const heads = names.map(() => new Set()), seqs = names.map(() => 0);
  const seen = new Set();
  const record = (r) => {
    const v = sorted(cfg, heads[r]), k = v.join(',');
    if (!seen.has(k)) { seen.add(k); cfg.versions.push(v); }
  };
  let fresh = 0, steps = 0, guard = 0;
  while (steps < size && guard++ < size * 8) {
    const r = randInt(rnd, R);
    if (cfg.order.length && rnd() < (instance.syncProbability ?? 0.3)) {
      const s = randInt(rnd, R);
      if (s === r) continue;
      for (const x of heads[s]) heads[r].add(x);
      record(r); steps++;
      continue;
    }
    const E = sorted(cfg, heads[r]);
    let state;
    try { state = can(K, cfg, E); } catch { continue; }
    if (state === BOTTOM) continue;
    const ctx = { replica: names[r], seq: seqs[r] + 1, fresh: () => ++fresh, events: E.map((id) => cfg.events.get(id)) };
    const o = instance.genEvent(rnd, state, ctx);
    if (o == null) continue;
    seqs[r]++;
    const id = `${names[r]}${seqs[r]}`;
    cfg.events.set(id, { id, replica: names[r], seq: seqs[r], op: o, vis: new Set(E), index: cfg.order.length });
    cfg.order.push(id); heads[r].add(id); record(r); steps++;
  }
  return cfg;
}

function closeDown(K, cfg, S) {
  const out = new Set();
  for (const x of S) for (const y of down(K, cfg, x)) out.add(y);
  return sorted(cfg, out);
}
function randomSubset(cfg, rnd, from = cfg.order) {
  const p = 0.2 + 0.6 * rnd();
  return from.filter(() => rnd() < p);
}
const randomWeaklyClosed = (K, cfg, rnd) => closeDown(K, cfg, randomSubset(cfg, rnd));
function randomCausallyClosed(cfg, rnd) {
  if (cfg.versions.length && rnd() < 0.6) return choose(rnd, cfg.versions);
  const out = new Set();
  for (const x of randomSubset(cfg, rnd)) { out.add(x); for (const y of cfg.events.get(x).vis) out.add(y); }
  return sorted(cfg, out);
}
const drawSet = (K, cfg, rnd) =>
  (cfg.versions.length && rnd() < 0.5 ? choose(rnd, cfg.versions) : randomWeaklyClosed(K, cfg, rnd));
const randomSeq = (cfg, rnd) => shuffle(rnd, randomSubset(cfg, rnd));

// ---------------------------------------------------------------------------
// The state pool used to witness non-commutation: every state reached by
// folding a sequence of distinct events of the configuration (exhaustive for
// at most four events, a fixed deterministic sample otherwise).

function statePool(K, cfg) {
  const m = memo(cfg);
  if (m.pool) return m.pool;
  const seqs = [[]];
  if (cfg.order.length <= 4) {
    const go = (cur, rest) => {
      for (let i = 0; i < rest.length; i++) {
        const next = [...cur, rest[i]];
        seqs.push(next);
        go(next, [...rest.slice(0, i), ...rest.slice(i + 1)]);
      }
    };
    go([], cfg.order);
  } else {
    const rnd = mulberry32(cfg.order.length * 7919 + 17);
    for (let i = 1; i <= cfg.order.length; i++) seqs.push(cfg.order.slice(0, i));
    for (let i = 0; i < 48; i++) seqs.push(randomSeq(cfg, rnd));
  }
  m.pool = seqs.map((seq) => ({ seq, state: fold(K, cfg, seq) }));
  return m.pool;
}

/** Continuations pi for conditional commutativity: every sequence of at most
 *  two events of the configuration when it has at most five events, a fixed
 *  sample of sequences of length at most three otherwise. */
function continuations(cfg) {
  const out = [[]];
  if (cfg.order.length <= 5) {
    for (const a of cfg.order) { out.push([a]); for (const b of cfg.order) out.push([a, b]); }
  } else {
    const rnd = mulberry32(cfg.order.length * 104729 + 3);
    for (let i = 0; i < 40; i++) out.push(Array.from({ length: 1 + randInt(rnd, 3) }, () => choose(rnd, cfg.order)));
  }
  return out;
}

function nonCommWitness(K, cfg, a, b) {
  const oa = op(cfg, a), ob = op(cfg, b);
  for (const { seq, state } of statePool(K, cfg)) {
    const ab = K.apply(K.apply(state, oa), ob), ba = K.apply(K.apply(state, ob), oa);
    if (!K.eq(ab, ba)) return { sigma: seq, sigmaState: K.show(state), [`${a};${b}`]: K.show(ab), [`${b};${a}`]: K.show(ba) };
  }
  return null;
}

// ---------------------------------------------------------------------------
// Shrinking and reporting.

const PASS = { status: 'pass' }, VACUOUS = { status: 'vacuous' };
const fail = (kind, detail) => ({ status: 'fail', kind, detail });
const inconclusive = (kind, detail) => ({ status: 'inconclusive', kind, detail });

function restrict(cx, removed) {
  for (const id of Object.values(cx.picks ?? {})) if (removed.has(id)) return null;
  const events = new Map([...cx.cfg.events].filter(([id]) => !removed.has(id)));
  const cfg = { events, order: cx.cfg.order.filter((id) => !removed.has(id)), versions: [] };
  const sets = Object.fromEntries(Object.entries(cx.sets ?? {}).map(([k, v]) => [k, v.filter((x) => !removed.has(x))]));
  const seqs = Object.fromEntries(Object.entries(cx.seqs ?? {}).map(([k, v]) => [k, v.filter((x) => !removed.has(x))]));
  return { ...cx, cfg, sets, seqs };
}

function* candidates(K, cx) {
  const ids = cx.cfg.order;
  for (let i = ids.length - 1; i >= 0; i--) {
    const e = ids[i], removed = new Set([e]);
    for (const x of ids) if (cx.cfg.events.get(x).vis.has(e)) removed.add(x);
    const c = restrict(cx, removed);
    if (c) yield c;
  }
  for (const [name, set] of Object.entries(cx.sets ?? {})) {
    for (const id of set) {
      yield { ...cx, sets: { ...cx.sets, [name]: set.filter((x) => x !== id) } };
      const above = set.filter((x) => x !== id && down(K, cx.cfg, x).has(id));
      if (above.length) yield { ...cx, sets: { ...cx.sets, [name]: set.filter((x) => x !== id && !above.includes(x)) } };
    }
  }
  for (const [name, seq] of Object.entries(cx.seqs ?? {})) {
    for (let i = 0; i < seq.length; i++) yield { ...cx, seqs: { ...cx.seqs, [name]: [...seq.slice(0, i), ...seq.slice(i + 1)] } };
  }
}

function safeCheck(prop, K, cx) {
  try { return prop.check(K, cx); } catch (err) {
    if (err instanceof CycleError) return fail('no-linear-extension', { cycleOn: err.ids });
    return fail('exception', { message: err.message });
  }
}

function shrink(prop, K, cx, result, budget = 2000) {
  let cur = cx, res = result, steps = 0, progress = true;
  while (progress && steps < budget) {
    progress = false;
    for (const cand of candidates(K, cur)) {
      if (++steps > budget) break;
      const r = safeCheck(prop, K, cand);
      if (r.status === 'fail' && r.kind === res.kind) { cur = cand; res = r; progress = true; break; }
    }
  }
  return { cx: cur, result: res };
}

function describe(cx, result) {
  const events = cx.cfg.order.map((id) => {
    const ev = cx.cfg.events.get(id);
    return { id, replica: ev.replica, seq: ev.seq, op: ev.op, vis: sorted(cx.cfg, [...ev.vis].filter((x) => cx.cfg.events.has(x))) };
  });
  return {
    kind: result.kind,
    size: events.length,
    events,
    sets: Object.fromEntries(Object.entries(cx.sets ?? {}).map(([k, v]) => [k, sorted(cx.cfg, v)])),
    picks: cx.picks ?? {},
    seqs: cx.seqs ?? {},
    detail: result.detail,
  };
}

/** Run one property: draw counterexample candidates from random
 *  configurations of growing size; on the first failure, shrink it. */
function runProperty(prop, datatype, instance, opts = {}) {
  const { seed = 1, trials = 100, maxSize = 10, perTrial = 4 } = opts;
  const K = kit(datatype, instance);
  let runs = 0, vacuous = 0, unresolved = 0;
  const inconclusiveExamples = [];
  const result = (failures = [], notApplicable = false) => {
    const status = notApplicable ? 'not-applicable' : failures.length ? 'fail'
      : unresolved ? 'inconclusive' : runs ? 'pass' : 'vacuous';
    return { name: prop.name, status, pass: status === 'pass', runs, vacuous,
      inconclusive: unresolved, inconclusiveExamples, failures,
      ...(notApplicable ? { notApplicable: true } : {}) };
  };
  if (prop.applies && !prop.applies(K)) return result([], true);
  for (let t = 0; t < trials; t++) {
    const rnd = mulberry32((Math.imul(seed, 1000003) + t) >>> 0);
    const size = 1 + Math.floor(((maxSize - 1) * (t + 1)) / trials);
    const cfg = generateConfiguration(datatype, instance, rnd, size, K);
    if (!cfg.order.length) continue;
    for (const part of prop.draw(K, cfg, rnd, perTrial, opts)) {
      const cx = { cfg, sets: {}, picks: {}, seqs: {}, ...part };
      const r = safeCheck(prop, K, cx);
      if (r.status === 'vacuous') { vacuous++; continue; }
      if (r.status === 'inconclusive') {
        unresolved++;
        if (!inconclusiveExamples.length) inconclusiveExamples.push(describe(cx, r));
        continue;
      }
      runs++;
      if (r.status === 'fail') {
        const s = shrink(prop, K, cx, r);
        return result([describe(s.cx, s.result)]);
      }
    }
  }
  return result();
}

const states = (K, cx, names) => Object.fromEntries(names.map((n) => [n, can(K, cx.cfg, cx.sets[n])]));
const foldSeq = (K, cx, name) => fold(K, cx.cfg, cx.seqs[name]);
const admissible = (K, cx, ...names) => names.every((n) => weaklyClosed(K, cx.cfg, cx.sets[n]));

// ---------------------------------------------------------------------------
// The properties.

const PROPS = {};

/** One state per set of events, and the join lemma. For a causally closed
 *  event set E, every linear extension of (E, lo_E) folds `apply` from the
 *  initial state to the same state (all extensions when there are at most
 *  120, otherwise a bounded sample). For weakly closed E1 and E2,
 *  merge(can(E1 ∩ E2), can(E1), can(E2)) = can(E1 ∪ E2). Without an rc
 *  relation, lo_E has no rc edges and the requirement covers every order
 *  allowed by non-commuting visibility. The option `parts` (default
 *  ['extensions', 'join']) restricts the check to one half. */
PROPS.eventSetDeterminesState = {
  name: 'eventSetDeterminesState',
  draw(K, cfg, rnd, n, opts) {
    const parts = opts.parts ?? ['extensions', 'join'];
    return Array.from({ length: n }, () => (choose(rnd, parts) === 'extensions'
      ? { mode: 'extensions', sets: { E: randomCausallyClosed(cfg, rnd) }, seed: randInt(rnd, 1 << 30) }
      : { mode: 'join', sets: { E1: drawSet(K, cfg, rnd), E2: drawSet(K, cfg, rnd) } }));
  },
  check(K, cx) {
    if (cx.mode === 'extensions') {
      const E = cx.sets.E;
      if (!causallyClosed(cx.cfg, E)) return VACUOUS;
      const base = topo(K, cx.cfg, E, () => 0);
      if (!base) return fail('no-linear-extension', { E });
      let exts = allExtensions(K, cx.cfg, E, 120);
      if (exts.length === 120) {
        const rnd = mulberry32(cx.seed);
        for (let i = 0; i < 40; i++) exts.push(topo(K, cx.cfg, E, (ready) => randInt(rnd, ready.length)));
      }
      const s0 = fold(K, cx.cfg, base);
      for (const pi of exts) {
        const s = fold(K, cx.cfg, pi);
        if (!K.eq(s, s0)) return fail('linear-extensions-disagree', { pi1: base, state1: K.show(s0), pi2: pi, state2: K.show(s) });
      }
      return PASS;
    }
    if (!admissible(K, cx, 'E1', 'E2')) return VACUOUS;
    const { E1, E2 } = cx.sets, c = cx.cfg;
    const lhs = K.merge(can(K, c, inter(E1, E2)), can(K, c, E1), can(K, c, E2)), rhs = can(K, c, union(E1, E2));
    return K.eq(lhs, rhs) ? PASS : fail('merge-not-canonical', { merge: K.show(lhs), canonicalOfUnion: K.show(rhs) });
  },
};

/** VC1 (merge-comm): for all states l, a, b, merge(l, a, b) = merge(l, b, a).
 *  Checked on canonical states (of an LCA set E1 ∩ E2 and branches E1, E2,
 *  or of three independent sets) and on arbitrary states, obtained by folding
 *  arbitrary sequences of events in arbitrary order. */
PROPS.vc1MergeComm = {
  name: 'vc1MergeComm',
  draw(K, cfg, rnd, n) {
    return Array.from({ length: n }, () => {
      const m = rnd();
      if (m < 0.35) { const E1 = drawSet(K, cfg, rnd), E2 = drawSet(K, cfg, rnd); return { mode: 'canonical', sets: { l: inter(E1, E2), a: E1, b: E2 } }; }
      if (m < 0.6) return { mode: 'canonical', sets: { l: drawSet(K, cfg, rnd), a: drawSet(K, cfg, rnd), b: drawSet(K, cfg, rnd) } };
      return { mode: 'arbitrary', seqs: { l: randomSeq(cfg, rnd), a: randomSeq(cfg, rnd), b: randomSeq(cfg, rnd) } };
    });
  },
  check(K, cx) {
    const { l, a, b } = cx.mode === 'canonical' ? states(K, cx, ['l', 'a', 'b'])
      : { l: foldSeq(K, cx, 'l'), a: foldSeq(K, cx, 'a'), b: foldSeq(K, cx, 'b') };
    const x = K.merge(l, a, b), y = K.merge(l, b, a);
    return K.eq(x, y) ? PASS : fail('merge-not-commutative', {
      l: K.show(l), a: K.show(a), b: K.show(b), 'merge(l,a,b)': K.show(x), 'merge(l,b,a)': K.show(y),
    });
  },
};

/** VC2 (merge-init): for every admissible E,
 *  merge(σ0, σ0, can(E)) = can(E). */
PROPS.vc2MergeInit = {
  name: 'vc2MergeInit',
  draw: (K, cfg, rnd, n) => Array.from({ length: n }, () => ({ sets: { E: drawSet(K, cfg, rnd) } })),
  check(K, cx) {
    if (!admissible(K, cx, 'E')) return VACUOUS;
    const s = can(K, cx.cfg, cx.sets.E), m = K.merge(K.init(), K.init(), s);
    return K.eq(m, s) ? PASS : fail('merge-init-not-identity', { canE: K.show(s), merge: K.show(m) });
  },
};

function maximaOf(K, cfg, U) {
  const succ = loOn(K, cfg, U);
  return U.filter((e) => succ.get(e).length === 0);
}

/** VC3 (local-redistribute): for admissible E1, E2 and an event e in
 *  E1 \ E2 that is maximal in E1 ∪ E2, with l = can(E1 ∩ E2),
 *  m = can(↓e \ {e}), x = can(E1 \ {e}) and y = can(E2),
 *  merge(l, merge(m, x, e(m)), y) = merge(m, merge(l, x, y), e(m)). */
PROPS.vc3LocalRedistribute = {
  name: 'vc3LocalRedistribute',
  draw(K, cfg, rnd, n) {
    const out = [];
    for (let i = 0; i < n * 3 && out.length < n; i++) {
      let E1 = drawSet(K, cfg, rnd), E2 = drawSet(K, cfg, rnd);
      const U = union(E1, E2);
      let cands;
      try { cands = maximaOf(K, cfg, U).filter((e) => !(E1.includes(e) && E2.includes(e))); } catch { cands = []; }
      if (!cands.length) { out.push({ sets: { E1, E2 }, picks: {} }); continue; }
      const e = choose(rnd, cands);
      if (!E1.includes(e)) [E1, E2] = [E2, E1];
      out.push({ sets: { E1, E2 }, picks: { e } });
    }
    return out;
  },
  check(K, cx) {
    const { e } = cx.picks, { E1, E2 } = cx.sets, c = cx.cfg;
    if (e === undefined || !E1.includes(e) || E2.includes(e) || !admissible(K, cx, 'E1', 'E2')) return VACUOUS;
    if (!maximal(K, c, union(E1, E2), e)) return VACUOUS;
    const l = can(K, c, inter(E1, E2)), m = can(K, c, [...down(K, c, e)].filter((x) => x !== e));
    const x = can(K, c, minus(E1, [e])), y = can(K, c, E2), em = K.apply(m, op(c, e));
    const lhs = K.merge(l, K.merge(m, x, em), y), rhs = K.merge(m, K.merge(l, x, y), em);
    return K.eq(lhs, rhs) ? PASS : fail('vc3', {
      l: K.show(l), m: K.show(m), x: K.show(x), y: K.show(y), 'e(m)': K.show(em), lhs: K.show(lhs), rhs: K.show(rhs),
    });
  },
};

/** VC4 (causal-delta): for admissible E and an event e maximal in E, with
 *  A = can(E \ {e}) and B = can(↓e \ {e}), merge(B, A, e(B)) = e(A). */
PROPS.vc4CausalDelta = {
  name: 'vc4CausalDelta',
  draw(K, cfg, rnd, n) {
    return Array.from({ length: n }, () => {
      const E = rnd() < 0.5 ? drawSet(K, cfg, rnd) : union(drawSet(K, cfg, rnd), drawSet(K, cfg, rnd));
      let ms;
      try { ms = maximaOf(K, cfg, E); } catch { ms = []; }
      return { sets: { E }, picks: ms.length ? { e: choose(rnd, ms) } : {} };
    });
  },
  check(K, cx) {
    const { e } = cx.picks, { E } = cx.sets, c = cx.cfg;
    if (e === undefined || !admissible(K, cx, 'E') || !maximal(K, c, E, e)) return VACUOUS;
    const A = can(K, c, minus(E, [e])), B = can(K, c, [...down(K, c, e)].filter((x) => x !== e));
    const lhs = K.merge(B, A, K.apply(B, op(c, e))), rhs = K.apply(A, op(c, e));
    return K.eq(lhs, rhs) ? PASS : fail('vc4', { A: K.show(A), B: K.show(B), lhs: K.show(lhs), rhs: K.show(rhs) });
  },
};

/** VC5 (redistribute): for admissible E1, E2 and an event e in E1 ∩ E2 that
 *  is maximal in E1 ∪ E2, with m = can(↓e \ {e}), x0 = can((E1 ∩ E2) \ {e}),
 *  x1 = can(E1 \ {e}) and x2 = can(E2 \ {e}),
 *  merge(merge(m, x0, e(m)), merge(m, x1, e(m)), merge(m, x2, e(m)))
 *    = merge(m, merge(x0, x1, x2), e(m)). */
PROPS.vc5Redistribute = {
  name: 'vc5Redistribute',
  draw(K, cfg, rnd, n) {
    const out = [];
    for (let i = 0; i < n * 3 && out.length < n; i++) {
      const E1 = drawSet(K, cfg, rnd), E2 = drawSet(K, cfg, rnd);
      let cands;
      try { cands = maximaOf(K, cfg, union(E1, E2)).filter((e) => E1.includes(e) && E2.includes(e)); } catch { cands = []; }
      out.push({ sets: { E1, E2 }, picks: cands.length ? { e: choose(rnd, cands) } : {} });
    }
    return out;
  },
  check(K, cx) {
    const { e } = cx.picks, { E1, E2 } = cx.sets, c = cx.cfg;
    if (e === undefined || !E1.includes(e) || !E2.includes(e) || !admissible(K, cx, 'E1', 'E2')) return VACUOUS;
    if (!maximal(K, c, union(E1, E2), e)) return VACUOUS;
    const m = can(K, c, [...down(K, c, e)].filter((x) => x !== e)), em = K.apply(m, op(c, e));
    const x0 = can(K, c, minus(inter(E1, E2), [e])), x1 = can(K, c, minus(E1, [e])), x2 = can(K, c, minus(E2, [e]));
    const lhs = K.merge(K.merge(m, x0, em), K.merge(m, x1, em), K.merge(m, x2, em));
    const rhs = K.merge(m, K.merge(x0, x1, x2), em);
    return K.eq(lhs, rhs) ? PASS : fail('vc5', {
      m: K.show(m), x0: K.show(x0), x1: K.show(x1), x2: K.show(x2), lhs: K.show(lhs), rhs: K.show(rhs),
    });
  },
};

function eventPairs(K, cfg, rnd, n, keep) {
  const pairs = [];
  for (const a of cfg.order) for (const b of cfg.order) {
    if (a < b && K.label(op(cfg, a)) !== K.label(op(cfg, b)) && keep(a, b)) pairs.push([a, b]);
  }
  return shuffle(rnd, pairs).slice(0, n);
}

// A finite witness establishes non-commutation. Absence of a witness does
// not establish commutation, even when every distinct-event sequence of the
// configuration was searched. Only the separate semantic oracle can decide
// the remaining cases; policy declarations never certify this fact.
function semanticCommutation(K, cfg, a, b) {
  const witness = nonCommWitness(K, cfg, a, b);
  if (witness) return { commutes: false, detail: witness };
  const exact = K.datatype.semanticCommutes?.(op(cfg, a), op(cfg, b));
  const detail = { pair: [a, b], statesSearched: statePool(K, cfg).length };
  if (typeof exact === 'boolean') return { commutes: exact, detail: { ...detail, semanticOracle: true } };
  return { commutes: undefined, detail };
}

/** rc-non-comm: for operations o1 ≠ o2, o1 and o2 fail to commute iff
 *  o1 rc o2 or o2 rc o1. Missing finite non-commutation witnesses are
 *  inconclusive unless datatype.semanticCommutes decides the pair. */
PROPS.rcNonComm = {
  name: 'rcNonComm',
  draw: (K, cfg, rnd, n) => eventPairs(K, cfg, rnd, n, () => true).map(([a, b]) => ({ picks: { o1: a, o2: b } })),
  check(K, cx) {
    const { o1, o2 } = cx.picks, c = cx.cfg, a = op(c, o1), b = op(c, o2);
    if (K.label(a) === K.label(b)) return VACUOUS;
    const related = K.rcOps(a, b) || K.rcOps(b, a), semantic = semanticCommutation(K, c, o1, o2);
    if (semantic.commutes === undefined) return inconclusive('commutation-unresolved', semantic.detail);
    if (!semantic.commutes && !related) return fail('non-commuting-without-rc', semantic.detail);
    if (semantic.commutes && related) return fail('rc-on-commuting-pair', { ...semantic.detail, rc: K.rcOps(a, b) ? [o1, o2] : [o2, o1] });
    return PASS;
  },
};

/** no-rc-chain: there are no operations o1, o2, o3 with o1 rc o2 rc o3. */
PROPS.noRcChain = {
  name: 'noRcChain',
  applies: (K) => !!K.instance.rc,
  draw: () => [{ mode: 'scan' }],
  check(K, cx) {
    const c = cx.cfg, ids = c.order;
    for (const b of ids) {
      const a = ids.find((x) => K.rcOps(op(c, x), op(c, b)));
      if (a === undefined) continue;
      const d = ids.find((x) => K.rcOps(op(c, b), op(c, x)));
      if (d !== undefined) return fail('rc-chain', { chain: [a, b, d] });
    }
    return PASS;
  },
};

/** cond-comm: whenever o1 rc o2 and o2 does not commute with o3,
 *  o3(π(o1(o2(σ)))) = o3(π(o2(o1(σ)))) for every state σ and every
 *  continuation π. Here σ ranges over the state pool and π over bounded
 *  continuations drawn from the configuration's events; o2 and o3 are taken
 *  as non-commuting when the declared commutativity says so or the pool
 *  holds a witness. */
PROPS.condComm = {
  name: 'condComm',
  applies: (K) => !!K.instance.rc,
  draw(K, cfg, rnd, n) {
    const out = [];
    for (const a of cfg.order) for (const b of cfg.order) {
      if (a === b || !K.rcOps(op(cfg, a), op(cfg, b))) continue;
      for (const d of cfg.order) if (d !== b && condNonComm(K, cfg, b, d)) out.push({ picks: { o1: a, o2: b, o3: d } });
    }
    return shuffle(rnd, out).slice(0, n);
  },
  check(K, cx) {
    const { o1, o2, o3 } = cx.picks, c = cx.cfg;
    if (!K.rcOps(op(c, o1), op(c, o2)) || !condNonComm(K, c, o2, o3)) return VACUOUS;
    for (const { seq, state } of statePool(K, c)) {
      const s12 = K.apply(K.apply(state, op(c, o2)), op(c, o1)), s21 = K.apply(K.apply(state, op(c, o1)), op(c, o2));
      for (const pi of continuations(c)) {
        const run = (s) => K.apply(pi.reduce((t, id) => K.apply(t, op(c, id)), s), op(c, o3));
        const x = run(s12), y = run(s21);
        if (!K.eq(x, y)) return fail('conditional-commutativity', { sigma: seq, pi, [`o3(pi(o1(o2(sigma))))`]: K.show(x), [`o3(pi(o2(o1(sigma))))`]: K.show(y) });
      }
    }
    return PASS;
  },
};
function condNonComm(K, cfg, a, b) {
  return !commE(K, cfg, a, b) || (cfg.order.length <= 6 && nonCommWitness(K, cfg, a, b) !== null);
}

/** spec-non-comm: for all operations o1, o2, if o1 and o2 do not commute in
 *  the sequential specification, they do not commute in the implementation.
 *  Specification commutativity is `instance.specCommutes`; implementation
 *  non-commutation is witnessed over the state pool or certified by
 *  datatype.semanticCommutes. A missing witness alone is inconclusive. */
PROPS.specNonComm = {
  name: 'specNonComm',
  applies: (K) => !!K.instance.specCommutes,
  draw: (K, cfg, rnd, n) => eventPairs(K, cfg, rnd, n, (a, b) => !K.instance.specCommutes(op(cfg, a), op(cfg, b)))
    .map(([a, b]) => ({ picks: { o1: a, o2: b } })),
  check(K, cx) {
    const { o1, o2 } = cx.picks, c = cx.cfg;
    if (K.label(op(c, o1)) === K.label(op(c, o2)) || K.instance.specCommutes(op(c, o1), op(c, o2))) return VACUOUS;
    const semantic = semanticCommutation(K, c, o1, o2);
    if (semantic.commutes === undefined) return inconclusive('commutation-unresolved', semantic.detail);
    return semantic.commutes ? fail('spec-non-commuting-pair-commutes', semantic.detail) : PASS;
  },
};

/** RA-linearizability of canonical states (second clause of the criterion):
 *  for a causally closed event set E there is a linear extension π of
 *  (E, lo_E) such that ops(π) is admitted by the specification and the
 *  specification's observation after ops(π) equals the implementation's
 *  observation of can(E). The search is a depth-first walk over prefixes of
 *  linear extensions that identifies prefixes with the same event set and
 *  the same specification state, trying ready events in `witnessOrder`
 *  first. The default bound is 50000 visited prefixes, configurable with
 *  maxSpecPrefixes; exhaustion without a witness is inconclusive. */
PROPS.specConformance = {
  name: 'specConformance',
  applies: (K) => !!(K.instance.spec && K.instance.observe),
  draw: (K, cfg, rnd, n, opts) => Array.from({ length: n }, () => ({
    sets: { E: randomCausallyClosed(cfg, rnd) }, maxPrefixes: opts.maxSpecPrefixes ?? 50000,
  })),
  check(K, cx) {
    const { E } = cx.sets, c = cx.cfg, { spec, observe, witnessOrder } = K.instance;
    if (!causallyClosed(c, E)) return VACUOUS;
    const want = JSON.stringify(observe(can(K, c, E)));
    const cmp = witnessOrder ? (x, y) => witnessOrder(c.events.get(x), c.events.get(y)) : byIndex(c);
    const succ = loOn(K, c, E), preds = new Map(E.map((x) => [x, []]));
    for (const [a, bs] of succ) for (const b of bs) preds.get(b).push(a);
    const order = [...E].sort(cmp), seen = new Set(), BOUND = cx.maxPrefixes;
    if (!Number.isSafeInteger(BOUND) || BOUND < 0) throw new RangeError('maxSpecPrefixes must be a nonnegative safe integer');
    let visited = 0, sample = null;
    const go = (used, pi, phi) => {
      if (pi.length === E.length) {
        const got = JSON.stringify(spec.observe(phi));
        if (got === want) return pi;
        if (!sample) sample = { pi: [...pi], spec: got };
        return null;
      }
      const k = `${[...used].sort().join(',')}|${JSON.stringify(phi)}`;
      if (seen.has(k) || ++visited > BOUND) return null;
      seen.add(k);
      for (const x of order) {
        if (used.has(x) || preds.get(x).some((y) => !used.has(y))) continue;
        const next = spec.step(phi, op(c, x));
        if (next === undefined) continue;
        used.add(x); pi.push(x);
        const r = go(used, pi, next);
        used.delete(x); pi.pop();
        if (r) return r;
      }
      return null;
    };
    if (go(new Set(), [], spec.init())) return PASS;
    if (visited > BOUND) return inconclusive('spec-search-bound-exhausted', { maxPrefixes: BOUND, visited });
    return fail('no-admitted-linear-extension', { implementation: want, closestAdmitted: sample });
  },
};

/** Merge idempotence: for admissible L ⊆ A with l = can(L) and a = can(A),
 *  merge(l, a, a) = a, merge(l, l, a) = a (fast-forward) and
 *  merge(a, a, a) = a. */
PROPS.mergeIdempotence = {
  name: 'mergeIdempotence',
  draw(K, cfg, rnd, n) {
    return Array.from({ length: n }, () => {
      const A = drawSet(K, cfg, rnd);
      return { sets: { L: closeDown(K, cfg, randomSubset(cfg, rnd, A)), A } };
    });
  },
  check(K, cx) {
    const { L, A } = cx.sets;
    if (!admissible(K, cx, 'L', 'A') || minus(L, A).length) return VACUOUS;
    const { L: l, A: a } = states(K, cx, ['L', 'A']);
    for (const [name, r] of [['merge(l,a,a)', K.merge(l, a, a)], ['merge(l,l,a)', K.merge(l, l, a)], ['merge(a,a,a)', K.merge(a, a, a)]]) {
      if (!K.eq(r, a)) return fail('merge-not-idempotent', { law: name, l: K.show(l), a: K.show(a), result: K.show(r) });
    }
    return PASS;
  },
};

/** Merge with the initial state: for every state s (canonical or obtained
 *  by folding an arbitrary event sequence), merge(σ0, σ0, s) = s and
 *  merge(σ0, s, σ0) = s. */
PROPS.mergeInit = {
  name: 'mergeInit',
  draw: (K, cfg, rnd, n) => Array.from({ length: n }, () => ({ seqs: { s: randomSeq(cfg, rnd) } })),
  check(K, cx) {
    const s = foldSeq(K, cx, 's'), i = K.init();
    for (const [name, r] of [['merge(σ0,σ0,s)', K.merge(i, i, s)], ['merge(σ0,s,σ0)', K.merge(i, s, i)]]) {
      if (!K.eq(r, s)) return fail('merge-init-not-identity', { law: name, s: K.show(s), result: K.show(r) });
    }
    return PASS;
  },
};

export const properties = Object.freeze(Object.keys(PROPS));

const bind = (name) => (datatype, instance, opts) => runProperty(PROPS[name], datatype, instance, opts);
export const eventSetDeterminesState = bind('eventSetDeterminesState');
export const vc1MergeComm = bind('vc1MergeComm');
export const vc2MergeInit = bind('vc2MergeInit');
export const vc3LocalRedistribute = bind('vc3LocalRedistribute');
export const vc4CausalDelta = bind('vc4CausalDelta');
export const vc5Redistribute = bind('vc5Redistribute');
export const rcNonComm = bind('rcNonComm');
export const noRcChain = bind('noRcChain');
export const condComm = bind('condComm');
export const specNonComm = bind('specNonComm');
export const specConformance = bind('specConformance');
export const mergeIdempotence = bind('mergeIdempotence');
export const mergeInit = bind('mergeInit');
export const vc4 = vc4CausalDelta;
export const vc5 = vc5Redistribute;

/** Every property on one datatype and instance. */
export function checkAll(datatype, instance, opts) {
  return properties.map((name) => runProperty(PROPS[name], datatype, instance, opts));
}

/** A compact one-line-per-event rendering of a shrunk counterexample. */
export function formatCounterexample(f) {
  const lines = [`${f.kind} (${f.size} events)`];
  for (const e of f.events) lines.push(`  ${e.id}: ${JSON.stringify(e.op)} vis {${e.vis.join(',')}}`);
  for (const [k, v] of Object.entries(f.sets)) lines.push(`  ${k} = {${v.join(',')}}`);
  for (const [k, v] of Object.entries(f.picks)) lines.push(`  ${k} = ${v}`);
  for (const [k, v] of Object.entries(f.seqs)) lines.push(`  ${k} = [${v.join(',')}]`);
  lines.push(`  ${JSON.stringify(f.detail)}`);
  return lines.join('\n');
}

/** A configuration from hand-written events
 *  `{ id, replica, seq, op, vis: [ids] }`, listed in issue order. */
export function makeConfiguration(events) {
  const cfg = { events: new Map(), order: [], versions: [] };
  events.forEach((e, index) => {
    cfg.events.set(e.id, { ...e, vis: new Set(e.vis ?? []), index });
    cfg.order.push(e.id);
  });
  return cfg;
}

/** Evaluation of the criterion's notions on a given configuration. */
export function evaluator(datatype, instance, cfg) {
  const K = kit(datatype, instance);
  return {
    can: (ids) => can(K, cfg, ids),
    lo: (ids) => [...loOn(K, cfg, ids)].flatMap(([a, bs]) => bs.map((b) => [a, b])),
    down: (id) => sorted(cfg, down(K, cfg, id)),
    weaklyClosed: (ids) => weaklyClosed(K, cfg, ids),
    maximal: (ids, e) => maximal(K, cfg, ids, e),
    apply: (s, id) => K.apply(s, op(cfg, id)),
    merge: K.merge,
    eq: K.eq,
    show: K.show,
  };
}
