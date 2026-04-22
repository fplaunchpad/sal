import fc from "fast-check";
import type { CRDTSpec, OpMeta } from "./types";

/**
 * Check the three CRDT lattice laws on `merge`:
 *   1. idempotence:   merge(s, s) ~ s
 *   2. commutativity: merge(a, b) ~ merge(b, a)
 *   3. associativity: merge(merge(a, b), c) ~ merge(a, merge(b, c))
 * plus a "strong convergence" sanity check:
 *   4. applying disjoint ops on two replicas then merging yields the same
 *      result regardless of merge direction.
 *
 * `eq` compares abstract views; use the CRDT's spec.abstract internally.
 *
 * Opaque Ops are generated via `arbOp` (a fast-check arbitrary). Meta counters
 * are synthesised monotonically; the CRDT is responsible for handling them.
 */
export function checkLattice<Concrete, Abstract, Op>(
  spec: CRDTSpec<Concrete, Abstract, Op>,
  arbOp: fc.Arbitrary<Op>,
  opts: { numRuns?: number; abstractEq?: (a: Abstract, b: Abstract) => boolean } = {},
) {
  const numRuns = opts.numRuns ?? 500;
  const absEq =
    opts.abstractEq ??
    ((a: Abstract, b: Abstract) =>
      JSON.stringify(a, replacer) === JSON.stringify(b, replacer));

  const stateView = (s: Concrete) => spec.abstract(s);
  const eqStates = (a: Concrete, b: Concrete) =>
    absEq(stateView(a), stateView(b));

  const applyAll = (ops: { op: Op; rid: number }[], startTs: number) => {
    let s = spec.init;
    let ts = startTs;
    for (const { op, rid } of ops) {
      const meta: OpMeta = { ts: ts++, rid };
      s = spec.apply(s, op, meta);
    }
    return { state: s, nextTs: ts };
  };

  const arbOpList = fc.array(
    fc.record({ op: arbOp, rid: fc.integer({ min: 0, max: 2 }) }),
    { minLength: 0, maxLength: 8 },
  );

  // 1. Idempotence
  fc.assert(
    fc.property(arbOpList, (ops) => {
      const { state } = applyAll(ops, 0);
      return eqStates(spec.merge(state, state), state);
    }),
    { numRuns },
  );

  // 2. Commutativity
  fc.assert(
    fc.property(arbOpList, arbOpList, (oa, ob) => {
      const { state: a, nextTs } = applyAll(oa, 0);
      const { state: b } = applyAll(ob, nextTs);
      return eqStates(spec.merge(a, b), spec.merge(b, a));
    }),
    { numRuns },
  );

  // 3. Associativity
  fc.assert(
    fc.property(arbOpList, arbOpList, arbOpList, (oa, ob, oc) => {
      const { state: a, nextTs: t1 } = applyAll(oa, 0);
      const { state: b, nextTs: t2 } = applyAll(ob, t1);
      const { state: c } = applyAll(oc, t2);
      const left = spec.merge(spec.merge(a, b), c);
      const right = spec.merge(a, spec.merge(b, c));
      return eqStates(left, right);
    }),
    { numRuns },
  );

  // 4. Strong convergence
  fc.assert(
    fc.property(arbOpList, arbOpList, (oa, ob) => {
      const { state: a, nextTs } = applyAll(oa, 0);
      const { state: b } = applyAll(ob, nextTs);
      return eqStates(spec.merge(a, b), spec.merge(b, a));
    }),
    { numRuns },
  );
}

// Stable JSON serialiser so Maps/Sets compare by content.
function replacer(_key: string, value: unknown): unknown {
  if (value instanceof Map) {
    return {
      __type: "Map",
      entries: [...value.entries()].sort((x, y) =>
        String(x[0]).localeCompare(String(y[0])),
      ),
    };
  }
  if (value instanceof Set) {
    return {
      __type: "Set",
      values: [...value.values()].sort((x, y) =>
        String(x).localeCompare(String(y)),
      ),
    };
  }
  return value;
}
