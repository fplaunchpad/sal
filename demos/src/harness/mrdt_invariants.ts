import fc from "fast-check";
import type { MRDTSpec } from "./mrdt_types";
import type { OpMeta } from "./types";

/**
 * Check the core MRDT laws on merge:
 *   1. left identity:   merge(l, l, b) ~ b
 *   2. right identity:  merge(l, a, l) ~ a
 *   3. commutativity:   merge(l, a, b) ~ merge(l, b, a)
 *
 * These are the standard MRDT properties. Note that `merge(l, a, a) ~ a`
 * (strict idempotence) is NOT an MRDT law: the closed-form counter MRDT
 * `merge(l,a,b) = a + b - l` fails it when a ≠ l (it would double-count the
 * delta). MRDTs only promise convergence given a coherent history DAG —
 * that's what the playground's commit DAG provides at runtime.
 */
export function checkMRDTLaws<C, A, O>(
  spec: MRDTSpec<C, A, O>,
  arbOp: fc.Arbitrary<O>,
  opts: { numRuns?: number; abstractEq?: (a: A, b: A) => boolean } = {},
) {
  const numRuns = opts.numRuns ?? 300;
  const absEq =
    opts.abstractEq ??
    ((a: A, b: A) =>
      JSON.stringify(a, replacer) === JSON.stringify(b, replacer));
  const eqStates = (a: C, b: C) => absEq(spec.abstract(a), spec.abstract(b));

  // Branch from a given starting state at a given ts. Fresh timestamps per
  // op so ops keyed by ts (RGA, MVR, …) stay coherent across the whole DAG.
  const applyFrom = (
    start: C,
    ops: { op: O; rid: number }[],
    startTs: number,
  ) => {
    let s = start;
    let ts = startTs;
    for (const { op, rid } of ops) {
      const meta: OpMeta = { ts: ts++, rid };
      s = spec.apply(s, op, meta);
    }
    return { state: s, nextTs: ts };
  };

  const arbOpList = fc.array(
    fc.record({ op: arbOp, rid: fc.integer({ min: 0, max: 2 }) }),
    { minLength: 0, maxLength: 6 },
  );

  // ts starts at 1 to match the playground harness (the DAG harness already
  // does the same). Lean specs reserve 0 as "never written" / sentinel.
  // 1. Left identity: merge(l, l, b) = b  (no changes on the left branch)
  fc.assert(
    fc.property(arbOpList, arbOpList, (lops, bops) => {
      const { state: l, nextTs: t1 } = applyFrom(spec.init, lops, 1);
      const { state: b } = applyFrom(l, bops, t1);
      return eqStates(spec.merge(l, l, b), b);
    }),
    { numRuns },
  );

  // 2. Right identity: merge(l, a, l) = a
  fc.assert(
    fc.property(arbOpList, arbOpList, (lops, aops) => {
      const { state: l, nextTs: t1 } = applyFrom(spec.init, lops, 1);
      const { state: a } = applyFrom(l, aops, t1);
      return eqStates(spec.merge(l, a, l), a);
    }),
    { numRuns },
  );

  // 3. Commutativity
  fc.assert(
    fc.property(arbOpList, arbOpList, arbOpList, (lops, aops, bops) => {
      const { state: l, nextTs: t1 } = applyFrom(spec.init, lops, 1);
      const { state: a, nextTs: t2 } = applyFrom(l, aops, t1);
      const { state: b } = applyFrom(l, bops, t2);
      return eqStates(spec.merge(l, a, b), spec.merge(l, b, a));
    }),
    { numRuns },
  );
}

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
