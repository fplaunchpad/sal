import { describe, it } from "vitest";
import fc from "fast-check";
import type { OpMeta } from "../../harness/types";
import { spec, type Concrete, type Op } from "../add_win_pq";

// rmv ops carry a prepare-time tombstone snapshot. Generate ops without
// the snapshot (kind, elem, value, amount only), then materialise it
// from the local replica state at apply time: exactly what the
// playground's opForm does interactively.
type RawOp =
  | { kind: "add"; elem: number; value: number }
  | { kind: "inc"; elem: number; amount: number }
  | { kind: "rmv"; elem: number };

const arbRawOp: fc.Arbitrary<RawOp> = fc.oneof(
  fc.record({
    kind: fc.constant("add" as const),
    elem: fc.integer({ min: 0, max: 3 }),
    value: fc.integer({ min: 0, max: 10 }),
  }),
  fc.record({
    kind: fc.constant("inc" as const),
    elem: fc.integer({ min: 0, max: 3 }),
    amount: fc.integer({ min: -5, max: 5 }),
  }),
  fc.record({
    kind: fc.constant("rmv" as const),
    elem: fc.integer({ min: 0, max: 3 }),
  }),
);

function materialise(s: Concrete, raw: RawOp): Op {
  if (raw.kind !== "rmv") return raw;
  const tombstones: string[] = [];
  for (const k of s.A.keys()) {
    if (s.R.has(k)) continue;
    if (Number(k.split(":")[0]) === raw.elem) tombstones.push(k);
  }
  return { kind: "rmv", elem: raw.elem, tombstones };
}

function applyAll(
  ops: { op: RawOp; rid: number }[],
  startTs: number,
): { state: Concrete; nextTs: number } {
  let s = spec.init;
  let ts = startTs;
  for (const { op, rid } of ops) {
    const meta: OpMeta = { ts: ts++, rid };
    s = spec.apply(s, materialise(s, op), meta);
  }
  return { state: s, nextTs: ts };
}

const eq = (a: Concrete, b: Concrete) =>
  JSON.stringify(spec.abstract(a)) === JSON.stringify(spec.abstract(b));

describe("Add-Wins Priority Queue", () => {
  const arbOpList = fc.array(
    fc.record({ op: arbRawOp, rid: fc.integer({ min: 0, max: 2 }) }),
    { minLength: 0, maxLength: 8 },
  );

  it("idempotence", () => {
    fc.assert(
      fc.property(arbOpList, (ops) => {
        const { state } = applyAll(ops, 1);
        return eq(spec.merge(state, state), state);
      }),
      { numRuns: 500 },
    );
  });

  it("commutativity", () => {
    fc.assert(
      fc.property(arbOpList, arbOpList, (oa, ob) => {
        const { state: a, nextTs } = applyAll(oa, 1);
        const { state: b } = applyAll(ob, nextTs);
        return eq(spec.merge(a, b), spec.merge(b, a));
      }),
      { numRuns: 500 },
    );
  });

  it("associativity", () => {
    fc.assert(
      fc.property(arbOpList, arbOpList, arbOpList, (oa, ob, oc) => {
        const { state: a, nextTs: t1 } = applyAll(oa, 1);
        const { state: b, nextTs: t2 } = applyAll(ob, t1);
        const { state: c } = applyAll(oc, t2);
        return eq(spec.merge(spec.merge(a, b), c), spec.merge(a, spec.merge(b, c)));
      }),
      { numRuns: 500 },
    );
  });
});
