import { describe, it } from "vitest";
import fc from "fast-check";
import { checkMRDTLaws } from "../../harness/mrdt_invariants";
import { spec, type Op } from "../add_win_pq";

const arbOp: fc.Arbitrary<Op> = fc.oneof(
  fc.record({
    kind: fc.constant("add" as const),
    elem: fc.integer({ min: 0, max: 2 }),
    value: fc.integer({ min: 0, max: 5 }),
  }),
  fc.record({
    kind: fc.constant("inc" as const),
    elem: fc.integer({ min: 0, max: 2 }),
    amount: fc.integer({ min: -3, max: 3 }),
  }),
  fc.record({
    kind: fc.constant("rmv" as const),
    elem: fc.integer({ min: 0, max: 2 }),
  }),
);

describe("Add-Wins Priority Queue MRDT", () => {
  it("merge laws", () => checkMRDTLaws(spec, arbOp));
});
