import { describe, it } from "vitest";
import fc from "fast-check";
import { checkLattice } from "../../harness/invariants";
import { spec, type Op } from "../add_win_pq";

const arbOp: fc.Arbitrary<Op> = fc.oneof(
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

describe("Add-Wins Priority Queue", () => {
  it("lattice laws", () => checkLattice(spec, arbOp));
});
