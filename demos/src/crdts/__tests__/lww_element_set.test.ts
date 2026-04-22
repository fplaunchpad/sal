import { describe, it } from "vitest";
import fc from "fast-check";
import { checkLattice } from "../../harness/invariants";
import { spec, type Op } from "../lww_element_set";

const arbOp: fc.Arbitrary<Op> = fc.oneof(
  fc.record({
    kind: fc.constant("add" as const),
    elem: fc.integer({ min: 0, max: 5 }),
  }),
  fc.record({
    kind: fc.constant("remove" as const),
    elem: fc.integer({ min: 0, max: 5 }),
  }),
);

describe("LWW-Element-Set", () => {
  it("lattice laws", () => checkLattice(spec, arbOp));
});
