import { describe, it } from "vitest";
import fc from "fast-check";
import { checkLattice } from "../../harness/invariants";
import { spec, type Op } from "../grow_only_set";

const arbOp: fc.Arbitrary<Op> = fc.record({
  kind: fc.constant("add" as const),
  elem: fc.integer({ min: 0, max: 10 }),
});

describe("Grow-Only Set", () => {
  it("lattice laws", () => checkLattice(spec, arbOp));
});
