import { describe, it } from "vitest";
import fc from "fast-check";
import { checkLattice } from "../../harness/invariants";
import { spec, type Op } from "../shopping_cart";

const arbOp: fc.Arbitrary<Op> = fc.oneof(
  fc.record({
    kind: fc.constant("add" as const),
    pid: fc.integer({ min: 0, max: 4 }),
  }),
  fc.record({
    kind: fc.constant("remove" as const),
    pid: fc.integer({ min: 0, max: 4 }),
  }),
);

describe("Shopping Cart", () => {
  it("lattice laws", () => checkLattice(spec, arbOp));
});
