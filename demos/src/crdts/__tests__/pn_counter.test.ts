import { describe, it } from "vitest";
import fc from "fast-check";
import { checkLattice } from "../../harness/invariants";
import { spec, type Op } from "../pn_counter";

const arbOp: fc.Arbitrary<Op> = fc.oneof(
  fc.record({
    kind: fc.constant("inc" as const),
    amount: fc.integer({ min: 1, max: 10 }),
  }),
  fc.record({
    kind: fc.constant("dec" as const),
    amount: fc.integer({ min: 1, max: 10 }),
  }),
);

describe("PN-Counter", () => {
  it("satisfies the CRDT lattice laws", () => {
    checkLattice(spec, arbOp);
  });
});
