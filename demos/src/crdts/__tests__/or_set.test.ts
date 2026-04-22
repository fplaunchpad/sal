import { describe, it } from "vitest";
import fc from "fast-check";
import { checkLattice } from "../../harness/invariants";
import { spec, type Op } from "../or_set";

const arbOp: fc.Arbitrary<Op> = fc.oneof(
  fc.record({
    kind: fc.constant("add" as const),
    elem: fc.constantFrom("a", "b", "c", "d"),
  }),
  fc.record({
    kind: fc.constant("remove" as const),
    elem: fc.constantFrom("a", "b", "c", "d"),
  }),
);

describe("OR-Set", () => {
  it("satisfies the CRDT lattice laws", () => {
    checkLattice(spec, arbOp, {
      // Abstract is a sorted string array; JSON-eq works fine.
    });
  });
});
