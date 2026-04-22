import { describe, it } from "vitest";
import fc from "fast-check";
import { checkMRDTLaws } from "../../harness/mrdt_invariants";
import { spec, type Op } from "../or_set";

const arbOp: fc.Arbitrary<Op> = fc.oneof(
  fc.record({
    kind: fc.constant("add" as const),
    elem: fc.integer({ min: 0, max: 3 }),
  }),
  fc.record({
    kind: fc.constant("remove" as const),
    elem: fc.integer({ min: 0, max: 3 }),
  }),
);

describe("OR-Set MRDT", () => {
  it("merge laws", () => checkMRDTLaws(spec, arbOp));
});
