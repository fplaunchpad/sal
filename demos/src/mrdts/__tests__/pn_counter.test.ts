import { describe, it } from "vitest";
import fc from "fast-check";
import { checkMRDTLaws } from "../../harness/mrdt_invariants";
import { spec, type Op } from "../pn_counter";

const arbOp: fc.Arbitrary<Op> = fc.oneof(
  fc.record({
    kind: fc.constant("inc" as const),
    amount: fc.integer({ min: 1, max: 5 }),
  }),
  fc.record({
    kind: fc.constant("dec" as const),
    amount: fc.integer({ min: 1, max: 5 }),
  }),
);

describe("PN-Counter MRDT", () => {
  it("merge laws", () => checkMRDTLaws(spec, arbOp));
});
