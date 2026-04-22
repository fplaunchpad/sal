import { describe, it } from "vitest";
import fc from "fast-check";
import { checkMRDTLaws } from "../../harness/mrdt_invariants";
import { spec, type Op } from "../grow_only_set";

const arbOp: fc.Arbitrary<Op> = fc.record({
  kind: fc.constant("add" as const),
  elem: fc.integer({ min: 0, max: 5 }),
});

describe("Grow-Only Set MRDT", () => {
  it("merge laws", () => checkMRDTLaws(spec, arbOp));
});
