import { describe, it } from "vitest";
import fc from "fast-check";
import { checkMRDTLaws } from "../../harness/mrdt_invariants";
import { spec, type Op } from "../grow_only_map";

const arbOp: fc.Arbitrary<Op> = fc.record({
  kind: fc.constant("put" as const),
  key: fc.integer({ min: 0, max: 3 }),
  value: fc.integer({ min: 0, max: 3 }),
});

describe("Grow-Only Map MRDT", () => {
  it("merge laws", () => checkMRDTLaws(spec, arbOp));
});
