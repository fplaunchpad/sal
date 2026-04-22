import { describe, it } from "vitest";
import fc from "fast-check";
import { checkMRDTLaws } from "../../harness/mrdt_invariants";
import { spec, type Op } from "../multi_valued_register";

const arbOp: fc.Arbitrary<Op> = fc.record({
  kind: fc.constant("write" as const),
  value: fc.integer({ min: 0, max: 10 }),
});

describe("Multi-Valued Register MRDT", () => {
  it("merge laws", () => checkMRDTLaws(spec, arbOp));
});
