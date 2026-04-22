import { describe, it } from "vitest";
import fc from "fast-check";
import { checkMRDTLaws } from "../../harness/mrdt_invariants";
import { spec, type Op } from "../rga";

const arbOp: fc.Arbitrary<Op> = fc.oneof(
  fc.record({
    kind: fc.constant("insert" as const),
    after: fc.constant(0),
    ele: fc.integer({ min: 1, max: 5 }),
  }),
  fc.record({
    kind: fc.constant("remove" as const),
    target: fc.integer({ min: 1, max: 10 }),
  }),
);

describe("RGA MRDT", () => {
  it("merge laws", () =>
    checkMRDTLaws(spec, arbOp, {
      abstractEq: (a, b) => {
        const s = (xs: { ts: number; ele: number }[]) =>
          xs.map((n) => `${n.ts}:${n.ele}`).join("|");
        return s(a.visible) === s(b.visible);
      },
    }));
});
