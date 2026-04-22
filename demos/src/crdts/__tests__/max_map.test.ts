import { describe, it } from "vitest";
import fc from "fast-check";
import { checkLattice } from "../../harness/invariants";
import { spec, type Op } from "../max_map";

const arbOp: fc.Arbitrary<Op> = fc.record({
  kind: fc.constant("write" as const),
  key: fc.integer({ min: 0, max: 4 }),
  value: fc.integer({ min: 0, max: 100 }),
});

describe("MAX-Map", () => {
  it("lattice laws", () => checkLattice(spec, arbOp));
});
