import { describe, it } from "vitest";
import fc from "fast-check";
import { checkLattice } from "../../harness/invariants";
import { spec, type Op } from "../pq_insert_only";

const arbOp: fc.Arbitrary<Op> = fc.record({
  kind: fc.constant("push" as const),
  prio: fc.integer({ min: 0, max: 9 }),
  elem: fc.integer({ min: 0, max: 9 }),
});

describe("Insert-Only Priority Queue", () => {
  it("lattice laws", () => checkLattice(spec, arbOp));
});
