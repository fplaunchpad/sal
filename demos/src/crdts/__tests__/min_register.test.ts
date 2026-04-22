import { describe, it } from "vitest";
import fc from "fast-check";
import { checkLattice } from "../../harness/invariants";
import { spec, type Op } from "../min_register";

const arbOp: fc.Arbitrary<Op> = fc.record({
  kind: fc.constant("write" as const),
  value: fc.integer({ min: 0, max: 100 }),
});

describe("MIN-Register", () => {
  it("lattice laws", () => checkLattice(spec, arbOp));
});
