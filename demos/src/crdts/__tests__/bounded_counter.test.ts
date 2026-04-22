import { describe, it } from "vitest";
import fc from "fast-check";
import { checkLattice } from "../../harness/invariants";
import { spec, type Op } from "../bounded_counter";

const arbOp: fc.Arbitrary<Op> = fc.oneof(
  fc.record({ kind: fc.constant("inc" as const) }),
  fc.record({ kind: fc.constant("dec" as const) }),
  fc.record({
    kind: fc.constant("transfer" as const),
    receiver: fc.integer({ min: 0, max: 2 }),
  }),
);

describe("Bounded Counter", () => {
  it("lattice laws", () =>
    checkLattice(spec, arbOp, {
      abstractEq: (a, b) => {
        if (a.net !== b.net) return false;
        const sortMap = (m: Map<number, number>) =>
          [...m.entries()].sort((x, y) => x[0] - y[0]);
        return JSON.stringify(sortMap(a.quotas)) === JSON.stringify(sortMap(b.quotas));
      },
    }));
});
