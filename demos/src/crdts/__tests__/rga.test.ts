import { describe, it } from "vitest";
import fc from "fast-check";
import { checkLattice } from "../../harness/invariants";
import { spec, type Op } from "../rga";

// Random ops are tricky for RGA because most sampled `after` OpIds won't
// refer to any inserted char — the invariants check still passes because
// those inserts just hang off a non-existent anchor and are invisible.
// But we bias toward "(start)" inserts and a small pool of remove targets.
const arbOp: fc.Arbitrary<Op> = fc.oneof(
  fc.record({
    kind: fc.constant("insert" as const),
    ch: fc.constantFrom("a", "b", "c", "d", "e"),
    after: fc.constant("0:0"),
  }),
  fc.record({
    kind: fc.constant("remove" as const),
    target: fc.constantFrom("1:0", "1:1", "1:2", "2:0", "2:1"),
  }),
);

describe("RGA", () => {
  it("lattice laws", () =>
    checkLattice(spec, arbOp, {
      abstractEq: (a, b) => {
        const sa = a.visible.map((n) => `${n.id}:${n.ch}`).join("|");
        const sb = b.visible.map((n) => `${n.id}:${n.ch}`).join("|");
        return sa === sb;
      },
    }));
});
