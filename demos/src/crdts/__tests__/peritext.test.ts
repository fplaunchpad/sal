import { describe, it } from "vitest";
import fc from "fast-check";
import { checkLattice } from "../../harness/invariants";
import { spec, type Op } from "../peritext";

const arbOp: fc.Arbitrary<Op> = fc.oneof(
  fc.record({
    kind: fc.constant("insert" as const),
    ch: fc.constantFrom("a", "b", "c"),
    after: fc.constant("0:0"),
  }),
  fc.record({
    kind: fc.constant("remove" as const),
    target: fc.constantFrom("1:0", "2:1", "3:2"),
  }),
  fc.record({
    kind: fc.constant("addMark" as const),
    startId: fc.constantFrom("1:0", "2:1"),
    endId: fc.constantFrom("1:0", "2:1", "3:0"),
    mtype: fc.constantFrom("bold" as const, "italic" as const),
  }),
  fc.record({
    kind: fc.constant("removeMark" as const),
    startId: fc.constantFrom("1:0", "2:1"),
    endId: fc.constantFrom("1:0", "2:1", "3:0"),
    mtype: fc.constantFrom("bold" as const, "italic" as const),
  }),
);

describe("Peritext", () => {
  it("lattice laws", () =>
    checkLattice(spec, arbOp, {
      abstractEq: (a, b) => {
        const fmt = (
          xs: { id: string; ch: string; bold: boolean; italic: boolean }[],
        ) =>
          xs
            .map((n) => `${n.id}:${n.ch}:${n.bold ? "B" : ""}${n.italic ? "I" : ""}`)
            .join("|");
        return fmt(a.visible) === fmt(b.visible);
      },
    }));
});
