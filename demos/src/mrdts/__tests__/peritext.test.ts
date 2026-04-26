import { describe, it } from "vitest";
import fc from "fast-check";
import { checkMRDTLaws } from "../../harness/mrdt_invariants";
import { spec, type Op } from "../peritext";

// Insert references the document-start anchor (ROOT="0:0"), and remove
// targets fixed dummy ids (which usually miss but exercise the tombstone
// growth). Mark ops anchor at ROOT on both ends so they're always
// well-formed regardless of generation order. The point of the property
// suite is the merge laws on the three grow-only components, not the
// rich-text rendering itself.
const arbOp: fc.Arbitrary<Op> = fc.oneof(
  fc.record({
    kind: fc.constant("insert" as const),
    ch: fc.constantFrom("a", "b", "c"),
    after: fc.constant("0:0"),
  }),
  fc.record({
    kind: fc.constant("remove" as const),
    target: fc.constant("0:0"),
  }),
  fc.record({
    kind: fc.constant("addMark" as const),
    startId: fc.constant("0:0"),
    endId: fc.constant("0:0"),
    mtype: fc.constantFrom("bold" as const, "italic" as const),
  }),
  fc.record({
    kind: fc.constant("removeMark" as const),
    startId: fc.constant("0:0"),
    endId: fc.constant("0:0"),
    mtype: fc.constantFrom("bold" as const, "italic" as const),
  }),
);

describe("Peritext MRDT", () => {
  it("merge laws", () =>
    checkMRDTLaws(spec, arbOp, {
      abstractEq: (a, b) => {
        const s = (xs: { id: string; ch: string; bold: boolean; italic: boolean }[]) =>
          xs.map((n) => `${n.id}:${n.ch}:${n.bold ? 1 : 0}:${n.italic ? 1 : 0}`).join("|");
        return s(a.visible) === s(b.visible);
      },
    }));
});
