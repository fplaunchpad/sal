import { describe, it } from "vitest";
import fc from "fast-check";
import { checkMRDTLaws } from "../../harness/mrdt_invariants";
import { spec } from "../increment_only_counter";

describe("Increment-Only Counter MRDT", () => {
  it("merge laws", () =>
    checkMRDTLaws(spec, fc.constant({ kind: "incr" as const })));
});
