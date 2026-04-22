import { describe, it } from "vitest";
import fc from "fast-check";
import { checkLattice } from "../../harness/invariants";
import { spec } from "../increment_only_counter";

describe("Increment-Only Counter", () => {
  it("satisfies the CRDT lattice laws", () => {
    checkLattice(spec, fc.constant({ kind: "inc" as const }));
  });
});
