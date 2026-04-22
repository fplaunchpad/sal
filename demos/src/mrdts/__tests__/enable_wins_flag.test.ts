import { describe, it } from "vitest";
import fc from "fast-check";
import { checkMRDTLaws } from "../../harness/mrdt_invariants";
import { spec, type Op } from "../enable_wins_flag";

const arbOp: fc.Arbitrary<Op> = fc.oneof(
  fc.record({ kind: fc.constant("enable" as const) }),
  fc.record({ kind: fc.constant("disable" as const) }),
);

describe("Enable-Wins Flag MRDT", () => {
  // The three base laws (left identity, right identity, commutativity) hold
  // for Enable-Wins Flag even though the Sal paper's inter_right_1op VC fails
  // — the bug only manifests in a specific four-state history scenario that
  // requires the DAG to expose, not a closed-form property check. Plausible
  // rediscovers it from the Lean side; the playground lets you reproduce it
  // interactively.
  it("merge laws", () => checkMRDTLaws(spec, arbOp));
});
