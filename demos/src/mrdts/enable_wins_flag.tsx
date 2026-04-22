import type { MRDTSpec } from "../harness/mrdt_types";

// Σ = (counter : Int, flag : Bool).
//   Enable  → (c + 1, true)
//   Disable → (c, false)
// Merge (per Lean): counter = a.c + b.c - l.c
// Merge flag (merge_flag in Lean) is a hand-written 4-case rule:
//   both a & b have flag=true           → true
//   both a & b have flag=false          → false
//   only a has flag=true                → a.c > l.c
//   only b has flag=true                → b.c > l.c
//
// This MRDT is the Sal paper's canonical counterexample: VC `inter_right_1op`
// fails, and Plausible rediscovers a minimal failing execution. Implementing
// it faithfully here lets the DAG playground drive users into that scenario.
export type Concrete = { counter: number; flag: boolean };
export type Abstract = boolean;
export type Op = { kind: "enable" } | { kind: "disable" };

function mergeFlag(
  l: Concrete,
  a: Concrete,
  b: Concrete,
): boolean {
  if (a.flag && b.flag) return true;
  if (!a.flag && !b.flag) return false;
  if (a.flag) return a.counter > l.counter;
  return b.counter > l.counter;
}

export const spec: MRDTSpec<Concrete, Abstract, Op> = {
  name: "Enable-Wins Flag",
  slug: "enable-wins-flag",
  tagline:
    "Boolean with a concurrent-enable-beats-disable resolution. ⚠ Known buggy — the inter_right_1op VC fails in the Sal paper; Plausible rediscovers the counterexample. Try Enable → diverge → Disable on one side, Enable on the other, Merge to see surprising flag flips.",
  init: { counter: 0, flag: false },
  apply(s, op, _meta) {
    void _meta;
    if (op.kind === "enable") return { counter: s.counter + 1, flag: true };
    return { counter: s.counter, flag: false };
  },
  merge(l, a, b) {
    return {
      counter: a.counter + b.counter - l.counter,
      flag: mergeFlag(l, a, b),
    };
  },
  abstract(s) {
    return s.flag;
  },
  renderAbstract(a) {
    return (
      <span
        className="big-number"
        style={{ color: a ? "#2da44e" : "#d93a49" }}
      >
        {a ? "enabled" : "disabled"}
      </span>
    );
  },
  renderConcrete(s) {
    return (
      <code>
        (counter={s.counter}, flag={s.flag ? "true" : "false"})
      </code>
    );
  },
  opForm({ dispatch }) {
    return (
      <div className="op-buttons">
        <button onClick={() => dispatch({ kind: "enable" })}>enable</button>
        <button onClick={() => dispatch({ kind: "disable" })}>disable</button>
      </div>
    );
  },
  formatOp(op, meta) {
    return `R${meta.rid} ${op.kind}`;
  },
};
