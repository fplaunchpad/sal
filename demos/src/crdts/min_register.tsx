import { useState } from "react";
import type { CRDTSpec } from "../harness/types";

// Σ = ℕ  (init 0; writes do min; merge = min)
// Degenerate on ℕ with init 0: state stays 0 once initialised. The Lean
// file documents this explicitly; we mirror the spec and flag the quirk
// in the tagline.
export type Concrete = number;
export type Abstract = number;
export type Op = { kind: "write"; value: number };

export const spec: CRDTSpec<Concrete, Abstract, Op> = {
  name: "MIN-Register",
  slug: "min-register",
  tagline:
    "State is one natural number. Write v sets state := min(state, v); merge = min. With init 0 and ℕ writes this is semantically degenerate (state stays 0): a lattice-law pedagogy case, not a useful CRDT.",
  init: 0,
  apply(s, op, _meta) {
    void _meta;
    return op.value >= 0 ? Math.min(s, op.value) : s;
  },
  merge(a, b) {
    return Math.min(a, b);
  },
  abstract(s) {
    return s;
  },
  renderAbstract(a) {
    return <span className="big-number">{a}</span>;
  },
  renderConcrete(s) {
    return <code>{s}</code>;
  },
  opForm({ dispatch }) {
    return <WriteForm dispatch={dispatch} />;
  },
  formatOp(op, meta) {
    return `R${meta.rid} write(${op.value})`;
  },
};

function WriteForm({ dispatch }: { dispatch: (op: Op) => void }) {
  const [v, setV] = useState(0);
  return (
    <div className="op-buttons">
      <input
        type="number"
        min={0}
        value={v}
        onChange={(e) => setV(Math.max(0, Number(e.target.value) || 0))}
      />
      <button onClick={() => dispatch({ kind: "write", value: v })}>
        write
      </button>
    </div>
  );
}
