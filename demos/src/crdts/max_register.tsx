import { useState } from "react";
import type { CRDTSpec } from "../harness/types";

// Σ = ℕ  (init 0; writes do max; merge = max)
export type Concrete = number;
export type Abstract = number;
export type Op = { kind: "write"; value: number };

export const spec: CRDTSpec<Concrete, Abstract, Op> = {
  name: "MAX-Register",
  slug: "max-register",
  tagline:
    "State is one natural number. A write sets state := max(state, v); merge = max. Monotonically non-decreasing.",
  init: 0,
  apply(s, op, _meta) {
    void _meta;
    return op.value >= 0 ? Math.max(s, op.value) : s;
  },
  merge(a, b) {
    return Math.max(a, b);
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
  const [v, setV] = useState(1);
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
