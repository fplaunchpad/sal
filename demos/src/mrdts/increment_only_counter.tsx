import type { MRDTSpec } from "../harness/mrdt_types";

// The canonical "Git for data types" teaching example.
// Σ = Int.  do(s, Incr) = s + 1.  merge(l, a, b) = a + b - l.
// The LCA-subtracting trick converts the non-commutative `+1` op
// into a commutative 3-way merge.
export type Concrete = number;
export type Abstract = number;
export type Op = { kind: "incr" };

export const spec: MRDTSpec<Concrete, Abstract, Op> = {
  name: "Increment-Only Counter",
  slug: "inc-counter",
  tagline:
    "Σ = Int, incr adds 1 per op. Merge is the closed-form a + b − l — the LCA's value is subtracted out so concurrent increments aren't double-counted.",
  init: 0,
  apply(s, _op, _meta) {
    void _op;
    void _meta;
    return s + 1;
  },
  merge(l, a, b) {
    return a + b - l;
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
    return (
      <div className="op-buttons">
        <button onClick={() => dispatch({ kind: "incr" })}>+1</button>
      </div>
    );
  },
  formatOp(_op, meta) {
    void _op;
    return `R${meta.rid} incr`;
  },
};
