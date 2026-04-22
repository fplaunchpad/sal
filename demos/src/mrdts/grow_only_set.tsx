import { useState } from "react";
import type { MRDTSpec } from "../harness/mrdt_types";

// Σ = set of naturals.  do adds; merge uses LCA to detect concurrent adds,
// but for a G-set the LCA is redundant — we simply union everything.
// Kept here as a pedagogical first set example contrasting the Inc-counter.
export type Concrete = Set<number>;
export type Abstract = number[];
export type Op = { kind: "add"; elem: number };

export const spec: MRDTSpec<Concrete, Abstract, Op> = {
  name: "Grow-Only Set",
  slug: "g-set",
  tagline:
    "G-set MRDT. do adds an element; merge(l, a, b) = a ∪ b (the LCA is subsumed by the union). Adds a minimal case where the LCA argument is vestigial.",
  init: new Set(),
  apply(s, op, _meta) {
    void _meta;
    const out = new Set(s);
    out.add(op.elem);
    return out;
  },
  merge(_l, a, b) {
    return new Set([...a, ...b]);
  },
  abstract(s) {
    return [...s].sort((x, y) => x - y);
  },
  renderAbstract(a) {
    return a.length === 0 ? (
      <em>∅</em>
    ) : (
      <code>{`{ ${a.join(", ")} }`}</code>
    );
  },
  renderConcrete(s) {
    const arr = [...s].sort((x, y) => x - y);
    return arr.length === 0 ? <em>∅</em> : <code>{`{ ${arr.join(", ")} }`}</code>;
  },
  opForm({ dispatch }) {
    return <Form dispatch={dispatch} />;
  },
  formatOp(op, meta) {
    return `R${meta.rid} add(${op.elem})`;
  },
};

function Form({ dispatch }: { dispatch: (op: Op) => void }) {
  const [e, setE] = useState(0);
  return (
    <div className="op-buttons">
      <input
        type="number"
        min={0}
        value={e}
        onChange={(ev) => setE(Math.max(0, Number(ev.target.value) || 0))}
      />
      <button onClick={() => dispatch({ kind: "add", elem: e })}>add</button>
    </div>
  );
}
