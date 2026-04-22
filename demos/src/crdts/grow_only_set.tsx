import { useState } from "react";
import type { CRDTSpec } from "../harness/types";

// Σ = set of natural numbers.  Only op is Add; merge = union.
export type Concrete = Set<number>;
export type Abstract = number[];
export type Op = { kind: "add"; elem: number };

export const spec: CRDTSpec<Concrete, Abstract, Op> = {
  name: "Grow-Only Set",
  slug: "g-set",
  tagline:
    "The simplest set CRDT. Only op is Add; state only grows; merge = union. No removes — tombstones aren't needed because nothing is ever deleted.",
  init: new Set(),
  apply(s, op, _meta) {
    void _meta;
    const out = new Set(s);
    out.add(op.elem);
    return out;
  },
  merge(a, b) {
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
    return <AddForm dispatch={dispatch} />;
  },
  formatOp(op, meta) {
    return `R${meta.rid} add(${op.elem})`;
  },
};

function AddForm({ dispatch }: { dispatch: (op: Op) => void }) {
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
