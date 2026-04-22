import { useState } from "react";
import type { MRDTSpec } from "../harness/mrdt_types";

// PN-counter MRDT: the scalar Int counter extended to integer-valued ops.
// Σ = Int, do(s, +v)=s+v, do(s, -v)=s-v, merge(l,a,b)=a+b-l.
export type Concrete = number;
export type Abstract = number;
export type Op = { kind: "inc"; amount: number } | { kind: "dec"; amount: number };

export const spec: MRDTSpec<Concrete, Abstract, Op> = {
  name: "PN-Counter",
  slug: "pn-counter",
  tagline:
    "Same closed-form as the Inc-only counter but with signed ops: do adds or subtracts, merge is a + b − l. Concurrent + and − compose without surprises.",
  init: 0,
  apply(s, op, _meta) {
    void _meta;
    return op.kind === "inc" ? s + op.amount : s - op.amount;
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
    return <Form dispatch={dispatch} />;
  },
  formatOp(op, meta) {
    const sign = op.kind === "inc" ? "+" : "−";
    return `R${meta.rid} ${sign}${op.amount}`;
  },
};

function Form({ dispatch }: { dispatch: (op: Op) => void }) {
  const [amount, setAmount] = useState(1);
  return (
    <div className="op-buttons">
      <input
        type="number"
        min={1}
        value={amount}
        onChange={(e) => setAmount(Math.max(1, Number(e.target.value) || 1))}
      />
      <button onClick={() => dispatch({ kind: "inc", amount })}>+{amount}</button>
      <button onClick={() => dispatch({ kind: "dec", amount })}>−{amount}</button>
    </div>
  );
}
