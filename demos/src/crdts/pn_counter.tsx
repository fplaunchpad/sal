import { useState } from "react";
import type { CRDTSpec, OpMeta } from "../harness/types";

// Σ = (incs : map rid -> Nat, decs : map rid -> Nat)
// abstract value = sum(incs) - sum(decs)
export type Concrete = {
  incs: Map<number, number>;
  decs: Map<number, number>;
};
export type Abstract = number;
export type Op = { kind: "inc"; amount: number } | { kind: "dec"; amount: number };

function sumMap(m: Map<number, number>): number {
  let s = 0;
  for (const n of m.values()) s += n;
  return s;
}

function mergeMaxMap(
  a: Map<number, number>,
  b: Map<number, number>,
): Map<number, number> {
  const out = new Map(a);
  for (const [k, v] of b) out.set(k, Math.max(out.get(k) ?? 0, v));
  return out;
}

export const spec: CRDTSpec<Concrete, Abstract, Op> = {
  name: "PN-Counter",
  slug: "pn-counter",
  tagline:
    "Two G-counters glued together: one tracks increments, one tracks decrements. The abstract value is their difference.",
  init: { incs: new Map(), decs: new Map() },

  apply(s: Concrete, op: Op, meta: OpMeta): Concrete {
    if (op.amount <= 0) return s;
    if (op.kind === "inc") {
      const incs = new Map(s.incs);
      incs.set(meta.rid, (incs.get(meta.rid) ?? 0) + op.amount);
      return { ...s, incs };
    } else {
      const decs = new Map(s.decs);
      decs.set(meta.rid, (decs.get(meta.rid) ?? 0) + op.amount);
      return { ...s, decs };
    }
  },

  merge(a: Concrete, b: Concrete): Concrete {
    return {
      incs: mergeMaxMap(a.incs, b.incs),
      decs: mergeMaxMap(a.decs, b.decs),
    };
  },

  abstract(s: Concrete): Abstract {
    return sumMap(s.incs) - sumMap(s.decs);
  },

  renderAbstract(a: Abstract) {
    return <span className="big-number">{a}</span>;
  },

  renderConcrete(s: Concrete) {
    const rids = new Set<number>([...s.incs.keys(), ...s.decs.keys()]);
    const rows = [...rids].sort((x, y) => x - y);
    if (rows.length === 0) return <em>∅</em>;
    return (
      <table>
        <thead>
          <tr>
            <th>replica</th>
            <th>+</th>
            <th>−</th>
          </tr>
        </thead>
        <tbody>
          {rows.map((rid) => (
            <tr key={rid}>
              <td>
                <code>R{rid}</code>
              </td>
              <td>{s.incs.get(rid) ?? 0}</td>
              <td>{s.decs.get(rid) ?? 0}</td>
            </tr>
          ))}
        </tbody>
      </table>
    );
  },

  opForm({ dispatch }) {
    return <OpForm dispatch={dispatch} />;
  },

  formatOp(op: Op, meta: OpMeta) {
    const sign = op.kind === "inc" ? "+" : "−";
    return `R${meta.rid} ${sign}${op.amount}`;
  },
};

function OpForm({ dispatch }: { dispatch: (op: Op) => void }) {
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
