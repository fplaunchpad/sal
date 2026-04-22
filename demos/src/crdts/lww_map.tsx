import { useState } from "react";
import type { CRDTSpec } from "../harness/types";

// Σ = map key -> (ts, rid, value).  Per-key lex-max on (ts, rid).
type Cell = { ts: number; rid: number; value: number };
export type Concrete = Map<number, Cell>;
export type Abstract = Map<number, number>;
export type Op = { kind: "write"; key: number; value: number };

function ltLex(a: Cell, b: Cell): boolean {
  return a.ts < b.ts || (a.ts === b.ts && a.rid < b.rid);
}

export const spec: CRDTSpec<Concrete, Abstract, Op> = {
  name: "LWW-Map",
  slug: "lww-map",
  tagline:
    "Last-Writer-Wins map. Per-key, the entry with the lex-max (timestamp, replica id) wins; concurrent writes to the same key are resolved by the rid tiebreaker.",
  init: new Map(),
  apply(s, op, meta) {
    const incoming: Cell = { ts: meta.ts, rid: meta.rid, value: op.value };
    const cur = s.get(op.key);
    if (cur && !ltLex(cur, incoming)) return s;
    const out = new Map(s);
    out.set(op.key, incoming);
    return out;
  },
  merge(a, b) {
    const out = new Map(a);
    for (const [k, cell] of b) {
      const cur = out.get(k);
      if (!cur || ltLex(cur, cell)) out.set(k, cell);
    }
    return out;
  },
  abstract(s) {
    const out = new Map<number, number>();
    for (const [k, c] of s) out.set(k, c.value);
    return out;
  },
  renderAbstract(a) {
    if (a.size === 0) return <em>∅</em>;
    const pairs = [...a.entries()]
      .sort((x, y) => x[0] - y[0])
      .map(([k, v]) => `${k}→${v}`);
    return <code>{`{ ${pairs.join(", ")} }`}</code>;
  },
  renderConcrete(s) {
    if (s.size === 0) return <em>∅</em>;
    const rows = [...s.entries()].sort((x, y) => x[0] - y[0]);
    return (
      <table>
        <thead>
          <tr>
            <th>key</th>
            <th>value</th>
            <th>ts</th>
            <th>rid</th>
          </tr>
        </thead>
        <tbody>
          {rows.map(([k, c]) => (
            <tr key={k}>
              <td>{k}</td>
              <td>{c.value}</td>
              <td>{c.ts}</td>
              <td>R{c.rid}</td>
            </tr>
          ))}
        </tbody>
      </table>
    );
  },
  opForm({ dispatch }) {
    return <Form dispatch={dispatch} />;
  },
  formatOp(op, meta) {
    return `R${meta.rid} write(k=${op.key}, v=${op.value})`;
  },
};

function Form({ dispatch }: { dispatch: (op: Op) => void }) {
  const [k, setK] = useState(0);
  const [v, setV] = useState(0);
  return (
    <div className="op-buttons">
      <label>
        k=
        <input
          type="number"
          min={0}
          value={k}
          onChange={(e) => setK(Math.max(0, Number(e.target.value) || 0))}
        />
      </label>
      <label>
        v=
        <input
          type="number"
          value={v}
          onChange={(e) => setV(Number(e.target.value) || 0)}
        />
      </label>
      <button onClick={() => dispatch({ kind: "write", key: k, value: v })}>
        write
      </button>
    </div>
  );
}
