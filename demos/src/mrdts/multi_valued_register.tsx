import { useState } from "react";
import type { MRDTSpec } from "../harness/mrdt_types";

// Σ = set of (ts, value); Write v adds (ts, v); merge = l ∪ a ∪ b.
type Entry = { ts: number; value: number };

export type Concrete = Entry[];
export type Abstract = number[];
export type Op = { kind: "write"; value: number };

function dedup(xs: Entry[]): Entry[] {
  const m = new Map<string, Entry>();
  for (const e of xs) m.set(`${e.ts}:${e.value}`, e);
  return [...m.values()].sort((a, b) => a.ts - b.ts || a.value - b.value);
}

export const spec: MRDTSpec<Concrete, Abstract, Op> = {
  name: "Multi-Valued Register",
  slug: "mv-register",
  tagline:
    "Every write adds (ts, v) to the state; merge unions all three sides. The user-facing value is the set of distinct values ever written.",
  init: [],
  apply(s, op, meta) {
    return dedup([...s, { ts: meta.ts, value: op.value }]);
  },
  merge(l, a, b) {
    return dedup([...l, ...a, ...b]);
  },
  abstract(s) {
    return [...new Set(s.map((e) => e.value))].sort((x, y) => x - y);
  },
  renderAbstract(a) {
    if (a.length === 0) return <em>∅</em>;
    if (a.length === 1) return <span className="big-number">{a[0]}</span>;
    return <code>{`{ ${a.join(", ")} }`}</code>;
  },
  renderConcrete(s) {
    if (s.length === 0) return <em>∅</em>;
    return (
      <table>
        <thead>
          <tr>
            <th>ts</th>
            <th>value</th>
          </tr>
        </thead>
        <tbody>
          {s.map((e) => (
            <tr key={`${e.ts}:${e.value}`}>
              <td>{e.ts}</td>
              <td>{e.value}</td>
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
    return `R${meta.rid} write(${op.value})`;
  },
};

function Form({ dispatch }: { dispatch: (op: Op) => void }) {
  const [v, setV] = useState(1);
  return (
    <div className="op-buttons">
      <input
        type="number"
        value={v}
        onChange={(e) => setV(Number(e.target.value) || 0)}
      />
      <button onClick={() => dispatch({ kind: "write", value: v })}>
        write
      </button>
    </div>
  );
}
