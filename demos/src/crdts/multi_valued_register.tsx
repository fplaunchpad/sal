import { useState } from "react";
import type { CRDTSpec } from "../harness/types";

// Σ = set of (ts, value). The Lean spec accumulates every write rather than
// replacing observed ones — so "abstract" surfaces the distinct values ever
// written, and the concrete view shows the full append-only log.
type Entry = { value: number; ts: number };

export type Concrete = Entry[]; // kept sorted for stable rendering
export type Abstract = number[];
export type Op = { kind: "write"; value: number };

function sortedDedup(xs: Entry[]): Entry[] {
  const keyed = new Map<string, Entry>();
  for (const e of xs) keyed.set(`${e.ts}:${e.value}`, e);
  return [...keyed.values()].sort((a, b) =>
    a.ts !== b.ts ? a.ts - b.ts : a.value - b.value,
  );
}

export const spec: CRDTSpec<Concrete, Abstract, Op> = {
  name: "Multi-Valued Register",
  slug: "mv-register",
  tagline:
    "Per the Lean spec, a write simply adds (ts, value) to the state. Merge = union; state accumulates. The abstract view surfaces the distinct values ever written — concurrent writes both survive.",
  init: [],
  apply(s, op, meta) {
    return sortedDedup([...s, { value: op.value, ts: meta.ts }]);
  },
  merge(a, b) {
    return sortedDedup([...a, ...b]);
  },
  abstract(s) {
    const vals = [...new Set(s.map((e) => e.value))];
    return vals.sort((x, y) => x - y);
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
            <th>value</th>
            <th>ts</th>
          </tr>
        </thead>
        <tbody>
          {s.map((e) => (
            <tr key={`${e.ts}:${e.value}`}>
              <td>{e.value}</td>
              <td>{e.ts}</td>
            </tr>
          ))}
        </tbody>
      </table>
    );
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
        value={v}
        onChange={(e) => setV(Number(e.target.value) || 0)}
      />
      <button onClick={() => dispatch({ kind: "write", value: v })}>
        write
      </button>
    </div>
  );
}
