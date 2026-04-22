import { useState } from "react";
import type { CRDTSpec } from "../harness/types";

// Σ = map (ts, rid, prio) -> elem.  Insert-only priority queue; no removal.
// Read-side projection sorts by (prio, ts).
type Key = { ts: number; rid: number; prio: number };
export type Concrete = Map<string, { key: Key; elem: number }>;
export type Abstract = { prio: number; elem: number; ts: number }[];
export type Op = { kind: "push"; prio: number; elem: number };

function keyStr(k: Key): string {
  return `${k.ts}:${k.rid}:${k.prio}`;
}

export const spec: CRDTSpec<Concrete, Abstract, Op> = {
  name: "Insert-Only Priority Queue",
  slug: "pq-insert-only",
  tagline:
    "Keys are (timestamp, replica id, priority); entries are never removed. Merge = map union. Abstract view sorts by priority, then by insertion timestamp.",
  init: new Map(),
  apply(s, op, meta) {
    const k: Key = { ts: meta.ts, rid: meta.rid, prio: op.prio };
    const out = new Map(s);
    out.set(keyStr(k), { key: k, elem: op.elem });
    return out;
  },
  merge(a, b) {
    const out = new Map(a);
    for (const [k, v] of b) if (!out.has(k)) out.set(k, v);
    return out;
  },
  abstract(s) {
    return [...s.values()]
      .map(({ key, elem }) => ({ prio: key.prio, elem, ts: key.ts }))
      .sort((a, b) => a.prio - b.prio || a.ts - b.ts);
  },
  renderAbstract(a) {
    if (a.length === 0) return <em>empty queue</em>;
    return (
      <ol>
        {a.map((e, i) => (
          <li key={i}>
            <code>prio {e.prio}</code> → {e.elem}
          </li>
        ))}
      </ol>
    );
  },
  renderConcrete(s) {
    const rows = [...s.values()].sort(
      (a, b) => a.key.ts - b.key.ts || a.key.rid - b.key.rid,
    );
    if (rows.length === 0) return <em>∅</em>;
    return (
      <table>
        <thead>
          <tr>
            <th>ts</th>
            <th>rid</th>
            <th>prio</th>
            <th>elem</th>
          </tr>
        </thead>
        <tbody>
          {rows.map((row) => (
            <tr key={keyStr(row.key)}>
              <td>{row.key.ts}</td>
              <td>R{row.key.rid}</td>
              <td>{row.key.prio}</td>
              <td>{row.elem}</td>
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
    return `R${meta.rid} push(prio=${op.prio}, elem=${op.elem})`;
  },
};

function Form({ dispatch }: { dispatch: (op: Op) => void }) {
  const [prio, setPrio] = useState(1);
  const [elem, setElem] = useState(0);
  return (
    <div className="op-buttons">
      <label>
        prio
        <input
          type="number"
          min={0}
          value={prio}
          onChange={(e) => setPrio(Math.max(0, Number(e.target.value) || 0))}
        />
      </label>
      <label>
        elem
        <input
          type="number"
          min={0}
          value={elem}
          onChange={(e) => setElem(Math.max(0, Number(e.target.value) || 0))}
        />
      </label>
      <button onClick={() => dispatch({ kind: "push", prio, elem })}>
        push
      </button>
    </div>
  );
}
