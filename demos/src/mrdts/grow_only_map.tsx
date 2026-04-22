import { useState } from "react";
import type { MRDTSpec } from "../harness/mrdt_types";

// Σ = Map<key, Set<value>>.  Put(k, v) adds v to the set at key k.
// Merge unions each key's sets from l, a, b.
export type Concrete = Map<number, Set<number>>;
export type Abstract = { key: number; values: number[] }[];
export type Op = { kind: "put"; key: number; value: number };

function keysOf(...maps: Concrete[]): number[] {
  const s = new Set<number>();
  for (const m of maps) for (const k of m.keys()) s.add(k);
  return [...s].sort((a, b) => a - b);
}

export const spec: MRDTSpec<Concrete, Abstract, Op> = {
  name: "Grow-Only Map",
  slug: "g-map",
  tagline:
    "Per-key grow-only set. Put(k, v) adds v to state[k]; merge unions all three sides per key. A hybrid between a map and a G-set.",
  init: new Map(),
  apply(s, op, _meta) {
    void _meta;
    const out = new Map(s);
    const cur = new Set(out.get(op.key) ?? new Set<number>());
    cur.add(op.value);
    out.set(op.key, cur);
    return out;
  },
  merge(l, a, b) {
    const out = new Map<number, Set<number>>();
    for (const k of keysOf(l, a, b)) {
      const u = new Set<number>([
        ...(l.get(k) ?? []),
        ...(a.get(k) ?? []),
        ...(b.get(k) ?? []),
      ]);
      out.set(k, u);
    }
    return out;
  },
  abstract(s) {
    return [...s.entries()]
      .sort((x, y) => x[0] - y[0])
      .map(([key, vs]) => ({
        key,
        values: [...vs].sort((a, b) => a - b),
      }));
  },
  renderAbstract(a) {
    if (a.length === 0) return <em>∅</em>;
    return (
      <ul style={{ margin: 0, paddingLeft: "1.25rem" }}>
        {a.map(({ key, values }) => (
          <li key={key}>
            <code>{key}</code> → <code>{`{ ${values.join(", ")} }`}</code>
          </li>
        ))}
      </ul>
    );
  },
  renderConcrete(s) {
    const keys = [...s.keys()].sort((a, b) => a - b);
    if (keys.length === 0) return <em>∅</em>;
    return (
      <table>
        <thead>
          <tr>
            <th>key</th>
            <th>values</th>
          </tr>
        </thead>
        <tbody>
          {keys.map((k) => (
            <tr key={k}>
              <td>{k}</td>
              <td>
                <code>{`{ ${[...(s.get(k) ?? [])].sort((a, b) => a - b).join(", ")} }`}</code>
              </td>
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
    return `R${meta.rid} put(k=${op.key}, v=${op.value})`;
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
          min={0}
          value={v}
          onChange={(e) => setV(Math.max(0, Number(e.target.value) || 0))}
        />
      </label>
      <button onClick={() => dispatch({ kind: "put", key: k, value: v })}>
        put
      </button>
    </div>
  );
}
