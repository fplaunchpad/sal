import { useState } from "react";
import type { CRDTSpec } from "../harness/types";

// Σ = map key -> value.  Per-key max.
export type Concrete = Map<number, number>;
export type Abstract = Map<number, number>;
export type Op = { kind: "write"; key: number; value: number };

export const spec: CRDTSpec<Concrete, Abstract, Op> = {
  name: "MAX-Map",
  slug: "max-map",
  tagline:
    "Per-key MAX register. A write(k, v) sets state[k] := max(state[k], v); merge = per-key max. Monotonically non-decreasing per key.",
  init: new Map(),
  apply(s, op, _meta) {
    void _meta;
    if (op.value < 0) return s;
    const cur = s.get(op.key) ?? 0;
    if (op.value <= cur) return s;
    const out = new Map(s);
    out.set(op.key, op.value);
    return out;
  },
  merge(a, b) {
    const out = new Map(a);
    for (const [k, v] of b) out.set(k, Math.max(out.get(k) ?? 0, v));
    return out;
  },
  abstract(s) {
    return new Map(s);
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
    return (
      <table>
        <thead>
          <tr>
            <th>key</th>
            <th>value</th>
          </tr>
        </thead>
        <tbody>
          {[...s.entries()]
            .sort((a, b) => a[0] - b[0])
            .map(([k, v]) => (
              <tr key={k}>
                <td>{k}</td>
                <td>{v}</td>
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
  const [v, setV] = useState(1);
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
      <button onClick={() => dispatch({ kind: "write", key: k, value: v })}>
        write
      </button>
    </div>
  );
}
