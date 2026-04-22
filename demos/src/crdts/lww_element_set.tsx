import { useState } from "react";
import type { CRDTSpec } from "../harness/types";

// Σ = (addTs : Map id -> ts, remTs : Map id -> ts)
// e ∈ set  iff  addTs[e] > remTs[e]  (add wins on ties? usually add wins;
// Lean uses strict > on remove, i.e. add wins when ts_add >= ts_rem).
// Here: e ∈ set iff addTs[e] > remTs[e] — ties go to remove (safe side).
export type Concrete = {
  addTs: Map<number, number>;
  remTs: Map<number, number>;
};
export type Abstract = number[];
export type Op =
  | { kind: "add"; elem: number }
  | { kind: "remove"; elem: number };

function mergeMaxMap(
  a: Map<number, number>,
  b: Map<number, number>,
): Map<number, number> {
  const out = new Map(a);
  for (const [k, v] of b) out.set(k, Math.max(out.get(k) ?? 0, v));
  return out;
}

export const spec: CRDTSpec<Concrete, Abstract, Op> = {
  name: "LWW-Element-Set",
  slug: "lww-element-set",
  tagline:
    "Two timestamp maps, one for adds, one for removes. An element is live when its latest add timestamp beats its latest remove. Merge = per-key max on both maps.",
  init: { addTs: new Map(), remTs: new Map() },
  apply(s, op, meta) {
    const ts = meta.ts + 1; // keep 0 as "never"
    if (op.kind === "add") {
      const addTs = new Map(s.addTs);
      addTs.set(op.elem, Math.max(addTs.get(op.elem) ?? 0, ts));
      return { ...s, addTs };
    } else {
      const remTs = new Map(s.remTs);
      remTs.set(op.elem, Math.max(remTs.get(op.elem) ?? 0, ts));
      return { ...s, remTs };
    }
  },
  merge(a, b) {
    return {
      addTs: mergeMaxMap(a.addTs, b.addTs),
      remTs: mergeMaxMap(a.remTs, b.remTs),
    };
  },
  abstract(s) {
    const elems = new Set<number>([...s.addTs.keys(), ...s.remTs.keys()]);
    const live: number[] = [];
    for (const e of elems) {
      const addT = s.addTs.get(e) ?? 0;
      const remT = s.remTs.get(e) ?? 0;
      if (addT > remT) live.push(e);
    }
    return live.sort((x, y) => x - y);
  },
  renderAbstract(a) {
    return a.length === 0 ? (
      <em>∅</em>
    ) : (
      <code>{`{ ${a.join(", ")} }`}</code>
    );
  },
  renderConcrete(s) {
    const elems = [
      ...new Set<number>([...s.addTs.keys(), ...s.remTs.keys()]),
    ].sort((a, b) => a - b);
    if (elems.length === 0) return <em>∅</em>;
    return (
      <table>
        <thead>
          <tr>
            <th>elem</th>
            <th>addTs</th>
            <th>remTs</th>
            <th>live?</th>
          </tr>
        </thead>
        <tbody>
          {elems.map((e) => {
            const add = s.addTs.get(e) ?? 0;
            const rem = s.remTs.get(e) ?? 0;
            return (
              <tr key={e}>
                <td>{e}</td>
                <td>{add || "—"}</td>
                <td>{rem || "—"}</td>
                <td>{add > rem ? "✓" : ""}</td>
              </tr>
            );
          })}
        </tbody>
      </table>
    );
  },
  opForm({ dispatch }) {
    return <Form dispatch={dispatch} />;
  },
  formatOp(op, meta) {
    return op.kind === "add"
      ? `R${meta.rid} add(${op.elem})`
      : `R${meta.rid} remove(${op.elem})`;
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
      <button onClick={() => dispatch({ kind: "remove", elem: e })}>
        remove
      </button>
    </div>
  );
}
