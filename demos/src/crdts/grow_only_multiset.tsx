import { useState } from "react";
import type { CRDTSpec } from "../harness/types";

// Σ = map (rid, eid) -> count.  Add(eid) at rid bumps [(rid, eid)] by 1.
// Merge = per-key max.  Abstract = multiset of eids (sum over rids).
export type Concrete = Map<string, number>;
export type Abstract = { elem: number; count: number }[];
export type Op = { kind: "add"; elem: number };

function key(rid: number, eid: number): string {
  return `${rid}:${eid}`;
}

export const spec: CRDTSpec<Concrete, Abstract, Op> = {
  name: "Grow-Only Multiset",
  slug: "g-multiset",
  tagline:
    "Like a grow-only set, but each replica tracks its own per-element count. Merge = per-(replica, element) max. Abstract view sums counts across replicas.",
  init: new Map(),
  apply(s, op, meta) {
    const k = key(meta.rid, op.elem);
    const out = new Map(s);
    out.set(k, (out.get(k) ?? 0) + 1);
    return out;
  },
  merge(a, b) {
    const out = new Map(a);
    for (const [k, v] of b) out.set(k, Math.max(out.get(k) ?? 0, v));
    return out;
  },
  abstract(s) {
    const sums = new Map<number, number>();
    for (const [k, v] of s) {
      const [, eidStr] = k.split(":");
      const eid = Number(eidStr);
      sums.set(eid, (sums.get(eid) ?? 0) + v);
    }
    return [...sums.entries()]
      .sort((a, b) => a[0] - b[0])
      .map(([elem, count]) => ({ elem, count }));
  },
  renderAbstract(a) {
    if (a.length === 0) return <em>∅</em>;
    return <code>{`{ ${a.map((x) => `${x.elem}×${x.count}`).join(", ")} }`}</code>;
  },
  renderConcrete(s) {
    const rows = [...s.entries()]
      .map(([k, count]) => {
        const [rid, eid] = k.split(":").map(Number);
        return { rid, eid, count };
      })
      .sort((a, b) => a.rid - b.rid || a.eid - b.eid);
    if (rows.length === 0) return <em>∅</em>;
    return (
      <table>
        <thead>
          <tr>
            <th>rid</th>
            <th>eid</th>
            <th>count</th>
          </tr>
        </thead>
        <tbody>
          {rows.map((r) => (
            <tr key={`${r.rid}:${r.eid}`}>
              <td>R{r.rid}</td>
              <td>{r.eid}</td>
              <td>{r.count}</td>
            </tr>
          ))}
        </tbody>
      </table>
    );
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
