import { useState } from "react";
import type { MRDTSpec } from "../harness/mrdt_types";

// Σ = (adds : Set<(ts, (afterTs, ele))>, removes : Set<ts>).
// Timestamps are the globally-unique OpIds (here: integers). Sentinel ts=0
// is reserved as the document-start anchor.
// Merge pointwise-unions both components of l, a, b.
type Add = { ts: number; afterTs: number; ele: number };
export type Concrete = { adds: Add[]; removes: Set<number> };
export type Abstract = { visible: { ts: number; ele: number }[] };
export type Op =
  | { kind: "insert"; after: number; ele: number }
  | { kind: "remove"; target: number };

function dedupAdds(xs: Add[]): Add[] {
  const m = new Map<number, Add>();
  for (const a of xs) m.set(a.ts, a);
  return [...m.values()].sort((x, y) => x.ts - y.ts);
}

function traverse(s: Concrete): { ts: number; ele: number; deleted: boolean }[] {
  // Children sorted by ts descending (newer inserts nearer the anchor).
  const children = new Map<number, Add[]>();
  for (const a of s.adds) {
    const arr = children.get(a.afterTs) ?? [];
    arr.push(a);
    children.set(a.afterTs, arr);
  }
  for (const arr of children.values()) arr.sort((a, b) => b.ts - a.ts);
  const out: { ts: number; ele: number; deleted: boolean }[] = [];
  const visit = (anchor: number) => {
    for (const c of children.get(anchor) ?? []) {
      out.push({ ts: c.ts, ele: c.ele, deleted: s.removes.has(c.ts) });
      visit(c.ts);
    }
  };
  visit(0);
  return out;
}

export const spec: MRDTSpec<Concrete, Abstract, Op> = {
  name: "Replicated Growable Array (RGA)",
  slug: "rga",
  tagline:
    "Sequence MRDT: inserts keyed by ts with afterTs predecessor, removes tombstone by ts. Merge unions the two components from all three sides.",
  init: { adds: [], removes: new Set() },
  apply(s, op, meta) {
    if (op.kind === "insert") {
      return {
        adds: dedupAdds([
          ...s.adds,
          { ts: meta.ts + 1, afterTs: op.after, ele: op.ele },
        ]),
        removes: s.removes,
      };
    } else {
      const removes = new Set(s.removes);
      removes.add(op.target);
      return { adds: s.adds, removes };
    }
  },
  merge(l, a, b) {
    return {
      adds: dedupAdds([...l.adds, ...a.adds, ...b.adds]),
      removes: new Set<number>([...l.removes, ...a.removes, ...b.removes]),
    };
  },
  abstract(s) {
    const seq = traverse(s).filter((n) => !n.deleted);
    return { visible: seq.map((n) => ({ ts: n.ts, ele: n.ele })) };
  },
  renderAbstract(a) {
    if (a.visible.length === 0) return <em>∅ (empty)</em>;
    return (
      <code style={{ fontSize: "1.1rem" }}>
        [{a.visible.map((c) => c.ele).join(", ")}]
      </code>
    );
  },
  renderConcrete(s) {
    const nodes = traverse(s);
    if (nodes.length === 0) return <em>∅</em>;
    return (
      <table>
        <thead>
          <tr>
            <th>ts</th>
            <th>ele</th>
            <th>after</th>
            <th>del?</th>
          </tr>
        </thead>
        <tbody>
          {s.adds.map((a) => (
            <tr
              key={a.ts}
              style={{ opacity: s.removes.has(a.ts) ? 0.5 : 1 }}
            >
              <td>{a.ts}</td>
              <td>{a.ele}</td>
              <td>{a.afterTs === 0 ? "(start)" : a.afterTs}</td>
              <td>{s.removes.has(a.ts) ? "✓" : ""}</td>
            </tr>
          ))}
        </tbody>
      </table>
    );
  },
  opForm({ state, dispatch }) {
    return <Form state={state} dispatch={dispatch} />;
  },
  formatOp(op, meta) {
    return op.kind === "insert"
      ? `R${meta.rid} insert(ele=${op.ele}, after=${op.after === 0 ? "start" : op.after})`
      : `R${meta.rid} remove(${op.target})`;
  },
};

function Form({
  state,
  dispatch,
}: {
  state: Concrete;
  dispatch: (op: Op) => void;
}) {
  const [ele, setEle] = useState(1);
  const [after, setAfter] = useState(0);
  const visible = traverse(state).filter((n) => !n.deleted);
  return (
    <div style={{ display: "flex", flexDirection: "column", gap: 4 }}>
      <div className="op-buttons">
        <span>insert</span>
        <input
          type="number"
          min={0}
          value={ele}
          onChange={(e) => setEle(Math.max(0, Number(e.target.value) || 0))}
          style={{ width: "4rem" }}
        />
        <span>after</span>
        <select
          value={after}
          onChange={(e) => setAfter(Number(e.target.value))}
          style={{ maxWidth: "8rem" }}
        >
          <option value={0}>(start)</option>
          {visible.map((n) => (
            <option key={n.ts} value={n.ts}>
              {n.ele} @ ts={n.ts}
            </option>
          ))}
        </select>
        <button onClick={() => dispatch({ kind: "insert", ele, after })}>
          insert
        </button>
      </div>
      <div className="op-buttons">
        <span>remove</span>
        <select
          onChange={(e) => {
            if (e.target.value) {
              dispatch({ kind: "remove", target: Number(e.target.value) });
              e.target.value = "";
            }
          }}
          defaultValue=""
          style={{ maxWidth: "10rem" }}
        >
          <option value="" disabled>
            pick…
          </option>
          {visible.map((n) => (
            <option key={n.ts} value={n.ts}>
              {n.ele} @ ts={n.ts}
            </option>
          ))}
        </select>
      </div>
    </div>
  );
}
