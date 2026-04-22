import { useState } from "react";
import type { MRDTSpec } from "../harness/mrdt_types";

// Σ = set of (rid, ts, element) triples.  Efficient OR-Set keeps at most one
// tag per (rid, element) pair; an Add at (rid, ts, e) replaces any prior
// (rid, *, e).  Rem(e) removes every tag for e.  Merge is the same three-way
// pattern as plain OR-Set.
type Tag = string; // `${rid}|${ts}|${elem}`
export type Concrete = Set<Tag>;
export type Abstract = number[];
export type Op =
  | { kind: "add"; elem: number }
  | { kind: "remove"; elem: number };

function tag(rid: number, ts: number, elem: number): Tag {
  return `${rid}|${ts}|${elem}`;
}
function parse(t: Tag): { rid: number; ts: number; elem: number } {
  const [rid, ts, elem] = t.split("|").map(Number);
  return { rid, ts, elem };
}

export const spec: MRDTSpec<Concrete, Abstract, Op> = {
  name: "OR-Set (efficient)",
  slug: "or-set-efficient",
  tagline:
    "Like OR-Set but compressed: keys are (rid, ts, elem) and Add at (rid, *, e) replaces any prior tag from the same replica for the same element. Trades tag uniqueness for bounded growth.",
  init: new Set(),
  apply(s, op, meta) {
    if (op.kind === "add") {
      const out = new Set<Tag>();
      for (const t of s) {
        const { rid, elem } = parse(t);
        if (rid === meta.rid && elem === op.elem) continue;
        out.add(t);
      }
      out.add(tag(meta.rid, meta.ts, op.elem));
      return out;
    } else {
      const out = new Set<Tag>();
      for (const t of s) if (parse(t).elem !== op.elem) out.add(t);
      return out;
    }
  },
  merge(l, a, b) {
    const iab = new Set<Tag>();
    for (const t of a) if (b.has(t)) iab.add(t);
    const ilab = new Set<Tag>();
    for (const t of l) if (iab.has(t)) ilab.add(t);
    const da = new Set<Tag>();
    for (const t of a) if (!l.has(t)) da.add(t);
    const db = new Set<Tag>();
    for (const t of b) if (!l.has(t)) db.add(t);
    return new Set<Tag>([...ilab, ...da, ...db]);
  },
  abstract(s) {
    const live = new Set<number>();
    for (const t of s) live.add(parse(t).elem);
    return [...live].sort((a, b) => a - b);
  },
  renderAbstract(a) {
    return a.length === 0 ? (
      <em>∅</em>
    ) : (
      <code>{`{ ${a.join(", ")} }`}</code>
    );
  },
  renderConcrete(s) {
    const rows = [...s].map(parse).sort(
      (a, b) => a.rid - b.rid || a.ts - b.ts || a.elem - b.elem,
    );
    if (rows.length === 0) return <em>∅</em>;
    return (
      <table>
        <thead>
          <tr>
            <th>rid</th>
            <th>ts</th>
            <th>elem</th>
          </tr>
        </thead>
        <tbody>
          {rows.map((r) => (
            <tr key={`${r.rid}|${r.ts}|${r.elem}`}>
              <td>R{r.rid}</td>
              <td>{r.ts}</td>
              <td>{r.elem}</td>
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
