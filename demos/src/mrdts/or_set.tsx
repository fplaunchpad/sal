import { useState } from "react";
import type { MRDTSpec } from "../harness/mrdt_types";

// Σ = set of (ts, element) tags.  Observed-remove semantics implemented via
// MRDT-style three-way merge:
//   merge(l, a, b) = (l ∩ a ∩ b) ∪ (a ∖ l) ∪ (b ∖ l)
// i.e. intact-baseline ∪ additions-since-LCA-from-a ∪ additions-since-LCA-from-b.
//
// - Add(e) at ts adds (ts, e).
// - Rem(e) removes every tag for e from the local state (no tombstone set:
//   the LCA diff in merge does the tombstoning).
type Tag = string; // `${ts}:${elem}`
export type Concrete = Set<Tag>;
export type Abstract = number[];
export type Op =
  | { kind: "add"; elem: number }
  | { kind: "remove"; elem: number };

function tag(ts: number, elem: number): Tag {
  return `${ts}:${elem}`;
}
function elemOf(t: Tag): number {
  return Number(t.split(":")[1]);
}

export const spec: MRDTSpec<Concrete, Abstract, Op> = {
  name: "OR-Set",
  slug: "or-set",
  tagline:
    "Observed-remove set with a three-way merge: keep elements intact at the LCA plus everything added in either branch since then. No tombstone set: the LCA diff does the work.",
  init: new Set(),
  apply(s, op, meta) {
    if (op.kind === "add") {
      const out = new Set(s);
      out.add(tag(meta.ts, op.elem));
      return out;
    } else {
      const out = new Set<Tag>();
      for (const t of s) if (elemOf(t) !== op.elem) out.add(t);
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
    for (const t of s) live.add(elemOf(t));
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
    const tags = [...s].sort();
    return tags.length === 0 ? (
      <em>∅</em>
    ) : (
      <code>{`{ ${tags.join(", ")} }`}</code>
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
