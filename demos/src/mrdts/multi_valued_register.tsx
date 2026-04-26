import { useState } from "react";
import type { MRDTSpec } from "../harness/mrdt_types";

// Σ = (writes : set (ts, value), removed : set ts).
// `Write v` records its prepare-time snapshot of currently-visible ts
// values into `removed`, then adds (ts, v) to `writes`. Visible value-set:
//   { v | ∃ ts. (ts, v) ∈ writes ∧ ts ∉ removed }.
// Three-way merge is `(l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)` per component
// (both grow-only); the LCA argument is vestigial here but kept for
// signature regularity with the rest of the MRDT suite.
type Entry = { value: number; ts: number };

export type Concrete = { writes: Entry[]; removed: number[] };
export type Abstract = number[];
export type Op = { kind: "write"; value: number };

function eKey(e: Entry): string {
  return `${e.ts}:${e.value}`;
}

function dedupWrites(xs: Entry[]): Entry[] {
  const m = new Map<string, Entry>();
  for (const e of xs) m.set(eKey(e), e);
  return [...m.values()].sort((a, b) =>
    a.ts !== b.ts ? a.ts - b.ts : a.value - b.value,
  );
}

function dedupRemoved(xs: number[]): number[] {
  return [...new Set(xs)].sort((a, b) => a - b);
}

function visibleTs(s: Concrete): number[] {
  const r = new Set(s.removed);
  const seen = new Set<number>();
  for (const e of s.writes) if (!r.has(e.ts)) seen.add(e.ts);
  return [...seen];
}

function threeWayWrites(l: Entry[], a: Entry[], b: Entry[]): Entry[] {
  const lk = new Set(l.map(eKey));
  const ak = new Set(a.map(eKey));
  const bk = new Set(b.map(eKey));
  const out = new Map<string, Entry>();
  for (const e of l) if (ak.has(eKey(e)) && bk.has(eKey(e))) out.set(eKey(e), e);
  for (const e of a) if (!lk.has(eKey(e))) out.set(eKey(e), e);
  for (const e of b) if (!lk.has(eKey(e))) out.set(eKey(e), e);
  return [...out.values()].sort((x, y) =>
    x.ts !== y.ts ? x.ts - y.ts : x.value - y.value,
  );
}

function threeWayRemoved(l: number[], a: number[], b: number[]): number[] {
  const ls = new Set(l);
  const as_ = new Set(a);
  const bs = new Set(b);
  const out = new Set<number>();
  for (const t of l) if (as_.has(t) && bs.has(t)) out.add(t);
  for (const t of a) if (!ls.has(t)) out.add(t);
  for (const t of b) if (!ls.has(t)) out.add(t);
  return [...out].sort((x, y) => x - y);
}

export const spec: MRDTSpec<Concrete, Abstract, Op> = {
  name: "Multi-Valued Register",
  slug: "mv-register",
  tagline:
    "Classical replace-on-write MVR. Each Write records (ts, v) into `writes` and tombstones the prepare-time snapshot of visible ts into `removed`. Concurrent writes survive; sequential writes overwrite. Three-way set merge per component.",
  init: { writes: [], removed: [] },
  apply(s, op, meta) {
    const snapshot = visibleTs(s);
    return {
      writes: dedupWrites([...s.writes, { value: op.value, ts: meta.ts }]),
      removed: dedupRemoved([...s.removed, ...snapshot]),
    };
  },
  merge(l, a, b) {
    return {
      writes: threeWayWrites(l.writes, a.writes, b.writes),
      removed: threeWayRemoved(l.removed, a.removed, b.removed),
    };
  },
  abstract(s) {
    const r = new Set(s.removed);
    const vals = new Set<number>();
    for (const e of s.writes) if (!r.has(e.ts)) vals.add(e.value);
    return [...vals].sort((x, y) => x - y);
  },
  renderAbstract(a) {
    if (a.length === 0) return <em>∅</em>;
    if (a.length === 1) return <span className="big-number">{a[0]}</span>;
    return <code>{`{ ${a.join(", ")} }`}</code>;
  },
  renderConcrete(s) {
    const r = new Set(s.removed);
    if (s.writes.length === 0 && s.removed.length === 0) return <em>∅</em>;
    return (
      <div>
        <div>
          <strong>writes:</strong>{" "}
          {s.writes.length === 0 ? (
            <em>∅</em>
          ) : (
            <table>
              <thead>
                <tr>
                  <th>ts</th>
                  <th>value</th>
                  <th>live?</th>
                </tr>
              </thead>
              <tbody>
                {s.writes.map((e) => (
                  <tr key={eKey(e)}>
                    <td>{e.ts}</td>
                    <td>{e.value}</td>
                    <td>{r.has(e.ts) ? "" : "✓"}</td>
                  </tr>
                ))}
              </tbody>
            </table>
          )}
        </div>
        <div>
          <strong>removed (ts):</strong>{" "}
          {s.removed.length === 0 ? (
            <em>∅</em>
          ) : (
            <code>{`{ ${s.removed.join(", ")} }`}</code>
          )}
        </div>
      </div>
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
