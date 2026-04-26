import { useState } from "react";
import type { CRDTSpec } from "../harness/types";

// Σ = (writes : set (ts, value), removed : set ts).
// `Write v` at (ts, rid) records its prepare-time snapshot of currently-
// visible ts values: those go into `removed` (they're superseded), and
// `(ts, v)` is added to `writes`. The visible value-set is then
//   { v | ∃ ts. (ts, v) ∈ writes ∧ ts ∉ removed }.
// Concurrent writes have disjoint snapshots (neither sees the other's
// fresh ts), so both survive the merge; sequential writes overwrite.
type Entry = { value: number; ts: number };

export type Concrete = { writes: Entry[]; removed: number[] };
export type Abstract = number[];
export type Op = { kind: "write"; value: number };

function dedupWrites(xs: Entry[]): Entry[] {
  const m = new Map<string, Entry>();
  for (const e of xs) m.set(`${e.ts}:${e.value}`, e);
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

export const spec: CRDTSpec<Concrete, Abstract, Op> = {
  name: "Multi-Valued Register",
  slug: "mv-register",
  tagline:
    "Classical replace-on-write MVR. Each Write records a (ts, v) into `writes` and tombstones the prepare-time snapshot of visible ts values into `removed`. Concurrent writes both stay visible; sequential writes overwrite.",
  init: { writes: [], removed: [] },
  apply(s, op, meta) {
    const snapshot = visibleTs(s);
    return {
      writes: dedupWrites([...s.writes, { value: op.value, ts: meta.ts }]),
      removed: dedupRemoved([...s.removed, ...snapshot]),
    };
  },
  merge(a, b) {
    return {
      writes: dedupWrites([...a.writes, ...b.writes]),
      removed: dedupRemoved([...a.removed, ...b.removed]),
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
                  <tr key={`${e.ts}:${e.value}`}>
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
