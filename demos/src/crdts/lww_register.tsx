import { useState } from "react";
import type { CRDTSpec } from "../harness/types";

// Σ = (value, timestamp, rid)  — last write wins under lex-max of (ts, rid).
// Lean keeps (ts, rid) as the register and treats the value as an alias for
// the timestamp; here we carry an explicit `value` so the abstract view is
// a user-provided write rather than a timestamp.
export type Concrete = { value: number; ts: number; rid: number };
export type Abstract = number | null; // null = never written
export type Op = { kind: "write"; value: number };

function ltLex(
  a: { ts: number; rid: number },
  b: { ts: number; rid: number },
): boolean {
  return a.ts < b.ts || (a.ts === b.ts && a.rid < b.rid);
}

export const spec: CRDTSpec<Concrete, Abstract, Op> = {
  name: "LWW-Register",
  slug: "lww-register",
  tagline:
    "Last-Writer-Wins register. Each write carries a (timestamp, replica id) key; merge picks the lex-max. Concurrent writes are ordered deterministically by the replica id tiebreaker.",
  init: { value: 0, ts: -1, rid: -1 },
  apply(s, op, meta) {
    const incoming = { value: op.value, ts: meta.ts, rid: meta.rid };
    return ltLex(s, incoming) ? incoming : s;
  },
  merge(a, b) {
    return ltLex(a, b) ? b : a;
  },
  abstract(s) {
    return s.ts < 0 ? null : s.value;
  },
  renderAbstract(a) {
    return a === null ? (
      <em>never written</em>
    ) : (
      <span className="big-number">{a}</span>
    );
  },
  renderConcrete(s) {
    if (s.ts < 0) return <em>∅</em>;
    return (
      <code>
        value={s.value} @ (ts={s.ts}, R{s.rid})
      </code>
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
