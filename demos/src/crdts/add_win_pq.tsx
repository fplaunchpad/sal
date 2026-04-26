import { useState } from "react";
import type { CRDTSpec } from "../harness/types";

// Σ = (A : map (elem, add_ts) -> innate value,
//      I : set (elem, inc_ts, amount),
//      R : set (elem, add_ts) tombstones)
//
// Per the Lean CRDT spec:
//   * Add e v at ts          -> A[(e, ts)] := v.
//   * Inc e a at ts          -> union {(e, ts, a)} into I.   ts is the OP's
//                                ts (not any add's), and the inc is keyed
//                                by element only at the read side.
//   * Rmv e   at the source  -> the op carries the prepare-time snapshot
//                                D = { (e, at) ∈ A : not yet tombstoned }
//                                of currently-visible add-records for e;
//                                do_ unions D into R. (Carrying D in the
//                                payload is what keeps `rc := Either`.)
//
// Read side:
//   live(e)     := { (e, at) ∈ A : (e, at) ∉ R }
//   innate(e)   := value with max add_ts in live(e)
//   acquired(e) := Σ over inc records with elem=e of amount
//   priority(e) := innate(e) + acquired(e)
type AddKey = string; // `${elem}:${ts}`
type IncKey = string; // `${elem}|${ts}|${amount}`
export type Concrete = {
  A: Map<AddKey, number>;
  I: Set<IncKey>;
  R: Set<AddKey>;
};
export type Abstract = { elem: number; priority: number }[];
export type Op =
  | { kind: "add"; elem: number; value: number }
  | { kind: "inc"; elem: number; amount: number }
  | { kind: "rmv"; elem: number; tombstones: AddKey[] };

function addK(elem: number, ts: number): AddKey {
  return `${elem}:${ts}`;
}
function parseAddK(k: AddKey): { elem: number; ts: number } {
  const [e, t] = k.split(":");
  return { elem: Number(e), ts: Number(t) };
}
function incK(elem: number, ts: number, amount: number): IncKey {
  return `${elem}|${ts}|${amount}`;
}
function parseIncK(k: IncKey): { elem: number; ts: number; amount: number } {
  const [e, t, a] = k.split("|");
  return { elem: Number(e), ts: Number(t), amount: Number(a) };
}

// Helper used by the op form to build the Rmv payload at the source replica:
// every currently-visible (elem, add_ts) record for `e` (live, not yet
// tombstoned). This is the prepare-time snapshot in the Lean spec.
function snapshotForRmv(s: Concrete, elem: number): AddKey[] {
  const out: AddKey[] = [];
  for (const k of s.A.keys()) {
    if (s.R.has(k)) continue;
    if (parseAddK(k).elem === elem) out.push(k);
  }
  return out;
}

export const spec: CRDTSpec<Concrete, Abstract, Op> = {
  name: "Add-Wins Priority Queue",
  slug: "add-win-pq",
  tagline:
    "Zhang et al. 2023 CRPQ. Add stakes (e, ts) → value into A; Inc stakes (e, op_ts, amount) into I keyed by element; Rmv carries a prepare-time snapshot of currently-visible (e, add_ts) records and unions it into R. Concurrent Add at another replica beats concurrent Rmv.",
  init: { A: new Map(), I: new Set(), R: new Set() },

  apply(s, op, meta) {
    if (op.kind === "add") {
      const A = new Map(s.A);
      A.set(addK(op.elem, meta.ts), op.value);
      return { ...s, A };
    } else if (op.kind === "inc") {
      // Lean: union {(elem, op_ts, amount)} into I unconditionally.
      const I = new Set(s.I);
      I.add(incK(op.elem, meta.ts, op.amount));
      return { ...s, I };
    } else {
      // Lean: do_ for Rmv just unions the op's tombstone payload D into R.
      // No reading of A. Keeping this `pure pointwise ∨` is what preserves
      // Add/Rmv commutativity at the do_ level.
      if (op.tombstones.length === 0) return s;
      const R = new Set(s.R);
      for (const k of op.tombstones) R.add(k);
      return { ...s, R };
    }
  },

  merge(a, b) {
    // Pointwise lattice join: max on A's value (LWW by add_ts ⇒ writes are
    // unique anyway), union on I and R.
    const A = new Map(a.A);
    for (const [k, v] of b.A) A.set(k, Math.max(A.get(k) ?? 0, v));
    return {
      A,
      I: new Set([...a.I, ...b.I]),
      R: new Set([...a.R, ...b.R]),
    };
  },

  abstract(s) {
    // Per Lean read-side:
    //   innate(e)   = max-add_ts winner's value among live(e),
    //   acquired(e) = Σ of inc amounts whose elem = e (regardless of R),
    //   priority(e) = innate(e) + acquired(e).
    const innateByElem = new Map<number, { ts: number; value: number }>();
    for (const [k, value] of s.A) {
      if (s.R.has(k)) continue;
      const { elem, ts } = parseAddK(k);
      const cur = innateByElem.get(elem);
      if (!cur || ts > cur.ts) innateByElem.set(elem, { ts, value });
    }
    const acquired = new Map<number, number>();
    for (const k of s.I) {
      const { elem, amount } = parseIncK(k);
      acquired.set(elem, (acquired.get(elem) ?? 0) + amount);
    }
    const out: { elem: number; priority: number }[] = [];
    for (const [elem, { value }] of innateByElem) {
      out.push({ elem, priority: value + (acquired.get(elem) ?? 0) });
    }
    return out.sort((a, b) => b.priority - a.priority || a.elem - b.elem);
  },

  renderAbstract(a) {
    if (a.length === 0) return <em>∅</em>;
    return (
      <ol>
        {a.map((e) => (
          <li key={e.elem}>
            elem {e.elem}: <strong>{e.priority}</strong>
          </li>
        ))}
      </ol>
    );
  },

  renderConcrete(s) {
    const liveAdds = [...s.A.entries()].filter(([k]) => !s.R.has(k));
    const incs = [...s.I];
    const tomb = [...s.R];
    return (
      <div>
        <div>
          <strong>A (live):</strong>{" "}
          {liveAdds.length === 0 ? (
            <em>∅</em>
          ) : (
            <code>
              {`{ ${liveAdds.map(([k, v]) => `${k}→${v}`).join(", ")} }`}
            </code>
          )}
        </div>
        <div>
          <strong>I:</strong>{" "}
          {incs.length === 0 ? (
            <em>∅</em>
          ) : (
            <code>{`{ ${incs.join(", ")} }`}</code>
          )}
        </div>
        <div>
          <strong>R (tombstones):</strong>{" "}
          {tomb.length === 0 ? (
            <em>∅</em>
          ) : (
            <code>{`{ ${tomb.join(", ")} }`}</code>
          )}
        </div>
      </div>
    );
  },

  opForm({ dispatch, state }) {
    return <Form dispatch={dispatch} state={state} />;
  },

  formatOp(op, meta) {
    switch (op.kind) {
      case "add":
        return `R${meta.rid} add(elem=${op.elem}, value=${op.value})`;
      case "inc":
        return `R${meta.rid} inc(elem=${op.elem}, ${op.amount >= 0 ? "+" : ""}${op.amount})`;
      case "rmv":
        return `R${meta.rid} rmv(elem=${op.elem}, D=${op.tombstones.length})`;
    }
  },
};

function Form({
  dispatch,
  state,
}: {
  dispatch: (op: Op) => void;
  state: Concrete;
}) {
  const [elem, setElem] = useState(0);
  const [value, setValue] = useState(1);
  const [amount, setAmount] = useState(1);
  return (
    <div className="op-buttons" style={{ flexDirection: "column", alignItems: "flex-start", gap: 4 }}>
      <div className="op-buttons">
        <label>
          elem
          <input
            type="number"
            min={0}
            value={elem}
            onChange={(e) => setElem(Math.max(0, Number(e.target.value) || 0))}
          />
        </label>
      </div>
      <div className="op-buttons">
        <label>
          value
          <input
            type="number"
            value={value}
            onChange={(e) => setValue(Number(e.target.value) || 0)}
          />
        </label>
        <button onClick={() => dispatch({ kind: "add", elem, value })}>
          add
        </button>
      </div>
      <div className="op-buttons">
        <label>
          amount
          <input
            type="number"
            value={amount}
            onChange={(e) => setAmount(Number(e.target.value) || 0)}
          />
        </label>
        <button onClick={() => dispatch({ kind: "inc", elem, amount })}>
          inc
        </button>
      </div>
      <div className="op-buttons">
        <button
          onClick={() =>
            dispatch({ kind: "rmv", elem, tombstones: snapshotForRmv(state, elem) })
          }
        >
          rmv
        </button>
      </div>
    </div>
  );
}
