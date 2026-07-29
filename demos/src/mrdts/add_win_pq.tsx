import { useState } from "react";
import type { MRDTSpec } from "../harness/mrdt_types";

// Σ = (A : set (add_ts, elem, innate),  I : set (inc_ts, elem, amount)).
// No tombstone set, LCA handles Add-Wins: merge = three-way set union
// per component.  Rmv is a simple local filter on A.
type ARec = { ts: number; elem: number; value: number };
type IRec = { ts: number; elem: number; amount: number };
export type Concrete = { A: ARec[]; I: IRec[] };
export type Abstract = { elem: number; priority: number }[];
export type Op =
  | { kind: "add"; elem: number; value: number }
  | { kind: "inc"; elem: number; amount: number }
  | { kind: "rmv"; elem: number };

function aKey(r: ARec): string {
  return `${r.ts}|${r.elem}|${r.value}`;
}
function iKey(r: IRec): string {
  return `${r.ts}|${r.elem}|${r.amount}`;
}

function dedupA(xs: ARec[]): ARec[] {
  const m = new Map<string, ARec>();
  for (const r of xs) m.set(aKey(r), r);
  return [...m.values()].sort((a, b) => a.ts - b.ts);
}
function dedupI(xs: IRec[]): IRec[] {
  const m = new Map<string, IRec>();
  for (const r of xs) m.set(iKey(r), r);
  return [...m.values()].sort((a, b) => a.ts - b.ts);
}

function threeWaySet<T>(
  l: T[],
  a: T[],
  b: T[],
  keyOf: (r: T) => string,
): T[] {
  const lk = new Set(l.map(keyOf));
  const ak = new Set(a.map(keyOf));
  const bk = new Set(b.map(keyOf));
  const out = new Map<string, T>();
  for (const r of l) if (ak.has(keyOf(r)) && bk.has(keyOf(r))) out.set(keyOf(r), r);
  for (const r of a) if (!lk.has(keyOf(r))) out.set(keyOf(r), r);
  for (const r of b) if (!lk.has(keyOf(r))) out.set(keyOf(r), r);
  return [...out.values()];
}

export const spec: MRDTSpec<Concrete, Abstract, Op> = {
  name: "Add-Wins Priority Queue",
  slug: "add-win-pq",
  tagline:
    "Zhang et al. 2023 CRPQ, MRDT-flavoured. Drops the CRDT's tombstone set because the version DAG's LCA supplies Add-Wins directly: merge is the standard three-way set union per component. Rmv is a simple local filter.",
  init: { A: [], I: [] },
  apply(s, op, meta) {
    if (op.kind === "add") {
      return {
        A: dedupA([
          ...s.A,
          { ts: meta.ts, elem: op.elem, value: op.value },
        ]),
        I: s.I,
      };
    }
    if (op.kind === "inc") {
      return {
        A: s.A,
        I: dedupI([
          ...s.I,
          { ts: meta.ts, elem: op.elem, amount: op.amount },
        ]),
      };
    }
    // Rmv: local filter on A only (I is untouched, matches the Lean spec).
    return {
      A: s.A.filter((r) => r.elem !== op.elem),
      I: s.I,
    };
  },
  merge(l, a, b) {
    return {
      A: dedupA(threeWaySet(l.A, a.A, b.A, aKey)),
      I: dedupI(threeWaySet(l.I, a.I, b.I, iKey)),
    };
  },
  abstract(s) {
    // An element is live iff A has at least one record for it.
    // priority(e) = innate(e) + acquired(e)
    //   innate(e) = value with max add-ts among A records for e
    //   acquired(e) = Σ amounts over I records for e (regardless of Rmv)
    const innateByElem = new Map<number, ARec>();
    for (const r of s.A) {
      const cur = innateByElem.get(r.elem);
      if (!cur || r.ts > cur.ts) innateByElem.set(r.elem, r);
    }
    const priority = new Map<number, number>();
    for (const [e, r] of innateByElem) priority.set(e, r.value);
    for (const r of s.I) {
      if (!innateByElem.has(r.elem)) continue;
      priority.set(r.elem, (priority.get(r.elem) ?? 0) + r.amount);
    }
    return [...priority.entries()]
      .sort((a, b) => b[1] - a[1] || a[0] - b[0])
      .map(([elem, p]) => ({ elem, priority: p }));
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
    return (
      <div>
        <div>
          <strong>A ({s.A.length}):</strong>{" "}
          {s.A.length === 0 ? (
            <em>∅</em>
          ) : (
            <code>
              {`{ ${s.A
                .map((r) => `${r.ts}→(${r.elem}, v=${r.value})`)
                .join(", ")} }`}
            </code>
          )}
        </div>
        <div>
          <strong>I ({s.I.length}):</strong>{" "}
          {s.I.length === 0 ? (
            <em>∅</em>
          ) : (
            <code>
              {`{ ${s.I
                .map((r) => `${r.ts}→(${r.elem}, ${r.amount >= 0 ? "+" : ""}${r.amount})`)
                .join(", ")} }`}
            </code>
          )}
        </div>
      </div>
    );
  },
  opForm({ dispatch }) {
    return <Form dispatch={dispatch} />;
  },
  formatOp(op, meta) {
    switch (op.kind) {
      case "add":
        return `R${meta.rid} add(elem=${op.elem}, value=${op.value})`;
      case "inc":
        return `R${meta.rid} inc(elem=${op.elem}, ${op.amount >= 0 ? "+" : ""}${op.amount})`;
      case "rmv":
        return `R${meta.rid} rmv(elem=${op.elem})`;
    }
  },
};

function Form({ dispatch }: { dispatch: (op: Op) => void }) {
  const [elem, setElem] = useState(0);
  const [value, setValue] = useState(1);
  const [amount, setAmount] = useState(1);
  return (
    <div
      className="op-buttons"
      style={{ flexDirection: "column", alignItems: "flex-start", gap: 4 }}
    >
      <div className="op-buttons">
        <label>
          elem
          <input
            type="number"
            min={0}
            value={elem}
            onChange={(e) => setElem(Math.max(0, Number(e.target.value) || 0))}
            style={{ width: "4rem" }}
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
            style={{ width: "4rem" }}
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
            style={{ width: "4rem" }}
          />
        </label>
        <button onClick={() => dispatch({ kind: "inc", elem, amount })}>
          inc
        </button>
      </div>
      <div className="op-buttons">
        <button onClick={() => dispatch({ kind: "rmv", elem })}>rmv</button>
      </div>
    </div>
  );
}
