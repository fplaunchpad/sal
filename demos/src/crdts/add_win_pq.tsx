import { useState } from "react";
import type { CRDTSpec } from "../harness/types";

// Σ = (A : map (elem, ts) -> value,
//      I : set (elem, ts, amount),
//      R : set (elem, ts))     tombstones on add-records
//
// Observed priority of elem e = Σ over non-tombstoned add-records for e of
//   (innate A[(e, ts)] + Σ of I-entries matching (e, ts)).
type AddKey = string; // `${elem}:${ts}`
export type Concrete = {
  A: Map<AddKey, number>; // elem|ts -> innate value
  I: Set<string>; // `${elem}|${ts}|${amount}`
  R: Set<AddKey>; // tombstones of add-records
};
export type Abstract = { elem: number; priority: number }[];
export type Op =
  | { kind: "add"; elem: number; value: number }
  | { kind: "inc"; elem: number; amount: number }
  | { kind: "rmv"; elem: number };

function addK(elem: number, ts: number): AddKey {
  return `${elem}:${ts}`;
}
function incK(elem: number, ts: number, amount: number): string {
  return `${elem}|${ts}|${amount}`;
}

export const spec: CRDTSpec<Concrete, Abstract, Op> = {
  name: "Add-Wins Priority Queue",
  slug: "add-win-pq",
  tagline:
    "Zhang et al. 2023 CRPQ: multiple Add records per element (keyed by ts), Inc records against a specific add, and Rmv tombstones a snapshot of observed adds. Concurrent Add beats concurrent Rmv.",
  init: { A: new Map(), I: new Set(), R: new Set() },

  apply(s, op, meta) {
    if (op.kind === "add") {
      const A = new Map(s.A);
      A.set(addK(op.elem, meta.ts), op.value);
      return { ...s, A };
    } else if (op.kind === "inc") {
      // Inc applies to the most recently observed add for elem, if any.
      const liveAdds = [...s.A.keys()]
        .filter((k) => !s.R.has(k) && k.startsWith(`${op.elem}:`))
        .map((k) => Number(k.split(":")[1]))
        .sort((a, b) => b - a);
      if (liveAdds.length === 0) return s;
      const ts = liveAdds[0];
      const I = new Set(s.I);
      I.add(incK(op.elem, ts, op.amount));
      return { ...s, I };
    } else {
      // Rmv tombstones every currently-observed add-record for this elem.
      const toTomb = [...s.A.keys()].filter((k) =>
        k.startsWith(`${op.elem}:`),
      );
      if (toTomb.length === 0) return s;
      const R = new Set(s.R);
      for (const k of toTomb) R.add(k);
      return { ...s, R };
    }
  },

  merge(a, b) {
    const A = new Map(a.A);
    for (const [k, v] of b.A) A.set(k, Math.max(A.get(k) ?? 0, v));
    return {
      A,
      I: new Set([...a.I, ...b.I]),
      R: new Set([...a.R, ...b.R]),
    };
  },

  abstract(s) {
    const per = new Map<number, number>();
    for (const [k, innate] of s.A) {
      if (s.R.has(k)) continue;
      const [elemStr, tsStr] = k.split(":");
      const elem = Number(elemStr);
      let acquired = 0;
      const prefix = `${elem}|${tsStr}|`;
      for (const rec of s.I) {
        if (rec.startsWith(prefix)) {
          const amount = Number(rec.slice(prefix.length));
          acquired += amount;
        }
      }
      per.set(elem, (per.get(elem) ?? 0) + innate + acquired);
    }
    return [...per.entries()]
      .filter(([, v]) => v !== 0)
      .sort((a, b) => b[1] - a[1] || a[0] - b[0])
      .map(([elem, priority]) => ({ elem, priority }));
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
    const tomb = [...s.R];
    const incs = [...s.I];
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
        <button onClick={() => dispatch({ kind: "rmv", elem })}>rmv</button>
      </div>
    </div>
  );
}
