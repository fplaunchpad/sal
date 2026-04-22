import { useState } from "react";
import type { CRDTSpec } from "../harness/types";

// Σ = (incs : Map rid -> ℕ,
//      decs : Map rid -> ℕ,
//      transfers : Map (sender, receiver) -> ℕ)
//
// The net counter value = Σ incs - Σ decs.
// Per-replica quota is a client-side invariant; we enforce it on the UI side:
// each replica starts with INITIAL_QUOTA units; a Dec or outgoing Transfer at
// rid consumes one unit of rid's quota; an incoming Transfer adds one.
// The CRDT itself places no guard on Dec/Transfer (Lean `do_` is unchecked).
const INITIAL_QUOTA = 3;

export type Concrete = {
  incs: Map<number, number>;
  decs: Map<number, number>;
  transfers: Map<string, number>; // `${sender}:${receiver}` -> count
};
export type Abstract = {
  net: number;
  quotas: Map<number, number>; // rid -> available quota
};
export type Op =
  | { kind: "inc" }
  | { kind: "dec" }
  | { kind: "transfer"; receiver: number };

function tkey(sender: number, receiver: number): string {
  return `${sender}:${receiver}`;
}

function sumMap(m: Map<number, number>): number {
  let s = 0;
  for (const v of m.values()) s += v;
  return s;
}
function mergeMaxNum(
  a: Map<number, number>,
  b: Map<number, number>,
): Map<number, number> {
  const out = new Map(a);
  for (const [k, v] of b) out.set(k, Math.max(out.get(k) ?? 0, v));
  return out;
}
function mergeMaxStr(
  a: Map<string, number>,
  b: Map<string, number>,
): Map<string, number> {
  const out = new Map(a);
  for (const [k, v] of b) out.set(k, Math.max(out.get(k) ?? 0, v));
  return out;
}

export const spec: CRDTSpec<Concrete, Abstract, Op> = {
  name: "Bounded Counter",
  slug: "bounded-counter",
  tagline: `PN-counter plus a sparse (sender, receiver) transfers table that redistributes decrement quota. Each replica starts with ${INITIAL_QUOTA} units of quota; Dec and outgoing Transfer consume it, incoming Transfer replenishes it. The bound is a client-side invariant.`,
  init: { incs: new Map(), decs: new Map(), transfers: new Map() },

  apply(s, op, meta) {
    if (op.kind === "inc") {
      const incs = new Map(s.incs);
      incs.set(meta.rid, (incs.get(meta.rid) ?? 0) + 1);
      return { ...s, incs };
    } else if (op.kind === "dec") {
      const decs = new Map(s.decs);
      decs.set(meta.rid, (decs.get(meta.rid) ?? 0) + 1);
      return { ...s, decs };
    } else {
      const transfers = new Map(s.transfers);
      const k = tkey(meta.rid, op.receiver);
      transfers.set(k, (transfers.get(k) ?? 0) + 1);
      return { ...s, transfers };
    }
  },

  merge(a, b) {
    return {
      incs: mergeMaxNum(a.incs, b.incs),
      decs: mergeMaxNum(a.decs, b.decs),
      transfers: mergeMaxStr(a.transfers, b.transfers),
    };
  },

  abstract(s) {
    const net = sumMap(s.incs) - sumMap(s.decs);
    const quotas = new Map<number, number>();
    // initial
    const allRids = new Set<number>([
      ...s.incs.keys(),
      ...s.decs.keys(),
      ...[...s.transfers.keys()].flatMap((k) => k.split(":").map(Number)),
    ]);
    for (const rid of allRids) quotas.set(rid, INITIAL_QUOTA);
    // incs don't affect quota (Lean spec)
    for (const [rid, n] of s.decs) {
      quotas.set(rid, (quotas.get(rid) ?? INITIAL_QUOTA) - n);
    }
    for (const [k, n] of s.transfers) {
      const [sender, receiver] = k.split(":").map(Number);
      quotas.set(
        sender,
        (quotas.get(sender) ?? INITIAL_QUOTA) - n,
      );
      quotas.set(
        receiver,
        (quotas.get(receiver) ?? INITIAL_QUOTA) + n,
      );
    }
    return { net, quotas };
  },

  renderAbstract(a) {
    return (
      <div>
        <div className="big-number">{a.net}</div>
        <div style={{ fontSize: "0.8rem", marginTop: 4 }}>
          quotas:{" "}
          {[...a.quotas.entries()]
            .sort((x, y) => x[0] - y[0])
            .map(([rid, q]) => `R${rid}=${q}`)
            .join(", ") || "—"}
        </div>
      </div>
    );
  },

  renderConcrete(s) {
    const rids = new Set<number>([...s.incs.keys(), ...s.decs.keys()]);
    const transfers = [...s.transfers.entries()].map(([k, n]) => {
      const [from, to] = k.split(":").map(Number);
      return { from, to, n };
    });
    return (
      <div>
        <div>
          <strong>incs / decs:</strong>
          {rids.size === 0 ? (
            " ∅"
          ) : (
            <table>
              <thead>
                <tr>
                  <th>rid</th>
                  <th>+</th>
                  <th>−</th>
                </tr>
              </thead>
              <tbody>
                {[...rids]
                  .sort((a, b) => a - b)
                  .map((rid) => (
                    <tr key={rid}>
                      <td>R{rid}</td>
                      <td>{s.incs.get(rid) ?? 0}</td>
                      <td>{s.decs.get(rid) ?? 0}</td>
                    </tr>
                  ))}
              </tbody>
            </table>
          )}
        </div>
        <div>
          <strong>transfers:</strong>{" "}
          {transfers.length === 0 ? (
            "∅"
          ) : (
            <code>
              {transfers
                .sort((a, b) => a.from - b.from || a.to - b.to)
                .map((t) => `R${t.from}→R${t.to}:${t.n}`)
                .join(", ")}
            </code>
          )}
        </div>
      </div>
    );
  },

  opForm({ state, dispatch }) {
    return <Form state={state} dispatch={dispatch} />;
  },

  formatOp(op, meta) {
    if (op.kind === "transfer") {
      return `R${meta.rid} transfer →R${op.receiver}`;
    }
    return op.kind === "inc" ? `R${meta.rid} inc` : `R${meta.rid} dec`;
  },
};

function Form({
  state,
  dispatch,
}: {
  state: Concrete;
  dispatch: (op: Op) => void;
}) {
  const [recv, setRecv] = useState(0);
  void state;
  return (
    <div className="op-buttons" style={{ flexWrap: "wrap" }}>
      <button onClick={() => dispatch({ kind: "inc" })}>+1</button>
      <button onClick={() => dispatch({ kind: "dec" })}>−1</button>
      <label>
        xfer to R
        <input
          type="number"
          min={0}
          max={9}
          value={recv}
          onChange={(e) => setRecv(Math.max(0, Number(e.target.value) || 0))}
          style={{ width: "3rem" }}
        />
      </label>
      <button onClick={() => dispatch({ kind: "transfer", receiver: recv })}>
        transfer
      </button>
    </div>
  );
}
