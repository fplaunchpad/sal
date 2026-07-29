import { useState } from "react";
import type { CRDTSpec } from "../harness/types";

// Σ = (adds : Map (rid, pid) -> count, rems : Map (rid, pid) -> count)
// abstract qty of product p = Σ_rid adds[(rid, p)] - Σ_rid min(rems[(rid, p)], adds[(rid, p)])
// (a remove can retract at most as many of its own adds as it issued).
export type Concrete = {
  adds: Map<string, number>; // key = `${rid}:${pid}`
  rems: Map<string, number>;
};
export type Abstract = Map<number, number>; // pid -> qty (non-negative)
export type Op =
  | { kind: "add"; pid: number }
  | { kind: "remove"; pid: number };

function keyOf(rid: number, pid: number): string {
  return `${rid}:${pid}`;
}

function mergeMaxMap(
  a: Map<string, number>,
  b: Map<string, number>,
): Map<string, number> {
  const out = new Map(a);
  for (const [k, v] of b) out.set(k, Math.max(out.get(k) ?? 0, v));
  return out;
}

export const spec: CRDTSpec<Concrete, Abstract, Op> = {
  name: "Shopping Cart",
  slug: "shopping-cart",
  tagline:
    "Per-replica add/remove counters per product id. The cart quantity for a product is the summed difference, capped at 0: you can only un-add what you added.",
  init: { adds: new Map(), rems: new Map() },
  apply(s, op, meta) {
    // Lean spec is unconditional: Add/Remove each just bump their own map.
    // The abstract projection caps per-replica net qty at 0 for display.
    const k = keyOf(meta.rid, op.pid);
    if (op.kind === "add") {
      const adds = new Map(s.adds);
      adds.set(k, (adds.get(k) ?? 0) + 1);
      return { ...s, adds };
    } else {
      const rems = new Map(s.rems);
      rems.set(k, (rems.get(k) ?? 0) + 1);
      return { ...s, rems };
    }
  },
  merge(a, b) {
    return {
      adds: mergeMaxMap(a.adds, b.adds),
      rems: mergeMaxMap(a.rems, b.rems),
    };
  },
  abstract(s) {
    const perReplicaNet = new Map<string, number>();
    for (const [k, n] of s.adds) perReplicaNet.set(k, n);
    for (const [k, n] of s.rems) {
      const cur = perReplicaNet.get(k) ?? 0;
      perReplicaNet.set(k, Math.max(0, cur - n));
    }
    const perProduct = new Map<number, number>();
    for (const [k, n] of perReplicaNet) {
      if (n === 0) continue;
      const pid = Number(k.split(":")[1]);
      perProduct.set(pid, (perProduct.get(pid) ?? 0) + n);
    }
    return perProduct;
  },
  renderAbstract(a) {
    if (a.size === 0) return <em>empty cart</em>;
    return (
      <ul className="cart">
        {[...a.entries()]
          .sort((x, y) => x[0] - y[0])
          .map(([pid, qty]) => (
            <li key={pid}>
              product {pid}: <strong>{qty}</strong>
            </li>
          ))}
      </ul>
    );
  },
  renderConcrete(s) {
    const all = new Set<string>([...s.adds.keys(), ...s.rems.keys()]);
    if (all.size === 0) return <em>∅</em>;
    return (
      <table>
        <thead>
          <tr>
            <th>rid</th>
            <th>pid</th>
            <th>adds</th>
            <th>rems</th>
          </tr>
        </thead>
        <tbody>
          {[...all]
            .map((k) => {
              const [rid, pid] = k.split(":").map(Number);
              return {
                key: k,
                rid,
                pid,
                adds: s.adds.get(k) ?? 0,
                rems: s.rems.get(k) ?? 0,
              };
            })
            .sort((a, b) => a.rid - b.rid || a.pid - b.pid)
            .map((row) => (
              <tr key={row.key}>
                <td>R{row.rid}</td>
                <td>{row.pid}</td>
                <td>{row.adds}</td>
                <td>{row.rems}</td>
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
    return `R${meta.rid} ${op.kind}(pid=${op.pid})`;
  },
};

function Form({
  state,
  dispatch,
}: {
  state: Concrete;
  dispatch: (op: Op) => void;
}) {
  const [pid, setPid] = useState(1);
  // Can remove only if my local replica has net qty > 0 for this product;
  // but we don't know which replica owns this form from here: enable by
  // default and let the apply guard no-op if the precondition fails.
  void state;
  return (
    <div className="op-buttons">
      <label>
        product
        <input
          type="number"
          min={0}
          value={pid}
          onChange={(e) => setPid(Math.max(0, Number(e.target.value) || 0))}
        />
      </label>
      <button onClick={() => dispatch({ kind: "add", pid })}>add</button>
      <button onClick={() => dispatch({ kind: "remove", pid })}>remove</button>
    </div>
  );
}
