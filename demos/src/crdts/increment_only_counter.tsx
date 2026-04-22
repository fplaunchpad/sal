import type { CRDTSpec, OpMeta } from "../harness/types";

// Σ = map rid -> count   (one integer per replica that ever incremented)
export type Concrete = Map<number, number>;
export type Abstract = number;
export type Op = { kind: "inc" };

export const spec: CRDTSpec<Concrete, Abstract, Op> = {
  name: "Increment-Only Counter",
  slug: "increment-only-counter",
  tagline:
    "The simplest CRDT: every replica owns its own counter slot; merge is pointwise max.",
  init: new Map(),

  apply(s: Concrete, _op: Op, meta: OpMeta): Concrete {
    const next = new Map(s);
    next.set(meta.rid, (next.get(meta.rid) ?? 0) + 1);
    return next;
  },

  merge(a: Concrete, b: Concrete): Concrete {
    const out = new Map(a);
    for (const [rid, n] of b) {
      out.set(rid, Math.max(out.get(rid) ?? 0, n));
    }
    return out;
  },

  abstract(s: Concrete): Abstract {
    let total = 0;
    for (const n of s.values()) total += n;
    return total;
  },

  renderAbstract(a: Abstract) {
    return <span className="big-number">{a}</span>;
  },

  renderConcrete(s: Concrete) {
    const entries = [...s.entries()].sort((x, y) => x[0] - y[0]);
    if (entries.length === 0) return <em>∅</em>;
    return (
      <table>
        <tbody>
          {entries.map(([rid, n]) => (
            <tr key={rid}>
              <td>
                <code>R{rid}</code>
              </td>
              <td>{n}</td>
            </tr>
          ))}
        </tbody>
      </table>
    );
  },

  opForm({ dispatch }) {
    return (
      <button onClick={() => dispatch({ kind: "inc" })}>+1</button>
    );
  },

  formatOp(op: Op, meta: OpMeta) {
    return `R${meta.rid} inc`;
    void op;
  },
};
