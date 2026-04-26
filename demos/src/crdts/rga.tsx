import { useState } from "react";
import type { CRDTSpec, OpMeta } from "../harness/types";

// Σ = (chars : Map OpId -> char, afters : Map OpId -> OpId, deleted : Set OpId).
// Sentinel "0:0" is the document start — no real op owns it.
//
// Abstract view: a left-to-right traversal of the afterId DAG. At each anchor
// we visit children ordered by OpId descending (RGA convention — newer
// inserts take the slot nearer the anchor); tombstones are skipped.
type OpId = string; // `${ts}:${rid}`
const ROOT: OpId = "0:0";

export type Concrete = {
  chars: Map<OpId, string>;
  afters: Map<OpId, OpId>;
  deleted: Set<OpId>;
};
export type Abstract = { visible: { id: OpId; ch: string }[] };
export type Op =
  | { kind: "insert"; ch: string; after: OpId }
  | { kind: "remove"; target: OpId };

function mkOid(meta: OpMeta): OpId {
  return `${meta.ts}:${meta.rid}`;
}

function cmpOidDesc(a: OpId, b: OpId): number {
  const [ta, ra] = a.split(":").map(Number);
  const [tb, rb] = b.split(":").map(Number);
  return tb - ta || rb - ra;
}

function traverse(s: Concrete): { id: OpId; ch: string; deleted: boolean }[] {
  // Build children index.
  const children = new Map<OpId, OpId[]>();
  for (const [id, after] of s.afters) {
    const arr = children.get(after) ?? [];
    arr.push(id);
    children.set(after, arr);
  }
  for (const arr of children.values()) arr.sort(cmpOidDesc);
  const out: { id: OpId; ch: string; deleted: boolean }[] = [];
  const visit = (anchor: OpId) => {
    for (const c of children.get(anchor) ?? []) {
      out.push({
        id: c,
        ch: s.chars.get(c) ?? "?",
        deleted: s.deleted.has(c),
      });
      visit(c);
    }
  };
  visit(ROOT);
  return out;
}

export const spec: CRDTSpec<Concrete, Abstract, Op> = {
  name: "Replicated Growable Array (RGA)",
  slug: "rga",
  tagline:
    "Classical sequence CRDT. Each inserted char has a unique OpId and an afterId pointer into its predecessor; the visible string is a deterministic traversal of the resulting DAG, skipping tombstones.",
  init: { chars: new Map(), afters: new Map(), deleted: new Set() },

  apply(s, op, meta) {
    if (op.kind === "insert") {
      const id = mkOid(meta);
      const chars = new Map(s.chars);
      const afters = new Map(s.afters);
      chars.set(id, op.ch);
      afters.set(id, op.after);
      return { ...s, chars, afters };
    } else {
      const deleted = new Set(s.deleted);
      deleted.add(op.target);
      return { ...s, deleted };
    }
  },

  merge(a, b) {
    const chars = new Map(a.chars);
    for (const [k, v] of b.chars) if (!chars.has(k)) chars.set(k, v);
    const afters = new Map(a.afters);
    for (const [k, v] of b.afters) if (!afters.has(k)) afters.set(k, v);
    const deleted = new Set([...a.deleted, ...b.deleted]);
    return { chars, afters, deleted };
  },

  abstract(s) {
    const seq = traverse(s).filter((n) => !n.deleted);
    return { visible: seq.map((n) => ({ id: n.id, ch: n.ch })) };
  },

  renderAbstract(a) {
    if (a.visible.length === 0) return <em>∅ (empty document)</em>;
    return (
      <div style={{ fontFamily: "monospace", fontSize: "1.2rem" }}>
        {a.visible.map((c) => c.ch).join("")}
      </div>
    );
  },

  renderConcrete(s) {
    const nodes = traverse(s);
    if (nodes.length === 0) return <em>∅</em>;
    return (
      <div>
        <div style={{ fontFamily: "monospace" }}>
          {nodes.map((n) => (
            <span
              key={n.id}
              style={{
                textDecoration: n.deleted ? "line-through" : "none",
                color: n.deleted ? "#a00" : "inherit",
                opacity: n.deleted ? 0.5 : 1,
              }}
              title={`id=${n.id}`}
            >
              {n.ch}
            </span>
          ))}
        </div>
        <table style={{ marginTop: "0.5rem", fontSize: "0.8rem" }}>
          <thead>
            <tr>
              <th>id</th>
              <th>ch</th>
              <th>after</th>
              <th>del?</th>
            </tr>
          </thead>
          <tbody>
            {nodes.map((n) => (
              <tr key={n.id}>
                <td>
                  <code>{n.id}</code>
                </td>
                <td>
                  <code>{n.ch}</code>
                </td>
                <td>
                  <code>{s.afters.get(n.id)}</code>
                </td>
                <td>{n.deleted ? "✓" : ""}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    );
  },

  opForm({ state, dispatch }) {
    return <Form state={state} dispatch={dispatch} />;
  },

  formatOp(op, meta) {
    if (op.kind === "insert") {
      return `R${meta.rid} insert('${op.ch}', after=${op.after})`;
    }
    return `R${meta.rid} remove(${op.target})`;
  },
};

function Form({
  state,
  dispatch,
}: {
  state: Concrete;
  dispatch: (op: Op) => void;
}) {
  const [ch, setCh] = useState("a");
  const [selected, setSelected] = useState<OpId>(ROOT);
  const visible = traverse(state).filter((n) => !n.deleted);
  const allNodes = traverse(state); // for remove target menu

  return (
    <div style={{ display: "flex", flexDirection: "column", gap: 4 }}>
      <div className="op-buttons">
        <span>insert</span>
        <input
          type="text"
          value={ch}
          onChange={(e) => setCh(e.target.value.slice(0, 1))}
          maxLength={1}
          style={{ width: "3rem", textAlign: "center" }}
        />
        <span>after</span>
        <select
          value={selected}
          onChange={(e) => setSelected(e.target.value)}
          style={{ maxWidth: "8rem" }}
        >
          <option value={ROOT}>(start)</option>
          {visible.map((n) => (
            <option key={n.id} value={n.id}>
              '{n.ch}' @ {n.id}
            </option>
          ))}
        </select>
        <button
          disabled={!ch}
          onClick={() => dispatch({ kind: "insert", ch, after: selected })}
        >
          insert
        </button>
      </div>
      <div className="op-buttons">
        <span>remove</span>
        <select
          onChange={(e) => {
            if (e.target.value) {
              dispatch({ kind: "remove", target: e.target.value });
              e.target.value = "";
            }
          }}
          defaultValue=""
          style={{ maxWidth: "10rem" }}
        >
          <option value="" disabled>
            pick a char…
          </option>
          {allNodes
            .filter((n) => !n.deleted)
            .map((n) => (
              <option key={n.id} value={n.id}>
                '{n.ch}' @ {n.id}
              </option>
            ))}
        </select>
      </div>
    </div>
  );
}
