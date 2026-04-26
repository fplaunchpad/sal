import { useState } from "react";
import type { CRDTSpec, OpMeta } from "../harness/types";

// Σ = RGA (chars, afters, deleted) + a flat set of AnchorAttachments.
// The Lean spec uses AnchorAttachment = (anchorChar, side, markOp); we mirror
// that layout here. A single AddMark/RemoveMark op contributes two
// attachments (one at the start anchor, one at the end).
//
// Effective formatting for a given char, mark-type pair: look at all marks
// that span this char; the one with the highest (ts, rid) wins; `isAdd`
// determines whether the char is formatted.
type OpId = string;
const ROOT: OpId = "0:0";

type MarkType = "bold" | "italic";

type MarkOp = {
  opId: OpId;
  startId: OpId;
  startSide: boolean; // before=false, after=true  (Lean convention)
  endId: OpId;
  endSide: boolean;
  mtype: MarkType;
  isAdd: boolean;
};

type AnchorAttachment = {
  anchor: OpId; // anchor_charId
  side: boolean;
  mark: MarkOp;
};

export type Concrete = {
  chars: Map<OpId, string>;
  afters: Map<OpId, OpId>;
  deleted: Set<OpId>;
  marks: AnchorAttachment[]; // kept deduped by attachment key
};

export type Abstract = {
  visible: { id: OpId; ch: string; bold: boolean; italic: boolean }[];
};

export type Op =
  | { kind: "insert"; ch: string; after: OpId }
  | { kind: "remove"; target: OpId }
  | {
      kind: "addMark";
      startId: OpId;
      endId: OpId;
      mtype: MarkType;
    }
  | {
      kind: "removeMark";
      startId: OpId;
      endId: OpId;
      mtype: MarkType;
    };

function mkOid(meta: OpMeta): OpId {
  return `${meta.ts}:${meta.rid}`;
}

function cmpOidDesc(a: OpId, b: OpId): number {
  const [ta, ra] = a.split(":").map(Number);
  const [tb, rb] = b.split(":").map(Number);
  return tb - ta || rb - ra;
}

function cmpOid(a: OpId, b: OpId): number {
  const [ta, ra] = a.split(":").map(Number);
  const [tb, rb] = b.split(":").map(Number);
  return ta - tb || ra - rb;
}

function attachmentKey(a: AnchorAttachment): string {
  const m = a.mark;
  return [
    a.anchor,
    a.side ? 1 : 0,
    m.opId,
    m.startId,
    m.startSide ? 1 : 0,
    m.endId,
    m.endSide ? 1 : 0,
    m.mtype,
    m.isAdd ? 1 : 0,
  ].join("|");
}

function traverse(s: Concrete): { id: OpId; ch: string; deleted: boolean }[] {
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

// Reconstruct the unique MarkOps from the attachments set, then compute which
// characters are covered by which.  A MarkOp's covered range in the visible
// sequence is all characters c with startId ≤ c ≤ endId (by traversal order).
function uniqueMarks(attachments: AnchorAttachment[]): MarkOp[] {
  const map = new Map<string, MarkOp>();
  for (const a of attachments) map.set(a.mark.opId, a.mark);
  return [...map.values()];
}

function effectiveFormatting(
  s: Concrete,
  visible: { id: OpId; ch: string }[],
): Map<OpId, { bold: boolean; italic: boolean }> {
  const pos = new Map<OpId, number>();
  visible.forEach((n, i) => pos.set(n.id, i));
  // For each (char, type) keep the highest-opId mark that covers it.
  const best = new Map<string, MarkOp>(); // `${charId}|${type}` -> winning MarkOp
  for (const m of uniqueMarks(s.marks)) {
    const sIdx = pos.get(m.startId);
    const eIdx = pos.get(m.endId);
    if (sIdx === undefined || eIdx === undefined) continue;
    const [lo, hi] = sIdx <= eIdx ? [sIdx, eIdx] : [eIdx, sIdx];
    for (let i = lo; i <= hi; i++) {
      const c = visible[i].id;
      const key = `${c}|${m.mtype}`;
      const cur = best.get(key);
      if (!cur || cmpOid(cur.opId, m.opId) < 0) best.set(key, m);
    }
  }
  const out = new Map<OpId, { bold: boolean; italic: boolean }>();
  for (const v of visible) out.set(v.id, { bold: false, italic: false });
  for (const [key, m] of best) {
    const [charId] = key.split("|");
    const fm = out.get(charId)!;
    if (m.mtype === "bold") fm.bold = m.isAdd;
    if (m.mtype === "italic") fm.italic = m.isAdd;
  }
  return out;
}

export const spec: CRDTSpec<Concrete, Abstract, Op> = {
  name: "Peritext (text-only)",
  slug: "peritext",
  tagline:
    "Rich-text CRDT: RGA for the character sequence plus a flat set of anchor-attached mark ops (bold, italic). A char is formatted when the highest-opId mark covering it is an Add; concurrent Add beats concurrent Remove on the same range.",
  init: {
    chars: new Map(),
    afters: new Map(),
    deleted: new Set(),
    marks: [],
  },

  apply(s, op, meta) {
    if (op.kind === "insert") {
      const id = mkOid(meta);
      const chars = new Map(s.chars);
      const afters = new Map(s.afters);
      chars.set(id, op.ch);
      afters.set(id, op.after);
      return { ...s, chars, afters };
    }
    if (op.kind === "remove") {
      const deleted = new Set(s.deleted);
      deleted.add(op.target);
      return { ...s, deleted };
    }
    // addMark / removeMark: create two attachments (start + end anchors).
    const m: MarkOp = {
      opId: mkOid(meta),
      startId: op.startId,
      startSide: false, // start anchors attach on the "before" side
      endId: op.endId,
      endSide: true, // end anchors attach on the "after" side
      mtype: op.mtype,
      isAdd: op.kind === "addMark",
    };
    const attachments: AnchorAttachment[] = [
      { anchor: op.startId, side: false, mark: m },
      { anchor: op.endId, side: true, mark: m },
    ];
    const keys = new Set(s.marks.map(attachmentKey));
    const marks = [...s.marks];
    for (const a of attachments) {
      const k = attachmentKey(a);
      if (!keys.has(k)) {
        keys.add(k);
        marks.push(a);
      }
    }
    return { ...s, marks };
  },

  merge(a, b) {
    const chars = new Map(a.chars);
    for (const [k, v] of b.chars) if (!chars.has(k)) chars.set(k, v);
    const afters = new Map(a.afters);
    for (const [k, v] of b.afters) if (!afters.has(k)) afters.set(k, v);
    const deleted = new Set([...a.deleted, ...b.deleted]);
    const keys = new Set<string>();
    const marks: AnchorAttachment[] = [];
    for (const at of [...a.marks, ...b.marks]) {
      const k = attachmentKey(at);
      if (!keys.has(k)) {
        keys.add(k);
        marks.push(at);
      }
    }
    return { chars, afters, deleted, marks };
  },

  abstract(s) {
    const vis = traverse(s).filter((n) => !n.deleted);
    const fmt = effectiveFormatting(s, vis);
    return {
      visible: vis.map((n) => ({
        id: n.id,
        ch: n.ch,
        bold: fmt.get(n.id)?.bold ?? false,
        italic: fmt.get(n.id)?.italic ?? false,
      })),
    };
  },

  renderAbstract(a) {
    if (a.visible.length === 0) return <em>∅ (empty document)</em>;
    return (
      <div style={{ fontFamily: "serif", fontSize: "1.2rem" }}>
        {a.visible.map((c, i) => {
          let el: React.ReactNode = c.ch;
          if (c.bold) el = <strong>{el}</strong>;
          if (c.italic) el = <em>{el}</em>;
          return <span key={`${c.id}:${i}`}>{el}</span>;
        })}
      </div>
    );
  },

  renderConcrete(s) {
    const nodes = traverse(s);
    const unique = uniqueMarks(s.marks);
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
        <div style={{ marginTop: "0.5rem", fontSize: "0.8rem" }}>
          <strong>Marks ({unique.length}):</strong>
          {unique.length === 0 ? (
            " ∅"
          ) : (
            <ul style={{ margin: 0, paddingLeft: "1.25rem" }}>
              {unique
                .sort((a, b) => cmpOid(a.opId, b.opId))
                .map((m) => (
                  <li key={m.opId}>
                    <code>{m.opId}</code> {m.isAdd ? "add" : "remove"} {m.mtype}{" "}
                    [{m.startId} → {m.endId}]
                  </li>
                ))}
            </ul>
          )}
        </div>
      </div>
    );
  },

  opForm({ state, dispatch }) {
    return <Form state={state} dispatch={dispatch} />;
  },

  formatOp(op, meta) {
    switch (op.kind) {
      case "insert":
        return `R${meta.rid} insert('${op.ch}', after=${op.after})`;
      case "remove":
        return `R${meta.rid} remove(${op.target})`;
      case "addMark":
        return `R${meta.rid} addMark(${op.mtype}, ${op.startId}→${op.endId})`;
      case "removeMark":
        return `R${meta.rid} removeMark(${op.mtype}, ${op.startId}→${op.endId})`;
    }
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
  const [markStart, setMarkStart] = useState<OpId>("");
  const [markEnd, setMarkEnd] = useState<OpId>("");
  const [mtype, setMtype] = useState<MarkType>("bold");

  const visible = traverse(state).filter((n) => !n.deleted);

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
          {visible.map((n) => (
            <option key={n.id} value={n.id}>
              '{n.ch}' @ {n.id}
            </option>
          ))}
        </select>
      </div>

      <div className="op-buttons">
        <span>mark</span>
        <select
          value={mtype}
          onChange={(e) => setMtype(e.target.value as MarkType)}
        >
          <option value="bold">bold</option>
          <option value="italic">italic</option>
        </select>
        <span>start</span>
        <select
          value={markStart}
          onChange={(e) => setMarkStart(e.target.value)}
          style={{ maxWidth: "7rem" }}
        >
          <option value="">—</option>
          {visible.map((n) => (
            <option key={n.id} value={n.id}>
              '{n.ch}'
            </option>
          ))}
        </select>
        <span>end</span>
        <select
          value={markEnd}
          onChange={(e) => setMarkEnd(e.target.value)}
          style={{ maxWidth: "7rem" }}
        >
          <option value="">—</option>
          {visible.map((n) => (
            <option key={n.id} value={n.id}>
              '{n.ch}'
            </option>
          ))}
        </select>
        <button
          disabled={!markStart || !markEnd}
          onClick={() =>
            dispatch({
              kind: "addMark",
              startId: markStart,
              endId: markEnd,
              mtype,
            })
          }
        >
          add
        </button>
        <button
          disabled={!markStart || !markEnd}
          onClick={() =>
            dispatch({
              kind: "removeMark",
              startId: markStart,
              endId: markEnd,
              mtype,
            })
          }
        >
          remove
        </button>
      </div>
    </div>
  );
}
