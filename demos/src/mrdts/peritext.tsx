import { useState } from "react";
import type { MRDTSpec } from "../harness/mrdt_types";
import type { OpMeta } from "../harness/types";

// Σ = (chars : set CharRec, removed : set OpId, marks : set AnchorAttachment)
//   CharRec = (id : OpId, after : OpId, ch : char)
//   AnchorAttachment carries the MarkOp and which side of which char it
//   anchors to. AddMark / RemoveMark each contribute two attachments.
//
// All three components are grow-only. Three-way merge is pointwise set
// `(l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)` per component — the LCA is vestigial
// (collapses to `l ∪ a ∪ b`), kept in this shape for parity with the
// rest of the MRDT suite.
//
// Effective formatting at read time: of the unique MarkOps covering a
// char, the one with the highest opId wins; isAdd determines whether
// the char carries that mark.
type OpId = string; // `${ts}:${rid}`
const ROOT: OpId = "0:0";

type MarkType = "bold" | "italic";

type MarkOp = {
  opId: OpId;
  startId: OpId;
  startSide: boolean;
  endId: OpId;
  endSide: boolean;
  mtype: MarkType;
  isAdd: boolean;
};

type CharRec = { id: OpId; after: OpId; ch: string };
type AnchorAttachment = { anchor: OpId; side: boolean; mark: MarkOp };

export type Concrete = {
  chars: CharRec[];
  removed: Set<OpId>;
  marks: AnchorAttachment[];
};

export type Abstract = {
  visible: { id: OpId; ch: string; bold: boolean; italic: boolean }[];
};

export type Op =
  | { kind: "insert"; ch: string; after: OpId }
  | { kind: "remove"; target: OpId }
  | { kind: "addMark"; startId: OpId; endId: OpId; mtype: MarkType }
  | { kind: "removeMark"; startId: OpId; endId: OpId; mtype: MarkType };

function mkOid(meta: OpMeta): OpId {
  return `${meta.ts}:${meta.rid}`;
}

function cmpOid(a: OpId, b: OpId): number {
  const [ta, ra] = a.split(":").map(Number);
  const [tb, rb] = b.split(":").map(Number);
  return ta - tb || ra - rb;
}

function cmpOidDesc(a: OpId, b: OpId): number {
  return cmpOid(b, a);
}

function charKey(c: CharRec): string {
  return `${c.id}|${c.after}|${c.ch}`;
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

function dedupChars(xs: CharRec[]): CharRec[] {
  const m = new Map<string, CharRec>();
  for (const c of xs) m.set(charKey(c), c);
  return [...m.values()];
}

function dedupAttachments(xs: AnchorAttachment[]): AnchorAttachment[] {
  const m = new Map<string, AnchorAttachment>();
  for (const a of xs) m.set(attachmentKey(a), a);
  return [...m.values()];
}

function threeWayKeyed<T>(
  l: T[],
  a: T[],
  b: T[],
  keyOf: (t: T) => string,
): T[] {
  const lk = new Set(l.map(keyOf));
  const ak = new Set(a.map(keyOf));
  const bk = new Set(b.map(keyOf));
  const out = new Map<string, T>();
  for (const t of l) {
    const k = keyOf(t);
    if (ak.has(k) && bk.has(k)) out.set(k, t);
  }
  for (const t of a) if (!lk.has(keyOf(t))) out.set(keyOf(t), t);
  for (const t of b) if (!lk.has(keyOf(t))) out.set(keyOf(t), t);
  return [...out.values()];
}

function threeWaySet<T>(l: Set<T>, a: Set<T>, b: Set<T>): Set<T> {
  const out = new Set<T>();
  for (const x of l) if (a.has(x) && b.has(x)) out.add(x);
  for (const x of a) if (!l.has(x)) out.add(x);
  for (const x of b) if (!l.has(x)) out.add(x);
  return out;
}

function traverse(
  s: Concrete,
): { id: OpId; ch: string; deleted: boolean }[] {
  const children = new Map<OpId, CharRec[]>();
  for (const c of s.chars) {
    const arr = children.get(c.after) ?? [];
    arr.push(c);
    children.set(c.after, arr);
  }
  for (const arr of children.values()) arr.sort((x, y) => cmpOidDesc(x.id, y.id));
  const out: { id: OpId; ch: string; deleted: boolean }[] = [];
  const visit = (anchor: OpId) => {
    for (const c of children.get(anchor) ?? []) {
      out.push({ id: c.id, ch: c.ch, deleted: s.removed.has(c.id) });
      visit(c.id);
    }
  };
  visit(ROOT);
  return out;
}

function uniqueMarks(attachments: AnchorAttachment[]): MarkOp[] {
  const m = new Map<string, MarkOp>();
  for (const a of attachments) m.set(a.mark.opId, a.mark);
  return [...m.values()];
}

function effectiveFormatting(
  s: Concrete,
  visible: { id: OpId }[],
): Map<OpId, { bold: boolean; italic: boolean }> {
  const pos = new Map<OpId, number>();
  visible.forEach((n, i) => pos.set(n.id, i));
  const best = new Map<string, MarkOp>(); // `${charId}|${type}` → winning MarkOp
  for (const m of uniqueMarks(s.marks)) {
    const sIdx = pos.get(m.startId);
    const eIdx = pos.get(m.endId);
    if (sIdx === undefined || eIdx === undefined) continue;
    const [lo, hi] = sIdx <= eIdx ? [sIdx, eIdx] : [eIdx, sIdx];
    for (let i = lo; i <= hi; i++) {
      const c = visible[i].id;
      const k = `${c}|${m.mtype}`;
      const cur = best.get(k);
      if (!cur || cmpOid(cur.opId, m.opId) < 0) best.set(k, m);
    }
  }
  const out = new Map<OpId, { bold: boolean; italic: boolean }>();
  for (const v of visible) out.set(v.id, { bold: false, italic: false });
  for (const [k, m] of best) {
    const [charId] = k.split("|");
    const fm = out.get(charId)!;
    if (m.mtype === "bold") fm.bold = m.isAdd;
    if (m.mtype === "italic") fm.italic = m.isAdd;
  }
  return out;
}

export const spec: MRDTSpec<Concrete, Abstract, Op> = {
  name: "Peritext (text-only)",
  slug: "peritext",
  tagline:
    "Rich-text MRDT: chars (RGA records fused into a flat set), tombstones, and anchor-attached mark ops. All three components are grow-only; merge is the standard three-way set union per component (LCA is vestigial). Concurrent Add beats concurrent Remove on the same range.",
  init: { chars: [], removed: new Set(), marks: [] },

  apply(s, op, meta) {
    if (op.kind === "insert") {
      const id = mkOid(meta);
      return {
        ...s,
        chars: dedupChars([...s.chars, { id, after: op.after, ch: op.ch }]),
      };
    }
    if (op.kind === "remove") {
      const removed = new Set(s.removed);
      removed.add(op.target);
      return { ...s, removed };
    }
    const m: MarkOp = {
      opId: mkOid(meta),
      startId: op.startId,
      startSide: false,
      endId: op.endId,
      endSide: true,
      mtype: op.mtype,
      isAdd: op.kind === "addMark",
    };
    const attachments: AnchorAttachment[] = [
      { anchor: op.startId, side: false, mark: m },
      { anchor: op.endId, side: true, mark: m },
    ];
    return { ...s, marks: dedupAttachments([...s.marks, ...attachments]) };
  },

  merge(l, a, b) {
    return {
      chars: threeWayKeyed(l.chars, a.chars, b.chars, charKey),
      removed: threeWaySet(l.removed, a.removed, b.removed),
      marks: threeWayKeyed(l.marks, a.marks, b.marks, attachmentKey),
    };
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
            dispatch({ kind: "addMark", startId: markStart, endId: markEnd, mtype })
          }
        >
          add
        </button>
        <button
          disabled={!markStart || !markEnd}
          onClick={() =>
            dispatch({ kind: "removeMark", startId: markStart, endId: markEnd, mtype })
          }
        >
          remove
        </button>
      </div>
    </div>
  );
}
