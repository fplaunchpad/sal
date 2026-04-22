import { useState } from "react";
import type { CRDTSpec, OpMeta } from "../harness/types";

// Σ = (adds : set (elem, opId), rems : set (elem, opId))
// abstract value = { e | ∃ oid. (e, oid) ∈ adds ∧ (e, oid) ∉ rems }
//
// A remove targets the specific add-id it observed; concurrent adds of the
// same element with different ids survive a remove of just one of them.
type Elem = string;
type OpId = string; // `${ts}.${rid}`
type Tag = `${Elem}|${OpId}`;

function tag(e: Elem, oid: OpId): Tag {
  return `${e}|${oid}` as Tag;
}
function tagElem(t: Tag): Elem {
  return t.split("|", 1)[0];
}

export type Concrete = {
  adds: Set<Tag>;
  rems: Set<Tag>;
};
export type Abstract = Elem[];
export type Op =
  | { kind: "add"; elem: Elem }
  | { kind: "remove"; elem: Elem };

function mkOid(meta: OpMeta): OpId {
  return `${meta.ts}.${meta.rid}`;
}

export const spec: CRDTSpec<Concrete, Abstract, Op> = {
  name: "OR-Set (Observed-Remove Set)",
  slug: "or-set",
  tagline:
    "Add-wins set. Each add carries a unique tag; a remove can only retract adds it observed. Concurrent adds survive a concurrent remove.",
  init: { adds: new Set(), rems: new Set() },

  apply(s: Concrete, op: Op, meta: OpMeta): Concrete {
    if (op.kind === "add") {
      const adds = new Set(s.adds);
      adds.add(tag(op.elem, mkOid(meta)));
      return { ...s, adds };
    } else {
      // Remove all observed add-tags for this element.
      const observed = [...s.adds].filter((t) => tagElem(t) === op.elem);
      if (observed.length === 0) return s;
      const rems = new Set(s.rems);
      for (const t of observed) rems.add(t);
      return { ...s, rems };
    }
  },

  merge(a: Concrete, b: Concrete): Concrete {
    return {
      adds: new Set([...a.adds, ...b.adds]),
      rems: new Set([...a.rems, ...b.rems]),
    };
  },

  abstract(s: Concrete): Abstract {
    const live = new Set<Elem>();
    for (const t of s.adds) {
      if (!s.rems.has(t)) live.add(tagElem(t));
    }
    return [...live].sort();
  },

  renderAbstract(a: Abstract) {
    if (a.length === 0) return <em>∅</em>;
    return <span className="set-view">{`{ ${a.join(", ")} }`}</span>;
  },

  renderConcrete(s: Concrete) {
    const live = [...s.adds].filter((t) => !s.rems.has(t)).sort();
    const tombstones = [...s.rems].sort();
    return (
      <div>
        <div>
          <strong>adds \ rems (live):</strong>{" "}
          {live.length === 0 ? <em>∅</em> : <code>{`{ ${live.join(", ")} }`}</code>}
        </div>
        <div>
          <strong>rems (tombstones):</strong>{" "}
          {tombstones.length === 0 ? (
            <em>∅</em>
          ) : (
            <code>{`{ ${tombstones.join(", ")} }`}</code>
          )}
        </div>
      </div>
    );
  },

  opForm({ state, dispatch }) {
    return <OpForm state={state} dispatch={dispatch} />;
  },

  formatOp(op: Op, meta: OpMeta) {
    return op.kind === "add"
      ? `R${meta.rid} add(${op.elem})@${mkOid(meta)}`
      : `R${meta.rid} remove(${op.elem})`;
  },
};

function OpForm({
  state,
  dispatch,
}: {
  state: Concrete;
  dispatch: (op: Op) => void;
}) {
  const [elem, setElem] = useState("");
  const observedLive = new Set<Elem>();
  for (const t of state.adds) if (!state.rems.has(t)) observedLive.add(tagElem(t));
  return (
    <div className="op-buttons">
      <input
        type="text"
        placeholder="element"
        value={elem}
        maxLength={12}
        onChange={(e) => setElem(e.target.value)}
      />
      <button
        disabled={!elem}
        onClick={() => {
          dispatch({ kind: "add", elem });
          setElem("");
        }}
      >
        add
      </button>
      <button
        disabled={!elem || !observedLive.has(elem)}
        onClick={() => {
          dispatch({ kind: "remove", elem });
          setElem("");
        }}
        title={
          observedLive.has(elem)
            ? ""
            : "Remove only retracts adds this replica has observed"
        }
      >
        remove
      </button>
    </div>
  );
}
