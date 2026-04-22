import { useMemo, useReducer, useState } from "react";
import type { CRDTSpec, OpMeta } from "./types";

interface ReplicaState<Concrete, Op> {
  state: Concrete;
  history: { op: Op; meta: OpMeta }[];
}

interface HarnessState<Concrete, Op> {
  replicas: ReplicaState<Concrete, Op>[];
  nextTs: number;
  showConcrete: boolean;
  mergeFrom: number | null;
  mergeTo: number | null;
}

type Action<Op> =
  | { kind: "apply"; rid: number; op: Op }
  | { kind: "merge"; from: number; to: number }
  | { kind: "addReplica" }
  | { kind: "resetReplica"; rid: number }
  | { kind: "toggleConcrete" }
  | { kind: "setMergeFrom"; rid: number | null }
  | { kind: "setMergeTo"; rid: number | null };

function reducer<Concrete, Abstract, Op>(
  spec: CRDTSpec<Concrete, Abstract, Op>,
): (
  s: HarnessState<Concrete, Op>,
  a: Action<Op>,
) => HarnessState<Concrete, Op> {
  return (s, a) => {
    switch (a.kind) {
      case "apply": {
        const meta: OpMeta = { ts: s.nextTs, rid: a.rid };
        const replicas = s.replicas.map((r, i) =>
          i === a.rid
            ? {
                state: spec.apply(r.state, a.op, meta),
                history: [...r.history, { op: a.op, meta }],
              }
            : r,
        );
        return { ...s, replicas, nextTs: s.nextTs + 1 };
      }
      case "merge": {
        if (a.from === a.to) return s;
        const merged = spec.merge(
          s.replicas[a.from].state,
          s.replicas[a.to].state,
        );
        // Both replicas converge to the merged state.
        const replicas = s.replicas.map((r, i) =>
          i === a.from || i === a.to
            ? {
                state: merged,
                history: [
                  ...r.history,
                  {
                    op: null as unknown as Op,
                    meta: { ts: s.nextTs, rid: i },
                  },
                ],
              }
            : r,
        );
        return { ...s, replicas, nextTs: s.nextTs + 1 };
      }
      case "addReplica":
        return {
          ...s,
          replicas: [...s.replicas, { state: spec.init, history: [] }],
        };
      case "resetReplica": {
        const replicas = s.replicas.map((r, i) =>
          i === a.rid ? { state: spec.init, history: [] } : r,
        );
        return { ...s, replicas };
      }
      case "toggleConcrete":
        return { ...s, showConcrete: !s.showConcrete };
      case "setMergeFrom":
        return { ...s, mergeFrom: a.rid };
      case "setMergeTo":
        return { ...s, mergeTo: a.rid };
    }
  };
}

export function Playground<Concrete, Abstract, Op>({
  spec,
  initialReplicas = 3,
}: {
  spec: CRDTSpec<Concrete, Abstract, Op>;
  initialReplicas?: number;
}) {
  const initial = useMemo<HarnessState<Concrete, Op>>(
    () => ({
      replicas: Array.from({ length: initialReplicas }, () => ({
        state: spec.init,
        history: [],
      })),
      nextTs: 0,
      showConcrete: false,
      mergeFrom: 0,
      mergeTo: 1,
    }),
    [spec, initialReplicas],
  );

  const [state, dispatch] = useReducer(reducer(spec), initial);
  const [historyOpen, setHistoryOpen] = useState<Set<number>>(new Set());

  const toggleHistory = (rid: number) => {
    setHistoryOpen((prev) => {
      const next = new Set(prev);
      if (next.has(rid)) next.delete(rid);
      else next.add(rid);
      return next;
    });
  };

  return (
    <div className="playground">
      <header>
        <h1>{spec.name}</h1>
        <p className="tagline">{spec.tagline}</p>
      </header>

      <section className="controls">
        <label>
          <input
            type="checkbox"
            checked={state.showConcrete}
            onChange={() => dispatch({ kind: "toggleConcrete" })}
          />
          Show concrete (lattice) state
        </label>
        <button onClick={() => dispatch({ kind: "addReplica" })}>
          Add replica
        </button>

        <div className="merge-controls">
          <span>Merge</span>
          <select
            value={state.mergeFrom ?? ""}
            onChange={(e) =>
              dispatch({
                kind: "setMergeFrom",
                rid: e.target.value === "" ? null : Number(e.target.value),
              })
            }
          >
            {state.replicas.map((_, i) => (
              <option key={i} value={i}>
                R{i}
              </option>
            ))}
          </select>
          <span>↔</span>
          <select
            value={state.mergeTo ?? ""}
            onChange={(e) =>
              dispatch({
                kind: "setMergeTo",
                rid: e.target.value === "" ? null : Number(e.target.value),
              })
            }
          >
            {state.replicas.map((_, i) => (
              <option key={i} value={i}>
                R{i}
              </option>
            ))}
          </select>
          <button
            disabled={
              state.mergeFrom === null ||
              state.mergeTo === null ||
              state.mergeFrom === state.mergeTo
            }
            onClick={() =>
              dispatch({
                kind: "merge",
                from: state.mergeFrom!,
                to: state.mergeTo!,
              })
            }
          >
            Merge
          </button>
        </div>
      </section>

      <section className="replicas">
        {state.replicas.map((r, rid) => (
          <div className="replica" key={rid}>
            <h2>R{rid}</h2>
            <div className="abstract">
              <strong>Value:</strong> {spec.renderAbstract(spec.abstract(r.state))}
            </div>
            {state.showConcrete && (
              <div className="concrete">
                <strong>Concrete:</strong>
                <div>{spec.renderConcrete(r.state)}</div>
              </div>
            )}
            <div className="op-form">
              <spec.opForm
                state={r.state}
                dispatch={(op) => dispatch({ kind: "apply", rid, op })}
              />
            </div>
            <div className="history">
              <button onClick={() => toggleHistory(rid)}>
                {historyOpen.has(rid)
                  ? `Hide history (${r.history.length})`
                  : `Show history (${r.history.length})`}
              </button>
              {historyOpen.has(rid) && (
                <ol>
                  {r.history.map((entry, i) => (
                    <li key={i}>
                      <code>ts={entry.meta.ts}</code>{" "}
                      {entry.op === null
                        ? "merge"
                        : spec.formatOp(entry.op, entry.meta)}
                    </li>
                  ))}
                </ol>
              )}
            </div>
            <button
              className="reset"
              onClick={() => dispatch({ kind: "resetReplica", rid })}
            >
              Reset R{rid}
            </button>
          </div>
        ))}
      </section>
    </div>
  );
}
