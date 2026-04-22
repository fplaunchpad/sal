import { useMemo, useReducer, useState } from "react";
import type { MRDTSpec } from "./mrdt_types";
import {
  addReplica,
  applyOp,
  type Commit,
  type CommitId,
  type DAGState,
  initDAG,
  mergeInto,
  resetReplica,
} from "./dag";

type Action<O> =
  | { kind: "apply"; rid: number; op: O }
  | { kind: "merge"; from: number; to: number }
  | { kind: "addReplica" }
  | { kind: "resetReplica"; rid: number }
  | { kind: "toggleConcrete" }
  | { kind: "setMergeFrom"; rid: number }
  | { kind: "setMergeTo"; rid: number }
  | { kind: "selectCommit"; id: CommitId | null };

interface HarnessState<C, O> {
  dag: DAGState<C, O>;
  showConcrete: boolean;
  mergeFrom: number;
  mergeTo: number;
  selectedCommit: CommitId | null;
}

function makeReducer<C, A, O>(spec: MRDTSpec<C, A, O>) {
  return (s: HarnessState<C, O>, a: Action<O>): HarnessState<C, O> => {
    switch (a.kind) {
      case "apply":
        return { ...s, dag: applyOp(spec, s.dag, a.rid, a.op) };
      case "merge":
        return { ...s, dag: mergeInto(spec, s.dag, a.from, a.to) };
      case "addReplica":
        return { ...s, dag: addReplica(s.dag) };
      case "resetReplica":
        return { ...s, dag: resetReplica(s.dag, a.rid) };
      case "toggleConcrete":
        return { ...s, showConcrete: !s.showConcrete };
      case "setMergeFrom":
        return { ...s, mergeFrom: a.rid };
      case "setMergeTo":
        return { ...s, mergeTo: a.rid };
      case "selectCommit":
        return { ...s, selectedCommit: a.id };
    }
  };
}

const REPLICA_COLORS = [
  "#0366d6",
  "#d93a49",
  "#2da44e",
  "#9333ea",
  "#e36209",
  "#0969da",
];

function colorFor(rid: number): string {
  if (rid < 0) return "#888";
  return REPLICA_COLORS[rid % REPLICA_COLORS.length];
}

export function MRDTPlayground<C, A, O>({
  spec,
  initialReplicas = 3,
}: {
  spec: MRDTSpec<C, A, O>;
  initialReplicas?: number;
}) {
  const initial = useMemo<HarnessState<C, O>>(
    () => ({
      dag: initDAG(spec, initialReplicas),
      showConcrete: false,
      mergeFrom: 0,
      mergeTo: 1,
      selectedCommit: null,
    }),
    [spec, initialReplicas],
  );
  const [state, dispatch] = useReducer(makeReducer(spec), initial);
  const [historyOpen, setHistoryOpen] = useState(false);

  const replicas = state.dag.heads.map((headId, rid) => {
    const head = state.dag.commits.get(headId)!;
    return { rid, head };
  });

  const selectedCommit = state.selectedCommit
    ? state.dag.commits.get(state.selectedCommit) ?? null
    : null;

  return (
    <div className="playground">
      <header>
        <h1>{spec.name} <span style={{ color: "#888", fontSize: "0.7em" }}>(MRDT)</span></h1>
        <p className="tagline">{spec.tagline}</p>
      </header>

      <section className="controls">
        <label>
          <input
            type="checkbox"
            checked={state.showConcrete}
            onChange={() => dispatch({ kind: "toggleConcrete" })}
          />
          Show concrete state
        </label>
        <button onClick={() => dispatch({ kind: "addReplica" })}>
          Add replica
        </button>
        <div
          className="merge-controls"
          title="3-way merge: target absorbs source using their LCA as the third argument. Creates a merge commit with two parents."
        >
          <span>Merge</span>
          <select
            value={state.mergeFrom}
            onChange={(e) =>
              dispatch({ kind: "setMergeFrom", rid: Number(e.target.value) })
            }
          >
            {replicas.map(({ rid }) => (
              <option key={rid} value={rid}>
                R{rid}
              </option>
            ))}
          </select>
          <span aria-label="into">→</span>
          <select
            value={state.mergeTo}
            onChange={(e) =>
              dispatch({ kind: "setMergeTo", rid: Number(e.target.value) })
            }
          >
            {replicas.map(({ rid }) => (
              <option key={rid} value={rid}>
                R{rid}
              </option>
            ))}
          </select>
          <button
            disabled={state.mergeFrom === state.mergeTo}
            onClick={() =>
              dispatch({
                kind: "merge",
                from: state.mergeFrom,
                to: state.mergeTo,
              })
            }
          >
            Merge
          </button>
        </div>
      </section>

      <section className="replicas">
        {replicas.map(({ rid, head }) => (
          <div
            className="replica"
            key={rid}
            style={{ borderTop: `3px solid ${colorFor(rid)}` }}
          >
            <h2 style={{ color: colorFor(rid) }}>
              R{rid} <code>@ {head.id}</code>
            </h2>
            <div className="abstract">
              <strong>Value:</strong> {spec.renderAbstract(spec.abstract(head.state))}
            </div>
            {state.showConcrete && (
              <div className="concrete">
                <strong>Concrete:</strong>
                <div>{spec.renderConcrete(head.state)}</div>
              </div>
            )}
            <div className="op-form">
              <spec.opForm
                state={head.state}
                dispatch={(op) => dispatch({ kind: "apply", rid, op })}
              />
            </div>
            <button
              className="reset"
              onClick={() => dispatch({ kind: "resetReplica", rid })}
              title="Point HEAD back to the root commit (keeps history intact)"
            >
              Reset R{rid}
            </button>
          </div>
        ))}
      </section>

      <section>
        <button onClick={() => setHistoryOpen((o) => !o)}>
          {historyOpen ? "Hide" : "Show"} history DAG ({state.dag.commits.size} commits)
        </button>
        {historyOpen && (
          <DAGView
            dag={state.dag}
            spec={spec}
            selected={state.selectedCommit}
            onSelect={(id) => dispatch({ kind: "selectCommit", id })}
          />
        )}
        {selectedCommit && historyOpen && (
          <CommitInspector commit={selectedCommit} spec={spec} />
        )}
      </section>
    </div>
  );
}

function DAGView<C, A, O>({
  dag,
  spec,
  selected,
  onSelect,
}: {
  dag: DAGState<C, O>;
  spec: MRDTSpec<C, A, O>;
  selected: CommitId | null;
  onSelect: (id: CommitId | null) => void;
}) {
  // Lane assignment: root in lane 0; op-commit inherits author's lane;
  // merge-commit goes to target replica's lane. We just use authorRid.
  const commits = [...dag.commits.values()].sort((a, b) => a.ts - b.ts);
  const laneCount = Math.max(
    1,
    ...commits.map((c) => (c.authorRid < 0 ? 0 : c.authorRid + 1)),
  );
  const rowH = 46;
  const laneW = 80;
  const radius = 12;
  const xOf = (lane: number) => laneW / 2 + lane * laneW;
  const yOf = (ts: number) => 30 + ts * rowH;
  const laneOf = (c: Commit<C, O>): number =>
    c.authorRid < 0 ? 0 : c.authorRid;

  const width = laneCount * laneW + 40;
  const height = (commits[commits.length - 1]?.ts ?? 0) * rowH + 80;

  const heads = new Set(dag.heads);

  return (
    <div
      style={{
        marginTop: "1rem",
        background: "white",
        border: "1px solid #ddd",
        borderRadius: 6,
        padding: "0.5rem",
        overflowX: "auto",
      }}
    >
      <svg width={width} height={height} role="img" aria-label="history DAG">
        {/* lane labels */}
        {Array.from({ length: laneCount }, (_, i) => (
          <text
            key={i}
            x={xOf(i)}
            y={18}
            textAnchor="middle"
            fontSize={11}
            fill={colorFor(i)}
            fontWeight={600}
          >
            R{i}
          </text>
        ))}
        {/* edges (parent → child) */}
        {commits.flatMap((c) =>
          c.parents.map((pId) => {
            const p = dag.commits.get(pId);
            if (!p) return null;
            const x1 = xOf(laneOf(p));
            const y1 = yOf(p.ts);
            const x2 = xOf(laneOf(c));
            const y2 = yOf(c.ts);
            return (
              <line
                key={`${pId}-${c.id}`}
                x1={x1}
                y1={y1}
                x2={x2}
                y2={y2}
                stroke="#666"
                strokeWidth={1.5}
              />
            );
          }),
        )}
        {/* commit dots */}
        {commits.map((c) => {
          const cx = xOf(laneOf(c));
          const cy = yOf(c.ts);
          const isSelected = selected === c.id;
          const isHead = heads.has(c.id);
          return (
            <g
              key={c.id}
              onClick={() => onSelect(isSelected ? null : c.id)}
              style={{ cursor: "pointer" }}
            >
              <circle
                cx={cx}
                cy={cy}
                r={radius}
                fill={c.kind === "merge" ? "white" : colorFor(c.authorRid)}
                stroke={colorFor(c.authorRid)}
                strokeWidth={isHead ? 3 : 2}
                strokeDasharray={c.kind === "merge" ? "3 2" : undefined}
              />
              <text
                x={cx}
                y={cy + 3}
                textAnchor="middle"
                fontSize={9}
                fill={c.kind === "merge" ? colorFor(c.authorRid) : "white"}
                fontWeight={600}
                pointerEvents="none"
              >
                {c.id}
              </text>
              <text
                x={cx + radius + 6}
                y={cy + 3}
                fontSize={10}
                fill="#333"
                pointerEvents="none"
              >
                {c.kind === "op"
                  ? spec.formatOp(c.op!.op, c.op!.meta)
                  : c.kind === "merge"
                    ? `merge ← R${c.mergeFrom}`
                    : "root"}
              </text>
              {isSelected && (
                <circle
                  cx={cx}
                  cy={cy}
                  r={radius + 4}
                  fill="none"
                  stroke="#333"
                  strokeWidth={1}
                />
              )}
            </g>
          );
        })}
      </svg>
    </div>
  );
}

function CommitInspector<C, A, O>({
  commit,
  spec,
}: {
  commit: Commit<C, O>;
  spec: MRDTSpec<C, A, O>;
}) {
  return (
    <div
      style={{
        marginTop: "0.5rem",
        background: "#f7f7f7",
        border: "1px solid #ddd",
        borderRadius: 6,
        padding: "0.75rem",
      }}
    >
      <div>
        <code>{commit.id}</code> — {commit.kind}
        {commit.kind === "op" && commit.op
          ? ` — ${spec.formatOp(commit.op.op, commit.op.meta)}`
          : commit.kind === "merge"
            ? ` — merge ← R${commit.mergeFrom}`
            : ""}
        {commit.parents.length > 0 && (
          <> · parents: {commit.parents.map((p) => <code key={p}>{p}</code>).reduce<React.ReactNode[]>((acc, x, i) => (i === 0 ? [x] : [...acc, ", ", x]), [])}</>
        )}
      </div>
      <div style={{ marginTop: 6 }}>
        <strong>Value:</strong> {spec.renderAbstract(spec.abstract(commit.state))}
      </div>
      <div style={{ marginTop: 6 }}>
        <strong>Concrete:</strong> {spec.renderConcrete(commit.state)}
      </div>
    </div>
  );
}
