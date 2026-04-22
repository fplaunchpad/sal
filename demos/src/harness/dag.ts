import type { MRDTSpec } from "./mrdt_types";
import type { OpMeta } from "./types";

export type CommitId = string;

export type CommitKind = "root" | "op" | "merge";

export interface Commit<Concrete, Op> {
  id: CommitId;
  kind: CommitKind;
  parents: CommitId[];
  state: Concrete;
  ts: number; // creation order — unique and monotonic
  authorRid: number; // which replica wrote this commit
  op?: { op: Op; meta: OpMeta }; // for kind === "op"
  mergeFrom?: number; // for kind === "merge": source replica id
}

/**
 * Compute the lowest common ancestor of two commits in the DAG, by BFS:
 *   1. Walk ancestors of A breadth-first, marking each as seen.
 *   2. Walk ancestors of B breadth-first; the first one that's in A's seen
 *      set is the LCA.
 * For criss-cross merges there may be multiple LCAs; we return the first one
 * we find (git calls this "recursive merge base"). For MRDT semantics that's
 * sufficient — the harness always uses *some* LCA, and replicas converge
 * under any consistent choice because merge is commutative.
 */
export function lca<C, O>(
  commits: Map<CommitId, Commit<C, O>>,
  a: CommitId,
  b: CommitId,
): CommitId {
  if (a === b) return a;
  const seen = new Set<CommitId>();
  const queue: CommitId[] = [a];
  while (queue.length > 0) {
    const id = queue.shift()!;
    if (seen.has(id)) continue;
    seen.add(id);
    const c = commits.get(id);
    if (c) queue.push(...c.parents);
  }
  const bq: CommitId[] = [b];
  const bseen = new Set<CommitId>();
  while (bq.length > 0) {
    const id = bq.shift()!;
    if (bseen.has(id)) continue;
    bseen.add(id);
    if (seen.has(id)) return id;
    const c = commits.get(id);
    if (c) bq.push(...c.parents);
  }
  // Unreachable if the DAG has a shared root.
  throw new Error(`No LCA between ${a} and ${b}`);
}

export interface DAGState<C, O> {
  commits: Map<CommitId, Commit<C, O>>;
  heads: CommitId[]; // per-replica HEAD pointers, index = rid
  nextCommit: number;
  nextTs: number;
}

export function initDAG<C, O>(
  spec: MRDTSpec<C, unknown, O>,
  replicaCount: number,
): DAGState<C, O> {
  const root: Commit<C, O> = {
    id: "c0",
    kind: "root",
    parents: [],
    state: spec.init,
    ts: 0,
    authorRid: -1,
  };
  return {
    commits: new Map([["c0", root]]),
    heads: Array.from({ length: replicaCount }, () => "c0"),
    nextCommit: 1,
    nextTs: 1,
  };
}

export function applyOp<C, O>(
  spec: MRDTSpec<C, unknown, O>,
  dag: DAGState<C, O>,
  rid: number,
  op: O,
): DAGState<C, O> {
  const parentId = dag.heads[rid];
  const parent = dag.commits.get(parentId)!;
  const meta: OpMeta = { ts: dag.nextTs, rid };
  const newState = spec.apply(parent.state, op, meta);
  const id = `c${dag.nextCommit}`;
  const commit: Commit<C, O> = {
    id,
    kind: "op",
    parents: [parentId],
    state: newState,
    ts: dag.nextTs,
    authorRid: rid,
    op: { op, meta },
  };
  const commits = new Map(dag.commits);
  commits.set(id, commit);
  const heads = dag.heads.slice();
  heads[rid] = id;
  return {
    commits,
    heads,
    nextCommit: dag.nextCommit + 1,
    nextTs: dag.nextTs + 1,
  };
}

export function mergeInto<C, O>(
  spec: MRDTSpec<C, unknown, O>,
  dag: DAGState<C, O>,
  fromRid: number,
  toRid: number,
): DAGState<C, O> {
  if (fromRid === toRid) return dag;
  const fromHead = dag.heads[fromRid];
  const toHead = dag.heads[toRid];
  if (fromHead === toHead) return dag;
  const baseId = lca(dag.commits, toHead, fromHead);
  const base = dag.commits.get(baseId)!;
  const fromState = dag.commits.get(fromHead)!.state;
  const toState = dag.commits.get(toHead)!.state;
  const merged = spec.merge(base.state, toState, fromState);
  const id = `c${dag.nextCommit}`;
  const commit: Commit<C, O> = {
    id,
    kind: "merge",
    parents: [toHead, fromHead],
    state: merged,
    ts: dag.nextTs,
    authorRid: toRid,
    mergeFrom: fromRid,
  };
  const commits = new Map(dag.commits);
  commits.set(id, commit);
  const heads = dag.heads.slice();
  heads[toRid] = id;
  return {
    commits,
    heads,
    nextCommit: dag.nextCommit + 1,
    nextTs: dag.nextTs + 1,
  };
}

export function resetReplica<C, O>(
  dag: DAGState<C, O>,
  rid: number,
): DAGState<C, O> {
  // Point HEAD back to root; don't prune commits (others may still reference them).
  const heads = dag.heads.slice();
  heads[rid] = "c0";
  return { ...dag, heads };
}

export function addReplica<C, O>(dag: DAGState<C, O>): DAGState<C, O> {
  return { ...dag, heads: [...dag.heads, "c0"] };
}
