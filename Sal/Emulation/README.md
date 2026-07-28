# Sal/Emulation: op-based ⇒ state-based emulation in Lean

Work-in-progress formalization. The goal is to mechanically prove a
meta-theorem of the shape:

> If an op-based CRDT $\mathcal{O}$ is hand-ported to a state-based CRDT
> $\mathcal{D}$ in Sal, and $\mathcal{D}$ is RA-linearizable (proved via
> the 24 VCs), then $\mathcal{O}$ is RA-linearizable.

**Scope: state-based CRDTs only.** No MRDTs, no 3-way merge, no version
DAG, no LCA. The TS here is the 2-way-merge specialisation of the one in
the Sal paper (lin.tex §3.1).

## Primary references

- `_references/arXiv-2502.19967v1/`: Ramesh, Soundarapandian,
  Sivaramakrishnan, *Automatically Verifying Replication-aware
  Linearizability* (the Sal paper). Defines the labeled TS
  $\mathcal{S}_\mathcal{D}$, RA-linearizability (Def. lin), and the
  "24 VCs ⟹ RA-linearizable" theorem (bottom-up linearization).
- `_references/arXiv-2504.05398v2/`: Liittschwager, Castello, Tsampas,
  Kuper, *CRDT Emulation, Simulation, and Representation Independence*
  (ICFP '25). Defines op-based / state-based TS, weak simulation,
  and the emulation-preserves-trace-properties theorem.

## File layout (current and planned)

- [`Labeled_TS.lean`](Labeled_TS.lean): generic labeled transition
  systems, executions, reachability.
- [`CRDT_Signature.lean`](CRDT_Signature.lean): the
  $\langle\Sigma, \sigma_0, \mathsf{do}, \mathsf{merge}, \mathsf{query},
  \mathsf{rc}\rangle$ signature as a Lean structure (2-way merge).
- [`CRDT_TS.lean`](CRDT_TS.lean): the labeled TS for state-based
  CRDTs: configurations carry per-replica state and event set plus a
  visibility relation; four transition rules (CreateReplica, Apply,
  Merge, Query).
- [`RA_Linearizability.lean`](RA_Linearizability.lean): the
  linearization relation $\mathsf{lo}_C$, `rc-non-comm`, `cond-comm`,
  the `IsRALinearizable` predicate (specialised from lin.tex Def. lin),
  and the stubbed bridge theorem.

Later (not yet landed):

- `Weak_Simulation.lean`: weak simulation à la Milner, weak trace
  inclusion.
- `Op_Based_TS.lean`: Liittschwager's op-based TS.
- `Emulation.lean`: the canonical op→state emulation $\mathcal{G}$.
- `Transfer.lean`: the main transfer theorem:
  state-based RA-lin ⟹ op-based RA-lin.
- Per-CRDT simulation proofs (one file per Sal CRDT).

## Status

Foundation definitions. No theorems proved yet; the "24 VCs ⟹ RA-lin"
bridge is stubbed with `sorry`. `SatisfiesVCs` currently carries only
`rcNonComm` and `condComm`; the remaining 22 VCs (from the per-CRDT
theorems in `Sal/CRDTs/*.lean`) still need to be transcribed.

For the ordered roadmap and per-step status, see [`PLAN.md`](PLAN.md).
