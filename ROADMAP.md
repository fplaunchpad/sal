# Sal research roadmap

A navigable index of the live research threads on top of the verified Sal
suite. The [`README.md`](README.md) catalogs *what is done* (28 RDTs × 24
VCs, kernel-checked); this file tracks *what is open and why it matters*.
It is an index, not a status dump — each thread links to the detailed
`PLAN.md` / `BLUEPRINT.md` that owns its day-to-day state.

The hallway-track narrative for threads 1–3 lives in [`Ideas.md`](Ideas.md);
this roadmap adds dependencies, current status, and entry points so a new
contributor can pick a thread and find the live working file in one hop.

## The shape of the suite (context)

Sal is the Lean port of **Neem** (Soundarapandian, Nagar, Rastogi,
Sivaramakrishnan, OOPSLA 2025). Neem reduces **RA-linearizability** of a
replicated data type to a fixed set of VCs over `do_`, `merge`, `rc`. Sal
mechanises the **VCs per RDT**. The reduction itself — "the VCs ⟹
RA-linearizability" — is, in the published work, a **pen-and-paper**
meta-theorem (Neem Theorem 2; `_references/Neem/lemmas.tex:238`). So every
RDT in the suite today rests on two legs: a Lean leg (its VCs) and a paper
leg (the meta-theorem). Threads 3 and 1 are about turning the paper legs
into Lean legs.

---

## Thread 3 (headline) — Mechanise the Neem soundness meta-theorem

**Goal.** A single kernel-checked Lean chain from `⟨Σ, σ₀, do_, merge, rc⟩`
+ the 24 VCs to RA-linearizability, with **no paper step in the trust
base**. Then every RDT earns a kernel-checked RA-linearizability theorem by
composing its mechanised VCs with the mechanised meta-theorem.

**Why now.** The path-carrying RGA
(`Sal/MRDTs/RGA_Tombstone_Free/RGA_Tombstone_Free_MRDT.lean`) made the gap
load-bearing: its `rc_non_comm'` is the standard VC with commutation
*conditioned* on `accurate` / `fresh_ts` (strictly weaker than Neem's
unconditioned `commutes_with`). Whether the weaker VC still implies
RA-linearizability cannot be decided from the VCs alone — it depends on
whether the soundness construction only ever invokes commutation at states
where the conditions hold. Mechanising soundness turns "probably fine" into
a checked obligation, and is the rigorous form of the
"applicability-conditioned `commutes_with` + re-derivation of soundness"
flagged in thread 2.

**Status — Phase-0 scaffolded; reduced to one blocker.** The ternary (MRDT)
meta-theorem is now built out and machine-checked through Phase-0 (all `0 sorry`,
kernel-clean):
- **S1** — `MRDTSig extends CRDTSig` + `mergeL`/`merge_init_slice`,
  `ConditionedMRDTSig`, `commutesOn`, ternary `lo`
  ([`Sal/Metatheory/MRDTSig.lean`](Sal/Metatheory/MRDTSig.lean)); `D.toCRDTSig` is a
  literal `CRDTSig`.
- **S2** — ternary `Configuration` (replica-keyed core + ranked-version store) +
  well-founded `Reaches` + `initConfig`
  ([`Sal/Metatheory/ExecutionModel.lean`](Sal/Metatheory/ExecutionModel.lean)).
- **S4** — `SatisfiesVCsT` (29-field ternary bundle) + the reuse contract
  `satisfiesVCs_of_T : SatisfiesVCsT D → SatisfiesVCs D.toCRDTSig`
  ([`Sal/Metatheory/VCs.lean`](Sal/Metatheory/VCs.lean)): **the ternary case provably
  reduces to the binary case** at `l := init`, so a fix to the binary bridge lifts
  automatically.
- **S5** — the conditioning gate (below).

That leaves **exactly one blocker**: the **binary merge-linearization induction**
(`Sal/Emulation/Merge_Linearization.lean:4137`, `merge_linearization_exists`, 6
`sorry`s). A probe closed **0 of 6** and found a genuine architectural dead-end, not
a grind: the peel-last strategy needs a *globally* `lo`-maximal event but gets only a
locally-maximal one; two `sorry`s (`:4308/:4311`) are **provably false** (they ask for
*upward* visibility closure, which `vis_causal` — a *backward* invariant — cannot
give); and the obstruction corresponds to an **under-specified commuting sub-case in
the paper** (`appendix.tex` Case 1.1.2). The three-item redesign (carving-based peel +
a vis-transitivity `Configuration` invariant + closing the paper sub-case) and the full
diagnosis are in [`Sal/Metatheory/FINDINGS.md`](Sal/Metatheory/FINDINGS.md). `S6` (the
ternary merge induction) is the ternary twin of this induction and is blocked on the
same redesign.

**Key surfaced finding.** The mechanisation has already shown the paper's
"24 VCs" are **not literally sufficient**: the soundness proof silently uses
5 further properties (`rc_non_comm_directional`, `cond_comm_lift`,
`merge_init`, `merge_peel_comm`, `shared_peel_1op`) the paper treats as
implicit. See `Sal/Emulation/RA_Linearizability.lean:149` (the 29-field
`SatisfiesVCs`). Surfacing and either discharging or admitting these is a
Sal-paper-level result on its own.

**Conditioning result (new, machine-checked — `Sal/MRDTs/RGA_Tombstone_Free/RGA_Reachability_Invariant.lean`).**
The blueprint's R2 keystone — that the forest invariant `anc_consistent`
(≈ `wf s ∧ contains s 0 = false`) is a reachable invariant — is **proved for
`do_`** (`Inv_init`/`Inv_doIns`/`Inv_doDel`, `sorry`-free; `Inv_doDel` is the
`Del`-rehoming case) but **refuted for `merge`** (`merge_breaks_wf`): the merge's
fuel-bounded `climb` (fuel = node id) can run out at a deleted node, leaving a
survivor anchored at an absent, non-root node. `wf`-preservation under `merge`
additionally needs **id-monotone anchors** (`anc t < t`) — a *generation-time*
property of monotone timestamp allocation, **not** a `do_`-invariant. **Now closed
(S5):** `Inv_merge` is proved under the single premise `id_mono l`, and `id_mono` is
itself a reachable invariant under monotone allocation (`id_mono_init` /
`id_mono_doIns` / `id_mono_doDel` / `id_mono_merge`) — so `RgaInv ∧ id_mono` is a
machine-checked reachable invariant that discharges merge soundness, and the keystone
(*conditioned VC sound ⟺ conditioning is a reachable invariant*) is a proved theorem
for the RGA. See BLUEPRINT §5.4 (updated).

**Dependencies.** Reuses the `Sal/Emulation/` execution model + `lo` +
`SatisfiesVCs` + convergence machinery; generalises them from binary to
ternary merge (adds the LCA / version-graph layer).

**Entry points.**
- **Findings / current state:** [`Sal/Metatheory/FINDINGS.md`](Sal/Metatheory/FINDINGS.md)
  — Phase-0 status, the single blocker, the verified diagnosis, and the redesign
  path. **Start here for where things stand.**
- **Phase-0 plan:** [`Sal/Metatheory/PHASE0_PLAN.md`](Sal/Metatheory/PHASE0_PLAN.md)
  — the TTL+RV design, target Lean signatures, sequenced steps (S1–S6).
- **Blueprint:** [`Sal/Metatheory/BLUEPRINT.md`](Sal/Metatheory/BLUEPRINT.md)
  — the dependency graph, VC inventory, and conditioning analysis.
- **Spec:** [`Sal/Metatheory/SOUNDNESS_SPEC.md`](Sal/Metatheory/SOUNDNESS_SPEC.md).
- Paper: `_references/Neem/lin.tex` (RA-lin def, `lo` relation,
  convergence), `_references/Neem/lemmas.tex` (the VC table + Theorems 1/2),
  `_references/Neem/appendix.tex:218-368` (the merge-case induction proof).
- Existing Lean: `Sal/Emulation/RA_Linearizability.lean`,
  `Sal/Emulation/Merge_Linearization.lean`, `Sal/Emulation/CRDT_TS.lean`.

---

## Thread 1 — Op-based ⇒ state-based transfer (Emulation)

**Goal.** Mechanise Liittschwager et al.'s (ICFP'25) result that every
state-based CRDT has a canonical op-based emulation, and weak simulation
transfers RA-linearizability across the two. Lands RA-linearizability for
*every op-based CRDT* in the suite for free, by composing Sal's bottom-up
linearization with Liittschwager's emulation simulation.

**Status.** Bridge (24 VCs ⟹ RA-lin, state-based) **partial**:
Apply/CreateReplica/Query proved, **Merge case open** (the 6 `sorry`s of
thread 3 above). Transfer machinery (weak simulation, weak trace properties)
**proved** (`Weak_Simulation.lean`, no sorries). Op-based TS and canonical
emulation 𝒢 **scaffolded** — but the headline op-side theorem
`op_RA_linearizable_of_vcs` is currently a **vacuous placeholder**
(`OpIsRALinearizable := True`, proof `trivial`; `Transfer.lean:40,67`), and
the 𝒢 simulation carries one `sorry` (`Emulation.lean:51`). Big remaining
piece: the simulation proof for 𝒢 (`Emulation.lean` `effectiveState` +
step 10). Estimated 3–5 months focused.

**Relationship to thread 3.** Thread 1's bridge **is** the thread-3
meta-theorem specialised to **2-way (CRDT) merge** — same `SatisfiesVCs`,
same `lo`, same merge-linearization. Closing thread 1's Merge case closes
the CRDT half of thread 3; thread 3 then generalises it to ternary MRDT
merge. The two share `Sal/Emulation/` outright. Thread 1 additionally
needs the op→state simulation, which thread 3 does not.

**Entry points.** `Sal/Emulation/PLAN.md` (live step-by-step status table),
`Sal/Emulation/MERGE_PROOF.md` (merge-case strategy),
`Sal/Emulation/README.md`.

---

## Thread 2 — Tree-as-primary RGA & the framework-limitation finding

**Goal / finding.** Building RGA with a literal `inductive RGATree` (rather
than flat-set + tombstones) surfaced a **framework limitation**: the 24 VCs
quantify universally over `s : concrete_st`, which is fine for flat-set
RDTs (every op is meaningful on every state) but wrong for structurally
typed state, where "meaningful" needs preconditions (target alive, paths
valid, timestamps fresh). The clean fix is an **applicability-conditioned
`commutes_with`** plus a re-derivation of soundness — i.e. exactly what
thread 3 mechanises.

**Status.**
- **Proved result on `main`:** the tombstone-free path-carrying RGA,
  `Sal/MRDTs/RGA_Tombstone_Free/RGA_Tombstone_Free_MRDT.lean` — builds
  clean, `rc_non_comm'` proved (every pair commutes on well-formed
  histories). This is the design whose *conditioned* VC motivates thread 3.
- **Impossibility (new, kernel-checked):** tombstone-freedom and
  prefix-freedom are **mutually exclusive** for RGA in Sal's VC framework —
  the conflicting `Ins-after-x` / `Del-x` pair is forced into a *merge-free,
  single-replica* `do_` VC (`rc_non_comm'` for `rc=Either`, else
  `cond_comm_base`) that the 3-way merge's LCA cannot reach.
  `Sal/MRDTs/RGA_Tombstone_Free/RGA_PrefixFree_Impossible.lean` (a
  parameterised theorem over *all* local prefix-free semantics; 0 `sorry`,
  no `native_decide`) is the `rc=Either` horn; `RGA_Splice_Counterexample.lean`
  (`cond_comm_base_violated`) is the ordered-`rc` horn. The two proved RGAs
  each break exactly one premise (path-carrying / tombstone-based). **Open:**
  whether the obstruction is fundamental to RA-linearizability or an artifact
  of the merge-free `do_` VC reduction — decidable only once thread 3's
  soundness is mechanised (merge *can* converge the concurrent pair via the
  LCA; the VCs just don't let it).
- **Observational-equivalence path:** `RGA_Tree`'s `read_side_equiv` closed
  end-to-end by Aristotle (kernel-checked) modulo the multi-replica merge
  case. Parked on branch `wip/rga-tree`.
- **Path variant:** `RGA_Tree_Path` — parked on `wip/rga-tree-path`.

**Dependencies → thread 3.** The conditioning analysis in the thread-3
blueprint (`accurate`/`fresh_ts`, the reachability invariant, the
`accurate`-staleness-under-delete risk) is the formal resolution of this
thread's open framework question.

**Entry points.** `AgentNotes.md` (the RGA design index — read before
touching anything under `Sal/MRDTs/RGA*`), `Ideas.md` §2.

---

## Cross-thread composition (the prize)

```
                 thread 3 (MRDT soundness, 3-way merge)
                          │  kernel-checked
   per-RDT VCs  ──────────┤
   (28 RDTs, done)        │
                          ▼
              RA-linearizable (state-based)
                          │
                 thread 1 (emulation transfer)
                          ▼
              RA-linearizable (op-based)
```

With threads 3 + 1 complete, every RDT in the suite — state-based *and*
op-based — carries a kernel-checked RA-linearizability theorem with **no
paper step anywhere** in the trust base. Thread 2 is what forces thread 3
to handle *conditioned* VCs rather than only the unconditioned ones, so the
structural-state RDTs (tree-RGA, path-RGA) compose too.

## How to use this file

One screen, links out. When a thread lands and merges into the framework,
move its summary to `README.md`'s "What's verified" catalog and delete the
thread here (same convention as `Ideas.md`). Keep the status lines honest:
they should match the owning `PLAN.md` / `BLUEPRINT.md` on every push.
</content>
</invoke>
