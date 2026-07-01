# Neem Soundness Meta-Theorem — Phase-0 Recommended Plan

**Status.** Decision-ready synthesis. Inputs: `SOUNDNESS_SPEC.md` (the target), three
ternary Phase-0 designs, and three judge panels (Tractability, Reuse,
Faithfulness+Conditioning). This document fixes the Phase-0 architecture, the target Lean
signatures, the reuse-vs-new map, the conditioning carry, and a sequenced, checkable work
plan. Citations re-verified against source while writing.

---

## 0. Decision

**Adopt a synthesis with Design 1 (Thin-Ternary-Layer) as the spine, grafted with
Design 2's ranked version layer (`Version := Nat`, `parents_lt`) and Design 3's explicit
lex carving measure + state-shape / generation-time conditioning split.**

Working name: **TTL+RV** (Thin-Ternary-Layer over a Ranked-Version store).

### Why, against the judge scores

| Design | Tractability | Reuse | Faithfulness+Cond. | Σ |
|---|---|---|---|---|
| 1 Thin-Ternary-Layer | **8** | **9** | 6 | 23 |
| 2 Version-DAG-first | 7 | 6 | **9** | 22 |
| 3 LCA-First-Class | 6 | 5 | 8 | 19 |

The two engineering axes (Tractability, Reuse) — the ones that decide whether Phase-0
*lands at all* against the proved 4400-line `Sal/Emulation` skeleton — are both won by
Design 1, decisively (8, 9). Design 1's `MRDTSig extends CRDTSig` + `merge_init_slice`
makes `D.toCRDTSig` a *literal* `CRDTSig` (`CRDT_Signature.lean:67`), so the entire
merge-independent corpus and the replica-keyed bridge cases
(`RA_Linearizability.lean:543,564,601,629`) reuse with byte-identical normal forms —
exactly what keeps `grind` effective.

The one axis Design 1 loses — Faithfulness+Conditioning (6 vs Design 2's 9) — is the
**research-critical** one (KC's research-first guidance; the conditioning is the open
crux per `SOUNDNESS_SPEC.md` Part 4.4). The faithfulness judge's decisive objection is
concrete and correct: Design 1's *unordered, `Set`-keyed* version store gives the
generation-time **id-monotone allocation** invariant — the property the machine-checked
`merge_breaks_wf` (`RGA_Reachability_Invariant.lean:209`) proves merge soundness requires
(`id_mono l : ∀ t, contains l t → anc l t = 0 ∨ anc l t < t`, `:227`) — **no structural
home**. Design 2's `Version := Nat` with `parents_lt : p ∈ parents v → p < v` fuses DAG
acyclicity and the generation clock into one decidable field and is the only proposed
home for that invariant.

**All three judges' composite recommendations converge on the same graft**: Design 1's
encoding + Design 2's Nat-keyed reachable-version store + Design 3's explicit lex measure
(on list-lengths / `Set.ncard`, **not** `Finset`) and conditioning split. TTL+RV is that
convergent graft, made precise below. The single real architectural decision it resolves
is the replica-keyed-vs-version-keyed fork: **keep the Configuration replica-keyed**
(Design 1 — protects reuse, keeps `IsRALinearizable` over replicas so the binary bridge
runs verbatim), and **add the ranked version store as an additive component** rather than
re-keying `N`/`L`. This buys Design 2's structural generation-time home and (optionally,
Phase-0-B) its free-IH-at-the-LCA, *without* paying Design 2/3's re-key tax that cost them
3 reuse points.

Design 3 is mined for two ideas only: the explicit `Nat ×ₗ Nat ×ₗ Nat` lex carving
measure (node-for-node with `appendix.tex:288/295/315`) and the clean Inv/applicable
conditioning split. We **reject** its `Finset`-valued carving: `lo`/`commutes` are
`∀ s, …` (`RA_Linearizability.lean:88`, `CRDT_Signature.lean:89`), so the carving sets are
`Classical`-noncomputable regardless, the decidable-`.card` win is illusory, and `Finset`
forces `Set ↔ Finset` bridging against the ported `Set`-valued carving lemmas
(`Merge_Linearization.lean:77-294`). Measure on `Set.ncard` / witness-list lengths.

---

## 1. Target Lean signatures

All under a new `Sal/Metatheory/` namespace; the binary `Sal/Emulation` is untouched.

### 1.1 Signature: `MRDTSig` (Design 1 spine) and the conditioned extension

```lean
/-- Ternary MRDT signature.  Inherits init/AppOp/update/query/rc UNCHANGED from
    CRDTSig; adds the ternary `mergeL l a b` and pins the inherited binary `merge`
    field to be exactly its `l := init` slice. -/
structure MRDTSig extends Sal.Emulation.CRDTSig where
  mergeL : State → State → State → State                 -- paper merge(l, a, b)
  merge_init_slice : ∀ a b, mergeL init a b = merge a b  -- the reuse contract

/-- State-shape Inv + per-event generation-time guard (Design 3 split). -/
structure ConditionedMRDTSig extends MRDTSig where
  Inv        : State → Prop          -- state-SHAPE reachability over-approx (e.g. RgaInv)
  applicable : Op AppOp → State → Prop  -- GENERATION-TIME guard; MAY read the op timestamp

/-- Commutation required ONLY on Inv/applicable reachable states (BLUEPRINT.md:437). -/
def ConditionedMRDTSig.commutesOn (D : ConditionedMRDTSig) (o₁ o₂ : Op D.AppOp) : Prop :=
  ∀ s, D.Inv s → D.applicable o₁ s → D.applicable o₂ s →
    D.update (D.update s o₁) o₂ = D.update (D.update s o₂) o₁
```

`commutesOn` **reduces definitionally to `CRDTSig.commutes`** when `Inv := fun _ => True`
and `applicable := fun _ _ => True`; the 28 existing flat RDTs and every `lo`-lemma are
then untouched (`rfl`).

### 1.2 The linearization order over `commutesOn`

```lean
/-- Identical shape to RA_Linearizability.lean:88, with `commutes → commutesOn` at the two
    ⇄-sites (spec ⚑1).  Paper-faithful because lo C is only read at events of reachable C. -/
def lo (D : ConditionedMRDTSig) (C : Configuration D) (e₁ e₂ : Op D.AppOp) : Prop :=
  (C.vis e₁ e₂ ∧ ¬ D.commutesOn e₁ e₂)
  ∨ (¬ C.vis e₁ e₂ ∧ ¬ C.vis e₂ e₁ ∧ D.rc e₁ e₂ = RcRes.Fst_then_snd
     ∧ ¬ ∃ e₃, C.vis e₂ e₃ ∧ ¬ D.commutesOn e₂ e₃)
```

`listPermOf`, `respects`, `IsRALinearizable`, `IsRALinearizableExec`
(`RA_Linearizability.lean:96-124`) port verbatim (signature retype only).

### 1.3 Execution model: replica-keyed Configuration + additive ranked version store

```lean
abbrev Version : Type := Nat   -- a version id IS its allocation rank (Design 2)

structure Configuration (D : ConditionedMRDTSig) where
  -- replica-keyed core: VERBATIM from CRDT_TS.lean:39-75 (retyped over ConditionedMRDTSig)
  N : Replica → Option D.State
  L : Replica → Option (Set (Op D.AppOp))
  vis : Op D.AppOp → Op D.AppOp → Prop
  -- dom_eq, vis_src, vis_tgt, vis_causal, timestamps_distinct, vis_total_same_replica : ported

  -- ADDITIVE ranked version store (the only new structural content) ----------------
  ver     : Version → Option (D.State × Set (Op D.AppOp))  -- version ↦ (state, event-set)
  head    : Replica → Option Version                       -- replica ↦ its head version id
  parents : Version → List Version                         -- the version DAG (G)
  parents_lt   : ∀ v p, p ∈ parents v → p < v              -- acyclicity ⊕ generation clock
  ver_init     : ver 0 = some (D.init, ∅)
  head_coherent : ∀ r v, head r = some v →
                    (ver v).map Prod.fst = C.N r ∧ (ver v).map Prod.snd = C.L r
  ver_inv      : ∀ v s e, ver v = some (s, e) → D.Inv s        -- commutesOn can fire anywhere
  lca_events   : ∀ {v₁ v₂ v⊤ s₁ e₁ s₂ e₂ s⊤ e⊤},             -- Lemma LCA / N10 (lin.tex:160)
      IsLCA parents v₁ v₂ v⊤ →
      ver v₁ = some (s₁,e₁) → ver v₂ = some (s₂,e₂) → ver v⊤ = some (s⊤,e⊤) →
      e⊤ = e₁ ∩ e₂

def Configuration.lcaState (C : Configuration D) (v₁ v₂ : Version) : Option D.State :=
  -- read l from the registered LCA version
  ...

/-- LCA = greatest common ancestor in the DAG; parents_lt ⇒ Reaches well-founded. -/
def Reaches (parents : Version → List Version) : Version → Version → Prop :=
  Relation.ReflTransGen (fun a b => a ∈ parents b)
def IsLCA (parents) (v₁ v₂ v⊤ : Version) : Prop :=
  Reaches parents v⊤ v₁ ∧ Reaches parents v⊤ v₂ ∧
  ∀ w, Reaches parents w v₁ → Reaches parents w v₂ → Reaches parents w v⊤
```

**Why replica-keyed core + additive store (not re-keyed):** `IsRALinearizable`
(`RA_Linearizability.lean:113`) quantifies over replicas (`C.N r`), and the proved bridge
cases `initConfig_RA_lin`/`RA_lin_preserved_createReplica`/`lo_shrink_under_apply`/
`RA_lin_preserved_apply` (`:543,564,601,629`) reference `C.N r`/`updateRep` at specific
replicas. Keeping the core replica-keyed makes those four cases port with verbatim proof
bodies (the reuse 9). The ranked store is read **only** by `Step.merge` and the
conditioning layer, so it never perturbs the reused cases.

### 1.4 `Step.merge` (the one ternary-ifying rule)

```lean
| merge {C : Configuration D} {r₁ r₂ : Replica}
    {v₁ v₂ v⊤ vm : Version} {l s₁ s₂ : D.State} {ev₁ ev₂ e⊤ : Set (Op D.AppOp)}
    (h_h₁ : C.head r₁ = some v₁) (h_h₂ : C.head r₂ = some v₂)
    (h_s₁ : C.N r₁ = some s₁)   (h_s₂ : C.N r₂ = some s₂)
    (h_ev₁ : C.L r₁ = some ev₁) (h_ev₂ : C.L r₂ = some ev₂)
    (h_lca : IsLCA C.parents v₁ v₂ v⊤)            -- LCA supplied + PROVED, first-class
    (h_l  : C.ver v⊤ = some (l, e⊤))              -- LCA STATE l (absent in binary)
    (h_fresh : C.ver vm = none) (h_alloc : v₁ < vm ∧ v₂ < vm)  -- monotone allocation
    (C' : Configuration D)
    (hN  : C'.N    = updateRep C.N r₁ (D.mergeL l s₁ s₂))
    (hL  : C'.L    = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hHd : C'.head = updateRep C.head r₁ vm)
    (hVer: C'.ver  = fun v => if v = vm then some (D.mergeL l s₁ s₂, ev₁ ∪ ev₂) else C.ver v)
    (hPar: C'.parents = fun v => if v = vm then [v₁, v₂] else C.parents v)
    (hvis: C'.vis  = C.vis) :
    Step D C (.merge r₁ r₂) C'
```

`createReplica` allocates a fresh-max version copying `(init, ∅)`/the parent;
`apply` allocates a fresh-max child version `(update s e, ev ∪ {e})` with one parent
**and carries the generation-time hypothesis** `h_app : D.applicable (t,r,o) s` (the only
new `apply` premise — the conditioning hook); `query` unchanged. The binary
`CRDT_TS.Step.merge` (`CRDT_TS.lean:122`) is recovered as the slice where `v⊤ = 0`
(`l = init`), via `merge_init_slice`.

### 1.5 Carving: re-anchor `ev_top` to the LCA event set; lex measure (no `Finset`)

```lean
-- Reuse: L_a / L_b / L_b_at already take `ev_top` as a PARAMETER (Merge_Linearization.lean:93,103,254).
-- Re-anchor:  ev_top := e⊤  (the LCA's event set), supplied by `lca_events`.
-- CAVEAT (judge-verified): L_top hardcodes ev₁∩ev₂ (Merge_Linearization.lean:77) and
--   L_top_a/L_top_b hardcode the intersection (:203-216) — re-anchoring there is a
--   REWRITE via `lca_events : e⊤ = ev₁∩ev₂`, not literally verbatim.

/-- Opaque carving record — the MergeCarving FIREWALL (Designs 2/3): the triple-nested
    induction runs against this, never seeing parents/IsLCA/ver, so grind keeps its
    proved binary shape. -/
structure MergeCarving (D : ConditionedMRDTSig) (C : Configuration D)
    (l : D.State) (e⊤ ev₁ ev₂ : Set (Op D.AppOp)) : Prop where
  top_eq : e⊤ = ev₁ ∩ ev₂                 -- from C.lca_events
  -- derived buckets L₁ᵃ L₂ᵃ L₁ᵇ L₂ᵇ L_⊤ᵃ L_⊤ᵇ, Mᵢᵃ := L_b_at … (all from L_a/L_b/L_b_at)

/-- Triple-nested induction (N6, appendix.tex:285-368) as well-founded lex recursion.
    Measure on `Set.ncard` / witness-list length — NOT Finset.card. -/
def mergeMeasure (cv : MergeCarving D C l e⊤ ev₁ ev₂) : Nat ×ₗ Nat ×ₗ Nat :=
  ( (L₁ᵃ ∪ L₂ᵃ).ncard ,   -- outer        appendix.tex:288/367
    (L_⊤ᵃ).ncard ,         -- inner        appendix.tex:295/298
    (M₁ᵃ ∪ M₂ᵃ).ncard )    -- inner-inner  appendix.tex:315/322/342
```

### 1.6 VCs: `SatisfiesVCsT` (ternary, `l` first-class) + the reuse contract

```lean
structure SatisfiesVCsT (D : ConditionedMRDTSig) : Prop where
  -- side conditions + cond-comm, over commutesOn (port of RA_Linearizability.lean:152-192,463):
  rc_non_comm rc_non_comm_directional no_rc_chain cond_comm_base cond_comm_lift : …
  -- merge axioms, genuinely ternary:
  merge_comm_T : ∀ l a b, D.mergeL l a b = D.mergeL l b a          -- merge(l,a,b)=merge(l,b,a)
  merge_idem_T : ∀ a,     D.mergeL a a a = a                       -- merge(a,a,a)=a
  merge_bot_T  : ∀ l b,   D.mergeL l l b = b                       -- lattice bottom
  -- BottomUp family with l first-class + Inv/applicable guards (feasible-state restriction):
  bottomUp_0op : ∀ l a b e⊤, D.Inv l → D.Inv a → D.Inv b →
      D.applicable e⊤ l → D.applicable e⊤ a → D.applicable e⊤ b →
      D.mergeL (D.update l e⊤) (D.update a e⊤) (D.update b e⊤) = D.update (D.mergeL l a b) e⊤
  bottomUp_2op : ∀ l a b e₁ e₂, e₁ ≠ e₂ →
      (D.rc e₁ e₂ = RcRes.Fst_then_snd ∨ D.commutesOn e₁ e₂) →   -- ⚑4 over commutesOn
      D.Inv l → D.Inv a → D.Inv b → D.applicable e₁ a → D.applicable e₂ b →
      D.mergeL l (D.update a e₁) (D.update b e₂) = D.update (D.mergeL l (D.update a e₁) b) e₂
  -- … bottomUp_1op + the 19-field ψ* expansion (Group 3/4/5) re-typed with l, plus ternary
  --   analogues of the 5 extras (merge_init↦merge_bot_T, rc_non_comm_directional,
  --   cond_comm_lift, merge_peel_comm, shared_peel_1op) over commutesOn.

/-- THE reuse linchpin: instantiate every *_T field at l := init, rewrite through
    merge_init_slice, recover the binary 29-field bundle so the EXISTING binary bridge
    (Merge_Linearization.lean:4390) runs unchanged on the init-LCA sub-family. -/
theorem satisfiesVCs_of_T (h : SatisfiesVCsT D) : Sal.Emulation.SatisfiesVCs D.toCRDTSig
```

`ind_lca_2op`/`ind_lca_1op` (`RA_Linearizability.lean:211,342`) **already** quantify an
LCA-like `l : State`; they retype to ternary by `merge ↦ mergeL l` with no structural
change — the smallest-delta seeds, written first.

### 1.7 Conditioning carrier `ReachInv`, headline, merge-existence

```lean
/-- Generation-time package.  merge_preserves is deliberately NOT
    `∀ l a b, Inv l→Inv a→Inv b→Inv (mergeL l a b)` — that is machine-checked FALSE
    (merge_breaks_wf, RGA_Reachability_Invariant.lean:209).  It takes the generation-time
    side-condition `AllocMono` hosted on the ranked DAG. -/
structure ReachInv (D : ConditionedMRDTSig) : Prop where
  init_inv     : D.Inv D.init
  do_preserves : ∀ s o, D.Inv s → D.applicable o s → D.Inv (D.update s o)
  merge_preserves :
    ∀ (C : Configuration D) (v⊤ v₁ v₂ : Version) {l a b e⊤ e₁ e₂},
      C.AllocMono →                                   -- GENERATION-TIME (id_mono, RGA:227)
      IsLCA C.parents v₁ v₂ v⊤ →
      C.ver v⊤ = some (l,e⊤) → C.ver v₁ = some (a,e₁) → C.ver v₂ = some (b,e₂) →
      D.Inv l → D.Inv a → D.Inv b → D.Inv (D.mergeL l a b)
  events_applicable :                                 -- the carrier, proved per-RDT
    ∀ C, (labeledTS D).ReachableFrom (initConfig D) C →
      ∀ e, e ∈ C.events → ∃ v s eset, C.ver v = some (s,eset) ∧ D.Inv s ∧ D.applicable e s

theorem ra_linearizable_of_vcs_T
    (D : ConditionedMRDTSig) (hVC : SatisfiesVCsT D) (hR : ReachInv D)
    (C : Configuration D) (hC : (labeledTS D).ReachableFrom (initConfig D) C) :
    IsRALinearizable C

theorem merge_linearization_exists_T
    (D) (hVC : SatisfiesVCsT D) (hR : ReachInv D) (C : Configuration D)
    {l a b : D.State} {v⊤ v₁ v₂ : Version} (h_lca : IsLCA C.parents v₁ v₂ v⊤)
    {ev₁ ev₂ e⊤ : Set (Op D.AppOp)} (cv : MergeCarving D C l e⊤ ev₁ ev₂)
    (π₁) (hπ₁ : listPermOf π₁ ev₁ ∧ respects π₁ (lo D C) ∧ applySeq D D.init π₁ = a)
    (π₂) (hπ₂ : listPermOf π₂ ev₂ ∧ respects π₂ (lo D C) ∧ applySeq D D.init π₂ = b) :
    ∃ π, listPermOf π (ev₁ ∪ ev₂) ∧ respects π (lo D C) ∧ applySeq D D.init π = D.mergeL l a b
```

`AllocMono : Configuration D → Prop` is the per-RDT generation-time hook (for RGA:
`∀ v t s e, ver v = some (s,e) → contains s t → anc s t = 0 ∨ anc s t < t`,
`RGA_Reachability_Invariant.lean:227`), established at `apply` (fresh-max id) and
maintained across `merge` (`vm > v₁,v₂`). For flat RDTs `AllocMono := fun _ => True`.

---

## 2. Reuse-vs-new map (`l := init` slice)

### Reuses VERBATIM from `Sal/Emulation` (no merge-arity dependence)

- **Generic layer:** `Labeled_TS.lean` (`LabeledTS`, `ReachableFrom`), all of
  `Weak_Simulation.lean` (`weakSim_sound`).
- **RA-lin defs + non-merge bridge cases:** `applySeq`, `listPermOf`, `respects`,
  `IsRALinearizable`, `IsRALinearizableExec` (`RA_Linearizability.lean:96-124`);
  `initConfig_RA_lin` (`:543`), `RA_lin_preserved_createReplica` (`:564`),
  `lo_shrink_under_apply` (`:601`), `RA_lin_preserved_apply` (`:629`) — replica-keyed,
  port with verbatim proof bodies (the reuse-9 dividend of keeping the core replica-keyed).
- **Convergence machinery:** `applySeq_swap_*`, `convergence` (`:609`), `cond_comm_lift`,
  `cond_comm_base`, `no_rc_chain` — pure `update`/`rc`/`lo` reasoning; reused with
  `commutes → commutesOn`.
- **Carving lemmas parameterized on `ev_top`:** `L_a`/`L_b`/`L_b_at` and their
  union/disjoint/subset/closure lemmas (`Merge_Linearization.lean:93,103,254` and
  `:111-291`) — reused by instantiating `ev_top := e⊤`.

### Slices in as the `l := init` instance (smallest delta)

- `ind_lca_2op`/`ind_lca_1op` (`RA_Linearizability.lean:211,342`) — already `∀ l : State`.
- `base_2op`/`bottomUp_2op_reachable` (`Merge_Linearization.lean:1008`) — the `l:=init`
  specialisations; the shared-event peel path `lem_0op`/`shared_peel_1op`/`merge_peel_shared`
  (`:439,532,1989`) is the binary proof's closest approach to a real LCA and seeds the
  ternary inner LCA-induction.
- The whole binary bridge `ra_linearizable_of_vcs` (`:4390`) runs on the init-LCA
  sub-family via `satisfiesVCs_of_T` (regression oracle).
- `Instances/Grow_Only_Set.lean` (29 fields closed): `Inv/applicable := True`,
  `mergeL l a b := a ∪ b`, `merge_init_slice` by `∅ ∪ x = x`.

### Built NEW (no binary analogue)

1. `MRDTSig`/`ConditionedMRDTSig` + `commutesOn` (`§1.1`).
2. The **ranked version store** `ver`/`head`/`parents`/`parents_lt` and its 4 coherence
   invariants `ver_init`/`head_coherent`/`ver_inv`/`lca_events` (`§1.3`) — the structural
   home for both the honest N10 and the generation-time invariant.
3. `IsLCA`/`Reaches` and the ternary `Step.merge` with LCA lookup (`§1.4`); the `apply`
   rule's `h_app` premise.
4. `MergeCarving` firewall + lex `mergeMeasure` (`§1.5`); the ternary BottomUp/`ψ*`
   re-statement `SatisfiesVCsT` + `satisfiesVCs_of_T` (`§1.6`).
5. `ReachInv` with the generation-time `merge_preserves`/`AllocMono`/`events_applicable`
   and the headline `ra_linearizable_of_vcs_T` (`§1.7`).

### Re-state, do NOT re-prove from scratch (mechanical retypes)

- `Configuration` invariants `dom_eq`/`vis_*`/`timestamps_distinct`/`vis_total_same_replica`
  (`CRDT_TS.lean:44-75`) — retyped over `ConditionedMRDTSig`, proof bodies unchanged.
- `initConfig`/`labeledTS` (`CRDT_TS.lean:147-175`) — add `ver 0`/`head`/`parents`
  discharge (trivial).

---

## 3. How the conditioning is carried (the research crux)

Conditioning is split exactly as the machine-checked RGA finding dictates
(`RGA_Reachability_Invariant.lean:21-26,209,227`):

- **State-shape `Inv`** (e.g. `RgaInv s := contains s 0 = false ∧ wf s`,
  `RGA_Reachability_Invariant.lean:57`) — inductive under `do_` (proved sorry-free:
  `Inv_init`/`Inv_doIns`/`Inv_doDel`, `:62,73,131`), carried by `ReachInv.init_inv`/
  `do_preserves`/`merge_preserves`.
- **Generation-time `applicable`** (e.g. `accurate ∧ fresh_ts ∧ id-monotone anchor`) —
  a property of *how the state was produced*, **not** of its shape, so it lives outside
  `Inv`. It enters at the `apply` rule (`h_app`) and is propagated by
  `ReachInv.events_applicable`.

Every ⚑ commutation site of the proof skeleton moves `commutes → commutesOn` and
discharges its `Inv`/`applicable` side-conditions from `ReachInv` — because every state
fed to `update`/`mergeL` inside the induction is a registered version (`ver_inv ⇒ Inv`).

The **id-monotone allocation** invariant is the part with no binary analogue and is why
the ranked store exists. `merge_breaks_wf` (`:209`) proves `wf` is *not* merge-inductive
from `Inv l/a/b` alone (`climb`'s fuel suffices only when anchor ids strictly decrease).
So `ReachInv.merge_preserves` takes `AllocMono` — `∀ v t s e, ver v = some (s,e) →
contains s t → anc s t = 0 ∨ anc s t < t` (`:227`) — as a generation-time premise.
`AllocMono` is **statable** precisely because `Version := Nat` is the allocation rank and
`parents_lt` orders versions: it is established at `apply` (fresh-max id > all anchor ids
in the head) and maintained across `merge` (`h_alloc : v₁,v₂ < vm`). The two danger sites
where commutation fires at a *merged* state — ⚑2 (convergence) and ⚑4 (BottomUp-2-OP) —
consume `AllocMono` here. Flat RDTs set `AllocMono := True`, collapsing everything to the
binary framework.

---

## 4. Sequenced Phase-0 steps (each with an exit criterion)

Ordered so the reuse-maximal foundation lands first and the research crux is reached
without a long correctness tail. **The 6 binary sorries
(`Merge_Linearization.lean:2681,2852,2868,2874,4308,4311`) are explicitly deferred** —
they are the binary distinct-last carving tail and are *sidestepped*, not inherited, by
the lex-measure peel-from-`L^a` recursion (Step 6).

**S1 — Signature + slice contract.** Define `MRDTSig extends CRDTSig`, `mergeL`,
`merge_init_slice`; `ConditionedMRDTSig`, `commutesOn`, ternary `lo`.
*Exit:* file compiles; `commutesOn`/`lo` reduce to `CRDTSig.commutes`/binary `lo` by `rfl`
under `Inv/applicable := True`; G-Set instance supplies `mergeL`/`merge_init_slice`.

**S2 — Configuration + ranked store + retyped invariants.** Add `ver`/`head`/`parents`/
`parents_lt` and the 6 ported core invariants + 4 store-coherence invariants; define
`Reaches`/`IsLCA`; discharge `initConfig`/`labeledTS`.
*Exit:* `Configuration`/`initConfig` compile with all invariants discharged; `Reaches`
shown well-founded from `parents_lt`.

**S3 — Step rules + non-merge bridge reuse.** Port `createReplica`/`apply`(+`h_app`)/
`query`/`merge` (`§1.4`); re-establish `initConfig_RA_lin`, `RA_lin_preserved_createReplica`,
`lo_shrink_under_apply`, `RA_lin_preserved_apply` over the new `Configuration`.
*Exit:* the four non-merge bridge cases compile with proof bodies unchanged modulo the
`Configuration` retype; `induction hReach` skeleton of `ra_linearizable_of_vcs_T` type-checks
with the merge case `sorry`.

**S4 — `SatisfiesVCsT` + `satisfiesVCs_of_T` (the reuse oracle).** Write the 29 ternary
fields (start with `ind_lca_*` — smallest delta); prove `satisfiesVCs_of_T`; honestly
bridge the 2 non-slicing merge axioms (`merge_idem`/`merge_init` from
`merge_idem_T`/`merge_bot_T` + `merge_init_slice`).
*Exit:* `satisfiesVCs_of_T : SatisfiesVCsT D → SatisfiesVCs D.toCRDTSig` closed; the binary
bridge `ra_linearizable_of_vcs` runs on the init-LCA sub-family (regression: G-Set still
linearizable through the ternary path).

**S5 — Conditioning carrier + RGA instantiation.** Define `ReachInv`/`AllocMono`;
instantiate `Inv := RgaInv`, `applicable := accurate ∧ fresh_ts ∧ id_mono`,
`AllocMono` for tombstone-free RGA, reusing `Inv_init`/`Inv_doIns`/`Inv_doDel`
(`RGA_Reachability_Invariant.lean:62,73,131`); prove `AllocMono` inductive on the execution
and `merge_preserves` from it (closing the `merge_breaks_wf` gap with the id-monotone
premise).
*Exit:* `ReachInv (RGA)` holds with `merge_preserves` discharged **using `AllocMono`**
(the `Inv_merge` `sorry` at `:238` closed under the generation-time hypothesis); `events_applicable`
proved by execution induction. **This is the Phase-0 research deliverable** — it answers
"can the generation-time id-monotonicity be carried as a reachable-execution invariant?".
**✅ DONE — the answer is yes.** `Inv_merge` is closed under the single premise
`id_mono l`; `id_mono` is a reachable invariant under `mono_alloc` (`id_mono_init` /
`id_mono_doIns` / `id_mono_doDel` / `id_mono_merge`), all kernel-clean. Sharpening: the
cross-branch compatibility budgeted here is **derivable from `wf`** — `id_mono l` is the
sole generation-time premise the RGA merge needs.

**S6 — Ternary merge case (carving + lex recursion).** Build `MergeCarving` (re-anchor
`ev_top := e⊤` via `lca_events`), `mergeMeasure`, and `merge_linearization_exists_T` as
well-founded lex recursion peeling from `L^a` (the paper's route that avoids re-permutation);
discharge ⚑ sites from `ReachInv`. Close the headline merge case.
*Exit:* `ra_linearizable_of_vcs_T` closed for the flat-RDT family (G-Set end-to-end) and
for RGA modulo any residual `ψ*` leaf VCs; **no** import of the 6 deferred binary sorries.

**Dependency order:** S1→S2→S3 (foundation, reuse-maximal); S4 in parallel after S1;
S5 after S2 (needs the store); S6 last (needs S4 VCs + S5 conditioning). S5 is the
research gate — if `AllocMono` is not a maintainable invariant, the conditioning design is
re-opened *before* the S6 grind, exactly per research-first guidance.

---

## 5. Open risks carried forward

- ~~**S5 is the genuine research risk**~~ **— RESOLVED (machine-checked).**
  `merge_preserves`/`AllocMono` is both provable and a reachable-execution invariant:
  `Inv_merge` (`:238`) is closed under `id_mono l`, and `id_mono` is inductive under
  `init` / `do_` (`mono_alloc`) / `merge`. The conditioning design is validated, so
  Phase-0 proceeds to S1/S6 without re-opening it.
- **`lca_events` as a maintained invariant** (not yet derived from unique-generator
  well-foundedness, `appendix.tex:6-37`) must be correctly maintained by `Step.merge`;
  schedule a standalone proof post-Phase-0.
- **`commutesOn` adds 3 premises** to every commute fact threaded through
  convergence/`cond_comm`/`lo`; mitigate by definitional collapse on flat RDTs and a single
  `ReachInv`-backed discharge lemma per ⚑ site (keep the commute fact syntactically binary
  inside the recursion).
- **Scope v1 (BLUEPRINT decision 3, `lin.tex:197`):** `IsLCA` demands a unique greatest
  common ancestor; potential-LCA / multi-LCA executions are excluded by a `Step.merge` side
  condition and deferred. Honest caveat: this makes the mechanised theorem weaker than
  Neem Thm 2 as stated until lifted.
- **Ternary VC count > 29:** the 5 binary extras likely need ternary analogues plus
  possibly new ones forced by non-trivial `l`; `SatisfiesVCsT` is not yet a closed field set.
