import Sal.ConditionedMRDTs.Metatheory.ArbAdequacy

/-!
# Fully-generic arbitration adequacy (task #119, half B-full; the rc-free recast #123)

The falsifiable tail named by `Metatheory/ArbAdequacy.lean` (§4, FINDING) and
`Metatheory/Arbitration_Refactor.lean` (phase-3b "no obstruction" claim): the
adequacy chain re-threaded over the **abstract** acyclic *antitone* arbitration,
with the fold pinned by `ArbConvergence` and `loOn` **absent** even as the fold
oracle. Compare `isRALinearizable3Arb_of_acyclicArb_refines_loOn` (ArbAdequacy §3),
which reuses `loOn` convergence and asks `arb` only to refine `loOn`; here the
order **and** the fold uniqueness are both the abstract `arb`.

## What lands here (kernel-clean; `#print axioms` at the foot)

* **§1 arb-canonical support**: `isCanonicalStateArb_empty`,
  `downset_max_arb` (an `arb`-maximal-in-its-own-downset fact from **acyclicity +
  extends-`vis`**, not `loOn`), `closure_diff_of_max_arb` (from **extends-`vis`**).
  These re-derive over the abstract `arb` the three `loOn`-flavoured facts the
  Join induction consumes about the linearization order beyond the three
  ArbAdequacy pillars.

* **§2 the arb-form VCs**: `CDVC3Arb`, `FeasibleDeltaVCs3Arb` — the ternary CD
  equation and the feasible delta contract with their `loOn`-maximality premise
  **re-keyed** to `arb`-maximality (`∀ x ∈ U, x ≠ e → ¬ arb U e x`). At `arb :=
  loOn (core C)` these are definitionally the published `CDVC3` /
  `FeasibleDeltaVCs3` at that configuration (`IsCanonicalStateArb C (loOn (core C))
  = IsCanonicalState (core C)` definitionally).

* **§3 the generic Join Lemma** `join_lemma3AtArb_of_cd_feasible`: from
  `CoreVCs3CD + AcyclicArbitration + antitone + ArbConvergence + CDVC3Arb +
  FeasibleDeltaVCs3Arb`, a ternary merge of `arb`-canonical sides at their `arb`-
  canonical LCA is the `arb`-canonical state of the union — the ~340-line
  `join_lemma3_of_cd_feasible` re-threaded verbatim over `IsCanonicalStateArb`,
  consuming the ArbAdequacy pillars (`isCanonicalStateArb_exists/_unique/_snoc`)
  and the §1 facts in place of the `loOn` machinery. **This is the MERGE case of
  the fully-generic transition induction, discharged loOn-free.**

## FINDING (the apply-case obstruction, refining the ArbAdequacy §3 FINDING)

ArbAdequacy §3 named the fully-generic engine's residue as "(i) the antitone
clause + (ii) a re-thread of the Join Lemma and the `GoodConfig3` transition
induction". Mechanizing the re-thread here closes (i) and the **merge** half of
(ii). The **apply** half of (ii) is *not* a pure re-thread: it needs a fourth
arbitration clause the ArbAdequacy dichotomy omitted.

The apply step re-attaches a causally-latest fresh event `e` (it observes all of
the parent set `E`) and must place it *last* in the witness, i.e. `e` must be
`arb`-maximal in `insert e E`. For `loOn` this is automatic (`isCanonicalState_
extend`): a `loOn`-edge `e → x` needs either `vis e x` (false, `e` is latest) or
concurrency `¬vis x e` (false, `e` observed `x`). For a **general** `arb` it is
NOT derivable from acyclicity + extends-`vis` + antitone + convergence: those
constrain only *non-commuting* pairs (via extends-`vis`), so an `arb` that orders
`e` **before** a *commuting* old event `x` stays acyclic, antitone, and convergent
yet breaks `e`'s maximality. The missing clause is **vis-consistency**:

> `∀ E {a b}, a ∈ E → b ∈ E → C.vis b a → ¬ arb E a b`
> (`arb` never orders `a` before an event `b` that `a` observed).

Both target instances satisfy it — `loOn` because both its arms are vacuous on an
observed pair, `lwwArb` because the timestamp order respects causality — but it is
independent of the stated bundle and is the precise obligation the `goodConfig3_
apply` re-thread requires. It is recorded here (`VisConsistentArbitration`,
`arb_extend_of_visConsistent`) so the transition-induction continuation
(`GoodConfig3Arb` via reachability, the remaining #119B-full tail) has an exact
contract; the merge case it depends on is already discharged below.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

variable {D : ConditionedMRDTSig}

/-! ## §1. Arb-canonical support lemmas (re-derived over the abstract `arb`) -/

/-- The empty set's `arb`-canonical state is `init` (mirror of
`isCanonicalState_empty`; order-independent). -/
theorem isCanonicalStateArb_empty {C : Configuration D}
    {arb : Set (Op D.AppOp) → Op D.AppOp → Op D.AppOp → Prop}
    {ev : Set (Op D.AppOp)} {s : D.State}
    (h_empty : ev = ∅) (h : IsCanonicalStateArb C arb ev s) : s = D.init := by
  obtain ⟨ρ, hp, _, hf⟩ := h
  subst h_empty
  match ρ, hp with
  | [], _ => rw [← hf]; rfl
  | x :: _, hp => exact absurd ((hp.2 x).mp List.mem_cons_self) id

/-- **`e` is `arb`-maximal in its own downset** — the abstract
`downset_max`, from **acyclicity + extends-`vis`** (no `loOn`). An out-edge
`arb(↓e) e x` closes an `arb`-cycle: the `vis`-noncomm chain `x → … → e` is an
`arb`-chain by extends-`vis`, and the out-edge closes it. -/
theorem downset_max_arb {C : Configuration D} (arb : AcyclicArbitration C)
    (h_ir : ∀ a : Op D.AppOp, ¬ C.vis a a) {e : Op D.AppOp}
    (h_ds_in : ∀ a ∈ downset (Configuration.core C) e, a ∈ C.events) :
    ∀ x ∈ downset (Configuration.core C) e, x ≠ e →
      ¬ arb.arb (downset (Configuration.core C) e) e x := by
  intro x hx hne h_arb
  -- every `vis`-noncomm chain into `e` inside `↓e` is an `arb(↓e)` chain
  have key : ∀ y z, Relation.TransGen (visNC (Configuration.core C)) y z →
      z ∈ downset (Configuration.core C) e →
      Relation.TransGen (arbNe (downset (Configuration.core C) e) arb.arb) y z := by
    intro y z hyz
    induction hyz with
    | single h =>
      intro hz
      have hyd : y ∈ downset (Configuration.core C) e :=
        downset_closed y _ h.1 h.2 hz
      have hyne : y ≠ _ := fun heq => h_ir _ (heq ▸ h.1)
      exact Relation.TransGen.single
        ⟨hyne, hyd, hz, arb.extends_vis _ hyd hz h.1 h.2⟩
    | tail _ h2 ih =>
      rename_i b z' _
      intro hz
      have hbd : b ∈ downset (Configuration.core C) e :=
        downset_closed b z' h2.1 h2.2 hz
      have hbne : b ≠ z' := fun heq => h_ir z' (heq ▸ h2.1)
      exact (ih hbd).tail ⟨hbne, hbd, hz, arb.extends_vis _ hbd hz h2.1 h2.2⟩
  have hxchain : Relation.TransGen (visNC (Configuration.core C)) x e := by
    rcases hx with rfl | h
    · exact absurd rfl hne
    · exact h
  have hxarb := key x e hxchain self_mem_downset
  have hedge : arbNe (downset (Configuration.core C) e) arb.arb e x :=
    ⟨fun heq => hne heq.symm, self_mem_downset, hx, h_arb⟩
  exact arb.acyclic (downset (Configuration.core C) e) h_ds_in e
    (Relation.TransGen.trans (Relation.TransGen.single hedge) hxarb)

/-- Backward closure survives removing an `arb`-maximal event (abstract
`closure_diff_of_max`): a `vis`-noncomm out-edge from the maximal `e` is an
`arb`-edge by extends-`vis`, contradicting maximality. -/
theorem closure_diff_of_max_arb {C : Configuration D} (arb : AcyclicArbitration C)
    {ev evU : Set (Op D.AppOp)} {e : Op D.AppOp}
    (h_e_evU : e ∈ evU) (h_sub : ev ⊆ evU)
    (h_closed : ∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev → a ∈ ev)
    (h_max : ∀ x ∈ evU, x ≠ e → ¬ arb.arb evU e x) :
    ∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b →
      b ∈ ev \ {e} → a ∈ ev \ {e} := by
  rintro a b hv hnc ⟨hb, hb_ne⟩
  refine ⟨h_closed a b hv hnc hb, ?_⟩
  intro ha_eq
  have ha_eq' : a = e := ha_eq
  subst ha_eq'
  exact h_max b (h_sub hb) hb_ne (arb.extends_vis evU h_e_evU (h_sub hb) hv hnc)

/-! ## §2. The arb-form VCs (loOn-maximality re-keyed to arb-maximality) -/

/-- **(CD3) in arb-form.** The ternary causal-delta equation with its
`loOn(U)`-maximality premise re-keyed to `arb U`-maximality. At `arb := loOn
(core C)` this is `CDVC3` specialised to `core C` (`IsCanonicalStateArb C (loOn
(core C)) = IsCanonicalState (core C)` definitionally). -/
def CDVC3Arb (C : Configuration D)
    (arb : Set (Op D.AppOp) → Op D.AppOp → Op D.AppOp → Prop) : Prop :=
  ∀ (U : Set (Op D.AppOp)) (A B : D.State) (e : Op D.AppOp),
    (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
    (∀ a : Op D.AppOp, ¬ C.vis a a) →
    (∀ a ∈ U, a ∈ C.events) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ U → a ∈ U) →
    e ∈ U →
    (∀ x ∈ U, x ≠ e → ¬ arb U e x) →
    IsCanonicalStateArb C arb (U \ {e}) A →
    IsCanonicalStateArb C arb (downset (Configuration.core C) e \ {e}) B →
    D.mergeL B A (D.update B e) = D.update A e

/-- **The feasible delta contract in arb-form.** The `FeasibleDeltaVCs3` fields
over `IsCanonicalStateArb`, `loOn`-maximality re-keyed to `arb`-maximality. -/
structure FeasibleDeltaVCs3Arb (C : Configuration D)
    (arb : Set (Op D.AppOp) → Op D.AppOp → Op D.AppOp → Prop) : Prop where
  feasible_init :
    ∀ (ev : Set (Op D.AppOp)) (s : D.State),
      (∀ a ∈ ev, a ∈ C.events) →
      IsCanonicalStateArb C arb ev s →
      D.mergeL D.init D.init s = s
  feasible_local_redistribute :
    ∀ (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ B t₁ s₂ : D.State) (e : Op D.AppOp),
      (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
      (∀ a : Op D.AppOp, ¬ C.vis a a) →
      (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
      (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
      (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
      e ∈ ev₁ → e ∉ ev₂ →
      (∀ x ∈ ev₁ ∪ ev₂, x ≠ e → ¬ arb (ev₁ ∪ ev₂) e x) →
      IsCanonicalStateArb C arb (ev₁ ∩ ev₂) s₀ →
      IsCanonicalStateArb C arb (downset (Configuration.core C) e \ {e}) B →
      IsCanonicalStateArb C arb (ev₁ \ {e}) t₁ →
      IsCanonicalStateArb C arb ev₂ s₂ →
      D.mergeL s₀ (D.mergeL B t₁ (D.update B e)) s₂
        = D.mergeL B (D.mergeL s₀ t₁ s₂) (D.update B e)
  feasible_redistribute :
    ∀ (ev₁ ev₂ : Set (Op D.AppOp)) (t₀ t₁ t₂ B : D.State) (e : Op D.AppOp),
      (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
      (∀ a : Op D.AppOp, ¬ C.vis a a) →
      (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
      (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
      (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
      e ∈ ev₁ → e ∈ ev₂ →
      (∀ x ∈ ev₁ ∪ ev₂, x ≠ e → ¬ arb (ev₁ ∪ ev₂) e x) →
      IsCanonicalStateArb C arb ((ev₁ ∩ ev₂) \ {e}) t₀ →
      IsCanonicalStateArb C arb (downset (Configuration.core C) e \ {e}) B →
      IsCanonicalStateArb C arb (ev₁ \ {e}) t₁ →
      IsCanonicalStateArb C arb (ev₂ \ {e}) t₂ →
      D.mergeL (D.mergeL B t₀ (D.update B e)) (D.mergeL B t₁ (D.update B e))
          (D.mergeL B t₂ (D.update B e))
        = D.mergeL B (D.mergeL t₀ t₁ t₂) (D.update B e)

/-! ## §3. The generic Join Lemma (the merge case, loOn-free) -/

/-- The ternary Join Lemma against an abstract arbitration, at a single
configuration `C` with a single arbitration `arb` — the arb-form of
`JoinLemma3At`. -/
def JoinLemma3AtArb (C : Configuration D)
    (arb : Set (Op D.AppOp) → Op D.AppOp → Op D.AppOp → Prop) : Prop :=
  ∀ (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State),
    (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
    (∀ a : Op D.AppOp, ¬ C.vis a a) →
    (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
    IsCanonicalStateArb C arb (ev₁ ∩ ev₂) s₀ →
    IsCanonicalStateArb C arb ev₁ s₁ → IsCanonicalStateArb C arb ev₂ s₂ →
    IsCanonicalStateArb C arb (ev₁ ∪ ev₂) (D.mergeL s₀ s₁ s₂)

/-- The Join Lemma at a fixed configuration and union-enumeration length
(measure package for the strong induction; arb-form of `JoinAtF`). -/
private def JoinAtArb (C : Configuration D)
    (arb : Set (Op D.AppOp) → Op D.AppOp → Op D.AppOp → Prop) (n : ℕ) : Prop :=
  ∀ (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State)
    (lU : List (Op D.AppOp)),
    listPermOf lU (ev₁ ∪ ev₂) → lU.length = n →
    (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
    IsCanonicalStateArb C arb (ev₁ ∩ ev₂) s₀ →
    IsCanonicalStateArb C arb ev₁ s₁ → IsCanonicalStateArb C arb ev₂ s₂ →
    IsCanonicalStateArb C arb (ev₁ ∪ ev₂) (D.mergeL s₀ s₁ s₂)

/-! ### Private list plumbing (copies of the Adequacy private helpers). -/

private theorem listPermOf_length_ltA {α : Type} {l l' : List α}
    {ev ev' : Set α} {x : α}
    (h : listPermOf l ev) (h' : listPermOf l' ev')
    (hsub : ev ⊆ ev') (hx : x ∈ ev') (hxn : x ∉ ev) :
    l.length < l'.length := by
  have hnd : (x :: l).Nodup := by
    rw [List.nodup_cons]
    exact ⟨fun hmem => hxn ((h.2 x).mp hmem), h.1⟩
  have hsp : List.Subperm (x :: l) l' := by
    refine List.subperm_of_subset hnd ?_
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact (h'.2 a).mpr hx
    · exact (h'.2 a).mpr (hsub ((h.2 a).mp ha'))
  have hle := hsp.length_le
  simp only [List.length_cons] at hle
  omega

private theorem exists_listPermOf_subsetA {α : Type} {l : List α}
    {T S : Set α} (h : listPermOf l T) (hsub : S ⊆ T) :
    ∃ l', listPermOf l' S := by
  classical
  refine ⟨l.filter (fun a => decide (a ∈ S)), h.1.filter _, fun a => ?_⟩
  rw [List.mem_filter]
  constructor
  · rintro ⟨_, hd⟩
    exact of_decide_eq_true hd
  · intro ha
    exact ⟨(h.2 a).mpr (hsub ha), decide_eq_true ha⟩

/-- **Side decomposition (arb-form)**, verbatim `side_decompositionF` with the
`loOn` machinery replaced by the ArbAdequacy pillars and the §1 facts. -/
private theorem side_decompositionArb {C : Configuration D}
    (arb : AcyclicArbitration C)
    (h_anti : ∀ {E' E'' : Set (Op D.AppOp)} {a b : Op D.AppOp},
       E' ⊆ E'' → arb.arb E'' a b → arb.arb E' a b)
    (hConv : ArbConvergence C arb.arb)
    (hCD : CDVC3Arb C arb.arb)
    (h_tr : ∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c)
    (h_ir : ∀ a : Op D.AppOp, ¬ C.vis a a)
    {n : ℕ} (IH : ∀ m, m < n → JoinAtArb C arb.arb m)
    {U : Set (Op D.AppOp)} {lU : List (Op D.AppOp)}
    (hpU : listPermOf lU U) (hlen : lU.length = n)
    (h_inU : ∀ a ∈ U, a ∈ C.events)
    (h_clU : ∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ U → a ∈ U)
    {e : Op D.AppOp} (h_e : e ∈ U)
    (h_max : ∀ x ∈ U, x ≠ e → ¬ arb.arb U e x)
    {A B : D.State}
    (hA : IsCanonicalStateArb C arb.arb (U \ {e}) A)
    (hB : IsCanonicalStateArb C arb.arb
      (downset (Configuration.core C) e \ {e}) B)
    {E : Set (Op D.AppOp)} {s t : D.State}
    (h_subE : E ⊆ U)
    (h_inE : ∀ a ∈ E, a ∈ C.events)
    (h_clE : ∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ E → a ∈ E)
    (h_eE : e ∈ E)
    (hs : IsCanonicalStateArb C arb.arb E s)
    (ht : IsCanonicalStateArb C arb.arb (E \ {e}) t) :
    s = D.mergeL B t (D.update B e) := by
  classical
  have h_dsU : downset (Configuration.core C) e ⊆ U := downset_subset h_clU h_e
  have h_ds_in : ∀ a ∈ downset (Configuration.core C) e, a ∈ C.events :=
    fun a ha => h_inU a (h_dsU ha)
  have hT : IsCanonicalStateArb C arb.arb (downset (Configuration.core C) e)
      (D.update B e) :=
    isCanonicalStateArb_snoc h_anti self_mem_downset
      (downset_max_arb arb h_ir h_ds_in) hB
  by_cases hEU : E = U
  · subst hEU
    have h_eq : D.mergeL B A (D.update B e) = D.update A e :=
      hCD E A B e h_tr h_ir h_inE h_clE h_eE h_max hA hB
    have htA : t = A :=
      isCanonicalStateArb_unique hConv (fun a ha => h_inE a ha.1) ht hA
    have hsA : s = D.update A e :=
      isCanonicalStateArb_unique hConv h_inE hs
        (isCanonicalStateArb_snoc h_anti h_eE h_max hA)
    rw [htA, h_eq]
    exact hsA
  · obtain ⟨lE, hpE, -, -⟩ := id hs
    obtain ⟨x, hxU, hxE⟩ : ∃ x ∈ U, x ∉ E := by
      by_contra h
      push_neg at h
      exact hEU (Set.Subset.antisymm h_subE h)
    have hlt : lE.length < n := by
      rw [← hlen]
      exact listPermOf_length_ltA hpE hpU h_subE hxU hxE
    have h_dsubE : downset (Configuration.core C) e ⊆ E :=
      downset_subset h_clE h_eE
    have hsetI : (E \ {e}) ∩ downset (Configuration.core C) e
        = downset (Configuration.core C) e \ {e} := by
      ext y
      constructor
      · rintro ⟨⟨_, hyne⟩, hyd⟩
        exact ⟨hyd, hyne⟩
      · rintro ⟨hyd, hyne⟩
        exact ⟨⟨h_dsubE hyd, hyne⟩, hyd⟩
    have hsetE : (E \ {e}) ∪ downset (Configuration.core C) e = E := by
      ext y
      constructor
      · rintro (hy | hy)
        · exact hy.1
        · exact h_dsubE hy
      · intro hy
        by_cases hye : y = e
        · subst hye
          exact Or.inr self_mem_downset
        · exact Or.inl ⟨hy, hye⟩
    have hB' : IsCanonicalStateArb C arb.arb
        ((E \ {e}) ∩ downset (Configuration.core C) e) B := by
      rw [hsetI]
      exact hB
    have h_merge_can : IsCanonicalStateArb C arb.arb
        ((E \ {e}) ∪ downset (Configuration.core C) e)
        (D.mergeL B t (D.update B e)) := by
      refine IH lE.length hlt _ _ B t (D.update B e) lE ?_ rfl
        (fun a ha => h_inE a ha.1)
        (fun a ha => h_inE a (h_dsubE ha))
        (closure_diff_of_max_arb arb h_e h_subE h_clE h_max)
        (downset_closed (C := Configuration.core C) (e := e)) hB' ht hT
      rw [hsetE]
      exact hpE
    have h_merge_can' : IsCanonicalStateArb C arb.arb E
        (D.mergeL B t (D.update B e)) := by
      rw [← hsetE]
      exact h_merge_can
    exact isCanonicalStateArb_unique hConv h_inE hs h_merge_can'

/-- **The generic ternary Join Lemma** — the ~340-line `join_lemma3_of_cd_
feasible` re-threaded over `IsCanonicalStateArb`, `loOn` absent throughout.
Existence is `isCanonicalStateArb_exists` (acyclicity), the maximal event is
`exists_maximal_of_acyclic` (acyclicity), fold-uniqueness is
`isCanonicalStateArb_unique` (`ArbConvergence`), re-attach is
`isCanonicalStateArb_snoc` (antitone), and the CD/feasible equations are the
arb-form VCs. -/
theorem join_lemma3AtArb_of_cd_feasible {C : Configuration D}
    (hMC : ∀ l a b : D.State, D.mergeL l a b = D.mergeL l b a)
    (arb : AcyclicArbitration C)
    (h_anti : ∀ {E' E'' : Set (Op D.AppOp)} {a b : Op D.AppOp},
       E' ⊆ E'' → arb.arb E'' a b → arb.arb E' a b)
    (hConv : ArbConvergence C arb.arb)
    (hFΔ : FeasibleDeltaVCs3Arb C arb.arb) (hCD : CDVC3Arb C arb.arb) :
    JoinLemma3AtArb C arb.arb := by
  intro ev₁ ev₂ s₀ s₁ s₂ h_tr h_ir h_in₁ h_in₂ h_cl₁ h_cl₂ hc₀ hc₁ hc₂
  classical
  obtain ⟨l₁, hp₁, -, -⟩ := id hc₁
  obtain ⟨l₂, hp₂, -, -⟩ := id hc₂
  have hpU₀ := listPermOf_union (D := D.toCRDTSig) hp₁ hp₂
  suffices gen : ∀ n, JoinAtArb (D := D) C arb.arb n by
    exact gen _ ev₁ ev₂ s₀ s₁ s₂ _ hpU₀ rfl h_in₁ h_in₂ h_cl₁ h_cl₂
      hc₀ hc₁ hc₂
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro ev₁ ev₂ s₀ s₁ s₂ lU hpU hlen h_in₁ h_in₂ h_cl₁ h_cl₂ hc₀ hc₁ hc₂
    -- Empty sides collapse via the feasible unit law.
    rcases Set.eq_empty_or_nonempty ev₁ with h_e₁ | h_ne₁
    · have hs₁ : s₁ = D.init := isCanonicalStateArb_empty h_e₁ hc₁
      have h_int : ev₁ ∩ ev₂ = ∅ := by rw [h_e₁, Set.empty_inter]
      have hs₀ : s₀ = D.init := isCanonicalStateArb_empty h_int hc₀
      have hinit := hFΔ.feasible_init ev₂ s₂ h_in₂ hc₂
      subst h_e₁
      rw [hs₀, hs₁, hinit, Set.empty_union]
      exact hc₂
    rcases Set.eq_empty_or_nonempty ev₂ with h_e₂ | h_ne₂
    · have hs₂ : s₂ = D.init := isCanonicalStateArb_empty h_e₂ hc₂
      have h_int : ev₁ ∩ ev₂ = ∅ := by rw [h_e₂, Set.inter_empty]
      have hs₀ : s₀ = D.init := isCanonicalStateArb_empty h_int hc₀
      have hinit := hFΔ.feasible_init ev₁ s₁ h_in₁ hc₁
      subst h_e₂
      rw [hs₀, hs₂, hMC, hinit, Set.union_empty]
      exact hc₁
    -- Select an arb(∪)-maximal event; build A = σ(U∖e), B = σ(↓e∖e).
    have h_inU : ∀ a ∈ ev₁ ∪ ev₂, a ∈ C.events := by
      rintro a (h | h)
      · exact h_in₁ a h
      · exact h_in₂ a h
    have h_clU : ∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b →
        b ∈ ev₁ ∪ ev₂ → a ∈ ev₁ ∪ ev₂ := by
      rintro a b hv hnc (h | h)
      · exact Or.inl (h_cl₁ a b hv hnc h)
      · exact Or.inr (h_cl₂ a b hv hnc h)
    obtain ⟨x₁, hx₁⟩ := h_ne₁
    obtain ⟨e, he_U, h_max⟩ :=
      exists_maximal_of_acyclic (R := arb.arb (ev₁ ∪ ev₂))
        (fun a => arb.acyclic (ev₁ ∪ ev₂) h_inU a) hpU ⟨x₁, Or.inl hx₁⟩
    have h_e_lU : e ∈ lU := (hpU.2 e).mpr he_U
    have hpU' : listPermOf (lU.filter (· ≠ e)) ((ev₁ ∪ ev₂) \ {e}) :=
      filter_ne_listPermOf hpU h_e_lU
    have hlen' : (lU.filter (· ≠ e)).length = n - 1 := by
      rw [listPermOf_diff_length hpU h_e_lU hpU', hlen]
    have h_pos : 0 < n := by
      rw [← hlen]
      exact List.length_pos_of_mem h_e_lU
    obtain ⟨A, hA⟩ : ∃ A, IsCanonicalStateArb C arb.arb ((ev₁ ∪ ev₂) \ {e}) A :=
      isCanonicalStateArb_exists arb (fun a ha => h_inU a ha.1) hpU'
    have h_dsub : downset (Configuration.core C) e ⊆ ev₁ ∪ ev₂ :=
      downset_subset h_clU he_U
    obtain ⟨lB, hpB⟩ :=
      exists_listPermOf_subsetA hpU
        (fun x (hx : x ∈ downset (Configuration.core C) e \ {e}) => h_dsub hx.1)
    obtain ⟨B, hB⟩ : ∃ B, IsCanonicalStateArb C arb.arb
        (downset (Configuration.core C) e \ {e}) B :=
      isCanonicalStateArb_exists arb
        (fun a ha => h_inU a (h_dsub ha.1)) hpB
    have h_cd : D.mergeL B A (D.update B e) = D.update A e :=
      hCD (ev₁ ∪ ev₂) A B e h_tr h_ir h_inU h_clU he_U h_max hA hB
    have h_target : IsCanonicalStateArb C arb.arb (ev₁ ∪ ev₂) (D.update A e) :=
      isCanonicalStateArb_snoc h_anti he_U h_max hA
    by_cases he₁ : e ∈ ev₁
    · obtain ⟨t₁, ht₁⟩ : ∃ t, IsCanonicalStateArb C arb.arb (ev₁ \ {e}) t := by
        obtain ⟨l₁', hp₁', -, -⟩ := id hc₁
        have h_e_l₁ : e ∈ l₁' := (hp₁'.2 e).mpr he₁
        exact isCanonicalStateArb_exists arb (fun a ha => h_in₁ a ha.1)
          (filter_ne_listPermOf hp₁' h_e_l₁)
      have hs₁d : s₁ = D.mergeL B t₁ (D.update B e) :=
        side_decompositionArb arb h_anti hConv hCD h_tr h_ir IH hpU hlen
          h_inU h_clU he_U h_max hA hB Set.subset_union_left h_in₁ h_cl₁ he₁ hc₁ ht₁
      by_cases he₂ : e ∈ ev₂
      · -- e shared: feasible redistribution.
        obtain ⟨t₂, ht₂⟩ : ∃ t, IsCanonicalStateArb C arb.arb (ev₂ \ {e}) t := by
          obtain ⟨l₂', hp₂', -, -⟩ := id hc₂
          have h_e_l₂ : e ∈ l₂' := (hp₂'.2 e).mpr he₂
          exact isCanonicalStateArb_exists arb (fun a ha => h_in₂ a ha.1)
            (filter_ne_listPermOf hp₂' h_e_l₂)
        have hs₂d : s₂ = D.mergeL B t₂ (D.update B e) :=
          side_decompositionArb arb h_anti hConv hCD h_tr h_ir IH hpU hlen
            h_inU h_clU he_U h_max hA hB Set.subset_union_right h_in₂ h_cl₂ he₂
            hc₂ ht₂
        have he₀ : e ∈ ev₁ ∩ ev₂ := ⟨he₁, he₂⟩
        have h_in₀ : ∀ a ∈ ev₁ ∩ ev₂, a ∈ C.events :=
          fun a ha => h_in₁ a ha.1
        have h_cl₀ : ∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b →
            b ∈ ev₁ ∩ ev₂ → a ∈ ev₁ ∩ ev₂ :=
          fun a b hv hnc hb =>
            ⟨h_cl₁ a b hv hnc hb.1, h_cl₂ a b hv hnc hb.2⟩
        obtain ⟨l₀', hp₀'⟩ :=
          exists_listPermOf_subsetA hpU
            (show (ev₁ ∩ ev₂) \ {e} ⊆ ev₁ ∪ ev₂ from
              fun x hx => Or.inl hx.1.1)
        obtain ⟨t₀, ht₀⟩ :
            ∃ t, IsCanonicalStateArb C arb.arb ((ev₁ ∩ ev₂) \ {e}) t :=
          isCanonicalStateArb_exists arb (fun a ha => h_in₁ a ha.1.1) hp₀'
        have hs₀d : s₀ = D.mergeL B t₀ (D.update B e) :=
          side_decompositionArb arb h_anti hConv hCD h_tr h_ir IH hpU hlen
            h_inU h_clU he_U h_max hA hB
            (show ev₁ ∩ ev₂ ⊆ ev₁ ∪ ev₂ from fun x hx => Or.inl hx.1)
            h_in₀ h_cl₀ he₀ hc₀ ht₀
        have hct₀' : IsCanonicalStateArb C arb.arb
            ((ev₁ \ {e}) ∩ (ev₂ \ {e})) t₀ := by
          rw [diff_inter_diff]
          exact ht₀
        have hsetm : (ev₁ \ {e}) ∪ (ev₂ \ {e}) = (ev₁ ∪ ev₂) \ {e} := by
          ext x
          simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
          tauto
        have h_mid_can : IsCanonicalStateArb C arb.arb
            ((ev₁ \ {e}) ∪ (ev₂ \ {e})) (D.mergeL t₀ t₁ t₂) := by
          refine IH (n - 1) (by omega) _ _ t₀ t₁ t₂
            (lU.filter (· ≠ e)) ?_ hlen'
            (fun a ha => h_in₁ a ha.1) (fun a ha => h_in₂ a ha.1)
            (closure_diff_of_max_arb arb he_U Set.subset_union_left h_cl₁ h_max)
            (closure_diff_of_max_arb arb he_U Set.subset_union_right h_cl₂ h_max)
            hct₀' ht₁ ht₂
          rw [hsetm]
          exact hpU'
        have h_mid_can' : IsCanonicalStateArb C arb.arb ((ev₁ ∪ ev₂) \ {e})
            (D.mergeL t₀ t₁ t₂) := by
          rw [← hsetm]
          exact h_mid_can
        have h_mid : D.mergeL t₀ t₁ t₂ = A :=
          isCanonicalStateArb_unique hConv (fun a ha => h_inU a ha.1)
            h_mid_can' hA
        have h_redis := hFΔ.feasible_redistribute ev₁ ev₂ t₀ t₁ t₂ B e
          h_tr h_ir h_in₁ h_in₂ h_cl₁ h_cl₂ he₁ he₂ h_max
          ht₀ hB ht₁ ht₂
        rw [hs₀d, hs₁d, hs₂d, h_redis, h_mid, h_cd]
        exact h_target
      · -- e local to side 1: feasible local redistribution.
        have hct₀' : IsCanonicalStateArb C arb.arb ((ev₁ \ {e}) ∩ ev₂) s₀ := by
          rw [inter_diff_left_of_not_mem he₂]
          exact hc₀
        have hset₁ : (ev₁ \ {e}) ∪ ev₂ = (ev₁ ∪ ev₂) \ {e} := by
          ext x
          simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
          constructor
          · rintro (⟨h, hne⟩ | h)
            · exact ⟨Or.inl h, hne⟩
            · exact ⟨Or.inr h, fun heq => he₂ (heq ▸ h)⟩
          · rintro ⟨h | h, hne⟩
            · exact Or.inl ⟨h, hne⟩
            · exact Or.inr h
        have h_mid_can : IsCanonicalStateArb C arb.arb ((ev₁ \ {e}) ∪ ev₂)
            (D.mergeL s₀ t₁ s₂) := by
          refine IH (n - 1) (by omega) _ _ s₀ t₁ s₂
            (lU.filter (· ≠ e)) ?_ hlen'
            (fun a ha => h_in₁ a ha.1) h_in₂
            (closure_diff_of_max_arb arb he_U Set.subset_union_left h_cl₁ h_max)
            h_cl₂ hct₀' ht₁ hc₂
          rw [hset₁]
          exact hpU'
        have h_mid_can' : IsCanonicalStateArb C arb.arb ((ev₁ ∪ ev₂) \ {e})
            (D.mergeL s₀ t₁ s₂) := by
          rw [← hset₁]
          exact h_mid_can
        have h_mid : D.mergeL s₀ t₁ s₂ = A :=
          isCanonicalStateArb_unique hConv (fun a ha => h_inU a ha.1)
            h_mid_can' hA
        have h_lr := hFΔ.feasible_local_redistribute ev₁ ev₂ s₀ B t₁ s₂ e
          h_tr h_ir h_in₁ h_in₂ h_cl₁ h_cl₂ he₁ he₂ h_max
          hc₀ hB ht₁ hc₂
        rw [hs₁d, h_lr, h_mid, h_cd]
        exact h_target
    · -- e local to side 2: mirror via mergeL_comm.
      have he₂ : e ∈ ev₂ := by
        rcases he_U with h | h
        · exact absurd h he₁
        · exact h
      obtain ⟨t₂, ht₂⟩ : ∃ t, IsCanonicalStateArb C arb.arb (ev₂ \ {e}) t := by
        obtain ⟨l₂', hp₂', -, -⟩ := id hc₂
        have h_e_l₂ : e ∈ l₂' := (hp₂'.2 e).mpr he₂
        exact isCanonicalStateArb_exists arb (fun a ha => h_in₂ a ha.1)
          (filter_ne_listPermOf hp₂' h_e_l₂)
      have hs₂d : s₂ = D.mergeL B t₂ (D.update B e) :=
        side_decompositionArb arb h_anti hConv hCD h_tr h_ir IH hpU hlen
          h_inU h_clU he_U h_max hA hB Set.subset_union_right h_in₂ h_cl₂ he₂ hc₂ ht₂
      have hct₀' : IsCanonicalStateArb C arb.arb (ev₁ ∩ (ev₂ \ {e})) s₀ := by
        rw [inter_diff_right_of_not_mem he₁]
        exact hc₀
      have hset₂ : ev₁ ∪ (ev₂ \ {e}) = (ev₁ ∪ ev₂) \ {e} := by
        ext x
        simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
        constructor
        · rintro (h | ⟨h, hne⟩)
          · exact ⟨Or.inl h, fun heq => he₁ (heq ▸ h)⟩
          · exact ⟨Or.inr h, hne⟩
        · rintro ⟨h | h, hne⟩
          · exact Or.inl h
          · exact Or.inr ⟨h, hne⟩
      have h_mid_can : IsCanonicalStateArb C arb.arb (ev₁ ∪ (ev₂ \ {e}))
          (D.mergeL s₀ s₁ t₂) := by
        refine IH (n - 1) (by omega) _ _ s₀ s₁ t₂
          (lU.filter (· ≠ e)) ?_ hlen'
          h_in₁ (fun a ha => h_in₂ a ha.1) h_cl₁
          (closure_diff_of_max_arb arb he_U Set.subset_union_right h_cl₂ h_max)
          hct₀' hc₁ ht₂
        rw [hset₂]
        exact hpU'
      have h_mid_can' : IsCanonicalStateArb C arb.arb ((ev₁ ∪ ev₂) \ {e})
          (D.mergeL s₀ s₁ t₂) := by
        rw [← hset₂]
        exact h_mid_can
      have h_mid : D.mergeL s₀ s₁ t₂ = A :=
        isCanonicalStateArb_unique hConv (fun a ha => h_inU a ha.1)
          h_mid_can' hA
      have h_max' : ∀ x ∈ ev₂ ∪ ev₁, x ≠ e → ¬ arb.arb (ev₂ ∪ ev₁) e x := by
        rw [Set.union_comm]
        exact h_max
      have hc₀_swap : IsCanonicalStateArb C arb.arb (ev₂ ∩ ev₁) s₀ := by
        rw [Set.inter_comm]
        exact hc₀
      have h_lr := hFΔ.feasible_local_redistribute ev₂ ev₁ s₀ B t₂ s₁ e
        h_tr h_ir h_in₂ h_in₁ h_cl₂ h_cl₁ he₂ he₁ h_max'
        hc₀_swap hB ht₂ hc₁
      rw [hs₂d, hMC s₀ s₁, h_lr,
        hMC s₀ t₂ s₁, h_mid, h_cd]
      exact h_target

/-! ## §4. The apply-case obstruction (vis-consistency), pinned for the
transition-induction continuation. -/

/-- **vis-consistency of an arbitration**: `arb` never orders `a` before an event
`b` that `a` observed. The clause the `goodConfig3_apply` re-thread needs (see the
file-header FINDING); independent of acyclicity/extends-`vis`/antitone/convergence,
satisfied by `loOn` (both arms vacuous on an observed pair) and by `lwwArb`
(timestamp order respects causality). -/
def VisConsistentArbitration (C : Configuration D)
    (arb : Set (Op D.AppOp) → Op D.AppOp → Op D.AppOp → Prop) : Prop :=
  ∀ (E : Set (Op D.AppOp)) {a b : Op D.AppOp},
    a ∈ E → b ∈ E → C.vis b a → ¬ arb E a b

/-- **The apply-case re-attach**, discharged from vis-consistency + antitone: a
causally-latest fresh event `e` (observing all of `E`) extends the `arb`-canonical
state of `E` to that of `insert e E`. This is the arb-form of
`isCanonicalState_extend`, and the exact obligation the transition induction's
Apply case consumes. -/
theorem isCanonicalStateArb_extend {C : Configuration D}
    {arb : Set (Op D.AppOp) → Op D.AppOp → Op D.AppOp → Prop}
    (h_anti : ∀ {E' E'' : Set (Op D.AppOp)} {a b : Op D.AppOp},
       E' ⊆ E'' → arb E'' a b → arb E' a b)
    (h_vc : VisConsistentArbitration C arb)
    {ev : Set (Op D.AppOp)} {s : D.State} {e : Op D.AppOp}
    (h_e_fresh : e ∉ ev)
    (h_e_sees : ∀ x ∈ ev, C.vis x e)
    (h : IsCanonicalStateArb C arb ev s) :
    IsCanonicalStateArb C arb (insert e ev) (D.update s e) := by
  obtain ⟨ρ, hp, hr, hs⟩ := h
  refine ⟨ρ ++ [e], ⟨?_, fun a => ?_⟩, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hp.1, List.nodup_singleton _, ?_⟩
    intro x hx y hy heq
    rw [List.mem_singleton] at hy; subst hy; subst heq
    exact h_e_fresh ((hp.2 x).mp hx)
  · rw [List.mem_append, List.mem_singleton, Set.mem_insert_iff]
    constructor
    · rintro (h' | rfl)
      · exact Or.inr ((hp.2 a).mp h')
      · exact Or.inl rfl
    · rintro (rfl | h')
      · exact Or.inr rfl
      · exact Or.inl ((hp.2 a).mpr h')
  · unfold respects
    rw [List.pairwise_append]
    refine ⟨hr.imp (fun hn h' => hn (h_anti (Set.subset_insert _ _) h')),
      List.pairwise_singleton _ _, ?_⟩
    intro y hy b hb
    rw [List.mem_singleton] at hb; subst hb
    have hy_ev : y ∈ ev := (hp.2 y).mp hy
    exact h_vc _ (Set.mem_insert _ _)
      (Set.mem_insert_of_mem _ hy_ev) (h_e_sees y hy_ev)
  · rw [applySeq_append_single, hs]

/-- **The createReplica-case transfer**, arb-form of `isCanonicalState_congr`:
an `arb`-canonical state stays canonical when the arbitration is replaced by one
that agrees on the event set (as happens when a transition leaves `vis`
unchanged on old events). The third transition pillar. -/
theorem isCanonicalStateArb_congr {C C' : Configuration D}
    {arb arb' : Set (Op D.AppOp) → Op D.AppOp → Op D.AppOp → Prop}
    {E : Set (Op D.AppOp)} {s : D.State}
    (h_agree : ∀ a ∈ E, ∀ b ∈ E, (arb E a b ↔ arb' E a b))
    (h : IsCanonicalStateArb C arb E s) : IsCanonicalStateArb C' arb' E s := by
  obtain ⟨ρ, hp, hr, hf⟩ := h
  refine ⟨ρ, hp, ?_, hf⟩
  refine hr.imp_of_mem ?_
  intro a b ha hb hn h'
  exact hn ((h_agree b ((hp.2 b).mp hb) a ((hp.2 a).mp ha)).mpr h')

/-! ## §5. Faithfulness at `loOn`: the generic engine subsumes the concrete
Join Lemma from the SAME VC bundle.

`IsCanonicalStateArb C (loOn (core C)) = IsCanonicalState (core C)` definitionally,
so the arb-form VCs at `arb := loOn (core C)` are the published `CDVC3` /
`FeasibleDeltaVCs3` specialised to `core C`. Together with `loOnArbitration`
(acyclicity), `loOn_mono` (antitone), and `loOn_arbConvergence` (convergence) —
all pre-existing — the generic `join_lemma3AtArb_of_cd_feasible` reproduces the
`loOn` ternary Join Lemma from exactly `CoreVCs3CD + FeasibleDeltaVCs3 + CDVC3`,
confirming the abstraction is faithful (not vacuous). -/

/-- The arb-form CD equation at `loOn` is the published `CDVC3` (definitional). -/
theorem cdvc3Arb_of_cdvc3 (hCD : CDVC3 D) (C : Configuration D) :
    CDVC3Arb C (fun E => loOn (Configuration.core C) E) :=
  fun U A B e h_tr h_ir h_inU h_clU he_U h_max hA hB =>
    hCD (Configuration.core C) U A B e h_tr h_ir h_inU h_clU he_U h_max hA hB

/-- The arb-form feasible delta contract at `loOn` is the published
`FeasibleDeltaVCs3` (definitional, field for field). -/
theorem feasibleDeltaVCs3Arb_of_feasible (hFΔ : FeasibleDeltaVCs3 D)
    (C : Configuration D) :
    FeasibleDeltaVCs3Arb C (fun E => loOn (Configuration.core C) E) where
  feasible_init := fun ev s h_in hcs =>
    hFΔ.feasible_init (Configuration.core C) ev s h_in hcs
  feasible_local_redistribute :=
    fun ev₁ ev₂ s₀ B t₁ s₂ e h_tr h_ir h1 h2 hcl1 hcl2 he1 he2 h_max hc0 hB ht1 hc2 =>
      hFΔ.feasible_local_redistribute (Configuration.core C) ev₁ ev₂ s₀ B t₁ s₂ e
        h_tr h_ir h1 h2 hcl1 hcl2 he1 he2 h_max hc0 hB ht1 hc2
  feasible_redistribute :=
    fun ev₁ ev₂ t₀ t₁ t₂ B e h_tr h_ir h1 h2 hcl1 hcl2 he1 he2 h_max ht0 hB ht1 ht2 =>
      hFΔ.feasible_redistribute (Configuration.core C) ev₁ ev₂ t₀ t₁ t₂ B e
        h_tr h_ir h1 h2 hcl1 hcl2 he1 he2 h_max ht0 hB ht1 ht2

/-- **The generic Join Lemma reproduces the `loOn` Join Lemma** from
`CoreVCs3CD + UpdateVCs + FeasibleDeltaVCs3 + CDVC3` — the same bundle the
concrete `join_lemma3_of_cd_feasible` consumes. Faithfulness of the abstraction:
the merge case of adequacy factors through the fully-generic engine with `loOn`
as one instance. -/
theorem join_lemma3AtArb_loOn {C : Configuration D}
    (hVC : CoreVCs3CD D) (hU : UpdateVCs D.toCRDTSig)
    (hFΔ : FeasibleDeltaVCs3 D) (hCD : CDVC3 D)
    (h_tr : ∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c)
    (h_ir : ∀ a : Op D.AppOp, ¬ C.vis a a) :
    JoinLemma3AtArb C (fun E => loOn (Configuration.core C) E) :=
  join_lemma3AtArb_of_cd_feasible hVC.mergeL_comm (loOnArbitration C hU h_tr h_ir)
    (fun {_ _ _ _} hsub h => loOn_mono hsub h) (loOn_arbConvergence hU)
    (feasibleDeltaVCs3Arb_of_feasible hFΔ C) (cdvc3Arb_of_cdvc3 hCD C)

#print axioms isCanonicalStateArb_empty
#print axioms downset_max_arb
#print axioms closure_diff_of_max_arb
#print axioms side_decompositionArb
#print axioms join_lemma3AtArb_of_cd_feasible
#print axioms isCanonicalStateArb_extend
#print axioms isCanonicalStateArb_congr
#print axioms cdvc3Arb_of_cdvc3
#print axioms feasibleDeltaVCs3Arb_of_feasible
#print axioms join_lemma3AtArb_loOn

end Sal.ConditionedMRDTs
