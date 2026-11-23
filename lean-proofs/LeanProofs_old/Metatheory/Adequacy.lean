import LeanProofs.Interface.VCRoute
import Artifact.MRDTs.Metatheory.Correctness
import Artifact.MRDTs.Paper1.ConcreteJoin

/-!
# Adequacy at the framework's reading of `lo^C_E`

Proved once, for every implementation. No datatype is named here and no
implementation may add to this file.

**Nothing in this file is on the path to Definition 4 any more.** Every row
now reaches its join lemma through `Metatheory/PaperAdequacy.lean`, which
reads canonicity at the relation Section 4 displays rather than at the one
the framework builds from `rc`, and so needs only the paper's guarded laws.
What survives from here are three pieces those rows still use: `replayLaws`,
the helper `causalDelta_of_commuting`, and `vcScheme`. The rest is the
original Section 5 route at `IsCanOn`, kept because it is the statement the
paper makes and because every row's `CanonicalJoinLaws` is still phrased in
its terms.

The chain follows Section 5 of the paper:

```
  Laws(D_type)  +  VC1..VC5        per implementation
      |
      v
  the join lemma                  merging canonical states is canonical
```

`Soundness` carries the chain further, to canonical correctness and then,
with `SpecSound`, to RA-linearizability. Nothing here consults `Spec`: as
the paper says, the canonical join laws alone do not establish conformance.

## Two routes to the join lemma

`joinLemma_of_vcs` is the route of Section 5: discharge the five VCs and the
lemma follows. The VCs are the paper's, premises and all, and this file
passes them to the framework's canonical-state constructor unchanged.

One row's join lemma depends on its issuance guard, so its conditions are
stated at the contexts that guard admits. `joinOn_of_vcs` is the same step
for it, by the framework's other induction. Both end at `JoinAt`, so nothing
downstream can tell them apart.
-/

namespace LeanProofs.Metatheory

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1 LeanProofs.Interface

variable {type : MRDTType} {D : Impl type}

/-! ## The general route

Everything in this section holds for an arbitrary `rc`. -/

/-- `Laws(D_type)` is the framework's replay contract. RC-NON-COMM supplies
`noncomm_covered`, NO-RC-CHAIN supplies acyclicity, COND-COMM supplies the
absorber clause. -/
theorem replayLaws (h : Laws D) (hru : UniformRcNonComm D) (hcc : UniformCondComm D) :
    @ReplayLaws D.toMRDTSig.toUpdateSig (rcOrder D) :=
  (h.toRestricted hru hcc).replayLaws

theorem joinCoreLaws (h : Laws D) (hru : UniformRcNonComm D) (hcc : UniformCondComm D)
    (vcs : CanonicalJoinLaws D) : @JoinCoreLaws D.toMRDTSig (rcOrder D) :=
  letI : EventOrder D.toMRDTSig.toUpdateSig := rcOrder D
  ⟨replayLaws h hru hcc, vcs.vc1_merge_comm⟩

/-- **VC2, VC3 and VC5** as the framework's canonical-state delta bundle.
Each field is the row's own obligation, passed through unchanged: the
premises `FeasibleDeltaLaws` carries are exactly the paper's. -/
theorem feasibleDeltaLaws (vcs : CanonicalJoinLaws D) :
    @FeasibleDeltaLaws D.toMRDTSig (rcOrder D) :=
  letI : EventOrder D.toMRDTSig.toUpdateSig := rcOrder D
  ⟨fun C E s hsup hcan => vcs.vc2_merge_init C E s hsup hcan,
   fun C E₁ E₂ l m x y e htr hirr h₁ h₂ hc₁ hc₂ he₁ he₂ hmax hl hm hx hy =>
     vcs.vc3_local_redistribute C E₁ E₂ l m x y e ⟨htr, hirr⟩ h₁ h₂ hc₁ hc₂
       he₁ he₂ hmax hl hm hx hy,
   fun C E₁ E₂ x₀ x₁ x₂ m e htr hirr h₁ h₂ hc₁ hc₂ he₁ he₂ hmax hx₀ hm hx₁ hx₂ =>
     vcs.vc5_redistribute C E₁ E₂ x₀ x₁ x₂ m e ⟨htr, hirr⟩ h₁ h₂ hc₁ hc₂
       he₁ he₂ hmax hx₀ hm hx₁ hx₂⟩

/-- **The join lemma** from the five VCs: merging canonical states produces
the canonical state of the union of their event sets.

This is the framework's own canonical-state constructor. Nothing is
strengthened on the way in. -/
theorem joinLemma_of_vcs (h : Laws D) (hru : UniformRcNonComm D)
    (hcc : UniformCondComm D) (vcs : CanonicalJoinLaws D) :
    @Join D.toMRDTSig (rcOrder D) :=
  letI : EventOrder D.toMRDTSig.toUpdateSig := rcOrder D
  Artifact.MRDTs.CanonicalJoinLaws.join
    ⟨joinCoreLaws h hru hcc vcs, feasibleDeltaLaws vcs, vcs.vc4_causal_delta⟩

/-! ## A helper for the all-commuting family

`Obligations` carries the row's own laws and its five conditions, and asks
nothing about commutation. `causalDelta_of_commuting` below is a helper, not
a VC: a row whose events all commute may use it to discharge **VC4**
cheaply, and a row whose events do not proves VC4 itself. -/

/-- **A way to discharge VC4 when every pair of events commutes.**

Not a VC and not a law: a helper. When everything commutes, `lo^C_E` orders
nothing, so the downset of `e` is `{e}` and the base `B` of CAUSAL-DELTA is
`sigma0`. The peel hypothesis then moves `e` outside the merge, and VC2 is
applied at `A`, which is canonical by assumption. `commuting_peel` lives
here, as a hypothesis of this helper, rather than among the paper's
conditions.

This mirrors `Artifact.MRDTs.causalDeltaLaw_of_all_comm`, which asks for
`merge(sigma0, sigma0, s)` at an arbitrary `s`. Only a canonical `s` is ever
needed, so the paper's VC2 suffices. -/
theorem causalDelta_of_commuting
    (merge_comm : ∀ l a b : D.Sigma, D.merge l a b = D.merge l b a)
    (vc2 : ∀ (C : Ctx D) (E : Set D.Event) (s : D.Sigma),
      SupportedOn D C E → IsCanOn D C E s → D.merge D.sigma0 D.sigma0 s = s)
    (peel : ∀ (a : D.Sigma) (e : D.Event) (pi₀ pi₂ : List D.Event),
      (∀ x ∈ pi₀, D.Commutes e x) → (∀ x ∈ pi₂, D.Commutes e x) →
      D.merge (D.applyList D.sigma0 pi₀) (D.do_ a e) (D.applyList D.sigma0 pi₂)
        = D.do_ (D.merge (D.applyList D.sigma0 pi₀) a (D.applyList D.sigma0 pi₂)) e)
    (all_comm : ∀ e₁ e₂ : D.Event, D.Commutes e₁ e₂) :
    @CausalDeltaLaw D.toMRDTSig (rcOrder D) := by
  letI : EventOrder D.toMRDTSig.toUpdateSig := rcOrder D
  intro C U A B e _ _ hU _ _ _ hA hB
  have h_down : downset C e \ {e} = ∅ := by
    ext x
    simp only [Set.mem_diff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false, not_and]
    rintro (hx | hx)
    · exact fun hne => hne hx
    · intro _
      exfalso
      cases hx with
      | single h' => exact h'.2 (all_comm _ _)
      | tail _ h' => exact h'.2 (all_comm _ _)
  have hBinit : B = D.sigma0 := isCanonicalState_empty h_down hB
  subst hBinit
  obtain ⟨ρ, -, -, hfA⟩ := id hA
  have hpc := peel D.sigma0 e [] ρ
    (fun x hx => absurd hx List.not_mem_nil) (fun x _ => all_comm e x)
  have h0 : D.applyList D.sigma0 ([] : List D.Event) = D.sigma0 := rfl
  rw [h0] at hpc
  rw [show D.applyList D.sigma0 ρ = A from hfA] at hpc
  rw [vc2 C (U \ {e}) A (fun a ha => hU a ha.1) hA] at hpc
  show D.merge D.sigma0 A (D.do_ D.sigma0 e) = D.do_ A e
  rw [merge_comm]
  exact hpc

/-! ## The guarded route

One row of Table 1 carries an issuance guard and its join lemma is false
without it, so its conditions are stated at the contexts the guard admits.
`Interface/VCRoute.lean` calls that predicate `Good`.

The framework's canonical-state induction, which `joinLemma_of_vcs` above
runs, takes its conditions at **every** context, so it cannot carry a guard.
The framework's other induction can: `ConcreteMRDT.Raw.join_at_sizes` is
indexed by a *representation* rather than by `IsCanonicalState` itself, and
it is already fixed at one context. Putting `Good C` inside the
representation is what carries the guard through, and that is what the three
definitions below do.

Both routes end at `JoinAt`, so nothing downstream can tell them apart, and
`Obligations.toOn` lets an unguarded row take this route as well. -/

/-- **The representation the guarded induction runs on**: the canonical state
of a supported event set, at a context `Good` admits. Carrying `Good C` here
rather than as a premise of each condition is what lets the framework's
induction, which fixes one context throughout, keep the guard. -/
def vcRepresentation (D : Impl type) (Good : Ctx D → Prop) :
    ConcreteMRDT.Representation D.toMRDTSig :=
  fun C E s => IsCanOn D C E s ∧ SupportedOn D C E ∧ Good C

/-- The metadata scheme: a `vis` edge between non-commuting events, which is
the relation `downset` is the backward closure of. -/
def vcScheme (D : Impl type) (C : Ctx D) :
    ConcreteMRDT.MetadataDependencies C :=
  ConcreteMRDT.MetadataDependencies.ofConcrete C

/-- The scheme's past is the principal downset, by definition of both. -/
theorem vcScheme_past (D : Impl type) (C : Ctx D) (e : D.Event) :
    (vcScheme D C).Past e = downset C e := rfl

/-- **The join lemma at the contexts `Good` admits**, from `Laws(D_type)` and
the five conditions stated there. With `Good = fun _ => True` this is
`joinLemma_of_vcs` again, by another induction. -/
theorem joinOn_of_vcs {Good : Ctx D → Prop} (h : Laws D)
    (hru : UniformRcNonComm D) (hcc : UniformCondComm D)
    (vcs : CanonicalJoinLawsOn D Good) (C : Ctx D) (hgood : Good C) :
    @JoinAt D.toMRDTSig (rcOrder D) C := by
  classical
  letI : EventOrder D.toMRDTSig.toUpdateSig := rcOrder D
  have hrl : @ReplayLaws D.toMRDTSig.toUpdateSig (rcOrder D) := replayLaws h hru hcc
  have hres : RestrictedLaws D.toMRDTSig.toUpdateSig (policy D) := h.toRestricted hru hcc
  -- The five conditions, as the framework's representation-indexed bundle.
  have vcs' : ConcreteMRDT.Raw.MergeVCs (policy D) (vcRepresentation D Good)
      (vcScheme D) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro _ _ _ l a b _ _ _ _ _ _ _
      exact vcs.vc1_merge_comm l a b
    · intro C' E s hsup _ hrep
      exact vcs.vc2_merge_init C' E s hrep.2.2 hsup hrep.1
    · intro C' U s B e htr hirr hsup hcl heU hsem _ hs hB _ _
      exact vcs.vc4_causal_delta C' U s B e hs.2.2
        ⟨fun hab hbc => htr hab hbc, hirr⟩ hsup
        (fun a b hv hnc hb => hcl a b ⟨hv, hnc⟩ hb) heU
        (fun x hx hne hlo =>
          hsem x hx hne ((paperOrder_iff_loOn hres C' U e x).mpr hlo))
        hs.1 hB.1
    · intro C' E₁ E₂ l B t b e ctx he₁ he₂ hl hB ht hb _ _ _
      exact vcs.vc3_local_redistribute C' E₁ E₂ l B t b e hl.2.2
        ⟨fun hab hbc => ctx.trans hab hbc, ctx.irrefl⟩
        ctx.supported₁ ctx.supported₂
        (fun a b' hv hnc hb' => ctx.closed₁ a b' ⟨hv, hnc⟩ hb')
        (fun a b' hv hnc hb' => ctx.closed₂ a b' ⟨hv, hnc⟩ hb')
        he₁ he₂
        (fun x hx hne hlo =>
          ctx.semantic x hx hne ((paperOrder_iff_loOn hres C' _ e x).mpr hlo))
        hl.1 hB.1 ht.1 hb.1
    · intro C' E₁ E₂ t₀ t₁ t₂ B e ctx he₁ he₂ h₀ hB h₁ h₂ _ _ _ _ _
      exact vcs.vc5_redistribute C' E₁ E₂ t₀ t₁ t₂ B e h₀.2.2
        ⟨fun hab hbc => ctx.trans hab hbc, ctx.irrefl⟩
        ctx.supported₁ ctx.supported₂
        (fun a b' hv hnc hb' => ctx.closed₁ a b' ⟨hv, hnc⟩ hb')
        (fun a b' hv hnc hb' => ctx.closed₂ a b' ⟨hv, hnc⟩ hb')
        he₁ he₂
        (fun x hx hne hlo =>
          ctx.semantic x hx hne ((paperOrder_iff_loOn hres C' _ e x).mpr hlo))
        h₀.1 hB.1 h₁.1 h₂.1
  -- Canonical states are unique, the empty set has one, and a representation
  -- carries an enumeration.
  have unique' : ConcreteMRDT.Raw.Unique (vcRepresentation D Good) :=
    fun _ _ _ _ ha hb =>
      isCanonicalState_unique_of_replayLaws hrl ha.2.1 ha.1 hb.1
  have initial' : ∀ C' E s, vcRepresentation D Good C' E s →
      vcRepresentation D Good C' ∅ D.toMRDTSig.init := by
    intro _ _ _ hs
    exact ⟨⟨[], ⟨List.nodup_nil, by simp⟩, List.Pairwise.nil, rfl⟩,
      fun a ha => absurd ha (by simp), hs.2.2⟩
  have finite' : ∀ C' E s, vcRepresentation D Good C' E s →
      ∃ π, listPermOf π E := by
    intro _ _ _ hs
    obtain ⟨π, hp, -, -⟩ := hs.1
    exact ⟨π, hp⟩
  intro ev₁ ev₂ s₀ s₁ s₂ h_tr h_ir h_in₁ h_in₂ h_cl₁ h_cl₂ hc₀ hc₁ hc₂
  -- At this context: every supported set has a representation, and a
  -- nonempty one has a maximal event to peel.
  have supply : ∀ (E : Set D.Event) (π : List D.Event), listPermOf π E →
      ConcreteMRDT.Supported C E → ∃ s, vcRepresentation D Good C E s := by
    intro E π hp hsup
    obtain ⟨s, hs⟩ := isCanonicalState_exists_of_replayLaws hrl h_tr h_ir hp hsup
    exact ⟨s, hs, hsup, hgood⟩
  have peel : ∀ (E : Set D.Event) (s : D.Sigma), vcRepresentation D Good C E s →
      ConcreteMRDT.Supported C E → E.Nonempty → (vcScheme D C).Closed E →
      Nonempty (ConcreteMRDT.Raw.PeelChoice (policy D) (vcRepresentation D Good)
        C (vcScheme D C) E) := by
    intro E s hrep hsup hne hcl
    obtain ⟨π, hp, -, -⟩ := id hrep.1
    have hclw : ∀ a b, C.vis a b → ¬ D.toMRDTSig.toUpdateSig.commutes a b →
        b ∈ E → a ∈ E := fun a b hv hnc hb => hcl a b ⟨hv, hnc⟩ hb
    obtain ⟨e, heE, hmax⟩ :=
      exists_loOn_maximal_of_replayLaws hrl h_tr h_ir hp hsup hne
    have hel : e ∈ π := (hp.2 e).mpr heE
    obtain ⟨A, hA⟩ := isCanonicalState_exists_of_replayLaws hrl h_tr h_ir
      (filter_ne_listPermOf hp hel) (fun a ha => hsup a ha.1)
    have hdsub : downset C e ⊆ E := downset_subset hclw heE
    obtain ⟨lB, hpB⟩ := ConcreteMRDT.enumeration_subset hp
      (show downset C e \ {e} ⊆ E from fun x hx => hdsub hx.1)
    obtain ⟨B, hB⟩ := isCanonicalState_exists_of_replayLaws hrl h_tr h_ir hpB
      (fun a ha => hsup a (hdsub ha.1))
    have hsupD : ConcreteMRDT.Supported C (downset C e) :=
      fun a ha => hsup a (hdsub ha)
    exact ⟨{ event := e
             member := heE
             semantic_maximal := fun x hx hne' hpo =>
               hmax x hx hne' ((paperOrder_iff_loOn hres C E e x).mp hpo)
             metadata_maximal := fun x hx hne' hbef =>
               hmax x hx hne'
                 (Or.inl ⟨hbef.1, hrl.noncomm_covered _ _ hbef.2⟩)
             remainder := A
             past := B
             remainder_rep := ⟨hA, fun a ha => hsup a ha.1, hgood⟩
             past_rep := ⟨hB, fun a ha => hsupD a ha.1, hgood⟩
             reconstructed_past :=
               ⟨isCanonicalState_snoc self_mem_downset
                  (downset_max h_tr h_ir) hB, hsupD, hgood⟩
             reconstructed_union :=
               ⟨isCanonicalState_snoc heE hmax hA, hsup, hgood⟩ }⟩
  have sizes := ConcreteMRDT.Raw.join_at_sizes vcs' unique' initial' finite' C
    (fun _ _ _ hab hbc => h_tr hab hbc) h_ir supply peel
  obtain ⟨l₁, hp₁, -, -⟩ := id hc₁
  obtain ⟨l₂, hp₂, -, -⟩ := id hc₂
  exact (sizes _ ev₁ ev₂ s₀ s₁ s₂ _
    (listPermOf_union (D := D.toMRDTSig.toUpdateSig) hp₁ hp₂) rfl h_in₁ h_in₂
    (fun a b hb hbe => h_cl₁ a b hb.1 hb.2 hbe)
    (fun a b hb hbe => h_cl₂ a b hb.1 hb.2 hbe)
    ⟨hc₀, fun a ha => h_in₁ a ha.1, hgood⟩
    ⟨hc₁, h_in₁, hgood⟩ ⟨hc₂, h_in₂, hgood⟩).1

end LeanProofs.Metatheory
