import LeanProofs_no_spec_non_comm.Interface.CausalRoute
import LeanProofs_no_spec_non_comm.Metatheory.Adequacy

/-!
# The join lemma at the full causal past

Proved once, for every implementation. No datatype is named here and no
implementation may add to this file.

This is `Metatheory/Adequacy.lean` run at `causalScheme` in place of
`vcScheme`, and it stops where the two routes converge:

```
  Laws(D_type) + VC1..VC5 at the causal past        per implementation
      |
      v
  the join lemma            PaperJoinOn D Good
      |
      v
  everything from `Metatheory/Adequacy.lean` onwards, shared
```

The convergence is not a coincidence. The framework's `RepresentationJoin`
is stated with **`vis`**-closure hypotheses and derives the scheme's own
closure from `MetadataDependencies.causal`, so the join lemma's statement
does not mention the scheme at all. Neither does the representation:
canonicity is `IsPaperCan` on both routes, read at `lo^C_E`. Only the
induction between them differs.

So `paperRepresentation`, `paperRepresentation_unique`,
`paperRepresentation_finite`, `paperRepresentation_supply`,
`representationJoin_of_paperJoin`, `closedJoinAt_of_paperJoin`,
`paperCanonicalConfig` and `paperCanonicalVersions` are reused verbatim
from the Part II file. Three things are rebuilt: the maximal-event
extraction, the peel step, and the translation of the five conditions.
-/

namespace LeanProofs.NoSpecNonComm.Metatheory

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

variable {type : MRDTType} {D : Impl type}

/-! ## The maximal event

Part II derives metadata maximality from semantic maximality, because every
`vcScheme` edge is a `lo^C_E` edge. At `causalScheme` that implication runs
the wrong way, so the two halves are taken from one enumeration instead. -/

/-- **A finite nonempty event set has an event maximal for `lo^C_E` and for
`vis` at once.** This is where `CausalEnumerable` is spent. -/
theorem exists_causalMaximal (hen : CausalEnumerable D)
    {C : Ctx D} {E : Set D.Event} {π : List D.Event}
    (hvs : VisStrict D C) (hsup : SupportedOn D C E) (hp : listPermOf π E)
    (hne : E.Nonempty) :
    ∃ e ∈ E, PaperMaximalOn D C E e ∧ CausalMaximalOn D C E e := by
  obtain ⟨ρ, hρ, hr, hrv⟩ := hen C E π hvs hsup hp
  exact ConcreteMRDT.joint_maximal_of_enumeration ρ hρ hne hr hrv

/-! ## The peel step -/

/-- **The peel step at the causal past.** A nonempty causally closed set has
an event maximal for both relations whose removal leaves a canonical state,
whose causal past has one, and which reconstructs both by one
application. -/
theorem causalReplaySupply (hl : GuardedReplay.Laws D.toMRDTSig.toUpdateSig (policy D))
    (hen : CausalEnumerable D) (C : Ctx D) (hvs : VisStrict D C)
    {Good : Ctx D → Prop} (hgood : Good C) :
    ConcreteMRDT.Raw.ReplaySupply (policy D) (paperRepresentation D Good)
      (causalScheme D) C := by
  obtain ⟨htr', hirr⟩ := hvs
  have htr : Transitive C.vis := fun _ _ _ hab hbc => htr' hab hbc
  refine ⟨fun E π hp hsup =>
    paperRepresentation_supply hl htr hirr hgood hp hsup, ?_⟩
  intro E s hs hsup hne hcl
  obtain ⟨π, hp⟩ := paperRepresentation_finite hs
  obtain ⟨e, heE, hmax, hmeta⟩ :=
    exists_causalMaximal hen ⟨htr', hirr⟩ hsup hp hne
  have hpast : (causalScheme D C).Past e ⊆ E :=
    (causalScheme D C).past_subset E e hcl heE
  obtain ⟨ρ, hρ⟩ := ConcreteMRDT.enumeration_subset hp
    (show E \ {e} ⊆ E from Set.diff_subset)
  obtain ⟨τ, hτ⟩ := ConcreteMRDT.enumeration_subset hp
    (show (causalScheme D C).Past e \ {e} ⊆ E from fun _ hx => hpast hx.1)
  obtain ⟨A, hA⟩ := paperRepresentation_supply hl htr hirr hgood hρ
    (fun a ha => hsup a ha.1)
  obtain ⟨B, hB⟩ := paperRepresentation_supply hl htr hirr hgood hτ
    (fun a ha => hsup a (hpast ha.1))
  refine ⟨⟨e, heE, hmax, hmeta, A, B, hA, hB, ?_, ?_⟩⟩
  · exact ⟨isPaperCan_snoc (Or.inl rfl)
      ((causalScheme D C).past_semantic_maximal (policy D) htr hirr e) hB.1,
      fun a ha => hsup a (hpast ha), hgood⟩
  · exact ⟨isPaperCan_snoc heE hmax hA.1, hsup, hgood⟩

/-! ## The five conditions -/

/-- **VC1 to VC5 as the framework's representation-indexed bundle.** Each
field is the row's own condition, passed through unchanged. The scheme's
`Closed` and `before` are `CausallyClosed` and `vis` by definition, so
unlike Part II there is not even a translation on the closure
hypotheses. -/
theorem causalMergeVCs {Good : Ctx D → Prop} (vcs : CausalJoinLawsOn D Good) :
    ConcreteMRDT.Raw.MergeVCs (policy D) (paperRepresentation D Good)
      (causalScheme D) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _ l a b _ _ _ _ _ _ _
    exact vcs.vc1_merge_comm l a b
  · intro C' E s hsup _ hrep
    exact vcs.vc2_merge_init C' E s hrep.2.2 hsup hrep.1
  · intro C' U s B e htr hirr hsup hcl heU hsem hmeta hs hB _ _
    exact vcs.vc4_causal_delta C' U s B e hs.2.2
      ⟨fun {_ _ _} hab hbc => htr hab hbc, hirr⟩
      hsup hcl heU hsem hmeta hs.1 hB.1
  · intro C' E₁ E₂ l B t b e ctx he₁ he₂ hl hB ht hb _ _ _
    exact vcs.vc3_local_redistribute C' E₁ E₂ l B t b e hl.2.2
      ⟨fun {_ _ _} hab hbc => ctx.trans hab hbc, ctx.irrefl⟩
      ctx.supported₁ ctx.supported₂ ctx.closed₁ ctx.closed₂
      he₁ he₂ ctx.semantic ctx.metadata hl.1 hB.1 ht.1 hb.1
  · intro C' E₁ E₂ t₀ t₁ t₂ B e ctx he₁ he₂ h₀ hB h₁ h₂ _ _ _ _ _
    exact vcs.vc5_redistribute C' E₁ E₂ t₀ t₁ t₂ B e h₀.2.2
      ⟨fun {_ _ _} hab hbc => ctx.trans hab hbc, ctx.irrefl⟩
      ctx.supported₁ ctx.supported₂ ctx.closed₁ ctx.closed₂
      he₁ he₂ ctx.semantic ctx.metadata h₀.1 hB.1 h₁.1 h₂.1

/-! ## The join lemma -/

/-- **The join lemma** from the five conditions at the causal past. The
statement is the paper's, at `lo^C_E`, and it is the very statement Part II
produces, so the two routes are interchangeable from here on. -/
theorem causalJoin_of_vcs {Good : Ctx D → Prop} (h : Laws D)
    (hself : EqualOpCommutes D) (hsame : SameReplicaCondComm D)
    (hen : CausalEnumerable D) (vcs : CausalJoinLawsOn D Good) :
    PaperJoinOn D Good := by
  have hl := guardedLaws h hself hsame
  have raw : ConcreteMRDT.RepresentationJoin (paperRepresentation D Good) := by
    refine ConcreteMRDT.Raw.representationJoin_of_vcs (causalMergeVCs vcs)
      (paperRepresentation_unique hl) ?_
      (fun _ _ _ hs => paperRepresentation_finite hs) ?_
    · intro _ _ _ hs
      exact ⟨⟨[], ⟨List.nodup_nil, by simp⟩, List.Pairwise.nil, rfl⟩,
        fun a ha => absurd ha (by simp), hs.2.2⟩
    · intro C' _ _ _ _ htr hirr _ _ ha _
      exact causalReplaySupply hl hen C'
        ⟨fun {_ _ _} hab hbc => htr hab hbc, hirr⟩ ha.2.2
  intro C E₁ E₂ l a b hgood hvs h₁ h₂ c₁ c₂ hl' ha hb
  have htr : Transitive C.vis := fun _ _ _ hxy hyz => hvs.1 hxy hyz
  exact (raw C E₁ E₂ l a b htr hvs.2 h₁ h₂ c₁ c₂
    ⟨hl', fun x hx => h₁ x hx.1, hgood⟩ ⟨ha, h₁, hgood⟩ ⟨hb, h₂, hgood⟩).1

/-- **The join lemma from the bundle.** The Part III counterpart of
`joinLemma`, with the same conclusion, so a row on this route reaches the
soundness entry points exactly as a Part II row does. -/
theorem causalJoinLemma {Good : Ctx D → Prop} (h : CausalObligationsOn D Good) :
    PaperJoinOn D Good :=
  causalJoin_of_vcs h.laws h.equal_op_commutes h.same_rep_cond_comm
    h.enumerable h.joinLaws

end LeanProofs.NoSpecNonComm.Metatheory
