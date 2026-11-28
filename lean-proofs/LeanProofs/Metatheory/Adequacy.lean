import LeanProofs_no_spec_non_comm.Interface.VCRoute
import Artifact.MRDTs.Metatheory.Correctness
import Artifact.MRDTs.Paper1.ConcreteJoin
import Artifact.MRDTs.Paper1.CertifiedClosedExecution

/-!
# Adequacy

Proved once, for every implementation. No datatype is named here and no
implementation may add to this file.

```
  Laws(D_type)  +  VC1..VC5 at lo^C_E        per implementation
      |
      v
  the join lemma                             merging canonical states is
      |                                      canonical
      v
  every stored version holds can(E(v))       along every certified execution
```

Both steps are the framework's, run at the representation
`can^C(E) = s`. The first is the five-VC induction of `ConcreteMRDT.Raw`;
the second is the execution induction of `CertifiedClosedExecution`, which
is indexed by an `EventOrder` and so is reached through the row's
`ExecutionOrder`.

Canonicity is read at the relation Section 4 displays, which is Part II of
`Interface/VCRoute.lean`, rather than at the one the framework builds from
`rc`. That is what lets the chain run on `GuardedReplay.Laws` and so keep
the paper's guards on RC-NON-COMM: `rc` is consulted only about pairs with
distinct timestamps issued by different replicas.

Nothing here consults `Spec`. As the paper says, the canonical join laws
alone do not establish conformance; `Soundness/` adds `AnyOrderSound` for that.

-/

namespace LeanProofs.NoSpecNonComm.Metatheory

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

variable {type : MRDTType} {D : Impl type}

/-! ## The dependency scheme both readings are built on -/

/-- The metadata scheme: a `vis` edge between non-commuting events, which is
the relation `downset` is the backward closure of. -/
def vcScheme (D : Impl type) (C : Ctx D) :
    ConcreteMRDT.MetadataDependencies C :=
  ConcreteMRDT.MetadataDependencies.ofConcrete C

/-- `vcScheme`'s edges are `lo^C_E` edges. -/
theorem metadata_of_paperOrder {C : Ctx D} {E : Set D.Event} {a b : D.Event}
    (h : (vcScheme D C).before a b) : paperOrder (policy D) C E a b :=
  Or.inl h

/-- **A finite nonempty event set has a maximal event**, maximal both for
`lo^C_E` and for the dependency scheme. The second follows from the first:
every scheme edge is a `lo^C_E` edge. -/
theorem exists_paperMaximal (hl : GuardedReplay.Laws D.toMRDTSig.toUpdateSig (policy D))
    {C : Ctx D} {E : Set D.Event} {π : List D.Event}
    (htr : Transitive C.vis) (hirr : ∀ x : D.Event, ¬ C.vis x x)
    (hsup : SupportedOn D C E) (hp : listPermOf π E) (hne : E.Nonempty) :
    ∃ e ∈ E, PaperMaximalOn D C E e ∧
      ∀ x ∈ E, x ≠ e → ¬ (vcScheme D C).before e x := by
  obtain ⟨ρ, hρ, hr⟩ := GuardedReplay.exists_paperOrder_enumeration hl
    (fun {_ _ _} hab hbc => htr hab hbc) hirr hsup hp
  exact ConcreteMRDT.joint_maximal_of_enumeration ρ hρ hne hr
    (hr.imp (fun {_ _} hno hedge => hno (metadata_of_paperOrder hedge)))

/-! ## The representation

`can^C(E) = s`, together with the record that `E` is observed in `C`. The
framework's induction is indexed by a representation rather than by a
canonicity predicate, and this is the one that makes the two agree. -/

/-- **The representation the induction runs on**: the canonical state of a
supported event set, read at `lo^C_E`. -/
def paperRepresentation (D : Impl type) (Good : Ctx D → Prop) :
    ConcreteMRDT.Representation D.toMRDTSig :=
  fun C E s => IsPaperCan D C E s ∧ SupportedOn D C E ∧ Good C

/-- Canonical states at `lo^C_E` are unique, which is the framework's
convergence theorem for the guarded contract. -/
theorem paperRepresentation_unique
    (hl : GuardedReplay.Laws D.toMRDTSig.toUpdateSig (policy D)) :
    ConcreteMRDT.Raw.Unique (paperRepresentation D Good) :=
  fun _ _ _ _ ha hb => ConcreteMRDT.canonical_unique hl _ _ ha.2.1 ha.1 hb.1

/-- A representation carries an enumeration, hence a finite event set. -/
theorem paperRepresentation_finite {Good : Ctx D → Prop} {C : Ctx D}
    {E : Set D.Event} {s : D.Sigma}
    (hs : paperRepresentation D Good C E s) : ∃ π, listPermOf π E := by
  obtain ⟨π, hp, -, -⟩ := hs.1
  exact ⟨π, hp⟩

/-- An enumerated set is finite. -/
theorem finite_of_listPermOf {E : Set D.Event} {π : List D.Event}
    (hp : listPermOf π E) : E.Finite := by
  classical
  have : E = (↑π.toFinset : Set D.Event) := by
    ext x; simpa using (hp.2 x).symm
  rw [this]
  exact π.toFinset.finite_toSet

/-- Every supported finite event set has a canonical state. -/
theorem paperRepresentation_supply
    (hl : GuardedReplay.Laws D.toMRDTSig.toUpdateSig (policy D))
    {C : Ctx D} (htr : Transitive C.vis) (hirr : ∀ x : D.Event, ¬ C.vis x x)
    {Good : Ctx D → Prop} (hgood : Good C)
    {E : Set D.Event} {π : List D.Event} (hp : listPermOf π E)
    (hsup : SupportedOn D C E) : ∃ s, paperRepresentation D Good C E s := by
  obtain ⟨s, hs⟩ := ConcreteMRDT.canonical_exists hl C E (finite_of_listPermOf hp)
    hsup (fun {_ _ _} hab hbc => htr hab hbc) hirr
  exact ⟨s, hs, hsup, hgood⟩

/-- **The peel step.** A nonempty weakly closed set has a maximal event
whose removal leaves a canonical state, whose downset has one, and which
reconstructs both by one application. -/
theorem paperReplaySupply (hl : GuardedReplay.Laws D.toMRDTSig.toUpdateSig (policy D))
    (C : Ctx D) (htr : Transitive C.vis) (hirr : ∀ x : D.Event, ¬ C.vis x x)
    {Good : Ctx D → Prop} (hgood : Good C) :
    ConcreteMRDT.Raw.ReplaySupply (policy D) (paperRepresentation D Good)
      (vcScheme D) C := by
  refine ⟨fun E π hp hsup => paperRepresentation_supply hl htr hirr hgood hp hsup, ?_⟩
  intro E s hs hsup hne hcl
  obtain ⟨π, hp⟩ := paperRepresentation_finite hs
  obtain ⟨e, heE, hmax, hmeta⟩ := exists_paperMaximal hl htr hirr hsup hp hne
  have hpast : (vcScheme D C).Past e ⊆ E :=
    (vcScheme D C).past_subset E e hcl heE
  obtain ⟨ρ, hρ⟩ := ConcreteMRDT.enumeration_subset hp (show E \ {e} ⊆ E from Set.diff_subset)
  obtain ⟨τ, hτ⟩ := ConcreteMRDT.enumeration_subset hp
    (show (vcScheme D C).Past e \ {e} ⊆ E from fun _ hx => hpast hx.1)
  obtain ⟨A, hA⟩ := paperRepresentation_supply hl htr hirr hgood hρ
    (fun a ha => hsup a ha.1)
  obtain ⟨B, hB⟩ := paperRepresentation_supply hl htr hirr hgood hτ
    (fun a ha => hsup a (hpast ha.1))
  refine ⟨⟨e, heE, hmax, hmeta, A, B, hA, hB, ?_, ?_⟩⟩
  · exact ⟨isPaperCan_snoc (Or.inl rfl)
      ((vcScheme D C).past_semantic_maximal (policy D)
        htr hirr e) hB.1, fun a ha => hsup a (hpast ha), hgood⟩
  · exact ⟨isPaperCan_snoc heE hmax hA.1, hsup, hgood⟩

/-! ## The join lemma -/

/-- **VC1 to VC5 as the framework's representation-indexed bundle.** Each
field is the row's own condition, passed through unchanged. Unlike the
route of `Metatheory/Adequacy.lean` there is no translation step on the way
in: the conditions already speak about `lo^C_E`, which is the relation the
framework's induction uses. -/
theorem paperMergeVCs {Good : Ctx D → Prop} (vcs : PaperJoinLawsOn D Good) :
    ConcreteMRDT.Raw.MergeVCs (policy D) (paperRepresentation D Good)
      (vcScheme D) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _ l a b _ _ _ _ _ _ _
    exact vcs.vc1_merge_comm l a b
  · intro C' E s hsup _ hrep
    exact vcs.vc2_merge_init C' E s hrep.2.2 hsup hrep.1
  · intro C' U s B e htr hirr hsup hcl heU hsem _ hs hB _ _
    exact vcs.vc4_causal_delta C' U s B e hs.2.2
      ⟨fun {_ _ _} hab hbc => htr hab hbc, hirr⟩
      hsup (fun a b hv hnc hb => hcl a b ⟨hv, hnc⟩ hb) heU hsem hs.1 hB.1
  · intro C' E₁ E₂ l B t b e ctx he₁ he₂ hl hB ht hb _ _ _
    exact vcs.vc3_local_redistribute C' E₁ E₂ l B t b e hl.2.2
      ⟨fun {_ _ _} hab hbc => ctx.trans hab hbc, ctx.irrefl⟩
      ctx.supported₁ ctx.supported₂
      (fun a b' hv hnc hb' => ctx.closed₁ a b' ⟨hv, hnc⟩ hb')
      (fun a b' hv hnc hb' => ctx.closed₂ a b' ⟨hv, hnc⟩ hb')
      he₁ he₂ ctx.semantic hl.1 hB.1 ht.1 hb.1
  · intro C' E₁ E₂ t₀ t₁ t₂ B e ctx he₁ he₂ h₀ hB h₁ h₂ _ _ _ _ _
    exact vcs.vc5_redistribute C' E₁ E₂ t₀ t₁ t₂ B e h₀.2.2
      ⟨fun {_ _ _} hab hbc => ctx.trans hab hbc, ctx.irrefl⟩
      ctx.supported₁ ctx.supported₂
      (fun a b' hv hnc hb' => ctx.closed₁ a b' ⟨hv, hnc⟩ hb')
      (fun a b' hv hnc hb' => ctx.closed₂ a b' ⟨hv, hnc⟩ hb')
      he₁ he₂ ctx.semantic h₀.1 hB.1 h₁.1 h₂.1

/-- **The join lemma** from the five conditions: merging canonical states
produces the canonical state of the union of their event sets.

The statement is the paper's, at `lo^C_E`. `representationJoin_of_paperJoin` below
puts it back in the shape the framework's inductions consume. -/
theorem paperJoin_of_vcs {Good : Ctx D → Prop} (h : Laws D)
    (hself : EqualOpCommutes D) (hsame : SameReplicaCondComm D)
    (vcs : PaperJoinLawsOn D Good) : PaperJoinOn D Good := by
  have hl := guardedLaws h hself hsame
  have raw : ConcreteMRDT.RepresentationJoin (paperRepresentation D Good) := by
    refine ConcreteMRDT.Raw.representationJoin_of_vcs (paperMergeVCs vcs)
      (paperRepresentation_unique hl) ?_
      (fun _ _ _ hs => paperRepresentation_finite hs) ?_
    · intro _ _ _ hs
      exact ⟨⟨[], ⟨List.nodup_nil, by simp⟩, List.Pairwise.nil, rfl⟩,
        fun a ha => absurd ha (by simp), hs.2.2⟩
    · intro C' _ _ _ _ htr hirr _ _ ha _
      exact paperReplaySupply hl C' htr hirr ha.2.2
  intro C E₁ E₂ l a b hgood hvs h₁ h₂ c₁ c₂ hl' ha hb
  have htr : Transitive C.vis := by
    intro x y z hxy hyz; exact hvs.1 hxy hyz
  exact (raw C E₁ E₂ l a b htr hvs.2 h₁ h₂ c₁ c₂
    ⟨hl', fun x hx => h₁ x hx.1, hgood⟩ ⟨ha, h₁, hgood⟩ ⟨hb, h₂, hgood⟩).1

/-- **The join lemma from the bundle.** Every row obtains it this way. -/
theorem joinLemma {Good : Ctx D → Prop} (h : ObligationsOn D Good) :
    PaperJoinOn D Good :=
  paperJoin_of_vcs h.laws h.equal_op_commutes h.same_rep_cond_comm h.joinLaws

/-- The join lemma as the framework's representation-indexed statement,
which is what the execution induction below runs on. -/
theorem representationJoin_of_paperJoin {Good : Ctx D → Prop}
    (h : PaperJoinOn D Good) :
    ConcreteMRDT.RepresentationJoin (paperRepresentation D Good) := by
  intro C E₁ E₂ l a b htr hirr h₁ h₂ c₁ c₂ hl ha hb
  refine ⟨h C E₁ E₂ l a b hl.2.2 ⟨fun {_ _ _} hxy hyz => htr hxy hyz, hirr⟩
    h₁ h₂ c₁ c₂ hl.1 ha.1 hb.1, ?_, hl.2.2⟩
  rintro x (hx | hx) <;> [exact h₁ x hx; exact h₂ x hx]

/-! ## From the join lemma to the stored versions

Clause 1 asks for the canonical state at every version a certified execution
allocates, and the framework proves that by an induction over executions. The
induction is indexed by an `EventOrder`, not by the displayed `lo^C_E`, which
is what the row's execution order is for: on the events a context observes it
makes the two relations coincide. -/

section Execution

variable (X : ExecutionOrder D)

/-- **The two relations agree on observed events.** The framework's `loOn`
consults the execution order where the displayed relation reads
`~(e1 <-> e2)`, and the execution order is exact, so the two disjuncts match
clause for clause. -/
theorem loOn_iff_paperOrder (C : Ctx D) (E : Set D.Event)
    (hsup : SupportedOn D C E) (a b : D.Event) (ha : a ∈ E) (hb : b ∈ E) :
    @loOn D.toMRDTSig.toUpdateSig X.order C E a b
      ↔ paperOrder (policy D) C E a b := by
  have hab := X.exact C a b (hsup a ha) (hsup b hb)
  have hbz : ∀ z ∈ E,
      (@UpdateSig.replayBefore D.toMRDTSig.toUpdateSig X.order b z ∨
        @UpdateSig.replayBefore D.toMRDTSig.toUpdateSig X.order z b)
        ↔ ¬ D.Commutes b z :=
    fun z hz => (X.exact C b z (hsup b hb) (hsup z hz)).symm
  simp only [loOn, paperOrder, ← hab]
  constructor
  · rintro (hc | ⟨hf, hbk, hedge, hfree⟩)
    · exact Or.inl hc
    · exact Or.inr ⟨hf, hbk, (X.concurrent C a b (hsup a ha) (hsup b hb) hf hbk).mp hedge,
        fun ⟨z, hz, hv, hnc⟩ => hfree ⟨z, hz, hv, (hbz z hz).mpr hnc⟩⟩
  · rintro (hc | ⟨hf, hbk, hedge, hfree⟩)
    · exact Or.inl hc
    · exact Or.inr ⟨hf, hbk, (X.concurrent C a b (hsup a ha) (hsup b hb) hf hbk).mpr hedge,
        fun ⟨z, hz, hv, hnc⟩ => hfree ⟨z, hz, hv, (hbz z hz).mp hnc⟩⟩

/-- Hence the two canonicity predicates agree on supported event sets. -/
theorem isCanonicalState_iff_isPaperCan (C : Ctx D) (E : Set D.Event)
    (hsup : SupportedOn D C E) (s : D.Sigma) :
    @IsCanonicalState D.toMRDTSig.toUpdateSig X.order C E s ↔ IsPaperCan D C E s := by
  constructor
  · rintro ⟨π, hp, hr, hf⟩
    refine ⟨π, hp, hr.imp_of_mem ?_, hf⟩
    intro a b ha hb hno hedge
    exact hno ((loOn_iff_paperOrder X C E hsup b a ((hp.2 b).mp hb)
      ((hp.2 a).mp ha)).mpr hedge)
  · rintro ⟨π, hp, hr, hf⟩
    refine ⟨π, hp, hr.imp_of_mem ?_, hf⟩
    intro a b ha hb hno hedge
    exact hno ((loOn_iff_paperOrder X C E hsup b a ((hp.2 b).mp hb)
      ((hp.2 a).mp ha)).mp hedge)

/-- The join lemma, in the shape the execution induction consumes. A
context the guard admits is what the representation carries, so the caller
supplies it. -/
theorem closedJoinAt_of_paperJoin {Good : Ctx D → Prop}
    (join : ConcreteMRDT.RepresentationJoin (paperRepresentation D Good))
    (C : Ctx D) (hgood : Good C) :
    @CertifiedClosedExecution.ClosedJoinAt D.toMRDTSig X.order C := by
  intro E₁ E₂ l a b htr hirr hsup₁ hsup₂ hcl₁ hcl₂ hl ha hb
  have hsup₀ : SupportedOn D C (E₁ ∩ E₂) := fun x hx => hsup₁ x hx.1
  have hsupU : SupportedOn D C (E₁ ∪ E₂) := by
    rintro x (hx | hx) <;> [exact hsup₁ x hx; exact hsup₂ x hx]
  have merged := join C E₁ E₂ l a b (fun {_ _ _} hab hbc => htr hab hbc) hirr
    hsup₁ hsup₂ (fun e f hv hf => hcl₁ e f hv hf) (fun e f hv hf => hcl₂ e f hv hf)
    ⟨(isCanonicalState_iff_isPaperCan X C _ hsup₀ l).mp hl, hsup₀, hgood⟩
    ⟨(isCanonicalState_iff_isPaperCan X C _ hsup₁ a).mp ha, hsup₁, hgood⟩
    ⟨(isCanonicalState_iff_isPaperCan X C _ hsup₂ b).mp hb, hsup₂, hgood⟩
  exact (isCanonicalState_iff_isPaperCan X C _ hsupU _).mpr merged.1

/-- **The canonical configuration**, at the execution order. This is the
framework's induction over certified executions, run at an order that
agrees with `lo^C_E` on everything a context observes.

`good` is where an issuance guard is read: every configuration a certified
execution reaches presents a context the guard admits. -/
theorem paperCanonicalConfig (X : ExecutionOrder D) {Good : Ctx D → Prop}
    {I : Issuance D.toMRDTSig}
    (join : ConcreteMRDT.RepresentationJoin (paperRepresentation D Good))
    (good : ∀ C : Configuration D.toMRDTSig,
      MintHonest D.toMRDTSig I.CanIssue C → Good C.replayContext)
    {C : Configuration D.toMRDTSig}
    (reach : MintCertifiedReachV D.toMRDTSig
      (canonicalVirtualMergeBase D.toMRDTSig) I C) :
    @CanonicalConfig D.toMRDTSig X.order C := by
  letI : EventOrder D.toMRDTSig.toUpdateSig := X.order
  exact CertifiedClosedExecution.canonicalConfig_of_mintCertifiedV
    (fun C' hm => closedJoinAt_of_paperJoin X join C'.replayContext (good C' hm))
    reach

/-- **Every stored version holds `can^C(E(v))`.** This is clause 1 of
Definition 4, and the only place the execution order appears. -/
theorem paperCanonicalVersions (X : ExecutionOrder D) {Good : Ctx D → Prop}
    {I : Issuance D.toMRDTSig}
    (join : ConcreteMRDT.RepresentationJoin (paperRepresentation D Good))
    (good : ∀ C : Configuration D.toMRDTSig,
      MintHonest D.toMRDTSig I.CanIssue C → Good C.replayContext)
    {C : Configuration D.toMRDTSig}
    (reach : MintCertifiedReachV D.toMRDTSig
      (canonicalVirtualMergeBase D.toMRDTSig) I C)
    (v : Version) (s : D.Sigma) (E : Set D.Event) (hv : C.ver v = some (s, E)) :
    IsPaperCan D C.replayContext E s := by
  letI : EventOrder D.toMRDTSig.toUpdateSig := X.order
  have hgood := paperCanonicalConfig X join good reach
  exact (isCanonicalState_iff_isPaperCan X C.replayContext E
    (hgood.version_events_supported v s E hv) s).mp (hgood.canonical v s E hv)

end Execution

/-! ## The framework's replay contract -/

/-- `Laws(D_type)` is the framework's replay contract, at the framework's
reading. RC-NON-COMM supplies `noncomm_covered`, NO-RC-CHAIN supplies
acyclicity, COND-COMM supplies the absorber clause. A row that proves its
five conditions at `IsCanOn` uses this to build the canonical states those
conditions are stated about. -/
theorem replayLaws (h : Laws D) (hru : UniformRcNonComm D) (hcc : UniformCondComm D) :
    @ReplayLaws D.toMRDTSig.toUpdateSig (rcOrder D) :=
  (h.toRestricted hru hcc).replayLaws

end LeanProofs.NoSpecNonComm.Metatheory
