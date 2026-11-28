import LeanProofs_no_spec_non_comm.Interface.VCRoute
import Artifact.MRDTs.Paper1.ConcreteJoin

/-!
# Part III: the five conditions at the full causal past

Parts I and II of `VCRoute.lean` both read an event's dependencies as its
`downset`, the backward closure of `vis` restricted to **non-commuting**
pairs. That is the smallest dependency set Section 5 could have chosen, and
for most rows it is the right one: a row whose state records only the
outcome of its conflicts needs nothing else.

A row with **cumulative single-writer cells** needs more. The bounded
counter is the case. Its merge is componentwise maximum, which recovers a
cumulative cell only from a state that already holds the earlier writes to
that cell, and the earlier writes commute with the later ones, so `downset`
discards exactly what the merge needs. `Implementations/BoundedCounter/Negative.lean`
proves VC4 false at that reading.

Enlarging the dependency set alone does not help, and the same file now
records why. `lo^C_E` relates only non-commuting pairs, so for a row where
everything commutes it is **empty**, and `PaperMaximalOn` is vacuously true
of every event of `E`. VC4 is then asked about the *first* increment of a
replica as readily as about the last, and the first increment has an empty
causal past under every reading.

So this part changes **both** halves at once, which is the one change the
framework was already built to accept. `ConcreteMRDT.MetadataDependencies`
parameterises the whole join induction over the dependency relation,
subject only to its sitting between `vis ∧ ¬commutes` and `vis`, and the
framework's `MergeVCs` carries a maximality hypothesis for the scheme
alongside the one for `lo^C_E`. Instantiating the scheme at `vis` therefore

* enlarges `downset` to the full causal past, and
* gives maximality teeth, as `CausalMaximalOn`.

Canonicity is **unchanged**: `IsPaperCan` still reads `lo^C_E`, because the
scheme indexes the induction, not the representation. So everything
downstream of the join lemma is shared with Part II, down to the entry
points of `Soundness/RALinearizability.lean`.

The price is one extra obligation, `CausalEnumerable`. The peel step needs
an enumeration respecting `lo^C_E` **and** `vis`, and
`GuardedReplay.exists_paperOrder_enumeration` delivers only the first. A
concurrent `rc` edge is terminal for `lo^C_E` precisely because its
absorber clause excludes non-commuting causal successors, and a *commuting*
causal successor is not excluded, so the union of the two relations is not
acyclic for free. `causalEnumerable_of_no_rc` discharges it for a row whose
`rc` is empty, which is the case this part exists to serve.
-/

namespace LeanProofs.NoSpecNonComm.Interface

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1

variable {type : MRDTType} (D : Impl type)

/-! ## The causal dependency scheme -/

/-- **The dependency scheme read at `vis` itself.** The two obligations
`MetadataDependencies` imposes are that every scheme edge is causal and
that every non-commuting causal edge is a scheme edge. Plain `vis` is the
largest relation satisfying both, as `vcScheme` is the smallest. -/
def causalScheme (C : Ctx D) :
    ConcreteMRDT.MetadataDependencies C where
  before a b := C.vis a b
  causal _ _ h := h
  covers _ _ hv _ := hv

/-- `e`'s full causal past, `e` included. -/
abbrev CausalPast (C : Ctx D) (e : D.Event) : Set D.Event :=
  (causalScheme D C).Past e

/-- `E` is closed under `vis` predecessors, commuting ones included. This is
the closure hypothesis the framework's `RepresentationJoin` already
carries, so Part III asks its rows for nothing Part II's rows are spared. -/
abbrev CausallyClosed (C : Ctx D) (E : Set D.Event) : Prop :=
  ∀ a b, C.vis a b → b ∈ E → a ∈ E

/-- **Maximality with teeth**: no event of `E` is causally after `e`. This
is the half `PaperMaximalOn` cannot supply for a row whose events all
commute. -/
abbrev CausalMaximalOn (C : Ctx D) (E : Set D.Event) (e : D.Event) : Prop :=
  ∀ x ∈ E, x ≠ e → ¬ C.vis e x

/-- Under `VisStrict` the transitive closure collapses, so the causal past
is the one-step one. Rows reason with this form. -/
theorem causalPast_eq {D : Impl type} {C : Ctx D} (hvs : VisStrict D C)
    (e : D.Event) :
    CausalPast D C e = {x | x = e ∨ C.vis x e} := by
  ext x
  constructor
  · rintro (rfl | h)
    · exact Or.inl rfl
    · refine Or.inr ?_
      induction h with
      | single h' => exact h'
      | tail _ h' ih => exact hvs.1 ih h'
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr (Relation.TransGen.single h)

/-- The punctured causal past is exactly the strict causal predecessors. -/
theorem causalPast_diff_eq {D : Impl type} {C : Ctx D} (hvs : VisStrict D C)
    (e : D.Event) :
    CausalPast D C e \ {e} = {x | C.vis x e} := by
  rw [causalPast_eq hvs]
  ext x
  simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨rfl | h, hne⟩
    · exact absurd rfl hne
    · exact h
  · exact fun h => ⟨Or.inr h, fun hx => hvs.2 e (hx ▸ h)⟩

/-! ## VC1 to VC5 at the causal past

Field for field the conditions of `PaperJoinLawsOn`, with three changes and
no others: `WeaklyClosed` becomes `CausallyClosed`, `downset` becomes
`CausalPast`, and each condition that names a maximal event receives
`CausalMaximalOn` beside `PaperMaximalOn`. -/

structure CausalJoinLawsOn (Good : Ctx D → Prop) : Prop where
  /-- **VC1** MERGE-COMM, over arbitrary states. -/
  vc1_merge_comm : ∀ l a b : D.Sigma, D.merge l a b = D.merge l b a
  /-- **VC2** MERGE-INIT. -/
  vc2_merge_init : ∀ (C : Ctx D) (E : Set D.Event) (s : D.Sigma),
    Good C → SupportedOn D C E → IsPaperCan D C E s →
    D.merge D.sigma0 D.sigma0 s = s
  /-- **VC3** LOCAL-REDISTRIBUTE, for a maximal `e` in `E1` only. -/
  vc3_local_redistribute : ∀ (C : Ctx D) (E₁ E₂ : Set D.Event)
    (l m x y : D.Sigma) (e : D.Event),
    Good C → VisStrict D C →
    SupportedOn D C E₁ → SupportedOn D C E₂ →
    CausallyClosed D C E₁ → CausallyClosed D C E₂ →
    e ∈ E₁ → e ∉ E₂ →
    PaperMaximalOn D C (E₁ ∪ E₂) e → CausalMaximalOn D C (E₁ ∪ E₂) e →
    IsPaperCan D C (E₁ ∩ E₂) l →
    IsPaperCan D C (CausalPast D C e \ {e}) m →
    IsPaperCan D C (E₁ \ {e}) x →
    IsPaperCan D C E₂ y →
    D.merge l (D.merge m x (D.do_ m e)) y
      = D.merge m (D.merge l x y) (D.do_ m e)
  /-- **VC4** CAUSAL-DELTA, for a maximal `e` of `E`. -/
  vc4_causal_delta : ∀ (C : Ctx D) (U : Set D.Event) (A B : D.Sigma)
    (e : D.Event),
    Good C → VisStrict D C →
    SupportedOn D C U → CausallyClosed D C U →
    e ∈ U → PaperMaximalOn D C U e → CausalMaximalOn D C U e →
    IsPaperCan D C (U \ {e}) A →
    IsPaperCan D C (CausalPast D C e \ {e}) B →
    D.merge B A (D.do_ B e) = D.do_ A e
  /-- **VC5** REDISTRIBUTE, for a maximal `e` in both branches. -/
  vc5_redistribute : ∀ (C : Ctx D) (E₁ E₂ : Set D.Event)
    (x₀ x₁ x₂ m : D.Sigma) (e : D.Event),
    Good C → VisStrict D C →
    SupportedOn D C E₁ → SupportedOn D C E₂ →
    CausallyClosed D C E₁ → CausallyClosed D C E₂ →
    e ∈ E₁ → e ∈ E₂ →
    PaperMaximalOn D C (E₁ ∪ E₂) e → CausalMaximalOn D C (E₁ ∪ E₂) e →
    IsPaperCan D C ((E₁ ∩ E₂) \ {e}) x₀ →
    IsPaperCan D C (CausalPast D C e \ {e}) m →
    IsPaperCan D C (E₁ \ {e}) x₁ →
    IsPaperCan D C (E₂ \ {e}) x₂ →
    D.merge (D.merge m x₀ (D.do_ m e)) (D.merge m x₁ (D.do_ m e))
        (D.merge m x₂ (D.do_ m e))
      = D.merge m (D.merge x₀ x₁ x₂) (D.do_ m e)

/-! ## The enumeration obligation

The peel step picks one event maximal for both relations at once, and it
gets it from a single enumeration respecting both. -/

/-- **A joint enumeration exists for every finite supported event set.**
Part II gets the `lo^C_E` half from `GuardedReplay`; the `vis` half has to
be asked for, because the union of the two relations is not acyclic on the
strength of `Laws(D_type)` alone. -/
def CausalEnumerable : Prop :=
  ∀ (C : Ctx D) (E : Set D.Event) (π : List D.Event),
    VisStrict D C → SupportedOn D C E → listPermOf π E →
    ∃ ρ, listPermOf ρ E ∧ respects ρ (paperOrder (policy D) C E) ∧
      respects ρ (fun a b : D.Event => C.vis a b)

/-- With no `rc` edges `lo^C_E` has no concurrent disjunct, so it is a
subrelation of `vis`. -/
theorem paperOrder_sub_vis {D : Impl type}
    (hrc : ∀ o₁ o₂ : type.OType, ¬ D.RcBefore o₁ o₂)
    {C : Ctx D} {E : Set D.Event} {a b : D.Event}
    (h : paperOrder (policy D) C E a b) : C.vis a b := by
  rcases h with ⟨hv, -⟩ | ⟨-, -, hp, -⟩
  · exact hv
  · exact absurd hp (hrc _ _)

/-- **The enumeration obligation for a row whose `rc` is empty.** A
topological sort of `vis` alone then respects both relations, since one
contains the other. -/
theorem causalEnumerable_of_no_rc {D : Impl type}
    (hrc : ∀ o₁ o₂ : type.OType, ¬ D.RcBefore o₁ o₂) : CausalEnumerable D := by
  intro C E π hvs _ hp
  obtain ⟨htr, hirr⟩ := hvs
  obtain ⟨ρ, hperm, hr⟩ := exists_respecting_perm
    (R := fun a b : D.Event => C.vis a b) (fun hab hbc => htr hab hbc) hirr π
  have hpE : listPermOf ρ E :=
    ⟨hperm.nodup hp.1, fun a => (hperm.mem_iff (a := a)).symm.trans (hp.2 a)⟩
  exact ⟨ρ, hpE, hr.imp (fun {_ _} hno hedge => hno (paperOrder_sub_vis hrc hedge)), hr⟩

/-! ## The bundle -/

/-- **The obligation bundle at the full causal past.** The three laws are
Part II's, unchanged. `joinLaws` is the five conditions at the enlarged
dependency set, `enumerable` is the one extra premise the enlargement
costs, and `executionOrder` is what the execution induction is indexed
by. -/
structure CausalObligationsOn (Good : Ctx D → Prop) : Prop where
  /-- `Laws(D_type)`: RC-NON-COMM, NO-RC-CHAIN and COND-COMM. -/
  laws : Laws D
  /-- The case RC-NON-COMM's `o1 /= o2` conjunct excludes. -/
  equal_op_commutes : EqualOpCommutes D
  /-- The case COND-COMM's replica guard excludes. -/
  same_rep_cond_comm : SameReplicaCondComm D
  /-- VC1 to VC5 of Section 5, at the full causal past. -/
  joinLaws : CausalJoinLawsOn D Good
  /-- Enumerations respecting `lo^C_E` and `vis` at once. -/
  enumerable : CausalEnumerable D
  /-- The order the execution induction is indexed by. -/
  executionOrder : Nonempty (ExecutionOrder D)

/-- **The bundle at every context.** -/
abbrev CausalObligations : Prop :=
  CausalObligationsOn D (fun _ => True)

end LeanProofs.NoSpecNonComm.Interface
