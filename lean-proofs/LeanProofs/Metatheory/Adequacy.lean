import LeanProofs.Interface.VCRoute
import LeanProofs.Interface.DirectRoute
import Artifact.MRDTs.Metatheory.Correctness

/-!
# Adequacy: the obligations imply the join lemma

Proved once, for every implementation. No datatype is named here and no
implementation may add to this file.

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
`Obligations` below adds, for the all-commuting family, the facts that make
`Laws` and VC4 cheap to prove. It does not make them free.

Not every row satisfies the arbitrary-state VCs of `CanonicalJoinLaws`. An
implementation outside that family proves `Join` directly, at `rcOrder`, and
passes it to `Soundness` itself. Both routes end at the same statement, so
nothing downstream can tell them apart.
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

/-- The join lemma for the all-commuting family. -/
theorem joinLemma (h : Obligations D) : @Join D.toMRDTSig (rcOrder D) :=
  joinLemma_of_vcs h.laws h.rc_non_comm h.cond_comm h.joinLaws

end LeanProofs.Metatheory
