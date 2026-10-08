import InductiveSupplement
import LocalExpansion

/-! Actual causal-delta equation induction. A local strict predecessor is a
new finite leaf. A last bad local event is retained as a frozen event until a
later absorber resets the equation; the remaining suffix then preserves it. -/
namespace NeemExpansion.Signature
open Sal.MRDTs.Foundation Classical

def CausalEquation (D : Signature) (B s : D.State) (e : Op D.AppOp) : Prop :=
  D.merge B s (D.step B e) = D.step s e

def causal_strict_kernel (D : Signature) : Prop := ∀ B s e h,
  D.FreshEquation B e → D.CausalEquation B s e →
  D.order h e = .Fst_then_snd → D.CausalEquation B (D.step s h) e

def Good (D : Signature) (e h : Op D.AppOp) : Prop :=
  D.Commutes e h ∨ D.order h e = .Fst_then_snd

def Bad (D : Signature) (B S : Set (Op D.AppOp)) (e h : Op D.AppOp) : Prop :=
  h ∈ S ∧ h ∉ B ∧ ¬ D.Good e h

private theorem last_bad {β : Type} (bad : β → Prop) (π : List β) :
    (∀ h ∈ π, ¬ bad h) ∨
    ∃ pre h post, π = pre ++ h :: post ∧ bad h ∧ ∀ q ∈ post, ¬ bad q := by
  induction π using List.reverseRecOn with
  | nil => exact Or.inl (by simp)
  | append_singleton π h ih =>
    by_cases bh : bad h
    · exact Or.inr ⟨π,h,[],by simp,bh,by simp⟩
    · rcases ih with all | ⟨pre,q,post,eq,bq,after⟩
      · refine Or.inl ?_
        intro x hx
        rcases List.mem_append.mp hx with old | last
        · exact all x old
        · exact List.mem_singleton.mp last ▸ bh
      · refine Or.inr ⟨pre,q,post ++ [h],by simp [eq,List.append_assoc],bq,?_⟩
        intro x hx
        rcases List.mem_append.mp hx with old | last
        · exact after x old
        · exact List.mem_singleton.mp last ▸ bh

theorem causal_restricted_step (D : Signature)
    (common : D.causal_common_kernel) (commuting : D.causal_commuting_kernel)
    (strict : D.causal_strict_kernel) (B S : Set (Op D.AppOp)) (subset : B ⊆ S)
    (e h : Op D.AppOp) (π : List (Op D.AppOp))
    (fresh : D.FreshEquation (D.restrictedReplay π B) e)
    (previous : D.CausalEquation (D.restrictedReplay π B) (D.restrictedReplay π S) e)
    (good : h ∈ S → h ∉ B → D.Good e h) :
    D.CausalEquation (D.restrictedReplay (π ++ [h]) B)
      (D.restrictedReplay (π ++ [h]) S) e := by
  rw [restrictedReplay_append,restrictedReplay_append]
  by_cases hb : h ∈ B
  · simp only [hb,subset hb,if_true]
    exact common _ _ e h previous
  · by_cases hs : h ∈ S
    · simp only [hb,hs,if_true,if_false]
      rcases good hs hb with commute | prior
      · exact commuting _ _ e h commute previous
      · exact strict _ _ e h fresh previous prior
    · simpa only [hb,hs,if_false] using previous

theorem causal_good_tail (D : Signature)
    (common : D.causal_common_kernel) (commuting : D.causal_commuting_kernel)
    (strict : D.causal_strict_kernel) (freshBase : D.fresh_base)
    (freshStep : D.fresh_step) (B S : Set (Op D.AppOp)) (subset : B ⊆ S)
    (e : Op D.AppOp) (pre tail : List (Op D.AppOp))
    (previous : D.CausalEquation (D.restrictedReplay pre B) (D.restrictedReplay pre S) e)
    (fresh : ∀ h ∈ pre ++ tail, D.distinct e h)
    (good : ∀ h ∈ tail, h ∈ S → h ∉ B → D.Good e h) :
    D.CausalEquation (D.restrictedReplay (pre ++ tail) B)
      (D.restrictedReplay (pre ++ tail) S) e := by
  induction tail using List.reverseRecOn with
  | nil => simpa using previous
  | append_singleton tail h ih =>
    have freshOld : ∀ q ∈ pre ++ tail, D.distinct e q :=
      fun q hq => fresh q (by simp only [List.mem_append] at *; tauto)
    have prior := ih freshOld
      (fun q hq => good q (List.mem_append_left [h] hq))
    have freshB := D.fresh_restrictedReplay freshBase freshStep (pre ++ tail) B e freshOld
    simpa only [← List.append_assoc] using D.causal_restricted_step common commuting strict
      B S subset e h (pre ++ tail) freshB prior (good h (by simp))

/-- Last-bad-event coverage. `reset` is exclusively an event/list obligation:
the later visible defeater lies outside B and gives the frozen absorber leaf.
The equation before that reset is deliberately not assumed. -/
theorem causal_restrictedReplay (D : Signature)
    (base : ∀ e, D.CausalEquation D.init D.init e)
    (common : D.causal_common_kernel) (commuting : D.causal_commuting_kernel)
    (strict : D.causal_strict_kernel) (absorber : D.causal_absorber_kernel)
    (freshBase : D.fresh_base) (freshStep : D.fresh_step)
    (B S : Set (Op D.AppOp)) (subset : B ⊆ S) (e : Op D.AppOp)
    (π : List (Op D.AppOp)) (fresh : ∀ h ∈ π, D.distinct e h)
    (reset : ∀ pre h post, π = pre ++ h :: post → D.Bad B S e h →
      (∀ q ∈ post, ¬ D.Bad B S e q) →
      ∃ mid c tail, post = mid ++ c :: tail ∧ c ∈ S ∧ c ∉ B ∧
        D.order e h = .Fst_then_snd ∧ D.order c h = .Fst_then_snd) :
    D.CausalEquation (D.restrictedReplay π B) (D.restrictedReplay π S) e := by
  rcases last_bad (D.Bad B S e) π with clean | ⟨pre,h,post,eq,bad,clean⟩
  · have initial : D.CausalEquation (D.restrictedReplay [] B) (D.restrictedReplay [] S) e :=
      base e
    exact D.causal_good_tail common commuting strict freshBase freshStep B S subset e [] π
      initial (by simpa using fresh) (by
        intro h hh hs hb
        by_contra failure
        exact clean h hh ⟨hs,hb,failure⟩)
  · obtain ⟨mid,c,tail,postEq,cS,cB,eh,ch⟩ := reset pre h post eq bad clean
    let ρ := pre ++ h :: mid
    have partition : π = (ρ ++ [c]) ++ tail := by
      simp [ρ,eq,postEq,List.append_assoc]
    have atReset : D.CausalEquation (D.restrictedReplay (ρ ++ [c]) B)
        (D.restrictedReplay (ρ ++ [c]) S) e := by
      rw [restrictedReplay_append,restrictedReplay_append]
      simp only [cS,cB,if_true,if_false]
      exact absorber _ _ e c h eh ch
    rw [partition]
    apply D.causal_good_tail common commuting strict freshBase freshStep B S subset e
      (ρ ++ [c]) tail atReset
    · simpa only [partition] using fresh
    · intro q hq qs qb
      by_contra failure
      exact clean q (by simp [postEq,hq]) ⟨qs,qb,failure⟩

theorem causal_base_of_diagonal (D : Signature) (comm : D.comm)
    (diagonal : ∀ l a, D.merge l a l = a) (e : Op D.AppOp) :
    D.CausalEquation D.init D.init e := by
  unfold CausalEquation
  rw [comm D.init D.init _,diagonal]

end NeemExpansion.Signature

namespace NeemExpansion.Exact
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1.ORSet
variable {α : Type} [DecidableEq α]
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
theorem trial : (signature (α := α)).causal_strict_kernel := by
  intro B s e h fresh ih prior
  dsimp [Signature.CausalEquation,Signature.FreshEquation,signature] at *
  rcases e with ⟨et,er,eo⟩; rcases h with ⟨ht,hr,ho⟩
  cases eo <;> cases ho <;> ext p <;>
    have hf := Finset.ext_iff.mp fresh p <;>
    have hi := Finset.ext_iff.mp ih p <;>
    simp [order,merge,step] at *
  -- SOLVER
end NeemExpansion.Exact
