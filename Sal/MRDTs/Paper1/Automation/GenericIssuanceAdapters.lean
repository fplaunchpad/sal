import Sal.MRDTs.Paper1.Automation.GenericCertifiedIssuance

/-! Finite issuance adapters independent of record layout and coordinate encoding. -/
namespace Sal.MRDTs.Paper1.Automation
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1

/-- Appending a positive delta preserves both entry validity and the timestamp sum.
This is the common arithmetic obligation of additive coordinate-chain issuers. -/
theorem append_delta_valid {Entry : Type} (delta : Entry → Nat) (valid : Entry → Prop)
    (xs : List Entry) (a t : Nat) (entry : Entry)
    (positive : ∀x∈xs,1≤delta x) (tags : ∀x∈xs,valid x)
    (sum : (xs.map delta).sum=a) (late : a<t)
    (entry_delta : delta entry=t-a) (entry_valid : valid entry) :
    (∀x∈xs++[entry],1≤delta x) ∧ (∀x∈xs++[entry],valid x) ∧
      ((xs++[entry]).map delta).sum=t := by
  refine ⟨?_,?_,?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with old | new
    · exact positive x old
    · simp only [List.mem_singleton] at new
      subst x; rw [entry_delta]; omega
  · intro x hx
    rcases List.mem_append.mp hx with old | new
    · exact tags x old
    · simp only [List.mem_singleton] at new
      subst x; exact entry_valid
  · simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,sum,entry_delta]
    omega

namespace CertifiedIssuance
variable {D : MRDTSig} {Record Live : Type} [DecidableEq Record]

/-- The zero target sentinel cannot denote an issued birth when valid records
have positive stamps. Thus local target provenance gives the archive creator
premise directly, retaining the original mint honesty assumption. -/
theorem creator_of_mint (K : Model D Record Live)
    (positive : ∀g,K.valid g → 0<K.stamp g)
    (C : Configuration D) (mint : MintHonest D K.guard C) :
    ∀d∈C.events,∀n,(∃e∈C.events,K.insertion e=true ∧ e.1=n) →
      K.target d n → ∃a∈C.events,C.vis a d ∧ K.insertion a=true ∧ a.1=n := by
  intro d hd n born kill
  rcases target_of_mint K C mint d hd n kill with zero | creator
  · obtain ⟨e,he,_,stamp⟩ := born
    have pos := positive (K.record e) (valid_of_mint K C mint e he)
    rw [K.record_stamp,stamp,zero] at pos
    omega
  · exact creator
end CertifiedIssuance
end Sal.MRDTs.Paper1.Automation
