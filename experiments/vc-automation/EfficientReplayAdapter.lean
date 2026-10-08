import InductiveMask
import ExpandedPolicy
import Sal.MRDTs.Paper1.ConcreteORSetRepresentation
import Sal.MRDTs.Paper1.GuardedOrder

/-! The existing efficient representation is a semantic relation, not a replay
constructor. This adapter derives its replay interpretation from generic fold
induction and finite operation certificates; it does not use the previous
datatype replay invariant or any merge-correctness theorem. -/
namespace EfficientReplayAdapter
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1
open Sal.MRDTs.Instances.EfficientORSet
open Classical
variable {α : Type} [DecidableEq α]

def birth (p : Record α) : Event α := (p.2.1,p.1,.add p.2.2)
def Born (p : Record α) (e : Event α) : Prop := e = birth p
def Kill (p : Record α) (e : Event α) : Prop := kills p.1 p.2.2 e

theorem update_certificate : InductiveMask.UpdateCertificate
    (update (α := α)) Born Kill := by
  constructor
  intro s e p
  rcases e with ⟨et,er,eo⟩
  rcases p with ⟨pr,pt,px⟩
  cases eo <;> simp [update,Born,birth,Kill,kills,Prod.mk.injEq] <;> grind only

theorem commutes_of_not_kill (p : Record α) (e : Event α)
    (notkill : ¬ Kill p e) : (D α).toUpdateSig.commutes (birth p) e := by
  intro s
  dsimp [D] at *
  rcases p with ⟨pr,pt,px⟩
  rcases e with ⟨et,er,eo⟩
  cases eo <;>
    ext q <;> simp [update,Kill,kills,birth] at * <;> grind only

theorem noncomm_of_kill (p : Record α) (e : Event α)
    (different : (birth p).time ≠ e.time) (kill : Kill p e) :
    ¬ (D α).toUpdateSig.commutes (birth p) e := by
  intro commute
  have h := commute (∅ : State α)
  rcases p with ⟨pr,pt,px⟩
  rcases e with ⟨et,er,eo⟩
  cases eo <;> simp_all [Kill,kills,D,update,birth,Op.time]
  have hm := Finset.ext_iff.mp h (pr,pt,px)
  simp [different] at hm

end EfficientReplayAdapter

namespace EfficientReplayAdapter
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1
open Sal.MRDTs.Instances.EfficientORSet Classical
variable {α : Type} [DecidableEq α]

private theorem supported_distinct (C : ReplayContext (D α).toUpdateSig)
    (b k : Event α) (hb : b ∈ C.events) (hk : k ∈ C.events) (ne : b ≠ k) :
    b.time ≠ k.time := by
  obtain ⟨r,A,head,member⟩ := hb
  obtain ⟨s,B,other,mem⟩ := hk
  exact C.timestamps_distinct head member other mem ne

/-- Event-level order evidence is derived from issuance comparability and the
new finite update/commutation certificates, not a state/history invariant. -/
theorem order_certificate (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Event α)) (support : ConcreteMRDT.Supported C E)
    (irrefl : ∀ e, ¬ C.vis e e) :
    InductiveMask.OrderCertificate Born Kill C.vis
      (fun b k => ¬ (D α).toUpdateSig.commutes b k)
      (fun b k => (EfficientORSet.EventSpec.conflict α).before b.op k.op) E := by
  constructor
  · exact irrefl
  · intro b k noncomm commute
    exact noncomm (fun s => (commute s).symm)
  · intro p b _ c _ hb hc
    exact hb.trans hc.symm
  · intro p b hb k hk born kill ne
    change b = birth p at born
    subst b
    exact noncomm_of_kill p k (supported_distinct C _ _ (support _ hb) (support _ hk) ne) kill
  · intro p b _ k _ born noncomm
    change b = birth p at born
    subst b
    by_contra notkill
    exact noncomm (commutes_of_not_kill p k notkill)
  · intro p b hb k hk born kill ne
    change b = birth p at born
    subst b
    rcases p with ⟨pr,pt,px⟩
    rcases k with ⟨kt,kr,ko⟩
    cases ko with
    | remove x =>
        change x = px at kill
        subst x
        exact Or.inr (Or.inr ⟨px,rfl,rfl⟩)
    | add x =>
        change kr = pr ∧ x = px at kill
        obtain ⟨rEq,xEq⟩ := kill
        subst kr; subst x
        obtain ⟨r,A,head,mem⟩ := support _ hb
        obtain ⟨s,B,other,member⟩ := support _ hk
        rcases C.vis_total_same_replica head mem other member ne rfl with forward | back
        · exact Or.inr (Or.inl forward)
        · exact Or.inl back

/-- Fresh generic fold induction reconstructs canonical replay from the ACTUAL
existing semantic representation. The previous sorted-fold state invariant and
all existing merge/VC proofs are absent from this derivation. -/
theorem representation_canonical (C : ReplayContext (D α).toUpdateSig)
    (E : Set (Event α)) (s : State α)
    (rep : EfficientORSet.ConcreteRep.representation C E s) :
    ConcreteMRDT.Canonical (EfficientORSet.EventSpec.conflict α) C E s := by
  obtain ⟨π,perm⟩ := rep.2.1
  have support := rep.2.2.1
  have trans := rep.2.2.2.1
  have mono := rep.2.2.2.2
  have irrefl : ∀ e, ¬ C.vis e e := by
    intro e self
    have impossible := mono e e self
    exact Nat.lt_irrefl _ impossible
  obtain ⟨ordered,permutation,ordering⟩ := GuardedReplay.exists_paperOrder_enumeration
    NeemExpansion.Efficient.expandedLaws (fun {a b c} ab bc => trans ab bc)
    irrefl support perm
  refine ⟨ordered,permutation,ordering,?_⟩
  apply Finset.ext
  intro p
  have generic := InductiveMask.replay_iff_alive update_certificate
    (order_certificate C E support irrefl) ordered permutation ordering p
  change p ∈ InductiveMask.run update ordered ↔ p ∈ s
  rw [generic,rep.1 p]
  unfold InductiveMask.Alive Born birth Kill live dead
  constructor
  · rintro ⟨b,hb,rfl,alive⟩
    exact ⟨hb,alive⟩
  · rintro ⟨member,alive⟩
    exact ⟨(p.2.1,p.1,.add p.2.2),member,rfl,alive⟩

end EfficientReplayAdapter
