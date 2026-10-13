import Sal.MRDTs.Paper1.Automation.InductiveMask
import Sal.MRDTs.Paper1.GuardedOrder

/-! Generic recovery of policy-ordered replay from a birth/kill semantic
representation. The only implementation inputs are finite update projection,
birth/kill commutation and killer shape; contextual ordering uses the actual
ReplayContext's timestamp uniqueness and same-replica comparability. -/
namespace Sal.MRDTs.Paper1.Automation.MaskCanonical
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1
open Classical

structure Kit (D : MRDTSig) (P : OperationPolicy D.AppOp) (Record : Type)
    [DecidableEq Record] where
  carrier : D.State → Finset Record
  step : Finset Record → Op D.AppOp → Finset Record
  birth : Record → Op D.AppOp
  kill : Record → Op D.AppOp → Prop
  injective : Function.Injective carrier
  empty : carrier D.init = ∅
  projection : ∀s e,carrier (D.update s e)=step (carrier s) e
  update : InductiveMask.UpdateCertificate step (fun p e=>e=birth p) kill
  commutes_notkill : ∀p e,¬kill p e→D.toUpdateSig.commutes (birth p) e
  noncomm_kill : ∀p e,(birth p).time≠e.time→kill p e→¬D.toUpdateSig.commutes (birth p) e
  killer_shape : ∀p e,kill p e→(birth p).rep=e.rep ∨ P.before e.op (birth p).op

variable {D : MRDTSig} {P : OperationPolicy D.AppOp} {Record : Type} [DecidableEq Record]
variable (K : Kit D P Record)

theorem order_certificate (C : ReplayContext D.toUpdateSig) (H : Set (Op D.AppOp))
    (support : ConcreteMRDT.Supported C H) (irrefl : ∀e,¬C.vis e e) :
    InductiveMask.OrderCertificate (fun p e=>e=K.birth p) K.kill C.vis
      (fun a b=>¬D.toUpdateSig.commutes a b) (fun a b=>P.before a.op b.op) H := by
  constructor
  · exact irrefl
  · intro a b hn hc; exact hn (fun s => (hc s).symm)
  · intro p b _ c _ hb hc; exact hb.trans hc.symm
  · intro p b hb e he born kill ne
    subst b
    apply K.noncomm_kill p e
    · intro time
      exact ne (C.ts_unique (support _ hb) (support _ he) time)
    · exact kill
  · intro p b _ e _ born noncomm
    subst b
    by_contra notkill
    exact noncomm (K.commutes_notkill p e notkill)
  · intro p b hb e he born kill ne
    subst b
    rcases K.killer_shape p e kill with same | prior
    · obtain ⟨r,A,head,member⟩ := support _ hb
      obtain ⟨q,B,other,mem⟩ := support _ he
      rcases C.vis_total_same_replica head member other mem ne same with forward | back
      · exact Or.inr (Or.inl forward)
      · exact Or.inl back
    · exact Or.inr (Or.inr prior)

theorem projection_run (xs : List (Op D.AppOp)) :
    K.carrier (applySeq D.toUpdateSig D.init xs) = InductiveMask.run K.step xs := by
  induction xs using List.reverseRecOn with
  | nil => exact K.empty
  | append_singleton xs e ih =>
    rw [applySeq_append_single,K.projection,ih]
    simp only [InductiveMask.run,List.foldl_append,List.foldl_cons,List.foldl_nil]

def Shape (C : ReplayContext D.toUpdateSig) (H : Set (Op D.AppOp)) (s : D.State) : Prop :=
  (∃xs,listPermOf xs H) ∧ ConcreteMRDT.Supported C H ∧ Transitive C.vis ∧
    (∀e,¬C.vis e e) ∧ ∀p,p∈K.carrier s ↔
      InductiveMask.Alive (fun p e=>e=K.birth p) K.kill C.vis H p

theorem canonical (laws : GuardedReplay.Laws D.toUpdateSig P)
    (C : ReplayContext D.toUpdateSig) (H : Set (Op D.AppOp)) (s : D.State)
    (rep : Shape K C H s) : ConcreteMRDT.Canonical P C H s := by
  obtain ⟨xs,perm⟩ := rep.1
  obtain ⟨ys,permutation,ordered⟩ := GuardedReplay.exists_paperOrder_enumeration laws
    (fun {_ _ _} h k=>rep.2.2.1 h k) rep.2.2.2.1 rep.2.1 perm
  refine ⟨ys,permutation,ordered,?_⟩
  apply K.injective
  rw [projection_run]
  ext p
  rw [InductiveMask.replay_iff_alive K.update
    (order_certificate K C H rep.2.1 rep.2.2.2.1) ys permutation ordered p]
  exact (rep.2.2.2.2 p).symm

end Sal.MRDTs.Paper1.Automation.MaskCanonical
