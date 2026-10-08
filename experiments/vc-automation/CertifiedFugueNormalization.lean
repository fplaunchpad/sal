import CertifiedFugueExpansion
import Sal.MRDTs.Paper1.CertifiedRGASidedVCAlgebra

namespace NeemExpansion.CertifiedFugue
open Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.EmbedRGA
open Sal.MRDTs.Instances.SidedEmbedRGA Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax
open CertifiedFugueVCReplay

structure HistoryEvidence (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig) : Prop where
  chain : ∀e∈C.events, ChainFacts (recordOf e)
  delete : ∀d∈C.events,∀x,d.2.2.op=.del x → x=0 ∨ ∃a∈C.events,C.vis a d ∧ mIsIns (recordOf a)=true ∧ a.1=x

theorem step_membership (Γ : OrderedPrefixCode) (s : State) (e : Op Payload)
    (fresh : e.1 ∉ sIds s.live) (p : SRec) :
    p∈(rawUpdate Γ s e).live ↔ Born Γ e p ∨ (p∈s.live ∧ ¬Kill e p) := by
  rcases e with ⟨t,r,⟨op,lo,ro,ch⟩⟩
  cases op with
  | del x => simp [rawUpdate,mStep,recordOf,Born,Kill,mIsIns]; tauto
  | ins a sd =>
    simp only [rawUpdate,mStep,recordOf,if_neg fresh,mem_sInsert]
    simp [Born,Kill,mIsIns,recordOf]
    tauto

theorem replay_alive (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (ev : HistoryEvidence Γ C) (xs : List (Op Payload)) (nodup : xs.Nodup)
    (support : ∀e∈xs,e∈C.events) (ordered : respects xs C.vis) (p : SRec) :
    p ∈ (xs.foldl (rawUpdate Γ) ⟨[],∅⟩).live ↔
      (∃e∈xs,Born Γ e p) ∧ ∀d∈xs,¬Kill d p := by
  apply CertifiedReplay.alive (rawUpdate Γ) ⟨[],∅⟩ (fun p s => p∈s.live) (Born Γ) Kill (by simp) xs
  · intro pre e post eq p
    apply step_membership
    intro hid
    obtain ⟨q,hq,id⟩ := List.mem_map.mp hid
    obtain ⟨birth,hb,_,rec⟩ := provenance Γ pre q hq
    have hbAll : birth∈xs := by rw [eq]; exact List.mem_append_left _ hb
    have heAll : e∈xs := by rw [eq]; simp
    have same := C.ts_unique (support birth hbAll) (support e heAll)
      (by simpa only [rec] using id)
    subst birth
    have nd : (pre++e::post).Nodup := eq ▸ nodup
    exact (List.nodup_append.mp nd).2.2 e hb e List.mem_cons_self rfl
  · intro e p hb
    rcases e with ⟨t,r,⟨op,lo,ro,ch⟩⟩
    cases op <;> simp_all [Born,Kill,mIsIns,recordOf]
  · intro pre d mid e post eq p hk hb
    have he : e∈C.events := support e (by rw [eq]; simp)
    rcases ev.delete d (support d (by rw [eq]; simp)) p.1 hk with zero | ⟨birth,hbirth,vis,_,time⟩
    · have positive : 0<e.1 := (ev.chain e he).1
      have pid : p.1=e.1 := congrArg Prod.fst hb.2
      exact (Nat.ne_of_gt positive) (pid.symm.trans zero)
    · have pid : p.1=e.1 := congrArg Prod.fst hb.2
      have same := C.ts_unique hbirth he (time.trans pid)
      subst birth
      rw [eq] at ordered
      exact (List.pairwise_cons.mp (List.pairwise_append.mp ordered).2.1).1 e (by simp) vis

theorem replay_membership (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (ev : HistoryEvidence Γ C) (H : Set (Op Payload)) (s : State)
    (rep : representation Γ C H s) (p : SRec) :
    p∈s.live ↔ (∃e∈H,Born Γ e p) ∧ ∀d∈H,¬Kill d p := by
  obtain ⟨xs,perm,ordered,fold⟩ := rep.2.2.2.2
  rw [←fold]
  change p∈(xs.foldl (rawUpdate Γ) ⟨[],∅⟩).live ↔ _
  rw [replay_alive Γ C ev xs perm.1 (fun e he => rep.2.2.2.1 ((perm.2 e).mp he)) ordered p]
  simp only [perm.2]

theorem keys_distinct (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (ev : HistoryEvidence Γ C) (a b : Op Payload) (ha : a∈C.events) (hb : b∈C.events)
    (ia : mIsIns (recordOf a)=true) (ib : mIsIns (recordOf b)=true) (different : a.1≠b.1) :
    sKey (fmCoordOf Γ a.2.2.chain) ≠ sKey (fmCoordOf Γ b.2.2.chain) := by
  intro keys
  obtain ⟨pa,ta,sa⟩ := (ev.chain a ha).2 ia
  obtain ⟨pb,tb,sb⟩ := (ev.chain b hb).2 ib
  have coord := sKey_inj keys
  have equal : a.2.2.chain=b.2.2.chain := fmCoordOf_inj Γ pa pb ta tb coord
  apply different
  calc a.1 = (a.2.2.chain.map fmδ).sum := sa.symm
       _ = (b.2.2.chain.map fmδ).sum := by rw [equal]
       _ = b.1 := sb

theorem replay_sorted (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (ev : HistoryEvidence Γ C) (xs : List (Op Payload))
    (support : ∀e∈xs,e∈C.events) : SSorted (xs.foldl (rawUpdate Γ) ⟨[],∅⟩).live := by
  induction xs using List.reverseRecOn with
  | nil => exact List.Pairwise.nil
  | append_singleton xs e ih =>
    have prior := ih (fun o ho => support o (List.mem_append_left _ ho))
    rw [List.foldl_append]
    rcases e with ⟨t,r,⟨op,lo,ro,ch⟩⟩
    cases op with
    | del x => exact List.Pairwise.filter _ prior
    | ins a sd =>
      change SSorted (if t∈sIds _ then _ else sInsert _ _)
      split
      · exact prior
      · rename_i fresh
        apply sInsert_sorted prior
        intro p hp
        obtain ⟨o,ho,ins,record⟩ := provenance Γ xs p hp
        have different : o.1≠t := by
          intro eq
          exact fresh (List.mem_map.mpr ⟨p,hp,by simpa [record] using eq⟩)
        have keys := keys_distinct Γ C ev o (t,r,⟨.ins a sd,lo,ro,ch⟩)
          (support o (List.mem_append_left _ ho)) (support _ (by simp)) ins rfl different
        simpa only [record] using keys

theorem sorted (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (ev : HistoryEvidence Γ C) (H : Set (Op Payload)) (s : State) (rep : representation Γ C H s) : SSorted s.live := by
  obtain ⟨xs,perm,_,fold⟩ := rep.2.2.2.2
  rw [←fold]
  exact replay_sorted Γ C ev xs (fun e he => rep.2.2.2.1 ((perm.2 e).mp he))
end NeemExpansion.CertifiedFugue
