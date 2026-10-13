import Sal.MRDTs.Paper1.GuardedReplay
import Sal.MRDTs.Paper1.PolicyObstructions
import Sal.MRDTs.Instances.Peritext
import Sal.MRDTs.Instances.SidedPeritext
import Sal.MRDTs.Instances.FugueMaxImplementation

namespace Sal.MRDTs.Paper1.ConcreteObstructions
open Foundation

theorem not_commutes_of_query {D : MRDTSig}
    (a b : Op D.AppOp) (s : D.State) (q : D.Query)
    (bad : D.query (D.update (D.update s a) b) q ≠
      D.query (D.update (D.update s b) a) q) : ¬ D.toUpdateSig.commutes a b :=
  fun h => bad (congrArg (fun state => D.query state q) (h s))

end Sal.MRDTs.Paper1.ConcreteObstructions

namespace Sal.MRDTs.Paper1.ConcreteObstructions
open Foundation Sal.EmbedRGA

namespace Embedded
open Instances.EmbedRGA
variable {α : Type} [DecidableEq α] [Inhabited α]

def tied (ts : Nat) (v : α) : Op (EOp α) := (ts,0,.ins v [] 3)

theorem query_orders (Γ : OrderedPrefixCode) (i j : Nat) (x y : α)
    (hi : i ≤ 3) (hj : j ≤ 3) (different : i ≠ j) :
    (E Γ α).query ((E Γ α).update ((E Γ α).update [] (tied i x)) (tied j y)) () = [x,y] ∧
    (E Γ α).query ((E Γ α).update ((E Γ α).update [] (tied j y)) (tied i x)) () = [y,x] := by
  have hji : j ≠ i := Ne.symm different
  simp [E, tied, eUpdate, eIds, eInsert, Nat.sub_eq_zero_of_le hi,
    Nat.sub_eq_zero_of_le hj, keyLt_irrefl, different, hji]

theorem query_control (Γ : OrderedPrefixCode) :
    (E Γ Nat).query ((E Γ Nat).update ((E Γ Nat).update [] (tied 1 9)) (tied 2 9)) () = [9,9] ∧
    (E Γ Nat).query ((E Γ Nat).update ((E Γ Nat).update [] (tied 2 9)) (tied 1 9)) () = [9,9] ∧
    (E Γ Nat).query ((E Γ Nat).update ((E Γ Nat).update [] (tied 1 10)) (tied 2 20)) () ≠
      (E Γ Nat).query ((E Γ Nat).update ((E Γ Nat).update [] (tied 2 20)) (tied 1 10)) () := by
  refine ⟨(query_orders Γ 1 2 9 9 (by omega) (by omega) (by omega)).1,
    (query_orders Γ 1 2 9 9 (by omega) (by omega) (by omega)).2,?_⟩
  rw [(query_orders Γ 1 2 10 20 (by omega) (by omega) (by omega)).1,
    (query_orders Γ 1 2 10 20 (by omega) (by omega) (by omega)).2]
  change ([10,20] : List Nat) ≠ [20,10]
  decide

end Embedded

namespace Sided
open Instances.SidedEmbedRGA

def tied (ts v : Nat) : Op SOp := (ts,0,.ins v [] 3 .R)

theorem query_orders (Γ : OrderedPrefixCode) (i j x y : Nat)
    (hi : i ≤ 3) (hj : j ≤ 3) (different : i ≠ j) :
    (S Γ).query ((S Γ).update ((S Γ).update [] (tied i x)) (tied j y)) () = [x,y] ∧
    (S Γ).query ((S Γ).update ((S Γ).update [] (tied j y)) (tied i x)) () = [y,x] := by
  have hji : j ≠ i := Ne.symm different
  simp [S, tied, sUpdate, sIds, sInsert, Nat.sub_eq_zero_of_le hi,
    Nat.sub_eq_zero_of_le hj, keyLt_irrefl, different, hji]

theorem query_control (Γ : OrderedPrefixCode) :
    (S Γ).query ((S Γ).update ((S Γ).update [] (tied 1 10)) (tied 2 20)) () = [10,20] ∧
    (S Γ).query ((S Γ).update ((S Γ).update [] (tied 2 20)) (tied 1 10)) () = [20,10] ∧
    (S Γ).query ((S Γ).update ((S Γ).update [] (tied 1 10)) (tied 2 20)) () ≠
      (S Γ).query ((S Γ).update ((S Γ).update [] (tied 2 20)) (tied 1 10)) () := by
  obtain ⟨h,k⟩ := query_orders Γ 1 2 10 20 (by omega) (by omega) (by omega)
  refine ⟨h,k,?_⟩
  rw [h,k]
  change ([10,20] : List Nat) ≠ [20,10]
  decide

end Sided

theorem peritext_query_control (Γ : OrderedPrefixCode) :
    (Instances.Peritext.D Γ).query
      ((Instances.Peritext.D Γ).update
        ((Instances.Peritext.D Γ).update [] (Embedded.tied 1 (.char 10)))
        (Embedded.tied 2 (.char 20))) () = [.char 10,.char 20] ∧
    (Instances.Peritext.D Γ).query
      ((Instances.Peritext.D Γ).update
        ((Instances.Peritext.D Γ).update [] (Embedded.tied 2 (.char 20)))
        (Embedded.tied 1 (.char 10))) () ≠ [.char 10,.char 20] := by
  obtain ⟨h,k⟩ := Embedded.query_orders Γ 1 2
    (Instances.Peritext.Element.char 10) (.char 20) (by omega) (by omega) (by omega)
  refine ⟨h,?_⟩
  rw [k]
  change ([Instances.Peritext.Element.char 20,.char 10] : List Instances.Peritext.Element) ≠
    [.char 10,.char 20]
  decide

namespace SidedPeritext
open Instances.SidedEmbedRGA Instances.SidedPeritext

def tied (ts v : Nat) : Op (Core Γ).AppOp :=
  inlOp (A₂ := Nat ⊕ MarkEvent) (Sided.tied ts v)

theorem core_query_orders (Γ : OrderedPrefixCode) (i j x y : Nat)
    (hi : i ≤ 3) (hj : j ≤ 3) (different : i ≠ j) :
    (Core Γ).query ((Core Γ).update ((Core Γ).update (Core Γ).init (tied i x))
      (tied j y)) (.inl ()) = .inl [x,y] ∧
    (Core Γ).query ((Core Γ).update ((Core Γ).update (Core Γ).init (tied j y))
      (tied i x)) (.inl ()) = .inl [y,x] := by
  simpa only [Core, prodSig, tied, inlOp, S, Prod.fst, Prod.snd] using
    And.intro (congrArg (Sum.inl (β := Stores.Value))
      (Sided.query_orders Γ i j x y hi hj different).1)
      (congrArg (Sum.inl (β := Stores.Value))
      (Sided.query_orders Γ i j x y hi hj different).2)

theorem core_query_control (Γ : OrderedPrefixCode) :
    (Core Γ).query ((Core Γ).update ((Core Γ).update (Core Γ).init (tied 1 10))
      (tied 2 20)) (.inl ()) = .inl [10,20] ∧
    (Core Γ).query ((Core Γ).update ((Core Γ).update (Core Γ).init (tied 2 20))
      (tied 1 10)) (.inl ()) ≠ .inl [10,20] := by
  obtain ⟨h,k⟩ := core_query_orders Γ 1 2 10 20 (by omega) (by omega) (by omega)
  refine ⟨h,?_⟩
  rw [k]
  intro eq
  have bad : (20 : Nat) = 10 := (List.cons.inj (Sum.inl.inj eq)).1
  omega

theorem rich_query_orders (Γ : OrderedPrefixCode) (i j x y : Nat)
    (hi : i ≤ 3) (hj : j ≤ 3) (different : i ≠ j) :
    (RichCore Γ).query ((RichCore Γ).update ((RichCore Γ).update (RichCore Γ).init
      (tied i x)) (tied j y)) .bold = [(x,false),(y,false)] ∧
    (RichCore Γ).query ((RichCore Γ).update ((RichCore Γ).update (RichCore Γ).init
      (tied j y)) (tied i x)) .bold = [(y,false),(x,false)] := by
  have hji : j ≠ i := Ne.symm different
  simp [RichCore, prodSig, tied, inlOp, S, Sided.tied, sUpdate, sIds, sInsert,
    Nat.sub_eq_zero_of_le hi, Nat.sub_eq_zero_of_le hj, keyLt_irrefl, different, hji,
    renderState, documentOf, Instances.PeritextRender.renderMarksDoc,
    Instances.PeritextRender.renderFlagWith, Instances.PeritextRender.DocD.liveIds,
    Instances.PeritextRender.DocD.birthIds, Instances.PeritextRender.DocD.cp,
    Instances.PeritextRender.fmtAt, Instances.PeritextRender.bestCover,
    Instances.FinsetStore.D]

theorem rich_query_control (Γ : OrderedPrefixCode) :
    (RichCore Γ).query ((RichCore Γ).update ((RichCore Γ).update (RichCore Γ).init
      (tied 1 10)) (tied 2 20)) .bold = [(10,false),(20,false)] ∧
    (RichCore Γ).query ((RichCore Γ).update ((RichCore Γ).update (RichCore Γ).init
      (tied 2 20)) (tied 1 10)) .bold ≠ [(10,false),(20,false)] := by
  obtain ⟨h,k⟩ := rich_query_orders Γ 1 2 10 20 (by omega) (by omega) (by omega)
  refine ⟨h,?_⟩
  rw [k]
  change ([(20,false),(10,false)] : List (Nat × Bool)) ≠ [(10,false),(20,false)]
  decide

end SidedPeritext

namespace RegisteredFugueMax
open Instances.SidedEmbedRGA Instances.SidedEmbedRGA.FugueMax

def tiedPayload : Payload := ⟨.ins 0 .R,0,none,[]⟩

theorem query_control (Γ : OrderedPrefixCode) :
    (datatype Γ).query ((datatype Γ).update ((datatype Γ).update (datatype Γ).init
      (1,0,tiedPayload)) (2,0,tiedPayload)) () = [1,2] ∧
    (datatype Γ).query ((datatype Γ).update ((datatype Γ).update (datatype Γ).init
      (2,0,tiedPayload)) (1,0,tiedPayload)) () = [2,1] ∧
    (datatype Γ).query ((datatype Γ).update ((datatype Γ).update (datatype Γ).init
      (1,0,tiedPayload)) (2,0,tiedPayload)) () ≠
    (datatype Γ).query ((datatype Γ).update ((datatype Γ).update (datatype Γ).init
      (2,0,tiedPayload)) (1,0,tiedPayload)) () := by
  simp [datatype, rawUpdate, recordOf, tiedPayload, mStep, sIds, sInsert, keyLt_irrefl]

end RegisteredFugueMax

end Sal.MRDTs.Paper1.ConcreteObstructions

namespace Sal.MRDTs.Paper1.ConcreteObstructions
open Foundation
namespace Queue
open Instances.Queue PolicyObstructions.Queue

/-- Hand-derived PASS+FAIL: equal enqueue values still expose distinct tags
at the production head query. -/
theorem query_control :
    Q.query (Q.update (Q.update [] left) right) () = some (1,7) ∧
    Q.query (Q.update (Q.update [] right) left) () = some (2,7) ∧
    Q.query (Q.update (Q.update [] left) right) () ≠
      Q.query (Q.update (Q.update [] right) left) () := by
  change _root_.List.head? (qUpdate (qUpdate [] left) right) = some (1,7) ∧
    _root_.List.head? (qUpdate (qUpdate [] right) left) = some (2,7) ∧
    _root_.List.head? (qUpdate (qUpdate [] left) right) ≠
      _root_.List.head? (qUpdate (qUpdate [] right) left)
  decide

theorem noncommute : ¬ Q.toUpdateSig.commutes left right :=
  not_commutes_of_query (D := Q) left right [] () query_control.2.2
end Queue
namespace MVR
open Instances.MVRLive PolicyObstructions.MVR
open Instances.MVR (MVROp clientStep queryValues writeValue overwrites)

/-- The overwrite removes value 10 only when delivered after its birth. -/
theorem query_control :
    10 ∉ queryValues (Instances.MVRLive.update (Instances.MVRLive.update ∅ birth) overwrite) ∧
    10 ∈ queryValues (Instances.MVRLive.update (Instances.MVRLive.update ∅ overwrite) birth) := by
  simp [Instances.MVRLive.update, clientStep, queryValues, writeValue, overwrites, birth, overwrite]

theorem noncommute : ¬ D.toUpdateSig.commutes birth overwrite := by
  apply not_commutes_of_query (D := D) birth overwrite (∅ : Instances.MVRLive.State) ()
  intro eq
  change queryValues (Instances.MVRLive.update (Instances.MVRLive.update ∅ birth) overwrite) =
    queryValues (Instances.MVRLive.update (Instances.MVRLive.update ∅ overwrite) birth) at eq
  exact query_control.1 (eq ▸ query_control.2)

theorem metadata_control :
    D.toUpdateSig.commutes unrelatedBirth unrelatedOverwrite ∧
    ¬ D.toUpdateSig.commutes birth overwrite ∧
    birth.op = unrelatedBirth.op ∧ overwrite.op = unrelatedOverwrite.op :=
  ⟨unrelated_commute,noncommute,rfl,rfl⟩
end MVR
end Sal.MRDTs.Paper1.ConcreteObstructions
