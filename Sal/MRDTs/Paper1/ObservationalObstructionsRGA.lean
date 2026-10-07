import Sal.MRDTs.Paper1.ObservationalObstructions
import Sal.MRDTs.Instances.Peritext
import Sal.MRDTs.Instances.SidedPeritext
import Sal.MRDTs.Instances.FugueMaxImplementation

/-! Query-relative obstructions for the six unchanged embedded production
signatures. Distinct values make coordinate ties visible; the older raw
same-value tie witness is deliberately not used for value-only queries.
All laws quantify over raw operations, so these witnesses need not satisfy
the production issuer guards. -/
namespace Sal.MRDTs.Paper1.ObservationalObstructions
open Foundation AbstractMRDT Sal.EmbedRGA

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

theorem noncommute (Γ : OrderedPrefixCode) (A : Model (E Γ α))
    (i j : Nat) (x y : α) (hi : i ≤ 3) (hj : j ≤ 3)
    (different : i ≠ j) (values : x ≠ y) :
    ¬ Commutes A (tied i x) (tied j y) := by
  apply not_commutes_of_query A _ _ [] ()
  rw [(query_orders Γ i j x y hi hj different).1,
    (query_orders Γ i j x y hi hj different).2]
  intro eq
  exact values (List.cons.inj eq).1

/-- The old raw equal-value witness does not distinguish immediate reads.
The negative companion fixes the distinct-value query-order falsifier. -/
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

theorem no_laws_three_values (Γ : OrderedPrefixCode) (A : Model (E Γ α))
    (x y z : α) (xy : x ≠ y) (yz : y ≠ z) (xz : x ≠ z) :
    ¬ ∃ P : OperationPolicy (EOp α), Laws A P :=
  no_laws_triangle A (tied 1 x) (tied 2 y) (tied 3 z)
    (noncommute Γ A 1 2 x y (by omega) (by omega) (by omega) xy)
    (noncommute Γ A 2 3 y z (by omega) (by omega) (by omega) yz)
    (noncommute Γ A 1 3 x z (by omega) (by omega) (by omega) xz)

theorem no_laws (Γ : OrderedPrefixCode) (A : Model (E Γ Nat)) :
    ¬ ∃ P : OperationPolicy (EOp Nat), Laws A P :=
  no_laws_three_values Γ A 10 20 30 (by decide) (by decide) (by decide)

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

theorem noncommute (Γ : OrderedPrefixCode) (A : Model (S Γ))
    (i j x y : Nat) (hi : i ≤ 3) (hj : j ≤ 3)
    (different : i ≠ j) (values : x ≠ y) :
    ¬ Commutes A (tied i x) (tied j y) := by
  apply not_commutes_of_query A _ _ [] ()
  rw [(query_orders Γ i j x y hi hj different).1,
    (query_orders Γ i j x y hi hj different).2]
  intro eq
  exact values (List.cons.inj eq).1

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

theorem no_laws (Γ : OrderedPrefixCode) (A : Model (S Γ)) :
    ¬ ∃ P : OperationPolicy SOp, Laws A P :=
  no_laws_triangle A (tied 1 10) (tied 2 20) (tied 3 30)
    (noncommute Γ A 1 2 10 20 (by omega) (by omega) (by omega) (by decide))
    (noncommute Γ A 2 3 20 30 (by omega) (by omega) (by omega) (by decide))
    (noncommute Γ A 1 3 10 30 (by omega) (by omega) (by omega) (by decide))

end Sided

theorem peritext_no_laws (Γ : OrderedPrefixCode) (A : Model (Instances.Peritext.D Γ)) :
    ¬ ∃ P : OperationPolicy (Instances.Peritext.D Γ).AppOp, Laws A P :=
  Embedded.no_laws_three_values Γ A (.char 10) (.char 20) (.char 30)
    (by decide) (by decide) (by decide)

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

theorem core_noncommute (Γ : OrderedPrefixCode) (A : Model (Core Γ))
    (i j x y : Nat) (hi : i ≤ 3) (hj : j ≤ 3)
    (different : i ≠ j) (values : x ≠ y) :
    ¬ Commutes A (tied i x) (tied j y) := by
  apply not_commutes_of_query A _ _ (Core Γ).init (.inl ())
  rw [(core_query_orders Γ i j x y hi hj different).1,
    (core_query_orders Γ i j x y hi hj different).2]
  intro eq
  exact values (List.cons.inj (Sum.inl.inj eq)).1

theorem core_no_laws (Γ : OrderedPrefixCode) (A : Model (Core Γ)) :
    ¬ ∃ P : OperationPolicy (Core Γ).AppOp, Laws A P :=
  no_laws_triangle A (tied 1 10) (tied 2 20) (tied 3 30)
    (core_noncommute Γ A 1 2 10 20 (by omega) (by omega) (by omega) (by decide))
    (core_noncommute Γ A 2 3 20 30 (by omega) (by omega) (by omega) (by decide))
    (core_noncommute Γ A 1 3 10 30 (by omega) (by omega) (by omega) (by decide))

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

theorem rich_noncommute (Γ : OrderedPrefixCode) (A : Model (RichCore Γ))
    (i j x y : Nat) (hi : i ≤ 3) (hj : j ≤ 3)
    (different : i ≠ j) (values : x ≠ y) :
    ¬ Commutes A (tied i x) (tied j y) := by
  apply not_commutes_of_query A _ _ (RichCore Γ).init .bold
  rw [(rich_query_orders Γ i j x y hi hj different).1,
    (rich_query_orders Γ i j x y hi hj different).2]
  intro eq
  exact values (congrArg Prod.fst (List.cons.inj eq).1)

theorem rich_no_laws (Γ : OrderedPrefixCode) (A : Model (RichCore Γ)) :
    ¬ ∃ P : OperationPolicy (RichCore Γ).AppOp, Laws A P :=
  no_laws_triangle A (tied 1 10) (tied 2 20) (tied 3 30)
    (rich_noncommute Γ A 1 2 10 20 (by omega) (by omega) (by omega) (by decide))
    (rich_noncommute Γ A 2 3 20 30 (by omega) (by omega) (by omega) (by decide))
    (rich_noncommute Γ A 1 3 10 30 (by omega) (by omega) (by omega) (by decide))

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

theorem noncommute (Γ : OrderedPrefixCode) (A : Model (datatype Γ)) :
    ¬ Commutes A (1,0,tiedPayload) (2,0,tiedPayload) :=
  not_commutes_of_query A _ _ (datatype Γ).init () (query_control Γ).2.2

theorem no_laws (Γ : OrderedPrefixCode) (A : Model (datatype Γ)) :
    ¬ ∃ P : OperationPolicy Payload, Laws A P :=
  no_laws_same_label A (1,0,tiedPayload) (2,0,tiedPayload) rfl (noncommute Γ A)

end RegisteredFugueMax

#print axioms Embedded.no_laws
#print axioms Sided.no_laws
#print axioms peritext_no_laws
#print axioms SidedPeritext.core_no_laws
#print axioms SidedPeritext.rich_no_laws
#print axioms RegisteredFugueMax.no_laws
#print axioms Embedded.query_control
#print axioms Sided.query_control
#print axioms peritext_query_control
#print axioms SidedPeritext.core_query_control
#print axioms SidedPeritext.rich_query_control
#print axioms RegisteredFugueMax.query_control

end Sal.MRDTs.Paper1.ObservationalObstructions
