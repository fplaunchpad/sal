import Sal.MRDTs.Paper1.ConcreteObstructions

/-! The six embedded production signatures still refute the corrected guarded
laws. Coordinate ties use distinct timestamps and different replicas. The
claims concern globally quantified concrete laws; they do not strengthen the issuer. -/
namespace Sal.MRDTs.Paper1.GuardedRGAObstructions
open Foundation Sal.EmbedRGA
open ConcreteObstructions

theorem no_guarded_laws_triangle {D : MRDTSig}
    (a b c : Op D.AppOp)
    (dab : distinctOps (D := D.toUpdateSig) a b)
    (dbc : distinctOps (D := D.toUpdateSig) b c)
    (dac : distinctOps (D := D.toUpdateSig) a c)
    (rab : a.rep ≠ b.rep) (rbc : b.rep ≠ c.rep) (rac : a.rep ≠ c.rep)
    (ab : ¬ D.toUpdateSig.commutes a b) (bc : ¬ D.toUpdateSig.commutes b c) (ac : ¬ D.toUpdateSig.commutes a c) :
    ¬ ∃ P : OperationPolicy D.AppOp, GuardedReplay.Laws D.toUpdateSig P := by
  rintro ⟨P,laws⟩
  have hab := (laws.noncomm_exact a b dab rab).mp ab
  have hbc := (laws.noncomm_exact b c dbc rbc).mp bc
  have hac := (laws.noncomm_exact a c dac rac).mp ac
  have dba : distinctOps (D := D.toUpdateSig) b a := Ne.symm dab
  have dcb : distinctOps (D := D.toUpdateSig) c b := Ne.symm dbc
  have dca : distinctOps (D := D.toUpdateSig) c a := Ne.symm dac
  rcases hab with hab | hba <;> rcases hbc with hbc | hcb <;> rcases hac with hac | hca
  · exact laws.no_chain a b c dab dbc ⟨hab,hbc⟩
  · exact laws.no_chain a b c dab dbc ⟨hab,hbc⟩
  · exact laws.no_chain a c b dac dcb ⟨hac,hcb⟩
  · exact laws.no_chain c a b dca dab ⟨hca,hab⟩
  · exact laws.no_chain b a c dba dac ⟨hba,hac⟩
  · exact laws.no_chain b c a dbc dca ⟨hbc,hca⟩
  · exact laws.no_chain c b a dcb dba ⟨hcb,hba⟩
  · exact laws.no_chain c b a dcb dba ⟨hcb,hba⟩

namespace Embedded
open Instances.EmbedRGA
variable {α : Type} [DecidableEq α] [Inhabited α]
def event (ts : Nat) (x : α) : Op (EOp α) := (ts,ts,.ins x [] 3)
theorem noncommute (Γ : OrderedPrefixCode)
    (i j : Nat) (x y : α) (hi : i ≤ 3) (hj : j ≤ 3) (different : i ≠ j) (values : x ≠ y) :
    ¬ (E Γ α).toUpdateSig.commutes (event i x) (event j y) := by
  apply not_commutes_of_query (D := E Γ α) _ _ [] ()
  change (E Γ α).query ((E Γ α).update ((E Γ α).update [] (ConcreteObstructions.Embedded.tied i x))
      (ConcreteObstructions.Embedded.tied j y)) () ≠
    (E Γ α).query ((E Γ α).update ((E Γ α).update [] (ConcreteObstructions.Embedded.tied j y))
      (ConcreteObstructions.Embedded.tied i x)) ()
  rw [(ConcreteObstructions.Embedded.query_orders Γ i j x y hi hj different).1,
    (ConcreteObstructions.Embedded.query_orders Γ i j x y hi hj different).2]
  exact fun h => values (List.cons.inj h).1

theorem no_laws_three_values (Γ : OrderedPrefixCode)
    (x y z : α) (xy : x ≠ y) (yz : y ≠ z) (xz : x ≠ z) :
    ¬ ∃ P : OperationPolicy (EOp α), GuardedReplay.Laws (E Γ α).toUpdateSig P := by
  apply no_guarded_laws_triangle (D := E Γ α) (event 1 x) (event 2 y) (event 3 z)
  all_goals first
    | exact noncommute Γ 1 2 x y (by omega) (by omega) (by omega) xy
    | exact noncommute Γ 2 3 y z (by omega) (by omega) (by omega) yz
    | exact noncommute Γ 1 3 x z (by omega) (by omega) (by omega) xz
    | simp [distinctOps, Op.time, Op.rep, event]
end Embedded

namespace Sided
open Instances.SidedEmbedRGA
def event (ts x : Nat) : Op SOp := (ts,ts,.ins x [] 3 .R)
theorem noncommute (Γ : OrderedPrefixCode)
    (i j x y : Nat) (hi : i ≤ 3) (hj : j ≤ 3) (different : i ≠ j) (values : x ≠ y) :
    ¬ (S Γ).toUpdateSig.commutes (event i x) (event j y) := by
  apply not_commutes_of_query (D := S Γ) _ _ [] ()
  change (S Γ).query ((S Γ).update ((S Γ).update [] (ConcreteObstructions.Sided.tied i x))
      (ConcreteObstructions.Sided.tied j y)) () ≠
    (S Γ).query ((S Γ).update ((S Γ).update [] (ConcreteObstructions.Sided.tied j y))
      (ConcreteObstructions.Sided.tied i x)) ()
  rw [(ConcreteObstructions.Sided.query_orders Γ i j x y hi hj different).1,
    (ConcreteObstructions.Sided.query_orders Γ i j x y hi hj different).2]
  exact fun h => values (List.cons.inj h).1

theorem no_laws (Γ : OrderedPrefixCode) :
    ¬ ∃ P : OperationPolicy SOp, GuardedReplay.Laws (S Γ).toUpdateSig P := by
  apply no_guarded_laws_triangle (D := S Γ) (event 1 10) (event 2 20) (event 3 30)
  all_goals first
    | exact noncommute Γ 1 2 10 20 (by omega) (by omega) (by omega) (by decide)
    | exact noncommute Γ 2 3 20 30 (by omega) (by omega) (by omega) (by decide)
    | exact noncommute Γ 1 3 10 30 (by omega) (by omega) (by omega) (by decide)
    | simp [distinctOps, Op.time, Op.rep, event]
end Sided

theorem embedded_no_laws (Γ : OrderedPrefixCode) :
    ¬ ∃ P, GuardedReplay.Laws (Instances.EmbedRGA.E Γ Nat).toUpdateSig P :=
  Embedded.no_laws_three_values Γ 10 20 30 (by decide) (by decide) (by decide)

theorem peritext_no_laws (Γ : OrderedPrefixCode) :
    ¬ ∃ P, GuardedReplay.Laws (Instances.Peritext.D Γ).toUpdateSig P :=
  Embedded.no_laws_three_values Γ (.char 10) (.char 20) (.char 30)
    (by decide) (by decide) (by decide)

namespace SidedPeritext
open Instances.SidedEmbedRGA Instances.SidedPeritext

def event (ts x : Nat) : Op (Core Γ).AppOp :=
  inlOp (A₂ := Nat ⊕ MarkEvent) (Sided.event ts x)

theorem core_noncommute (Γ : OrderedPrefixCode)
    (i j x y : Nat) (hi : i ≤ 3) (hj : j ≤ 3) (different : i ≠ j) (values : x ≠ y) :
    ¬ (Core Γ).toUpdateSig.commutes (event i x) (event j y) := by
  apply not_commutes_of_query (D := Core Γ) _ _ (Core Γ).init (.inl ())
  change (Core Γ).query ((Core Γ).update ((Core Γ).update (Core Γ).init
    (ConcreteObstructions.SidedPeritext.tied i x))
    (ConcreteObstructions.SidedPeritext.tied j y)) (.inl ()) ≠
    (Core Γ).query ((Core Γ).update ((Core Γ).update (Core Γ).init
    (ConcreteObstructions.SidedPeritext.tied j y))
    (ConcreteObstructions.SidedPeritext.tied i x)) (.inl ())
  rw [(ConcreteObstructions.SidedPeritext.core_query_orders Γ i j x y hi hj different).1,
    (ConcreteObstructions.SidedPeritext.core_query_orders Γ i j x y hi hj different).2]
  exact fun h => values (List.cons.inj (Sum.inl.inj h)).1

theorem core_no_laws (Γ : OrderedPrefixCode) :
    ¬ ∃ P, GuardedReplay.Laws (Core Γ).toUpdateSig P := by
  apply no_guarded_laws_triangle (D := Core Γ) (event 1 10) (event 2 20) (event 3 30)
  all_goals first
    | exact core_noncommute Γ 1 2 10 20 (by omega) (by omega) (by omega) (by decide)
    | exact core_noncommute Γ 2 3 20 30 (by omega) (by omega) (by omega) (by decide)
    | exact core_noncommute Γ 1 3 10 30 (by omega) (by omega) (by omega) (by decide)
    | simp [distinctOps, Op.time, Op.rep, event, inlOp, Sided.event]

theorem rich_noncommute (Γ : OrderedPrefixCode)
    (i j x y : Nat) (hi : i ≤ 3) (hj : j ≤ 3) (different : i ≠ j) (values : x ≠ y) :
    ¬ (RichCore Γ).toUpdateSig.commutes (event i x) (event j y) := by
  apply not_commutes_of_query (D := RichCore Γ) _ _ (RichCore Γ).init (.bold)
  change (RichCore Γ).query ((RichCore Γ).update ((RichCore Γ).update (RichCore Γ).init
    (ConcreteObstructions.SidedPeritext.tied i x))
    (ConcreteObstructions.SidedPeritext.tied j y)) (.bold) ≠
    (RichCore Γ).query ((RichCore Γ).update ((RichCore Γ).update (RichCore Γ).init
    (ConcreteObstructions.SidedPeritext.tied j y))
    (ConcreteObstructions.SidedPeritext.tied i x)) (.bold)
  rw [(ConcreteObstructions.SidedPeritext.rich_query_orders Γ i j x y hi hj different).1,
    (ConcreteObstructions.SidedPeritext.rich_query_orders Γ i j x y hi hj different).2]
  exact fun h => values (congrArg Prod.fst (List.cons.inj h).1)

theorem rich_no_laws (Γ : OrderedPrefixCode) :
    ¬ ∃ P, GuardedReplay.Laws (RichCore Γ).toUpdateSig P := by
  apply no_guarded_laws_triangle (D := RichCore Γ) (event 1 10) (event 2 20) (event 3 30)
  all_goals first
    | exact rich_noncommute Γ 1 2 10 20 (by omega) (by omega) (by omega) (by decide)
    | exact rich_noncommute Γ 2 3 20 30 (by omega) (by omega) (by omega) (by decide)
    | exact rich_noncommute Γ 1 3 10 30 (by omega) (by omega) (by omega) (by decide)
    | simp [distinctOps, Op.time, Op.rep, event, inlOp, Sided.event]
end SidedPeritext

namespace RegisteredFugueMax
open Instances.SidedEmbedRGA.FugueMax
def event (ts : Nat) : Op Payload := (ts,ts,ConcreteObstructions.RegisteredFugueMax.tiedPayload)
theorem query_control (Γ : OrderedPrefixCode) :
    (datatype Γ).query ((datatype Γ).update ((datatype Γ).update (datatype Γ).init (event 1)) (event 2)) () = [1,2] ∧
    (datatype Γ).query ((datatype Γ).update ((datatype Γ).update (datatype Γ).init (event 2)) (event 1)) () = [2,1] ∧
    (datatype Γ).query ((datatype Γ).update ((datatype Γ).update (datatype Γ).init (event 1)) (event 2)) () ≠
      (datatype Γ).query ((datatype Γ).update ((datatype Γ).update (datatype Γ).init (event 2)) (event 1)) () := by
  simp [datatype, rawUpdate, recordOf, event,
    ConcreteObstructions.RegisteredFugueMax.tiedPayload, Instances.SidedEmbedRGA.mStep,
    Instances.SidedEmbedRGA.sIds, Instances.SidedEmbedRGA.sInsert, keyLt_irrefl]

theorem no_laws (Γ : OrderedPrefixCode) :
    ¬ ∃ P, GuardedReplay.Laws (datatype Γ).toUpdateSig P := by
  rintro ⟨P,laws⟩
  have nc : ¬ (datatype Γ).toUpdateSig.commutes (event 1) (event 2) :=
    not_commutes_of_query (D := datatype Γ) _ _ (datatype Γ).init () (query_control Γ).2.2
  have covered := (laws.noncomm_exact (event 1) (event 2) (by simp [distinctOps,Op.time,event]) (by simp [Op.rep,event])).mp nc
  have self : P.before (event 1).op (event 1).op := by
    simpa only [event,Op.op,or_self] using covered
  exact laws.no_chain (event 1) (event 2) (event 3) (by simp [distinctOps,Op.time,event]) (by simp [distinctOps,Op.time,event]) ⟨self,self⟩
end RegisteredFugueMax

/-! These controls separate the global API obstruction from production
execution: all three coordinate-tie insertions are rejected at every origin.
A fresh root insertion is accepted, pinning that rejection to the witness. -/

theorem embedded_never_issuable {α : Type} [DecidableEq α] [Inhabited α]
    (ts : Nat) (x : α) (small : ts ≤ 3) (s : Instances.EmbedRGA.EState α) :
    ¬ Instances.EmbedRGA.eApplicable (Embedded.event ts x) s := by
  simp only [Instances.EmbedRGA.eApplicable,Embedded.event]
  omega

theorem sided_never_issuable (ts x : Nat) (small : ts ≤ 3)
    (s : Instances.SidedEmbedRGA.SState) :
    ¬ Instances.SidedEmbedRGA.sApplicable (Sided.event ts x) s := by
  simp only [Instances.SidedEmbedRGA.sApplicable,Sided.event]
  omega

/-- PASS+FAIL: exactness guards hold and reads disagree, while the unchanged
issuer accepts a root insertion and rejects every triangle event. -/
theorem embedded_guarded_control (Γ : OrderedPrefixCode)
    (s : Instances.EmbedRGA.EState Nat) :
    distinctOps (D := (Instances.EmbedRGA.E Γ Nat).toUpdateSig)
      (Embedded.event 1 10) (Embedded.event 2 20) ∧
    (Embedded.event 1 10).rep ≠ (Embedded.event 2 20).rep ∧
    (Instances.EmbedRGA.E Γ Nat).query
      ((Instances.EmbedRGA.E Γ Nat).update ((Instances.EmbedRGA.E Γ Nat).update [] (Embedded.event 1 10))
        (Embedded.event 2 20)) () = [10,20] ∧
    (Instances.EmbedRGA.E Γ Nat).query
      ((Instances.EmbedRGA.E Γ Nat).update ((Instances.EmbedRGA.E Γ Nat).update [] (Embedded.event 2 20))
        (Embedded.event 1 10)) () ≠ [10,20] ∧
    Instances.EmbedRGA.eApplicable (4,4,.ins 40 [] 0) s ∧
    (∀ ts ∈ [1,2,3], ¬ Instances.EmbedRGA.eApplicable (Embedded.event ts 10) s) := by
  refine ⟨by simp [distinctOps,Op.time,Embedded.event],by simp [Op.rep,Embedded.event],?_,?_,by simp [Instances.EmbedRGA.eApplicable],?_⟩
  · exact (ConcreteObstructions.Embedded.query_orders Γ 1 2 10 20 (by omega) (by omega) (by omega)).1
  · change (Instances.EmbedRGA.E Γ Nat).query
      ((Instances.EmbedRGA.E Γ Nat).update ((Instances.EmbedRGA.E Γ Nat).update [] (ConcreteObstructions.Embedded.tied 2 20))
        (ConcreteObstructions.Embedded.tied 1 10)) () ≠ [10,20]
    rw [(ConcreteObstructions.Embedded.query_orders Γ 1 2 10 20 (by omega) (by omega) (by omega)).2]
    change ([20,10] : List Nat) ≠ [10,20]
    decide
  · intro ts mem
    apply embedded_never_issuable ts 10 _ s
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    omega

theorem sided_guarded_control (Γ : OrderedPrefixCode)
    (s : Instances.SidedEmbedRGA.SState) :
    distinctOps (D := (Instances.SidedEmbedRGA.S Γ).toUpdateSig)
      (Sided.event 1 10) (Sided.event 2 20) ∧
    (Sided.event 1 10).rep ≠ (Sided.event 2 20).rep ∧
    (Instances.SidedEmbedRGA.S Γ).query
      ((Instances.SidedEmbedRGA.S Γ).update ((Instances.SidedEmbedRGA.S Γ).update [] (Sided.event 1 10))
        (Sided.event 2 20)) () = [10,20] ∧
    (Instances.SidedEmbedRGA.S Γ).query
      ((Instances.SidedEmbedRGA.S Γ).update ((Instances.SidedEmbedRGA.S Γ).update [] (Sided.event 2 20))
        (Sided.event 1 10)) () ≠ [10,20] ∧
    Instances.SidedEmbedRGA.sApplicable (4,4,.ins 40 [] 0 .R) s ∧
    (∀ ts ∈ [1,2,3], ¬ Instances.SidedEmbedRGA.sApplicable (Sided.event ts 10) s) := by
  refine ⟨by simp [distinctOps,Op.time,Sided.event],by simp [Op.rep,Sided.event],?_,?_,by simp [Instances.SidedEmbedRGA.sApplicable],?_⟩
  · exact (ConcreteObstructions.Sided.query_orders Γ 1 2 10 20 (by omega) (by omega) (by omega)).1
  · change (Instances.SidedEmbedRGA.S Γ).query
      ((Instances.SidedEmbedRGA.S Γ).update ((Instances.SidedEmbedRGA.S Γ).update [] (ConcreteObstructions.Sided.tied 2 20))
        (ConcreteObstructions.Sided.tied 1 10)) () ≠ [10,20]
    rw [(ConcreteObstructions.Sided.query_orders Γ 1 2 10 20 (by omega) (by omega) (by omega)).2]
    change ([20,10] : List Nat) ≠ [10,20]
    decide
  · intro ts mem
    apply sided_never_issuable ts 10 _ s
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    omega

theorem peritext_never_issuable (ts : Nat) (small : ts ≤ 3)
    (s : Instances.EmbedRGA.EState Instances.Peritext.Element) :
    ¬ Instances.EmbedRGA.eApplicable (Embedded.event ts (Instances.Peritext.Element.char 10)) s :=
  embedded_never_issuable ts _ small s

theorem core_never_issuable (Γ : OrderedPrefixCode) (ts x : Nat) (small : ts ≤ 3)
    (s : (Instances.SidedPeritext.Core Γ).State) :
    ¬ Instances.SidedPeritext.coreGuard Γ (SidedPeritext.event ts x) s := by
  change ¬ Instances.SidedEmbedRGA.sApplicable (Sided.event ts x) s.1
  exact sided_never_issuable ts x small s.1

theorem rich_never_issuable (Γ : OrderedPrefixCode) (ts x : Nat) (small : ts ≤ 3)
    (s : (Instances.SidedPeritext.RichCore Γ).State) :
    ¬ (Instances.SidedPeritext.richGeneration Γ).CanIssue (SidedPeritext.event ts x) s := by
  exact core_never_issuable Γ ts x small s

/-- PASS+FAIL: native Peritext inherits exactly the embedded issuer. -/
theorem peritext_issuer_control (s : Instances.EmbedRGA.EState Instances.Peritext.Element) :
    Instances.EmbedRGA.eApplicable (4,4,.ins (.char 40) [] 0) s ∧
    ¬ Instances.EmbedRGA.eApplicable (Embedded.event 1 (Instances.Peritext.Element.char 10)) s :=
  ⟨by simp [Instances.EmbedRGA.eApplicable],peritext_never_issuable 1 (by omega) s⟩

/-- PASS+FAIL: cross-component text issuance accepts the fresh root insertion
and rejects the tied-coordinate text event. -/
theorem core_issuer_control (Γ : OrderedPrefixCode) (s : (Instances.SidedPeritext.Core Γ).State) :
    Instances.SidedPeritext.coreGuard Γ
      (inlOp (A₂ := Nat ⊕ Instances.SidedPeritext.MarkEvent) (4,4,Instances.SidedEmbedRGA.SOp.ins 40 [] 0 .R)) s ∧
    ¬ Instances.SidedPeritext.coreGuard Γ (SidedPeritext.event 1 10) s := by
  refine ⟨?_,core_never_issuable Γ 1 10 (by omega) s⟩
  change Instances.SidedEmbedRGA.sApplicable (4,4,.ins 40 [] 0 .R) s.1
  simp [Instances.SidedEmbedRGA.sApplicable]

theorem rich_issuer_control (Γ : OrderedPrefixCode) (s : (Instances.SidedPeritext.RichCore Γ).State) :
    (Instances.SidedPeritext.richGeneration Γ).CanIssue
      (inlOp (A₂ := Nat ⊕ Instances.SidedPeritext.MarkEvent) (4,4,Instances.SidedEmbedRGA.SOp.ins 40 [] 0 .R)) s ∧
    ¬ (Instances.SidedPeritext.richGeneration Γ).CanIssue (SidedPeritext.event 1 10) s :=
  core_issuer_control Γ s

namespace RegisteredFugueMax
open Instances.SidedEmbedRGA Instances.SidedEmbedRGA.FugueMax

/-- Every generated insertion carries a nonempty chain; the conflict witness
carries an empty chain and cannot pass the original issuer at any origin. -/
theorem never_issuable (Γ : OrderedPrefixCode) (ts : Nat) (s : State) :
    ¬ applicable Γ (event ts) s := by
  rintro ⟨births,_,issued⟩
  have hi : mIsIns (recordOf (event ts)) = true := rfl
  obtain ⟨_,_,i,eq⟩ := (canIssue_insert_iff Γ ⟨s.live,births⟩ (recordOf (event ts)) hi).mp issued
  have chain := congrArg MRec.chain eq
  simp only [recordOf,event,ConcreteObstructions.RegisteredFugueMax.tiedPayload] at chain
  unfold prepareInsert mGenInsAfter at chain
  split at chain <;> simp at chain
/-- PASS+FAIL: the witness stores the hand-chosen empty chain; every genuine
prepared insertion differs in this exact issuer-required field. -/
theorem chain_control (Γ : OrderedPrefixCode) (ts : Nat) (s : IssuerState) (i : Nat) :
    (recordOf (event ts)).chain = [] ∧
    (prepareInsert Γ s ts ts i).chain ≠ [] := by
  refine ⟨rfl,?_⟩
  unfold prepareInsert mGenInsAfter
  split <;> simp

end RegisteredFugueMax

#print axioms embedded_guarded_control
#print axioms sided_guarded_control
#print axioms embedded_never_issuable
#print axioms core_never_issuable
#print axioms RegisteredFugueMax.never_issuable

#print axioms embedded_no_laws
#print axioms Sided.no_laws
#print axioms peritext_no_laws
#print axioms SidedPeritext.core_no_laws
#print axioms SidedPeritext.rich_no_laws
#print axioms RegisteredFugueMax.no_laws
end Sal.MRDTs.Paper1.GuardedRGAObstructions
