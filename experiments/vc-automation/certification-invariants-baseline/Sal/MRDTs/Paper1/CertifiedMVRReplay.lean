import Sal.MRDTs.Paper1.CertifiedReplay
import Sal.MRDTs.Paper1.CertifiedQueueMVRCommutation

/-! Compact MVR instantiated in the certified replay scope. Prefixes retain
finite supported event provenance and causal closure inside the eligible set.
No global-policy or arbitrary-state representation law is assumed. -/
namespace Sal.MRDTs.Paper1.CertifiedQueueMVR.MVR
open Foundation Classical
open Instances.MVRLive

abbrev emptyPolicy : OperationPolicy D.AppOp := commutingPolicy D.AppOp

def Prefix (C : Configuration D) (E H : Set Event) (s : State) : Prop :=
  H ⊆ E ∧ (∀ a ∈ E, ∀ b ∈ H, C.vis a b → a ∈ H) ∧ H.Finite ∧ Represents H s

def scopeC (C : Configuration D) (E : Set Event) : CertifiedReplay.Scope D.toUpdateSig where
  context := C.replayContext
  events := E
  represented := Prefix C E

theorem prefix_empty (C : Configuration D) (E : Set Event) : Prefix C E ∅ D.init := by
  refine ⟨Set.empty_subset _,?_,Set.finite_empty,represents_empty⟩
  intro a _ b hb; exact hb.elim

theorem scope_laws {C : Configuration D} (execution : CertifiedExecution D issuance C)
    (E : Set Event) (supported : E ⊆ C.events) :
    CertifiedReplay.Laws (scopeC C E) emptyPolicy := by
  constructor
  · intro H s e hs ready
    rcases hs with ⟨sub,closed,finite,rep⟩
    rcases ready with ⟨he,fresh,preds⟩
    refine ⟨Set.insert_subset he sub,?_,finite.insert e,?_⟩
    · intro a ha b hb vis
      rcases hb with rfl | hb
      · exact Or.inr (preds a ha vis)
      · exact Or.inr (closed a ha b hb vis)
    · have updated := represents_update e rep ?_ ?_
      · simpa only [Set.union_singleton] using updated
      · intro b hb target
        have vis := overwrite_implies_visibility execution (supported he) (supported (sub hb)) target
        exact fresh (closed e he b hb vis)
      · intro target
        exact Nat.lt_irrefl _ (issued_overwrite_lt execution.mintHonest (supported he) target)
  · intro H s a b hs ha hb hva hvb _ _
    exact concurrent_commutes execution (supported ha.1) (supported hb.1) ⟨hva,hvb⟩ s

theorem legal_of_causal_enumeration (C : Configuration D) (E : Set Event)
    {π : List Event} (hp : listPermOf π E) (hc : respects π C.vis) :
    CertifiedReplay.Legal (scopeC C E) ∅ π :=
  CertifiedReplay.legal_of_causal_enumeration
    (fun e h => Nat.lt_irrefl e.time (C.causal_mono h)) hp hc

theorem canonical_of_causal_fold (C : Configuration D) (E : Set Event)
    {π : List Event} (hp : listPermOf π E) (hc : respects π C.vis) :
    CertifiedReplay.Canonical (scopeC C E) emptyPolicy D.init
      (applySeq D.toUpdateSig D.init π) := by
  refine ⟨π,hp,legal_of_causal_enumeration C E hp hc,hc,?_,rfl⟩
  apply hc.imp
  intro a b hab order
  rcases order with order | order
  · exact hab order.1
  · exact order.2.2.1.elim

/-- Empty payload policy has no chains even before restricting eligibility. -/
theorem policy_no_chain (a b c : Event) :
    ¬ (emptyPolicy.before a.op b.op ∧ emptyPolicy.before b.op c.op) := by
  simp [emptyPolicy,commutingPolicy]

/-- Scoped policy exactness concerns concurrent certified eligible events;
causal overwrite conflicts remain represented by the unchanged paper order. -/
theorem policy_concurrent_exact {C : Configuration D}
    (execution : CertifiedExecution D issuance C) {E : Set Event}
    (supported : E ⊆ C.events) {a b : Event} (ha : a ∈ E) (hb : b ∈ E)
    (concurrent : ¬ C.vis a b ∧ ¬ C.vis b a) :
    ¬ D.toUpdateSig.commutes a b ↔ emptyPolicy.before a.op b.op ∨ emptyPolicy.before b.op a.op :=
  concurrent_empty_exact execution (supported ha) (supported hb) concurrent

/-- Scoped canonical MVR histories determine exactly one raw state. -/
theorem canonical_unique {C : Configuration D} (execution : CertifiedExecution D issuance C)
    {E : Set Event} (supported : E ⊆ C.events) {a b : State}
    (ha : CertifiedReplay.Canonical (scopeC C E) emptyPolicy D.init a)
    (hb : CertifiedReplay.Canonical (scopeC C E) emptyPolicy D.init b) : a = b :=
  CertifiedReplay.canonical_unique (scope_laws execution E supported) (prefix_empty C E) ha hb

/-- Reordered eligible folds preserve the compact live-write representation. -/
theorem canonical_represents {C : Configuration D} (execution : CertifiedExecution D issuance C)
    {E : Set Event} (supported : E ⊆ C.events) {s : State}
    (canonical : CertifiedReplay.Canonical (scopeC C E) emptyPolicy D.init s) :
    Represents E s :=
  (CertifiedReplay.canonical_represented (scope_laws execution E supported)
    (prefix_empty C E) canonical).2.2.2

/-- The paper order remains unchanged; for the empty payload policy its only
edges are causal actual noncommutation. -/
theorem paperOrder_iff (C : Configuration D) (E : Set Event) (a b : Event) :
    paperOrder emptyPolicy C.replayContext E a b ↔
      C.vis a b ∧ ¬ D.toUpdateSig.commutes a b := by
  simp [paperOrder,emptyPolicy,commutingPolicy]

end Sal.MRDTs.Paper1.CertifiedQueueMVR.MVR
