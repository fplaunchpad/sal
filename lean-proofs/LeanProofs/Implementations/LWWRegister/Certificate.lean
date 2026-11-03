import LeanProofs.Implementations.LWWRegister.Laws
import LeanProofs.Metatheory.Adequacy
import LeanProofs.Soundness.RALinearizability

/-!
# The last-writer-wins register: `Spec` and its certificate

The independent sequential specification of Appendix `app:dt-lww-register`:
an overwrite register in which every sequence of writes is admitted and no
chronological legality condition restricts the machine.

This is the first implementation here that needs the **scoped** premise.
The specification's `write(v)` simply overwrites, so folding an arbitrary
order of events through it answers with the *last* write in that order, while
the implementation answers with the *greatest key*. Those agree only when the
history is sorted by key, so `Soundness.SpecSound` is false for this datatype
and `Soundness.HistorySound` is what holds: given an event set, the witness
selected below is its chronological sort.

The appendix records the same choice: "The selected witness sorts writes by
increasing `(t,r,v)`."
-/

namespace LeanProofs.Implementations.LWWRegister

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

/-- Issuance: `G(e, O) <=> true`. -/
def issuance : Issuance D.toMRDTSig where
  CanIssue := fun _ _ => True

/-- `Spec`: an overwrite register. Timestamp and replica are ignored. -/
def specMachine : DeterministicSpec type.OType type.QType type.ValType where
  State := Option Nat
  initial := none
  update _ o := match o with | .write v => some v
  query s _ := s

/-- `Spec` as a history language. -/
def historySpec : Soundness.Spec type := specMachine.toSpec

/-! ## The chronological witness -/

/-- Compare events by their write key. -/
def keyLe (a b : D.Event) : Bool := decide (packed a ≤ packed b)

theorem keyLe_trans (a b c : D.Event) :
    keyLe a b = true → keyLe b c = true → keyLe a c = true := by
  simp only [keyLe, decide_eq_true_eq]; exact le_trans

theorem keyLe_total (a b : D.Event) : (keyLe a b || keyLe b a) = true := by
  simp only [keyLe, Bool.or_eq_true, decide_eq_true_eq]
  exact le_total _ _

/-- Folding `max` from any state bounded by `k` stays bounded by `k`. -/
private theorem fold_le : ∀ (pi : List D.Event) (s k : St),
    s ≤ k → (∀ x ∈ pi, (↑(packed x) : St) ≤ k) → D.applyList s pi ≤ k := by
  intro pi
  induction pi with
  | nil => intro s _ hs _; exact hs
  | cons e rest ih =>
      intro s k hs h
      exact ih _ k (max_le hs (h e (List.mem_cons_self ..)))
        (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- **The key step.** On a history sorted by write key, the implementation's
answer is the specification's answer: the greatest key is the last write. -/
theorem sorted_agrees : ∀ (pi : List D.Event),
    List.Pairwise (fun a b => keyLe a b = true) pi →
    D.query (D.applyList D.sigma0 pi) ()
      = specMachine.query ((pi.map Op.op).foldl specMachine.update specMachine.initial) () := by
  intro pi
  induction pi using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton xs e ih =>
      intro hs
      have hsplit := List.pairwise_append.mp hs
      have hle : ∀ x ∈ xs, (↑(packed x) : St) ≤ ↑(packed e) := by
        intro x hx
        have := hsplit.2.2 x hx e (by simp)
        simp only [keyLe, decide_eq_true_eq] at this
        exact WithBot.coe_le_coe.mpr this
      have hfold : D.applyList D.sigma0 (xs ++ [e])
          = max (D.applyList D.sigma0 xs) ↑(packed e) := by
        simp [Impl.applyList, List.foldl_append]
      have hbound : D.applyList D.sigma0 xs ≤ (↑(packed e) : St) :=
        fold_le xs D.sigma0 _ bot_le hle
      rw [hfold, max_eq_right hbound]
      rcases e with ⟨t, r, o⟩
      cases o
      simp [readOf, writeValue, packed, valueOf, specMachine, List.foldl_append]

/-! ## RA-linearizability -/

/-- The scoped sequential premise. The witness is the chronological sort of
the event set, so the greatest key is last and the overwrite register's
answer matches. -/
theorem historySound : Soundness.HistorySound D historySpec issuance := by
  rintro C _ E _ _ ⟨pi, hpi⟩ q
  cases q
  classical
  refine ⟨pi.mergeSort keyLe, ?_, ?_, ?_⟩
  · refine ⟨hpi.1.perm (pi.mergeSort_perm keyLe).symm, fun e => ?_⟩
    exact ((pi.mergeSort_perm keyLe).mem_iff).trans (hpi.2 e)
  · exact (hpi.1.perm (pi.mergeSort_perm keyLe).symm).imp
      (fun {_ _} _ => paperOrder_false_of_all_commute all_commute _ _ _ _)
  · rw [show projectedUpdates (D := D.toMRDTSig) (pi.mergeSort keyLe)
          = DeterministicSpec.updateLabels ((pi.mergeSort keyLe).map Op.op) by
        simp [projectedUpdates, DeterministicSpec.updateLabels, List.map_map,
          Function.comp],
      historySpec, specMachine.updates_query_iff]
    exact sorted_agrees _ (List.pairwise_mergeSort keyLe_trans keyLe_total pi)

/-- **RA-linearizability.** Every certified execution of the LWW register
satisfies Definition 4 against `Spec`. -/
theorem raLinearizable :
    Soundness.CertifiedRA D historySpec issuance :=
  Soundness.certifiedRA_scoped obligations historySound

/-- The join lemma, proved by the metatheory from the obligations. -/
theorem joinLemma : @Join D.toMRDTSig (Metatheory.rcOrder D) :=
  Metatheory.joinLemma obligations

/-- **VC4** CAUSAL-DELTA, derived rather than assumed. -/
theorem vc4_causal_delta : CausalDeltaLaw D.toMRDTSig :=
  Metatheory.vc4_causal_delta obligations

#print axioms joinLemma
#print axioms raLinearizable

end LeanProofs.Implementations.LWWRegister
