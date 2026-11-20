import LeanProofs.Implementations.LWWRegister.LinearExtension
import LeanProofs.Soundness.SequentialSpec

/-!
# The LWW register: clause 2

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
      (fun {_ _} _ => Soundness.paperOrder_false obligations all_commute _ _ _ _)
  · rw [show projectedUpdates (D := D.toMRDTSig) (pi.mergeSort keyLe)
          = DeterministicSpec.updateLabels ((pi.mergeSort keyLe).map Op.op) by
        simp [projectedUpdates, DeterministicSpec.updateLabels, List.map_map,
          Function.comp],
      historySpec, specMachine.updates_query_iff]
    exact sorted_agrees _ (List.pairwise_mergeSort keyLe_trans keyLe_total pi)
/-! ## `Laws(D_type, Spec)`: the fourth law **fails** for this row

SPEC-NON-COMM does not hold here, and both halves of the counterexample are
already proved.

* In the implementation every pair of events commutes. `do` is `max` on
  write keys, which is what `Laws.all_commute` says.
* In `Spec` two writes do not commute. The specification overwrites, so the
  two orders leave it in different states, and a history may end in a query
  label that sees the difference.

`write 0` and `write 1` are therefore a pair the law forbids: a conflict the
specification has, erased by the implementation. The witness below puts them
on distinct timestamps and distinct replicas, so the failure is not an
artefact of a pair that no reachable execution produces. This is the same shape as
the broken set of Section 6, and it is why this row needs the **scoped**
premise `Soundness.HistorySound`, which chooses a key-sorted witness, rather
than `Soundness.SpecSound`, which is false here for the same reason.

Nothing downstream consumes SPEC-NON-COMM, so the certificate is unaffected.
What the failure costs is the stronger criterion of
`Artifact/MRDTs/Paper1/SpecificationVisibility.lean`, which this row cannot
reach. -/

/-- `write 0` and `write 1` do not commute in `Spec`: the query at the end
of the history tells the two orders apart. -/
theorem not_spec_commutes :
    ¬ Interface.spec_commutes historySpec (.write 0) (.write 1) := by
  intro h
  have lhs : historySpec.admits
      ([SeqLabel.update (AppOp.write 0), .update (.write 1)]
        ++ [.query () (some 1)]) :=
    (specMachine.updates_query_iff [.write 0, .write 1] () (some 1)).mpr rfl
  have rhs := (h [] [SeqLabel.query () (some 1)]).mp (by simpa using lhs)
  have key : (some 1 : Option Nat) = some 0 :=
    (specMachine.updates_query_iff [AppOp.write 1, .write 0] ()
      (some 1)).mp (by simpa using rhs)
  simp at key

/-- **SPEC-NON-COMM fails for the LWW register.** The two writes commute in
the implementation and do not commute in `Spec`. -/
theorem not_spec_non_comm : ¬ Interface.spec_non_comm D historySpec := fun h =>
  h (0, 0, .write 0) (1, 1, .write 1) not_spec_commutes (all_commute _ _)

end LeanProofs.Implementations.LWWRegister
