import LeanProofs1.Implementations.LWWRegister.Definition
import LeanProofs1.Interface.VCRoute

/-!
# The LWW register: every obligation

`Laws(D_type, Spec)` of Section 4 and VC1 to VC5 of Section 5, all four laws
and all five conditions, for the tuple of `Definition.lean`. `obligations`
bundles what the metatheory consumes; `spec_non_comm` and `specSound` are the
two further premises `Soundness.certifiedSpecRA` asks for.
-/

namespace LeanProofs1.Implementations.LWWRegister

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-- Two writes commute: both orders take the greater key. By RC-NON-COMM
`rc` is therefore empty. -/
theorem all_commute (e₁ e₂ : D.Event) : D.Commutes e₁ e₂ := by
  intro s
  change max (max s ↑(packed e₁)) ↑(packed e₂)
    = max (max s ↑(packed e₂)) ↑(packed e₁)
  simp [max_assoc, max_comm, max_left_comm]

/-! ## `Laws(D_type)`, the three conditions that constrain `rc`

Proved here, not derived in the metatheory, and under the same names every
other row uses.

`rc` is `Either` at every pair for this datatype, so `no_rc_edge` is
immediate from the tuple and needs no lemma of its own. `all_commute` above
supplies the other half of each proof. The fourth law, SPEC-NON-COMM, needs
`Spec` and is at the end of this file. -/

/-- `rc` orders no pair of events: the tuple's `rc` is `Either`. -/
theorem no_rc_edge (e₁ e₂ : D.Event) : ¬ D.EventRcBefore e₁ e₂ :=
  fun hb => OrderResult.noConfusion hb

/-- **NO-RC-CHAIN**: there is no `rc` edge at all, so there is none to
chain. -/
theorem no_rc_chain (o₁ o₂ o₃ : type.OType) :
    ¬ (D.RcBefore o₁ o₂ ∧ D.RcBefore o₂ o₃) :=
  fun hc => OrderResult.noConfusion hc.1

/-- **RC-NON-COMM**, without the concurrency guard. Both sides are false:
the left by `all_commute`, the right because `rc` is empty. -/
theorem rc_non_comm : UniformRcNonComm D := fun e₁ e₂ =>
  ⟨fun hn => (hn (all_commute e₁ e₂)).elim,
   fun hb => (hb.elim (no_rc_edge _ _) (no_rc_edge _ _)).elim⟩

/-- **COND-COMM**, without the concurrency guard. The absorber clause is
reached only behind an `rc` edge, and there is none. -/
theorem cond_comm : UniformCondComm D := fun _ e e' _ _ hb _ =>
  (no_rc_edge e e' hb).elim

/-- **`Laws(D_type)`.** RC-NON-COMM carries the paper's `o1 /= o2` conjunct,
which NO-RC-CHAIN supplies through `rcNonComm_of_exact`. -/
theorem laws : Laws D :=
  ⟨rcNonComm_of_exact no_rc_chain (fun e₁ e₂ _ _ => rc_non_comm e₁ e₂),
   no_rc_chain,
   fun _ e e' _ _ _ _ hb _ => (no_rc_edge e e' hb).elim⟩

/-! ## VC1 to VC5

Stated as Section 5 states them and proved here. A `merge` that never
inspects its delta lets each proof abstract `e(m)` in one step and close by
arithmetic, but the theorem proved is the condition, not a stronger
equation that the condition is read off from. -/

/-- **VC1** MERGE-COMM, over arbitrary states as the paper has it. -/
theorem vc1_merge_comm (l a b : D.Sigma) :
    D.merge l a b = D.merge l b a := by
  change max a b = max b a
  exact max_comm _ _

/-- **VC2** MERGE-INIT. -/
theorem vc2_merge_init :
    ∀ (C : Ctx D) (E : Set D.Event) (s : D.Sigma),
      SupportedOn D C E → IsCanOn D C E s →
      D.merge D.sigma0 D.sigma0 s = s := by
  intro _ _ s _ _
  change max (⊥ : St) s = s
  exact max_eq_right bot_le

/-- **VC3** LOCAL-REDISTRIBUTE. -/
theorem vc3_local_redistribute :
    ∀ (C : Ctx D) (E₁ E₂ : Set D.Event) (l m x y : D.Sigma)
      (e : D.Event),
      VisStrict D C →
      SupportedOn D C E₁ → SupportedOn D C E₂ →
      WeaklyClosed D C E₁ → WeaklyClosed D C E₂ →
      e ∈ E₁ → e ∉ E₂ → MaximalOn D C (E₁ ∪ E₂) e →
      IsCanOn D C (E₁ ∩ E₂) l →
      IsCanOn D C (downset C e \ {e}) m →
      IsCanOn D C (E₁ \ {e}) x →
      IsCanOn D C E₂ y →
      D.merge l (D.merge m x (D.do_ m e)) y
        = D.merge m (D.merge l x y) (D.do_ m e) := by
  intro _ _ _ l m x y e _ _ _ _ _ _ _ _ _ _ _ _
  generalize D.do_ m e = c
  change max (max x c) y = max (max x y) c
  simp [max_assoc, max_comm, max_left_comm]

/-- **VC5** REDISTRIBUTE. -/
theorem vc5_redistribute :
    ∀ (C : Ctx D) (E₁ E₂ : Set D.Event) (x₀ x₁ x₂ m : D.Sigma)
      (e : D.Event),
      VisStrict D C →
      SupportedOn D C E₁ → SupportedOn D C E₂ →
      WeaklyClosed D C E₁ → WeaklyClosed D C E₂ →
      e ∈ E₁ → e ∈ E₂ → MaximalOn D C (E₁ ∪ E₂) e →
      IsCanOn D C ((E₁ ∩ E₂) \ {e}) x₀ →
      IsCanOn D C (downset C e \ {e}) m →
      IsCanOn D C (E₁ \ {e}) x₁ →
      IsCanOn D C (E₂ \ {e}) x₂ →
      D.merge (D.merge m x₀ (D.do_ m e)) (D.merge m x₁ (D.do_ m e))
          (D.merge m x₂ (D.do_ m e))
        = D.merge m (D.merge x₀ x₁ x₂) (D.do_ m e) := by
  intro _ _ _ x₀ x₁ x₂ m e _ _ _ _ _ _ _ _ _ _ _ _
  generalize D.do_ m e = c
  change max (max x₁ c) (max x₂ c) = max (max x₁ x₂) c
  simp [max_assoc, max_comm, max_left_comm]

/-- **VC4** CAUSAL-DELTA.

Every pair of events commutes, so `lo^C_E` has no edges, `down(e) \ {e}` is
empty and `B` is forced to `sigma0`. The condition is then the row's own
merge identity at the initial state. -/
theorem vc4_causal_delta :
    ∀ (C : Ctx D) (U : Set D.Event) (A B : D.Sigma) (e : D.Event),
      VisStrict D C →
      SupportedOn D C U → WeaklyClosed D C U →
      e ∈ U → MaximalOn D C U e →
      IsCanOn D C (U \ {e}) A →
      IsCanOn D C (downset C e \ {e}) B →
      D.merge B A (D.do_ B e) = D.do_ A e := by
  letI : EventOrder D.toMRDTSig.toUpdateSig := Interface.rcOrder D
  intro C U A B e _ _ _ _ _ _ hB
  rw [isCanonicalState_empty (downset_diff_self_of_commuting all_commute C e) hB]
  show D.merge D.sigma0 A (D.do_ D.sigma0 e) = D.do_ A e
  change max A (max (⊥ : St) ↑(packed e)) = max A ↑(packed e)
  rw [max_eq_right bot_le]

/-- **VC1 to VC5** of Section 5. -/
theorem joinLaws : CanonicalJoinLawsOn D (fun _ => True) where
  vc1_merge_comm := vc1_merge_comm
  vc2_merge_init := fun C E s _ => vc2_merge_init C E s
  vc3_local_redistribute := fun C E₁ E₂ l m x y e _ =>
    vc3_local_redistribute C E₁ E₂ l m x y e
  vc4_causal_delta := fun C U A B e _ => vc4_causal_delta C U A B e
  vc5_redistribute := fun C E₁ E₂ x₀ x₁ x₂ m e _ =>
    vc5_redistribute C E₁ E₂ x₀ x₁ x₂ m e

/-- Everything the metatheory consumes. `laws` is this row's own, not
something the metatheory reconstructs; the unguarded forms of RC-NON-COMM
and COND-COMM follow from it and `all_commute`. -/
theorem obligations : Obligations D :=
  Obligations.ofCommuting laws all_commute joinLaws

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
      (fun {_ _} _ => Soundness.paperOrder_false rc_non_comm all_commute _ _ _ _)
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

end LeanProofs1.Implementations.LWWRegister
