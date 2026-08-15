import Sal.ConditionedMRDTs.Metatheory.GenerationContract
import Sal.ConditionedMRDTs.MRDT_Instances.BoundedCounter.BoundedCounter
import Sal.ConditionedMRDTs.MRDT_Instances.MergeableQueue.MergeableQueue
import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA
import Sal.ConditionedMRDTs.MRDT_Instances.SidedRGA.SidedRGA
import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_Embed.PeritextEmbed
import Sal.ConditionedMRDTs.MRDT_Instances.VerifiedCertificates
import Sal.ConditionedMRDTs.Metatheory.UnifiedVerifiedMRDT

/-! Public generation contracts for the nontrivially conditioned production
instances.  These definitions make the actual issuer guards discoverable from
one API even where the legacy signature still advertises `applicable := True`.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode)

/-- For the counter only, one mint enumeration implies every enumeration:
the guard reads per-replica increment/decrement counts, which permutations
preserve. -/
theorem bcGenHonest_of_mintHonest (C : Configuration BC)
    (h : MintHonest BC bcApplicable (Configuration.core C)) :
    GenHonest BC bcApplicable C := by
  intro e he π hπ
  obtain ⟨π0, hπ0, _hrespects, hguard⟩ := h e he
  have hp : π.Perm π0 := listPermOf_perm hπ hπ0
  obtain ⟨ts, r, op⟩ := e
  cases op with
  | inc => trivial
  | dec =>
      have hi := hp.countP_eq (bcIsIncAt r)
      have hd := hp.countP_eq (bcIsDecAt r)
      have hπ1 := bc_fold_incs π BC.init r
      have hπ2 := bc_fold_decs π BC.init r
      have hπ01 := bc_fold_incs π0 BC.init r
      have hπ02 := bc_fold_decs π0 BC.init r
      simp only [BC_init_fst, BC_init_snd, zero_add] at hπ1 hπ2 hπ01 hπ02
      show (applySeq BC.toCRDTSig BC.init π).2 r + 1 ≤
        (applySeq BC.toCRDTSig BC.init π).1 r
      change (applySeq BC.toCRDTSig BC.init π0).2 r + 1 ≤
        (applySeq BC.toCRDTSig BC.init π0).1 r at hguard
      omega

/-- The counter uses its established all-enumerations history predicate, now
derived soundly from existential mint evidence via count invariance. -/
noncomputable def boundedCounterGeneration : GenerationContract BC where
  Guard := bcApplicable
  History := BCHonest
  history_of_mint := fun C h =>
    (BCHonest_iff_genHonest C).mpr (bcGenHonest_of_mintHonest C h)

/-- Queue generation uses the existential causal fold: demanding every
enumeration would incorrectly require every permutation to expose one head. -/
noncomputable def queueGeneration : GenerationContract Q where
  Guard := qApplicable
  History := QHonest
  history_of_mint := by
    intro C h
    apply qHonest_of_applicable C
    intro e he t hop
    obtain ⟨π, hperm, _hrespects, hguard⟩ := h e he
    exact ⟨π, hperm, hguard⟩

noncomputable def embedGeneration {α : Type} [DecidableEq α] [Inhabited α]
    (Γ : OrderedPrefixCode) : GenerationContract (E Γ α) where
  Guard := eApplicable
  History := EHonest Γ
  history_of_mint := by
    intro C h
    apply eHonest_of_applicable C
    intro e he
    obtain ⟨π, hperm, _hrespects, hguard⟩ := h e he
    exact ⟨π, hperm, hguard⟩

noncomputable def sidedGeneration (Γ : OrderedPrefixCode) :
    GenerationContract (S Γ) where
  Guard := sApplicable
  History := SHonest Γ
  history_of_mint := by
    intro C h
    apply sHonest_of_applicable C
    intro e he
    obtain ⟨π, hperm, _hrespects, hguard⟩ := h e he
    exact ⟨π, hperm, hguard⟩

/-- Canonical Embed-based Peritext inherits the EmbedRGA issuer contract
verbatim at the rich-text payload. -/
noncomputable def peritextEmbedGeneration (Γ : OrderedPrefixCode) :
    GenerationContract
      (E Γ Sal.ConditionedMRDTs.Peritext.PeritextElt) :=
  embedGeneration Γ

/-! ## Bounded-counter sequential intent -/

/-- Independent sequential view: each replica owns one integer balance. -/
def boundedCounterSequentialSpec : SequentialSpec (Op BCOp) where
  State := ℕ → ℤ
  init := fun _ => 0
  step q e := fun r =>
    match e.2.2 with
    | .inc => q r + if r = e.2.1 then 1 else 0
    | .dec => q r - if r = e.2.1 then 1 else 0

def BCSequentialHonest (ops : List (Op BCOp)) : Prop :=
  ∀ pre suf, ops = pre ++ suf → BCInv (applySeq BC.toCRDTSig BC.init pre)

theorem bc_sequential_run (ops : List (Op BCOp)) :
    ∀ r, boundedCounterSequentialSpec.run ops r =
      (applySeq BC.toCRDTSig BC.init ops).1 r -
      (applySeq BC.toCRDTSig BC.init ops).2 r := by
  induction ops using List.reverseRecOn with
  | nil => intro r; rfl
  | append_singleton ops e ih =>
      intro r
      obtain ⟨ts, ro, op⟩ := e
      rw [SequentialSpec.run_append_single, applySeq_append_single]
      cases op with
      | inc =>
          change boundedCounterSequentialSpec.run ops r +
              (if r = ro then 1 else 0) = _
          rw [ih r]
          simp only [BC_update_eq, bcUpdate_inc_fst, bcUpdate_inc_snd]
          split_ifs <;> omega
      | dec =>
          change boundedCounterSequentialSpec.run ops r -
              (if r = ro then 1 else 0) = _
          rw [ih r]
          simp only [BC_update_eq, bcUpdate_dec_fst, bcUpdate_dec_snd]
          split_ifs <;> omega

def boundedCounterSequentialRefinement :
    HistorySequentialRefinement BC boundedCounterSequentialSpec where
  Honest := BCSequentialHonest
  Rel s q := BCInv s ∧ ∀ r, q r = s.1 r - s.2 r
  init := ⟨bc_inv_init, fun _ => rfl⟩
  sound := fun ops h =>
    ⟨h ops [] (by simp), bc_sequential_run ops⟩

def boundedCounterVerified : VerifiedMRDT BC where
  Honest := fun _ => True
  initInv := trivial
  join := fun C _ => (joinKitAt_plain_iff BC C).2
    ((join_lemma3_of_cd_feasible BC_coreVCs3.toCD
      (feasibleDeltaVCs3_of_delta BC_coreVCs3 BC_deltaVCs3)
      (cdVC3_of_all_comm BC_coreVCs3 BC_all_comm)) C)
  Spec := boundedCounterSequentialSpec
  seq := boundedCounterSequentialRefinement

theorem bc_version_invV (C : Configuration BC)
    (hReach : HonestReachV BC BCHonest trivial C) (hHon : BCHonest C) :
    ∀ v s E, C.ver v = some (s, E) → BCInv s := by
  let hJoin : ∀ C' : Configuration BC,
      BCHonest C' → JoinLemma3At BC (Configuration.core C') :=
    fun C' _ =>
      (join_lemma3_of_cd_feasible BC_coreVCs3.toCD
        (feasibleDeltaVCs3_of_delta BC_coreVCs3 BC_deltaVCs3)
        (cdVC3_of_all_comm BC_coreVCs3 BC_all_comm)) (Configuration.core C')
  have hGood : GoodConfig3 C := goodConfig3_of_honest_reachV hJoin hReach
  have hCC : CausalCanonical C :=
    causalCanonical_of_all_comm_rc_either BC_all_comm BC_rc_either hGood
  have hObs : ObservedRegistered C :=
    observedRegistered_of_honest_reachV hReach
  exact version_inv_on_of_causal_canonical bc_inv_init bc_safetyStep hGood hCC
    (bc_honestAppOn hObs hCC hHon)

-- Positive controls: the public guard is definitionally the real issuer check.
example : boundedCounterGeneration.Guard = bcApplicable := rfl
example : queueGeneration.Guard = qApplicable := rfl

-- Negative control: the queue contract does not collapse to a trivial guard.
example : ¬ (∀ (o : Op QOp) (s : QState), queueGeneration.Guard o s) := by
  intro h
  have := h (0, 0, QOp.deq 7) []
  simpa [queueGeneration, qApplicable] using this

#print axioms queueGeneration
#print axioms embedGeneration
#print axioms sidedGeneration
#print axioms peritextEmbedGeneration

/-! ## Bounded-counter flagship

One public result now connects the actual issuer guard, raw convergence,
history honesty, the per-version escrow invariant, and its observable bound.
The independent sequential balance machine is packaged below; this
configuration theorem states its distributed convergence and safety half. -/

structure BoundedCounterFlagship (C : Configuration BC) : Prop where
  guard_public : boundedCounterGeneration.Guard = bcApplicable
  ra_linearizable : IsRALinearizable3 C
  versions_safe : ∀ v s E, C.ver v = some (s, E) → BCInv s
  values_nonnegative : ∀ v s E, C.ver v = some (s, E) → ∀ rs : List ℕ,
    0 ≤ (rs.map (fun r => s.1 r - s.2 r)).sum

def boundedCounterSafety : SafetyCertificate BC boundedCounterGeneration where
  Safe := BCInv
  Observable := fun s => ∀ rs : List ℕ,
    0 ≤ (rs.map (fun r => s.1 r - s.2 r)).sum
  preservation := by
    intro hInit C h
    apply bc_version_inv C
    · exact rawReach_of_guardedReach (guardedReach_of_mintCertified h)
    · exact boundedCounterGeneration.history_of_mint C
        (mintHonest_of_mintCertified h)
  preservationV := by
    intro hInit C h
    apply bc_version_invV C (honestReachV_of_mintCertified h)
    exact boundedCounterGeneration.history_of_mint C (by
      cases h with
      | init => exact mintHonest_init boundedCounterGeneration.Guard hInit
      | step _ _ _ hpost => exact hpost)
  consequence := by
    intro s hs rs
    induction rs with
    | nil => simp
    | cons r rs ih =>
        have hr := hs r
        simp only [List.map_cons, List.sum_cons]
        omega

noncomputable def boundedCounterUnified : UnifiedVerifiedMRDT BC where
  verified := boundedCounterVerified
  generation := boundedCounterGeneration
  history_entails_honest := fun _ _ => trivial
  safety := boundedCounterSafety

open LabeledTS in
theorem boundedCounter_flagship (C : Configuration BC)
    (hReach : (labeledTS3 BC).ReachableFrom (initConfig BC trivial) C)
    (hHonest : BCHonest C) : BoundedCounterFlagship C where
  guard_public := rfl
  ra_linearizable := bc_ra_linearizable3 C hReach
  versions_safe := bc_version_inv C hReach hHonest
  values_nonnegative := by
    intro v s E hv rs
    exact bc_value_nonneg C hReach hHonest v s E hv rs

/-- End-to-end conditioned entry point: the operational derivation itself
records every issuer-head check, from which both raw reachability and the
counter's established all-enumerations honesty premise follow. -/
theorem boundedCounter_guarded_flagship (C : Configuration BC)
    (h : MintCertifiedReach3 BC boundedCounterGeneration trivial C) :
    BoundedCounterFlagship C := by
  apply boundedCounter_flagship C
  · exact rawReach_of_guardedReach (guardedReach_of_mintCertified h)
  · exact boundedCounterGeneration.history_of_mint C
      (mintHonest_of_mintCertified h)

/-- The bounded counter's complete public conditioned package. It uses the
history/global safety certificate (not the refuted arbitrary-merge rule) and
includes the independent sequential balance machine. -/
structure BoundedCounterCertificate where
  generation : GenerationContract BC
  sequential : HistorySequentialRefinement BC boundedCounterSequentialSpec
  safety : SafetyCertificate BC generation
  guarded_correct : ∀ C,
    MintCertifiedReach3 BC generation trivial C → BoundedCounterFlagship C

noncomputable def boundedCounterCertificate : BoundedCounterCertificate where
  generation := boundedCounterGeneration
  sequential := boundedCounterSequentialRefinement
  safety := boundedCounterSafety
  guarded_correct := boundedCounter_guarded_flagship

#print axioms boundedCounter_flagship
#print axioms boundedCounter_guarded_flagship
#print axioms boundedCounterCertificate

/-! ## Unified positive certificates

These instances have no additional client-safety predicate beyond structural
well-formedness, so their safety component is explicitly `True`.  Their
generation and Join histories remain nontrivial. -/

noncomputable def queueUnified : UnifiedVerifiedMRDT Q where
  verified := queueVerified
  generation := queueGeneration
  history_entails_honest := fun _ h => qHonest_core h
  safety := SafetyCertificate.trivial queueGeneration

noncomputable def embedUnified {α : Type} [DecidableEq α] [Inhabited α]
    (Γ : OrderedPrefixCode) : UnifiedVerifiedMRDT (E Γ α) where
  verified := embedVerified Γ
  generation := embedGeneration Γ
  history_entails_honest := fun _ h => eHonest_core h
  safety := SafetyCertificate.trivial (embedGeneration Γ)

noncomputable def sidedUnified (Γ : OrderedPrefixCode) :
    UnifiedVerifiedMRDT (S Γ) where
  verified := sidedVerified Γ
  generation := sidedGeneration Γ
  history_entails_honest := fun _ h => sHonest_core h
  safety := SafetyCertificate.trivial (sidedGeneration Γ)

noncomputable def peritextEmbedUnified (Γ : OrderedPrefixCode) :
    UnifiedVerifiedMRDT
      (E Γ Sal.ConditionedMRDTs.Peritext.PeritextElt) :=
  embedUnified Γ

#print axioms queueUnified
#print axioms embedUnified
#print axioms sidedUnified
#print axioms peritextEmbedUnified

end Sal.ConditionedMRDTs
