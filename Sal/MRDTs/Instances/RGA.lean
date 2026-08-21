import Sal.MRDTs.Metatheory.Correctness
import Sal.MRDTs.Instances.Common



/-!
# RGA (tombstone-based): flat VC discharge and the conditioned capstone
-/

set_option maxHeartbeats 1000000

namespace Sal.MRDTs.Instances.RGA

open Sal.MRDTs.Foundation
open Classical

/-! ## RGA, tombstone-based (production mirror: `Sal/MRDTs/RGA`),
Tier-1 in disguise: both components grow-only, `rc = Either`, all pairs
commute, LCA-inclusive union merge. -/

inductive RGAOp : Type where
  | addAfter : ℕ → ℕ → RGAOp
  | remove : ℕ → RGAOp
deriving DecidableEq

def rgaUpdate (s : ((ℕ × ℕ × ℕ) → Bool) × (ℕ → Bool)) (o : Op RGAOp) :
    ((ℕ × ℕ × ℕ) → Bool) × (ℕ → Bool) :=
  match o.2.2 with
  | .addAfter af el => (fun p => s.1 p || decide (p = (o.1, af, el)), s.2)
  | .remove id => (s.1, fun x => s.2 x || decide (x = id))

noncomputable def RGAM : MRDTSig where
  State := ((ℕ × ℕ × ℕ) → Bool) × (ℕ → Bool)
  dec_state := fun _ _ => Classical.propDecidable _
  init := (fun _ => false, fun _ => false)
  AppOp := RGAOp
  dec_op := inferInstance
  Query := Unit
  Value := ((ℕ × ℕ × ℕ) → Bool) × (ℕ → Bool)
  update := rgaUpdate
  merge := fun a b =>
    (fun p => false || (a.1 p || b.1 p), fun x => false || (a.2 x || b.2 x))
  query := fun s _ => s
  rc := fun _ _ => RcRes.Either
  mergeL := fun l a b =>
    (fun p => l.1 p || (a.1 p || b.1 p), fun x => l.2 x || (a.2 x || b.2 x))
  merge_init_slice := fun _ _ => rfl

theorem RGAM_rc_either : ∀ o₁ o₂ : Op RGAM.AppOp,
    RGAM.toCRDTSig.rc o₁ o₂ = RcRes.Either := fun _ _ => rfl

theorem RGAM_all_comm : ∀ a b : Op RGAM.AppOp,
    RGAM.toCRDTSig.commutes a b := by
  rintro ⟨tsa, ra, opa⟩ ⟨tsb, rb, opb⟩ s
  cases opa <;> cases opb
  · exact Prod.ext (funext fun p => bor_rc (s.1 p) _ _) rfl
  · rfl
  · rfl
  · exact Prod.ext rfl (funext fun x => bor_rc (s.2 x) _ _)

theorem RGAM_updateVCs : UpdateVCs RGAM.toCRDTSig := by
  refine ⟨?_, ?_, ?_⟩
  · intro o₁ o₂ _ _
    constructor
    · intro h
      exact absurd (RGAM_all_comm o₁ o₂) h
    · rintro (h | h) <;>
        (rw [RGAM_rc_either] at h; exact RcRes.noConfusion h)
  · intro o₁ o₂ o₃ _ _
    rintro ⟨h, _⟩
    rw [RGAM_rc_either] at h
    exact RcRes.noConfusion h
  · intro s e e' e'' π _ _ _ h_rc _
    rw [RGAM_rc_either] at h_rc
    exact RcRes.noConfusion h_rc

theorem RGAM_coreVCs3 : CoreVCs3 RGAM := by
  refine ⟨RGAM_updateVCs, ?_, ?_, ?_, ?_⟩
  · intro l a b
    exact Prod.ext (funext fun p => bor_comm (l.1 p) (a.1 p) (b.1 p))
      (funext fun x => bor_comm (l.2 x) (a.2 x) (b.2 x))
  · intro s
    exact Prod.ext (funext fun p => bor_init (s.1 p))
      (funext fun x => bor_init (s.2 x))
  · rintro l a b ⟨ts, r, op⟩
    cases op with
    | addAfter af el =>
      exact Prod.ext (funext fun p => bor_0op (l.1 p) (a.1 p) (b.1 p) _) rfl
    | remove id =>
      exact Prod.ext rfl (funext fun x => bor_0op (l.2 x) (a.2 x) (b.2 x) _)
  · rintro a ⟨ts, r, op⟩ π₀ π₂ _ _
    cases op with
    | addAfter af el =>
      exact Prod.ext (funext fun p =>
        bor_peel ((applySeq RGAM.toCRDTSig RGAM.init π₀).1 p) (a.1 p)
          ((applySeq RGAM.toCRDTSig RGAM.init π₂).1 p) _) rfl
    | remove id =>
      exact Prod.ext rfl (funext fun x =>
        bor_peel ((applySeq RGAM.toCRDTSig RGAM.init π₀).2 x) (a.2 x)
          ((applySeq RGAM.toCRDTSig RGAM.init π₂).2 x) _)

theorem RGAM_deltaVCs3 : DeltaVCs3 RGAM := by
  constructor
  · intro m x₀ x₁ x₂ c
    exact Prod.ext
      (funext fun p => bor_redis (m.1 p) (x₀.1 p) (x₁.1 p) (x₂.1 p) (c.1 p))
      (funext fun x => bor_redis (m.2 x) (x₀.2 x) (x₁.2 x) (x₂.2 x) (c.2 x))
  · intro l m x c y
    exact Prod.ext
      (funext fun p => bor_lredis (l.1 p) (m.1 p) (x.1 p) (c.1 p) (y.1 p))
      (funext fun q => bor_lredis (l.2 q) (m.2 q) (x.2 q) (c.2 q) (y.2 q))

private theorem rgaJoin : JoinLemma3 RGAM :=
  join_lemma3_of_cd_feasible RGAM_coreVCs3.toCD
    (feasibleDeltaVCs3_of_delta RGAM_coreVCs3 RGAM_deltaVCs3)
    (cdVC3_of_all_comm RGAM_coreVCs3 RGAM_all_comm)

abbrev RGAEntry := ℕ × ℕ × ℕ

structure RGASeqState where
  adds : Finset RGAEntry
  grave : Finset ℕ
  deriving DecidableEq

private def insertAfter (anchor value : ℕ) : List ℕ → List ℕ
  | [] => if anchor = 0 then [value] else []
  | x :: tail =>
      if anchor = 0 then value :: x :: tail
      else if x = anchor then x :: value :: tail
      else x :: insertAfter anchor value tail

noncomputable def sequence (q : RGASeqState) : List ℕ :=
  let ordered := q.adds.toList.mergeSort (fun a b => a.1 ≤ b.1)
  let inserted := ordered.foldl (fun xs e => insertAfter e.2.1 e.2.2 xs) []
  inserted.filter (fun id => id ∉ q.grave)

def spec : SequentialSpec (Op RGAOp) where
  State := RGASeqState
  init := ⟨∅, ∅⟩
  step q e := match e.2.2 with
    | .addAfter anchor id => ⟨insert (e.1, anchor, id) q.adds, q.grave⟩
    | .remove id => ⟨q.adds, insert id q.grave⟩

def stateRel (s : RGAM.State) (q : RGASeqState) : Prop :=
  (∀ e, s.1 e = decide (e ∈ q.adds)) ∧
  (∀ id, s.2 id = decide (id ∈ q.grave))

def applicable (e : Op RGAOp) (s : RGAM.State) : Prop :=
  match e.2.2 with
  | .addAfter anchor id =>
      (anchor = 0 ∨ ∃ ts parent, ts < e.1 ∧ s.1 (ts, parent, anchor) = true) ∧
      (∀ anchor' id', s.1 (e.1, anchor', id') = false) ∧
      (∀ ts anchor', s.1 (ts, anchor', id) = false) ∧ s.2 id = false
  | .remove id =>
      (∃ ts anchor, s.1 (ts, anchor, id) = true) ∧ s.2 id = false

/-- Every operation passed the public generation guard at its exact local
prefix.  The extensional state relation below does not need this premise, but
the certificate retains the client/runtime protocol instead of erasing it. -/
def HistoryOK (ops : List (Op RGAOp)) : Prop :=
  ∀ (pre : List (Op RGAOp)) (e : Op RGAOp) (post : List (Op RGAOp)),
    ops = pre ++ e :: post →
    applicable e (applySeq RGAM.toCRDTSig RGAM.init pre)

theorem sequentialSound (ops : List (Op RGAOp)) :
    stateRel (applySeq RGAM.toCRDTSig RGAM.init ops) (spec.run ops) := by
  induction ops using List.reverseRecOn with
  | nil =>
      constructor <;> intro x <;> simp [applySeq, SequentialSpec.run, RGAM, spec]
  | append_singleton ops e ih =>
      rw [applySeq_append_single, SequentialSpec.run_append_single]
      rcases e with ⟨ts, replica, op⟩
      cases op with
      | addAfter anchor id =>
          constructor
          · intro p
            change ((applySeq RGAM.toCRDTSig RGAM.init ops).1 p ||
                decide (p = (ts, anchor, id))) =
              decide (p ∈ insert (ts, anchor, id) (spec.run ops).adds)
            rw [ih.1 p]
            simp [Bool.or_comm]
          · intro x
            simpa [rgaUpdate, spec] using ih.2 x
      | remove id =>
          constructor
          · intro p
            simpa [rgaUpdate, spec] using ih.1 p
          · intro x
            change ((applySeq RGAM.toCRDTSig RGAM.init ops).2 x || decide (x = id)) =
              decide (x ∈ insert id (spec.run ops).grave)
            rw [ih.2 x]
            simp [eq_comm, Bool.or_comm]

def generation : GenerationContract RGAM where
  Guard := applicable
  History := fun _ => True
  history_of_mint := fun _ _ => True.intro

def convergence : ConvergenceCertificate RGAM generation where
  sound := fun h => ra_of_mintCertified (fun _ _ => rgaJoin _) h
  soundV := fun h => ra_of_mintCertifiedV (fun _ _ => rgaJoin _) h

def sequential : SequentialRefinement RGAM spec where
  Honest := HistoryOK
  Rel := stateRel
  init := by constructor <;> intro x <;> simp [RGAM, spec]
  sound := fun ops _ => sequentialSound ops

noncomputable def verified : VerifiedMRDT RGAM where
  generation := generation
  convergence := convergence
  Spec := spec
  sequential := sequential
  sequential_of_mint := fun _ h => by
    simpa [sequential, HistoryOK, generation] using h.guarded
  safety := SafetyCertificate.trivial generation

#print axioms verified
#print axioms sequentialSound

end Sal.MRDTs.Instances.RGA
