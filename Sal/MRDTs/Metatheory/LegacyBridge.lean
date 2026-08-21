import Sal.MRDTs.Framework.StateGC
import Sal.ConditionedMRDTs.Metatheory.Adequacy
import Sal.ConditionedMRDTs.Metatheory.UnifiedVerifiedMRDT

/-!
# Temporary migration bridge

This module is permitted only on the refactoring branch.  It establishes that
dropping vacuous signature conditioning and the stored `ver_inv` proof does
not change operational data.  Production modules must not depend on it at the
final cutover.
-/

namespace Sal.MRDTs

open Sal.Emulation

namespace LegacyBridge

abbrev OldSig := Sal.ConditionedMRDTs.ConditionedMRDTSig
abbrev OldConfiguration := Sal.ConditionedMRDTs.Configuration

/-- Forget signature-level conditioning without changing the datatype. -/
def signature (D : OldSig) : MRDTSig where
  toCRDTSig := D.toCRDTSig
  mergeL := D.mergeL
  merge_init_slice := D.merge_init_slice

def eraseLabel {D : OldSig} :
    Sal.ConditionedMRDTs.Label3 D → Label (signature D)
  | .createReplica r => .createReplica r
  | .apply t r o => .apply t r o
  | .merge r₁ r₂ => .merge r₁ r₂
  | .query r q v => .query r q v

def liftLabel {D : OldSig} :
    Label (signature D) → Sal.ConditionedMRDTs.Label3 D
  | .createReplica r => .createReplica r
  | .apply t r o => .apply t r o
  | .merge r₁ r₂ => .merge r₁ r₂
  | .query r q v => .query r q v

@[simp] theorem erase_liftLabel {D : OldSig} (l : Label (signature D)) :
    eraseLabel (liftLabel l) = l := by
  cases l <;> rfl

/-- Forget only the proof that every registered state satisfies `D.Inv`. -/
def eraseConfiguration {D : OldSig}
    (C : OldConfiguration D) : Configuration (signature D) where
  N := C.N
  L := C.L
  vis := C.vis
  dom_eq := C.dom_eq
  vis_src := C.vis_src
  vis_tgt := C.vis_tgt
  vis_causal := C.vis_causal
  timestamps_distinct := C.timestamps_distinct
  causal_mono := C.causal_mono
  vis_total_same_replica := C.vis_total_same_replica
  ver := C.ver
  head := C.head
  parents := C.parents
  parents_lt := C.parents_lt
  ver_init := C.ver_init
  head_coherent := C.head_coherent
  lca_events := C.lca_events

/-- Flat signatures can temporarily recover the old proof-carrying
configuration.  The need for `invEverywhere` is exactly why this bridge must
not become the new public API. -/
def liftConfiguration (D : OldSig) (invEverywhere : ∀ s, D.Inv s)
    (C : Configuration (signature D)) : OldConfiguration D where
  N := C.N
  L := C.L
  vis := C.vis
  dom_eq := C.dom_eq
  vis_src := C.vis_src
  vis_tgt := C.vis_tgt
  vis_causal := C.vis_causal
  timestamps_distinct := C.timestamps_distinct
  causal_mono := C.causal_mono
  vis_total_same_replica := C.vis_total_same_replica
  ver := C.ver
  head := C.head
  parents := C.parents
  parents_lt := C.parents_lt
  ver_init := C.ver_init
  head_coherent := C.head_coherent
  ver_inv := fun _ s _ _ => invEverywhere s
  lca_events := C.lca_events

@[simp] theorem erase_lift (D : OldSig) (invEverywhere : ∀ s, D.Inv s)
    (C : Configuration (signature D)) :
    eraseConfiguration (liftConfiguration D invEverywhere C) = C := rfl

@[simp] theorem lift_erase_data {D : OldSig} (invEverywhere : ∀ s, D.Inv s)
    (C : OldConfiguration D) :
    eraseConfiguration (liftConfiguration D invEverywhere
      (eraseConfiguration C)) = eraseConfiguration C := rfl

@[simp] theorem erase_init (D : OldSig) (hInit : D.Inv D.init) :
    eraseConfiguration (Sal.ConditionedMRDTs.initConfig D hInit) =
      initConfig (signature D) := rfl

/-- Erasing proof-only conditioning maps every old raw step to the new raw
step with the same label and operational data. -/
theorem erase_step {D : OldSig} {C C' : OldConfiguration D}
    {l : Sal.ConditionedMRDTs.Label3 D}
    (h : Sal.ConditionedMRDTs.Step3 D C l C') :
    Step (signature D) (eraseConfiguration C)
      (eraseLabel l)
      (eraseConfiguration C') := by
  cases h with
  | createReplica fresh C' hN hL hvis hver hhead hparents =>
      exact .createReplica fresh _ hN hL hvis hver hhead hparents
  | apply hhead hver ht hs hv hr C' hN hL hvis hver' hhead' hparents =>
      exact .apply hhead hver ht hs hv hr _ hN hL hvis hver' hhead' hparents
  | @merge r₁ r₂ v₁ v₂ vT vm s₁ s₂ sT ev₁ ev₂ evT
      hh₁ hh₂ hv₁ hv₂ hlca hvT hvm hr₁ hr₂ C'
      hN hL hvis hver hhead hparents =>
      have hlca' : IsLCA C.parents v₁ v₂ vT := by
        simpa [IsLCA, Reaches, Sal.ConditionedMRDTs.IsLCA,
          Sal.ConditionedMRDTs.Reaches] using hlca
      exact .merge hh₁ hh₂ hv₁ hv₂ hlca' hvT hvm hr₁ hr₂ _
        hN hL hvis hver hhead hparents
  | query hs hv => exact .query hs hv

/-- For a flat legacy signature, every new raw step can be reflected into the
old proof-carrying semantics. -/
theorem lift_step (D : OldSig) (invEverywhere : ∀ s, D.Inv s)
    {C C' : Configuration (signature D)} {l : Label (signature D)}
    (h : Step (signature D) C l C') :
    Sal.ConditionedMRDTs.Step3 D
      (liftConfiguration D invEverywhere C)
      (liftLabel l)
      (liftConfiguration D invEverywhere C') := by
  cases h with
  | createReplica fresh C' hN hL hvis hver hhead hparents =>
      exact .createReplica fresh _ hN hL hvis hver hhead hparents
  | apply hhead hver ht hs hv hr C' hN hL hvis hver' hhead' hparents =>
      exact .apply hhead hver ht hs hv hr _ hN hL hvis hver' hhead' hparents
  | @merge r₁ r₂ v₁ v₂ vT vm s₁ s₂ sT ev₁ ev₂ evT
      hh₁ hh₂ hv₁ hv₂ hlca hvT hvm hr₁ hr₂ C'
      hN hL hvis hver hhead hparents =>
      have hlca' : Sal.ConditionedMRDTs.IsLCA C.parents v₁ v₂ vT := by
        simpa [IsLCA, Reaches, Sal.ConditionedMRDTs.IsLCA,
          Sal.ConditionedMRDTs.Reaches] using hlca
      exact .merge hh₁ hh₂ hv₁ hv₂ hlca' hvT hvm hr₁ hr₂ _
        hN hL hvis hver hhead hparents
  | query hs hv => exact .query hs hv

/-- The observable RA-linearizability statement is unchanged by the
proof-field migration. -/
theorem raLinearizable_iff (D : OldSig) (invEverywhere : ∀ s, D.Inv s)
    (C : Configuration (signature D)) :
    IsRALinearizable (signature D) C ↔
      Sal.ConditionedMRDTs.IsRALinearizable3
        (liftConfiguration D invEverywhere C) := by
  rfl

theorem mintHonest_iff (D : OldSig) (invEverywhere : ∀ s, D.Inv s)
    (Guard : Op D.AppOp → D.State → Prop)
    (C : Configuration (signature D)) :
    MintHonest (signature D) Guard C ↔
      Sal.ConditionedMRDTs.MintHonest D Guard
        (Sal.ConditionedMRDTs.Configuration.core
          (liftConfiguration D invEverywhere C)) := by
  rfl

/-- Temporary adapter for an existing production generation contract. -/
noncomputable def generation (D : OldSig) (invEverywhere : ∀ s, D.Inv s)
    (G : Sal.ConditionedMRDTs.GenerationContract D) :
    GenerationContract (signature D) where
  Guard := G.Guard
  History := fun C => G.History (liftConfiguration D invEverywhere C)
  history_of_mint := by
    intro C h
    apply G.history_of_mint
    exact (mintHonest_iff D invEverywhere G.Guard C).mp h

theorem lift_guardedStep (D : OldSig) (invEverywhere : ∀ s, D.Inv s)
    (G : Sal.ConditionedMRDTs.GenerationContract D)
    {C C' : Configuration (signature D)} {l : Label (signature D)}
    (h : GuardedStep (signature D) (generation D invEverywhere G) C l C') :
    Sal.ConditionedMRDTs.GuardedStep3 D G
      (liftConfiguration D invEverywhere C) (liftLabel l)
      (liftConfiguration D invEverywhere C') := by
  cases h with
  | nonApply raw hn =>
      apply Sal.ConditionedMRDTs.GuardedStep3.nonApply
      · exact lift_step D invEverywhere raw
      · intro t r o heq
        cases l with
        | createReplica r' => cases heq
        | apply t' r' o' => exact hn t' r' o' rfl
        | merge r₁ r₂ => cases heq
        | query r' q v => cases heq
  | apply hh hv hg raw =>
      exact Sal.ConditionedMRDTs.GuardedStep3.apply hh hv hg
        (lift_step D invEverywhere raw)

theorem lift_mintCertified (D : OldSig) (invEverywhere : ∀ s, D.Inv s)
    (G : Sal.ConditionedMRDTs.GenerationContract D)
    {C : Configuration (signature D)}
    (h : MintCertifiedReach (signature D) (generation D invEverywhere G) C) :
    Sal.ConditionedMRDTs.MintCertifiedReach3 D G (invEverywhere D.init)
      (liftConfiguration D invEverywhere C) := by
  induction h with
  | init => exact .init
  | @step C C' l _ hpre hstep hpost ih =>
      exact .step ih
        ((mintHonest_iff D invEverywhere G.Guard C).mp hpre)
        (lift_guardedStep D invEverywhere G hstep)
        ((mintHonest_iff D invEverywhere G.Guard C').mp hpost)

def sequentialSpec {D : OldSig}
    (S : Sal.ConditionedMRDTs.SequentialSpec (Op D.AppOp)) :
    SequentialSpec (Op (signature D).AppOp) where
  State := S.State
  init := S.init
  step := S.step

def sequentialRefinement {D : OldSig}
    {S : Sal.ConditionedMRDTs.SequentialSpec (Op D.AppOp)}
    (R : Sal.ConditionedMRDTs.HistorySequentialRefinement D S) :
    SequentialRefinement (signature D) (sequentialSpec S) where
  Honest := R.Honest
  Rel := R.Rel
  init := R.init
  sound := R.sound

theorem linearMintHistory_iff {D : OldSig}
    (Guard : Op D.AppOp → D.State → Prop) (ops : List (Op D.AppOp)) :
    LinearMintHistory (signature D) Guard ops ↔
      Sal.ConditionedMRDTs.LinearMintHistory D Guard ops := by
  constructor
  · intro h
    exact ⟨h.guarded, h.clocked⟩
  · intro h
    exact ⟨h.guarded, h.clocked⟩

/-- The established recursive-MCA virtual base, exposed through the new
proof-erasing configuration boundary. -/
noncomputable def virtualLCA (D : OldSig) (invEverywhere : ∀ s, D.Inv s) :
    VirtualLCAResolver (signature D) where
  state := fun C v₁ v₂ =>
    Sal.ConditionedMRDTs.virtualLCAState
      (liftConfiguration D invEverywhere C) v₁ v₂

theorem lift_stepV (D : OldSig) (invEverywhere : ∀ s, D.Inv s)
    {C C' : Configuration (signature D)} {l : Label (signature D)}
    (h : StepV (signature D) (virtualLCA D invEverywhere) C l C') :
    Sal.ConditionedMRDTs.Step3V D
      (liftConfiguration D invEverywhere C) (liftLabel l)
      (liftConfiguration D invEverywhere C') := by
  cases h with
  | base h => exact .base (lift_step D invEverywhere h)
  | mergeVirtual hh₁ hh₂ hv₁ hv₂ hvm hr₁ hr₂ C' hN hL hvis hver hhead hparents =>
      exact .mergeVirtual hh₁ hh₂ hv₁ hv₂ hvm hr₁ hr₂ _
        hN hL hvis hver hhead hparents

theorem erase_stepV (D : OldSig) (invEverywhere : ∀ s, D.Inv s)
    {C C' : OldConfiguration D} {l : Sal.ConditionedMRDTs.Label3 D}
    (h : Sal.ConditionedMRDTs.Step3V D C l C') :
    StepV (signature D) (virtualLCA D invEverywhere)
      (eraseConfiguration C) (eraseLabel l) (eraseConfiguration C') := by
  cases h with
  | base h => exact .base (erase_step h)
  | mergeVirtual hh₁ hh₂ hv₁ hv₂ hvm hr₁ hr₂ C' hN hL hvis hver hhead hparents =>
      exact .mergeVirtual hh₁ hh₂ hv₁ hv₂ hvm hr₁ hr₂ _
        hN hL hvis (by simpa [virtualLCA]) hhead hparents

theorem lift_guardedStepV (D : OldSig) (invEverywhere : ∀ s, D.Inv s)
    (G : Sal.ConditionedMRDTs.GenerationContract D)
    {C C' : Configuration (signature D)} {l : Label (signature D)}
    (h : GuardedStepV (signature D) (virtualLCA D invEverywhere)
      (generation D invEverywhere G) C l C') :
    Sal.ConditionedMRDTs.GuardedStep3V D G
      (liftConfiguration D invEverywhere C) (liftLabel l)
      (liftConfiguration D invEverywhere C') := by
  cases h with
  | base hguard => exact .base (lift_guardedStep D invEverywhere G hguard)
  | virtual hraw hnot =>
      exact .virtual (lift_stepV D invEverywhere hraw) (by
        intro hold
        apply hnot
        simpa using erase_step hold)

theorem lift_mintCertifiedV (D : OldSig) (invEverywhere : ∀ s, D.Inv s)
    (G : Sal.ConditionedMRDTs.GenerationContract D)
    {C : Configuration (signature D)}
    (h : MintCertifiedReachV (signature D) (virtualLCA D invEverywhere)
      (generation D invEverywhere G) C) :
    Sal.ConditionedMRDTs.MintCertifiedReach3V D G (invEverywhere D.init)
      (liftConfiguration D invEverywhere C) := by
  induction h with
  | init => exact .init
  | @step C C' l _ hpre hstep hpost ih =>
      exact .step ih
        ((mintHonest_iff D invEverywhere G.Guard C).mp hpre)
        (lift_guardedStepV D invEverywhere G hstep)
        ((mintHonest_iff D invEverywhere G.Guard C').mp hpost)

def safety (D : OldSig) (invEverywhere : ∀ s, D.Inv s)
    (G : Sal.ConditionedMRDTs.GenerationContract D)
    (S : Sal.ConditionedMRDTs.SafetyCertificate D G) :
    SafetyCertificate (signature D) (virtualLCA D invEverywhere)
      (generation D invEverywhere G) where
  Safe := S.Safe
  Observable := S.Observable
  preservation := by
    intro C h
    exact S.preservation (lift_mintCertified D invEverywhere G h)
  preservationV := by
    intro C h
    exact S.preservationV (lift_mintCertifiedV D invEverywhere G h)
  consequence := S.consequence

/-- Temporary end-to-end package adapter for flat production signatures.
The only extra premise is the already-public bridge from clocked local minting
to the sequential theorem's history discipline. -/
noncomputable def verified (D : OldSig) (invEverywhere : ∀ s, D.Inv s)
    (U : Sal.ConditionedMRDTs.UnifiedVerifiedMRDT D)
    (sequential_of_mint : ∀ ops,
      Sal.ConditionedMRDTs.LinearMintHistory D U.generation.Guard ops →
        U.verified.seq.Honest ops) :
    VerifiedMRDT (signature D) where
  generation := generation D invEverywhere U.generation
  virtualLCA := virtualLCA D invEverywhere
  convergence := {
    sound := by
      intro C h
      apply (raLinearizable_iff D invEverywhere C).mpr
      exact U.ra_linearizable (lift_mintCertified D invEverywhere U.generation h)
    soundV := by
      intro C h
      apply (raLinearizable_iff D invEverywhere C).mpr
      exact U.ra_linearizableV
        (lift_mintCertifiedV D invEverywhere U.generation h) }
  Spec := sequentialSpec U.verified.Spec
  sequential := sequentialRefinement U.verified.seq
  sequential_of_mint := by
    intro ops h
    apply sequential_of_mint ops
    exact (linearMintHistory_iff U.generation.Guard ops).mp h
  safety := safety D invEverywhere U.generation U.safety

end LegacyBridge

end Sal.MRDTs
