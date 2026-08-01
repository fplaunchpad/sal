import Sal.ConditionedMRDTs.Metatheory.Stability_VC

/-!
# World-indexed observational compaction

A settled cut is a monotone world.  This file isolates the part of multi-epoch
reasoning that is independent of MRDT states and DAG plumbing: once a later
compaction absorbs every earlier world observationally, any finite prefix of
earlier compactions collapses beneath the final one.
-/

namespace Sal.ConditionedMRDTs

/-- A family of representation-changing callbacks indexed by monotone worlds.
`coherent` is the common-observation form of `EpochCoherentObs`. -/
structure WorldCompaction (World State Obs : Type) [Preorder World] where
  compact : World → State → State
  observe : State → Obs
  coherent : ∀ {w w'}, w ≤ w' → ∀ s,
    observe (compact w' (compact w s)) = observe (compact w' s)

namespace WorldCompaction

variable {World State Obs : Type} [Preorder World]
  (F : WorldCompaction World State Obs)

/-- Apply a sequence of compaction epochs, oldest first. -/
def compactSeq : List World → State → State
  | [], s => s
  | w :: ws, s => compactSeq ws (F.compact w s)

/-- **Finite epoch collapse.** If every epoch in a prefix is below the final
world, applying the entire prefix and then compacting at the final world is
observationally identical to compacting at the final world directly.  No
relation between adjacent prefix worlds is required. -/
theorem observe_compactSeq_collapse {last : World} {ws : List World}
    (hBelow : ∀ w ∈ ws, w ≤ last) (s : State) :
    F.observe (F.compact last (F.compactSeq ws s)) =
      F.observe (F.compact last s) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    rw [compactSeq]
    calc
      F.observe (F.compact last (F.compactSeq ws (F.compact w s))) =
          F.observe (F.compact last (F.compact w s)) :=
        ih (fun x hx => hBelow x (List.mem_cons_of_mem w hx)) _
      _ = F.observe (F.compact last s) :=
        F.coherent (hBelow w (List.mem_cons_self)) s

/-- The three-epoch form used most often by staggered replicas. -/
theorem observe_three_collapse {w₁ w₂ w₃ : World}
    (h₁ : w₁ ≤ w₃) (h₂ : w₂ ≤ w₃) (s : State) :
    F.observe (F.compact w₃ (F.compact w₂ (F.compact w₁ s))) =
      F.observe (F.compact w₃ s) := by
  simpa [compactSeq] using
    F.observe_compactSeq_collapse
      (ws := [w₁, w₂]) (last := w₃)
      (fun w hw => by
        simp at hw
        rcases hw with rfl | rfl
        · exact h₁
        · exact h₂) s

end WorldCompaction

/-- A `StabilityVC` family with a shared observation interface.  Individual
epochs retain their full step/merge simulation bundles; `world` supplies the
generic finite-epoch theorem above. -/
structure StabilityEpochFamily (D : ConditionedMRDTSig) (World : Type)
    [Preorder World] where
  Obs : Type
  bundle : World → StabilityVC D
  observe : D.State → Obs
  observe_agrees : ∀ w s,
    ∃ h : (bundle w).Obs = Obs, h ▸ (bundle w).obs s = observe s
  cut_mono : ∀ {w w'}, w ≤ w' → (bundle w).S ⊆ (bundle w').S
  compact_coherent : ∀ {w w'}, w ≤ w' → ∀ s,
    observe ((bundle w').compact ((bundle w).compact s)) =
      observe ((bundle w').compact s)

def StabilityEpochFamily.world {D : ConditionedMRDTSig} {World : Type}
    [Preorder World] (F : StabilityEpochFamily D World) :
    WorldCompaction World D.State F.Obs where
  compact w := (F.bundle w).compact
  observe := F.observe
  coherent := F.compact_coherent

/-- Multi-epoch collapse for a family of complete stability bundles. -/
theorem StabilityEpochFamily.multiEpoch_reads
    {D : ConditionedMRDTSig} {World : Type} [Preorder World]
    (F : StabilityEpochFamily D World) {last : World} {ws : List World}
    (hBelow : ∀ w ∈ ws, w ≤ last) (s : D.State) :
    F.observe ((F.bundle last).compact ((F.world).compactSeq ws s)) =
      F.observe ((F.bundle last).compact s) :=
  F.world.observe_compactSeq_collapse hBelow s

#print axioms WorldCompaction.observe_compactSeq_collapse
#print axioms StabilityEpochFamily.multiEpoch_reads

end Sal.ConditionedMRDTs
