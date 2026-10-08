import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! Evidence-carrying finite expansion for immutable record carriers. The
kernels inspect one record at a time; their premises are birth freshness,
kill coverage and coherent common-history membership, never the target VC.
They impose no commutativity or state invariant on the implementation. -/
set_option maxHeartbeats 2000000
namespace NeemExpansion.Certified
variable {Record : Type} [DecidableEq Record]

def merge (l a b : Finset Record) : Finset Record :=
  (l ∩ a ∩ b) ∪ (a \ l) ∪ (b \ l)

/-- The four observable bits left after finite membership expansion. -/
def cell (l a b : Prop) : Prop := (l ∧ a ∧ b) ∨ (a ∧ ¬l) ∨ (b ∧ ¬l)

theorem merge_mem (p : Record) (l a b : Finset Record) :
    p ∈ merge l a b ↔ cell (p ∈ l) (p ∈ a) (p ∈ b) := by
  simp [merge,cell]

/-- A more semantic causal packet: its update is births plus surviving old
records. Births are fresh in the past; all killed remainder records occur in
that past. Neither field assumes a merge equality. -/
structure DeltaEvidence (B a : Finset Record) (born killed : Record → Prop) : Prop where
  birthFresh : ∀ p, born p → p ∉ B
  killedCovered : ∀ p ∈ a, killed p → p ∈ B

structure LocalEvidence (l B b d : Finset Record) : Prop where
  common : ∀ p, p ∈ B → p ∉ d → p ∈ b → p ∈ l
  newborn : ∀ p, p ∉ B → p ∈ d → p ∉ l

/-- Finite kernels, discharged by propositional automation after membership
normalization. Arbitrarily large finite carriers use the same checked cells. -/
theorem comm (l a b : Finset Record) : merge l a b = merge l b a := by
  ext p; simp only [merge_mem,cell]; tauto

theorem initial (a : Finset Record) : merge ∅ ∅ a = a := by
  ext p; simp [merge]

theorem causal (B a d u : Finset Record) (born killed : Record → Prop)
    (evidence : DeltaEvidence B a born killed)
    (pastUpdate : ∀ p, p ∈ d ↔ born p ∨ (p ∈ B ∧ ¬ killed p))
    (remainderUpdate : ∀ p, p ∈ u ↔ born p ∨ (p ∈ a ∧ ¬ killed p)) :
    merge B a d = u := by
  ext p
  have fresh := evidence.birthFresh p
  have covered := evidence.killedCovered p
  rw [merge_mem,pastUpdate,remainderUpdate]
  simp only [cell]
  tauto

theorem local_redistribute (l B t b d : Finset Record) (evidence : LocalEvidence l B b d) :
    merge l (merge B t d) b = merge B (merge l t b) d := by
  ext p
  have common := evidence.common p
  have newborn := evidence.newborn p
  simp only [merge_mem,cell]
  tauto

theorem shared (t₀ t₁ t₂ B d : Finset Record) :
    merge (merge B t₀ d) (merge B t₁ d) (merge B t₂ d) =
      merge B (merge t₀ t₁ t₂) d := by
  ext p
  simp only [merge_mem,cell]
  tauto

end NeemExpansion.Certified
