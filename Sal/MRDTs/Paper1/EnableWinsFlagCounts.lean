import Sal.MRDTs.Instances.EnableWinsFlag

namespace Sal.MRDTs.Paper1.NeemFlagCounts
open Foundation ConcreteMRDT Instances.NeemFlag

def winningAt (r : Nat) (e : Op Action) : Prop := e.rep = r ∧ e.op = .winning
instance (r : Nat) (e : Op Action) : Decidable (winningAt r e) := inferInstanceAs
  (Decidable (e.rep = r ∧ e.op = .winning))
def winners (F : Finset (Op Action)) (r : Nat) : Finset (Op Action) :=
  F.filter (winningAt r)
def count (F : Finset (Op Action)) (r : Nat) : Int := (winners F r).card

/-- Logical single-writer histories make winning prefixes comparable at each
row. This is execution evidence, not an assumed source merge equation. -/
theorem prefixes_comparable {initialFlag : Bool}
    (C : ReplayContext (D initialFlag).toUpdateSig) (E₁ E₂ : Set (Op Action))
    (F G : Finset (Op Action)) (hF : (↑F : Set (Op Action)) = E₁)
    (hG : (↑G : Set (Op Action)) = E₂)
    (sup₁ : Supported C E₁) (sup₂ : Supported C E₂)
    (closed₁ : ∀ a b, C.vis a b → b ∈ E₁ → a ∈ E₁)
    (closed₂ : ∀ a b, C.vis a b → b ∈ E₂ → a ∈ E₂) (r : Nat) :
    winners F r ⊆ winners G r ∨ winners G r ⊆ winners F r := by
  classical
  by_cases sub : winners F r ⊆ winners G r
  · exact Or.inl sub
  · right
    obtain ⟨a,ha,absent⟩ := Finset.not_subset.mp sub
    obtain ⟨haF,ownA⟩ := Finset.mem_filter.mp ha
    have absentG : a ∉ G := by
      intro hg
      exact absent (Finset.mem_filter.mpr ⟨hg,ownA⟩)
    intro b hb
    obtain ⟨hbG,ownB⟩ := Finset.mem_filter.mp hb
    refine Finset.mem_filter.mpr ⟨?_,ownB⟩
    have haE : a ∈ E₁ := by rw [← hF]; exact haF
    have hbE : b ∈ E₂ := by rw [← hG]; exact hbG
    have ne : a ≠ b := by intro eq; subst b; exact absentG hbG
    obtain ⟨ra,Sa,hLa,haS⟩ := sup₁ a haE
    obtain ⟨rb,Sb,hLb,hbS⟩ := sup₂ b hbE
    rcases C.vis_total_same_replica hLa haS hLb hbS ne (ownA.1.trans ownB.1.symm) with ab | ba
    · have ag := closed₂ a b ab hbE
      rw [← hG] at ag
      exact (absentG ag).elim
    · have bf := closed₁ b a ba haE
      rw [← hF] at bf
      exact bf

theorem winners_inter (F G : Finset (Op Action)) (r : Nat) :
    winners (F ∩ G) r = winners F r ∩ winners G r := by
  ext e; simp [winners]; tauto

theorem count_min_of_comparable (F G : Finset (Op Action)) (r : Nat)
    (h : winners F r ⊆ winners G r ∨ winners G r ⊆ winners F r) :
    count (F ∩ G) r = min (count F r) (count G r) := by
  unfold count
  rw [winners_inter]
  rcases h with sub | sub
  · rw [Finset.inter_eq_left.mpr sub]
    have bound := Finset.card_le_card sub
    omega
  · rw [Finset.inter_eq_right.mpr sub]
    have bound := Finset.card_le_card sub
    omega

theorem count_mono (F G : Finset (Op Action)) (sub : F ⊆ G) (r : Nat) :
    count F r ≤ count G r := by
  unfold count
  have sub' : winners F r ⊆ winners G r := Finset.filter_subset_filter _ sub
  exact_mod_cast Finset.card_le_card sub'

end Sal.MRDTs.Paper1.NeemFlagCounts
