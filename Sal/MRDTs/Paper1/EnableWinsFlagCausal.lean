import Sal.MRDTs.Paper1.EnableWinsFlagReplay
import Sal.MRDTs.Paper1.EnableWinsFlagAlgebra

set_option maxHeartbeats 1000000

namespace Sal.MRDTs.Paper1.NeemFlagCausal
open Foundation ConcreteMRDT Instances.NeemFlag NeemFlagReplay
open Classical

/-- Adding history without adding this row's winning events can only clear
its bit, never create a new live winner. -/
theorem true_of_equal_count_subset {initialFlag : Bool}
    {C : ReplayContext (D initialFlag).toUpdateSig} {E F : Set Event} {a b : State}
    (ha : representation initialFlag C E a) (hb : representation initialFlag C F b)
    (sub : E ⊆ F) (r : Nat) (same : (a r).1 = (b r).1) (bit : (b r).2 = true) :
    (a r).2 = true := by
  obtain ⟨_,A,hA,ac,ab⟩ := ha
  obtain ⟨_,B,hB,bc,bb⟩ := hb
  have subset : NeemFlagCounts.winners A r ⊆ NeemFlagCounts.winners B r := by
    intro e he
    obtain ⟨he,hw⟩ := Finset.mem_filter.mp he
    refine Finset.mem_filter.mpr ⟨?_,hw⟩
    have ee : e ∈ E := by rw [← hA]; exact he
    have ef := sub ee
    rw [← hB] at ef
    exact ef
  have cardeq : (NeemFlagCounts.winners A r).card = (NeemFlagCounts.winners B r).card := by
    rw [ac,bc] at same
    unfold count NeemFlagCounts.count at same
    exact_mod_cast same
  have eqsets := Finset.eq_of_subset_of_card_le subset (Nat.le_of_eq cardeq.symm)
  apply (ab r).mpr
  rcases (bb r).mp bit with ⟨w,hw,hr,win,live⟩ | ⟨init,nr⟩
  · left
    have hwB : w ∈ NeemFlagCounts.winners B r := by
      apply Finset.mem_filter.mpr
      refine ⟨?_,hr,win⟩
      rw [← hB] at hw
      exact hw
    rw [← eqsets] at hwB
    have hwE : w ∈ E := by rw [← hA]; exact (Finset.mem_filter.mp hwB).1
    exact ⟨w,hwE,hr,win,fun d hd => live d (sub hd)⟩
  · exact Or.inr ⟨init,fun d hd => nr d (sub hd)⟩

private theorem live_before_reset {initialFlag : Bool}
    {C : ReplayContext (D initialFlag).toUpdateSig} {E : Set Event} {e w : Event}
    (reset : e.op = .reset) (hw : w ∈ E) (own : w.rep = r) (win : w.op = .winning)
    (live : ∀ d ∈ E, d.op = .reset → ¬ C.vis w d)
    (killed : ¬ Live C (insert e E) r) : C.vis w e := by
  by_contra hn
  apply killed
  refine ⟨w,Or.inr hw,own,win,?_⟩
  intro d hd hop
  rcases hd with rfl | hd
  · exact hn
  · exact live d hd hop

/-- If a maximal reset will clear a currently true row, every winning event
of that row is already in the reset's past. Single-writer order is essential. -/
theorem true_row_winners_before_reset {initialFlag : Bool}
    {C : ReplayContext (D initialFlag).toUpdateSig} {E : Set Event} {e : Event}
    (trans : Transitive C.vis) (sup : Supported C E)
    (reset : e.op = .reset) (r : Nat) (bit : Bit C E r)
    (killed : ¬ Live C (insert e E) r) :
    ∀ w ∈ E, w.rep = r → w.op = .winning → C.vis w e := by
  intro w hw own win
  rcases bit with ⟨u,hu,uown,uwin,ulive⟩ | ⟨_,nr⟩
  · have ue := live_before_reset reset hu uown uwin ulive killed
    by_cases same : w = u
    · exact same ▸ ue
    obtain ⟨rw,Sw,hLw,hwS⟩ := sup w hw
    obtain ⟨ru,Su,hLu,huS⟩ := sup u hu
    rcases C.vis_total_same_replica hLw hwS hLu huS same (own.trans uown.symm) with wu | uw
    · exact trans wu ue
    · apply live_before_reset reset hw own win _ killed
      intro d hd hop wd
      exact ulive d hd hop (trans uw wd)
  · apply live_before_reset reset hw own win _ killed
    intro d hd hop
    exact (nr d hd hop).elim

theorem causal_delta (initialFlag : Bool)
    (C : ReplayContext (D initialFlag).toUpdateSig) (U : Set Event)
    (s B : State) (e : Event)
    (trans : Transitive C.vis) (irrefl : ∀ x, ¬ C.vis x x)
    (supported : Supported C U) (closed : (scheme initialFlag C).Closed U) (mem : e ∈ U)
    (semantic : ∀ x ∈ U, x ≠ e → ¬ paperOrder policy C U e x)
    (metadata : ∀ x ∈ U, x ≠ e → ¬ (scheme initialFlag C).before e x)
    (hs : representation initialFlag C (U \ {e}) s)
    (hB : representation initialFlag C ((scheme initialFlag C).Past e \ {e}) B)
    (lower : ∀ r, (B r).1 ≤ (s r).1)
    (same : (s e.rep).1 = (B e.rep).1) :
    merge B s (update B e) = update s e := by
  have sub : ((scheme initialFlag C).Past e \ {e}) ⊆ (U \ {e}) := by
    intro x hx
    exact ⟨(scheme initialFlag C).past_subset U e closed mem hx.1,hx.2⟩
  have tied : ∀ r, (s r).1 = (B r).1 → (s r).2 = true → (B r).2 = true := by
    intro r eq bit
    exact true_of_equal_count_subset hB hs sub r eq.symm bit
  have count_if_true : e.op = .reset → ∀ r, (s r).2 = true → (s r).1 = (B r).1 := by
    intro reset r bit
    have ins : insert e (U \ {e}) = U := by simpa [Set.insert_eq_of_mem mem] using (Set.insert_diff_singleton : insert e (U \ {e}) = insert e U)
    have killed : ¬ Live C (insert e (U \ {e})) r := by
      apply reset_kills_live reset
      · intro x hx ne
        rw [ins]
        exact semantic x hx.1 ne
      · intro x hx
        exact metadata x hx.1 hx.2
    have before := true_row_winners_before_reset trans hs.1 reset r
      ((hs.2.choose_spec.2.2 r).mp bit) killed
    obtain ⟨_,F,hF,sc,sb⟩ := hs
    obtain ⟨_,G,hG,bc,bb⟩ := hB
    have eqwins : NeemFlagCounts.winners F r = NeemFlagCounts.winners G r := by
      ext w
      constructor
      · intro hw
        obtain ⟨hw,own,win⟩ := Finset.mem_filter.mp hw
        have hwU : w ∈ U \ {e} := by rw [← hF]; exact hw
        have we := before w hwU own win
        have wp : w ∈ (scheme initialFlag C).Past e \ {e} :=
          ⟨Or.inr (.single we),hwU.2⟩
        rw [← hG] at wp
        exact Finset.mem_filter.mpr ⟨wp,own,win⟩
      · intro hw
        obtain ⟨hw,own,win⟩ := Finset.mem_filter.mp hw
        have wp : w ∈ (scheme initialFlag C).Past e \ {e} := by rw [← hG]; exact hw
        have wu := sub wp
        rw [← hF] at wu
        exact Finset.mem_filter.mpr ⟨wu,own,win⟩
    rw [sc,bc]
    unfold count NeemFlagCounts.count
    rw [eqwins]
  funext r
  have low := lower r
  have tie := tied r
  cases hop : e.op with
  | winning =>
    rcases e with ⟨ts,rep,op⟩
    simp only [Op.op] at hop
    subst op
    by_cases hr : r = rep
    · subst r
      simp only [Op.rep] at same
      simp [merge,mergeCell,mergeFlag,update,Op.op,same]
    · apply Prod.ext
      · simp [merge,mergeCell,update,Op.op,hr]
      · simp only [merge,mergeCell,update,Op.op,if_neg hr]
        cases hb : (B r).2 <;> cases hsbit : (s r).2
        · simp [mergeFlag,hb,hsbit]
        · have ne : (s r).1 ≠ (B r).1 := by
            intro eq
            have bad := tie eq hsbit
            simp [hb] at bad
          have strict : (B r).1 < (s r).1 := by omega
          simp [mergeFlag,hb,hsbit,strict]
        · simp [mergeFlag,hb,hsbit]
        · simp [mergeFlag,hb,hsbit]
  | reset =>
    have ct := count_if_true hop r
    rcases e with ⟨ts,rep,op⟩
    simp only [Op.op] at hop
    subst op
    simp only [merge,mergeCell,mergeFlag,update,Op.op]
    cases hs : (s r).2 <;> simp_all <;> omega

end Sal.MRDTs.Paper1.NeemFlagCausal
