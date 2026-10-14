import Sal.MRDTs.Paper1.OptionalRegisterCoherence

namespace Sal.MRDTs.Paper1.OptionalRegister
open Foundation Instances.OptionalRegister

/-- Source's refinement can be checked at every lookup, including absent keys. -/
def CellWellFormed (c : Cell) : Prop := c.1.2 = false ↔ c.2 = (0,0)

theorem lookup_wellFormed (s : State) (valid : SourceWellFormed s) (r : Nat) :
    CellWellFormed (s.cells r) := by
  by_cases present : r ∈ s.domain
  · exact valid r present
  · rw [s.outside r present]
    simp [CellWellFormed,zero]

theorem initial_sourceWellFormed : SourceWellFormed initial := by
  intro r h; simp [initial] at h

theorem update_sourceWellFormed (s : State) (valid : SourceWellFormed s) (e : Op Action)
    (issued : generation.CanIssue e s) : SourceWellFormed (update s e) := by
  intro r _
  have cell := lookup_wellFormed s valid r
  cases hop : e.op with
  | unset => simp [update,hop]
  | set v =>
    by_cases own : r = e.rep
    · have positive : 0 < e.time := issued
      simp [update,hop,own,Nat.ne_of_gt positive]
    · simpa [update,hop,own] using cell

theorem mergePayload_nonzero (l a b : Payload) (ha : a ≠ (0,0)) (hb : b ≠ (0,0)) :
    mergePayload l a b ≠ (0,0) := by
  rcases a with ⟨ta,av⟩; rcases b with ⟨tb,bv⟩
  unfold mergePayload
  split_ifs with equal greater
  · intro zero
    have tzero : ta = 0 := congrArg Prod.fst zero
    have vzero : (av+bv)/2 = 0 := congrArg Prod.snd zero
    have hav : ¬ (ta = 0 ∧ av = 0) := fun h => ha (by simp [h.1,h.2])
    have hbv : ¬ (tb = 0 ∧ bv = 0) := fun h => hb (by simp [h.1,h.2])
    omega
  · exact ha
  · exact hb

theorem mergeCell_sourceWellFormed (l a b : Cell)
    (ha : CellWellFormed a) (hb : CellWellFormed b) : CellWellFormed (mergeCell l a b) := by
  have pa : a.1.2 = true → a.2 ≠ (0,0) := by
    intro h eq
    have bad := ha.mpr eq
    rw [h] at bad; contradiction
  have pb : b.1.2 = true → b.2 ≠ (0,0) := by
    intro h eq
    have bad := hb.mpr eq
    rw [h] at bad; contradiction
  unfold CellWellFormed mergeCell
  dsimp only
  cases hf : Instances.NeemFlag.mergeFlag l.1 a.1 b.1
  · simp
  · simp only [Bool.not_true,ite_false,Bool.true_eq_false,false_iff]
    cases af : a.1.2 <;> cases bf : b.1.2
    · simp [Instances.NeemFlag.mergeFlag,af,bf] at hf
    · simpa [af,bf] using pb bf
    · simpa [af,bf] using pa af
    · simpa [af,bf] using mergePayload_nonzero l.2 a.2 b.2 (pa af) (pb bf)

theorem merge_sourceWellFormed (l a b : State)
    (ha : SourceWellFormed a) (hb : SourceWellFormed b) : SourceWellFormed (merge l a b) := by
  intro r _
  exact mergeCell_sourceWellFormed (l.cells r) (a.cells r) (b.cells r)
    (lookup_wellFormed a ha r) (lookup_wellFormed b hb r)

/-- Event semantics plus certified positive timestamps recover the exact source
refinement, without assuming the refinement as a representation field. -/
theorem sourceWellFormed_of_representation (C : ReplayContext D.toUpdateSig)
    (E : Set (Op Action)) (s : State) (hs : representation C E s)
    (positive : ∀ e ∈ E, 0 < e.time) : SourceWellFormed s := by
  intro r _
  cases flag : (s.cells r).1.2
  · exact ⟨fun _ => hs.inactive r flag,fun _ => rfl⟩
  · constructor
    · intro h; contradiction
    · intro zero
      obtain ⟨w,hw,own,live,payload,latest⟩ := hs.payload r flag
      have ts0 : w.time = 0 := by
        have eq := congrArg Prod.fst (payload.symm.trans zero)
        exact eq
      have greater := positive w hw
      exact False.elim ((Nat.ne_of_gt greater) ts0)

theorem positive_events {C : Configuration D} (execution : CertifiedExecution D generation C) :
    ∀ e ∈ C.events, 0 < e.time := by
  have honest : MintHonest D generation.CanIssue C := by
    cases execution with
    | ordinary reach => exact reach.mintHonest
    | virtual reach => exact reach.mintHonest
  intro e he
  obtain ⟨past,perm,order,issued⟩ := honest e he
  exact issued

/-- Equal timestamps of active represented payloads identify the same Set.
Inactive zero payloads are outside this claim. -/
theorem active_timestamp_tie_payload_agreement (C : ReplayContext D.toUpdateSig)
    (E₁ E₂ : Set Event) (a b : State)
    (closed₁ : ∀ x y, C.vis x y → y ∈ E₁ → x ∈ E₁)
    (closed₂ : ∀ x y, C.vis x y → y ∈ E₂ → x ∈ E₂)
    (ha : representation C E₁ a) (hb : representation C E₂ b) (r : Nat)
    (active₁ : (a.cells r).1.2 = true) (active₂ : (b.cells r).1.2 = true)
    (same : (a.cells r).2.1 = (b.cells r).2.1) :
    (a.cells r).2 = (b.cells r).2 := by
  have coherent := (represented_coherent C E₁ E₂ a b closed₁ closed₂ ha hb r).1 active₁ active₂
  have equal : (a.cells r).1.1 = (b.cells r).1.1 := by
    rcases lt_trichotomy (a.cells r).1.1 (b.cells r).1.1 with less | equal | greater
    · have impossible := coherent.1 less
      rw [same] at impossible
      exact (lt_irrefl _ impossible).elim
    · exact equal
    · have impossible := coherent.2.1 greater
      rw [same] at impossible
      exact (lt_irrefl _ impossible).elim
  exact coherent.2.2 equal

theorem policy_nontrivial : policy.before .unset (.set 10) ∧ ¬ policy.before (.set 10) .unset := by
  simp [policy]

/-- Positive time issuance is essential for the source's exact refinement,
although a stored value zero is a perfectly valid optional-register value. -/
theorem zero_value_positive_time_valid :
    SourceWellFormed (update initial (1,0,.set 0)) ∧
      ¬ SourceWellFormed (update initial (0,0,.set 0)) := by
  constructor
  · exact update_sourceWellFormed initial initial_sourceWellFormed _ (by change 0 < 1; decide)
  · intro valid
    have bad := valid 0 (by simp [update,Op.op,Op.rep])
    simp [update,Op.op,Op.rep,Op.time] at bad

#print axioms update_sourceWellFormed
#print axioms merge_sourceWellFormed
#print axioms zero_value_positive_time_valid
end Sal.MRDTs.Paper1.OptionalRegister
