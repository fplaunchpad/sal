import LeanProofs_no_spec_non_comm.Implementations.EmbeddedRGA.Scheme
import Artifact.MRDTs.Paper1.InvariantOrder

/-!
# Embedded RGA: the state invariant and its closure

`Negative.lean` proves that no choice of `rc` gives this row `Laws`,
because Section 4's `Commutes` quantifies over every state of `Sigma`. The
repair is `Artifact/MRDTs/Paper1/InvariantOrder.lean`, where commutation is
asked only at the states an execution produces. This file supplies the
state predicate and discharges `InvariantOrder.Closed` for it.

The invariant has two halves, and each is forced by one operation.

* **`SortedDown`**, strictly descending in key order. The sorted insert
  commutes with a filter only on a sorted list: on `[v, u]` with `v` below
  `u` in key order, inserting and then dropping `v` is not the same as
  dropping `v` and then inserting.
* **`Sourced`**, every record traceable to an insertion the context
  observes. Strict sortedness is preserved by the merge only when the two
  sides share no key, and that is a fact about the observed events rather
  than about the state.

The two halves meet in exactly one place, `key_ne_of_sourced`, and only in
the company of `CoordHonest`, the context-level statement that distinct
observed insertions carve out distinct coordinates. That is the hypothesis
`Negative.lean` refutes at an arbitrary pair of operations and that
`Certificate.lean` will derive, from issuance and `enc_append_cancel`, for
the pairs a certified execution observes.

Nothing here mentions `rc`, because the invariant route runs at the
framework's empty policy rather than at the row's `rc`.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.EmbeddedRGA

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

variable {Γ : Scheme} {α : Type} [DecidableEq α] {Q : QueryOf Γ α}

/-- Records with different coordinates have different keys. -/
theorem recKey_ne {z w : Record Γ α} (h : z.2.2 ≠ w.2.2) : recKey z ≠ recKey w :=
  fun hk => h (Γ.key_inj hk)

/-- `s` is strictly descending in key order: every earlier record has a
strictly larger key. -/
def SortedDown (s : St Γ α) : Prop :=
  s.Pairwise (fun y z => lexLt (recKey z) (recKey y) = true)

theorem sortedDown_nil : SortedDown ([] : St Γ α) := List.Pairwise.nil

theorem sortedDown_of_cons {y : Record Γ α} {Y : St Γ α} (h : SortedDown (y :: Y)) :
    SortedDown Y := (List.pairwise_cons.mp h).2

theorem sortedDown_head {y : Record Γ α} {Y : St Γ α} (h : SortedDown (y :: Y)) :
    ∀ w ∈ Y, lexLt (recKey w) (recKey y) = true := (List.pairwise_cons.mp h).1

/-! ## Sorted insertion -/

theorem mem_insertDown {z : Record Γ α} : ∀ {s : St Γ α} {x : Record Γ α},
    x ∈ insertDown z s ↔ x = z ∨ x ∈ s := by
  intro s
  induction s with
  | nil => intro x; simp [insertDown]
  | cons y Y ih =>
    intro x
    simp only [insertDown]
    split_ifs with h
    · simp [or_comm, or_left_comm]
    · simp only [List.mem_cons, ih]
      tauto

theorem ids_insertDown {z : Record Γ α} {s : St Γ α} {t : Nat} :
    t ∈ ids (insertDown z s) ↔ t = z.1 ∨ t ∈ ids s := by
  simp only [ids, List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases mem_insertDown.mp hx with rfl | hx'
    · exact Or.inl rfl
    · exact Or.inr ⟨x, hx', rfl⟩
  · rintro (rfl | ⟨x, hx, rfl⟩)
    · exact ⟨z, mem_insertDown.mpr (Or.inl rfl), rfl⟩
    · exact ⟨x, mem_insertDown.mpr (Or.inr hx), rfl⟩

/-- **Sorted insertion keeps the list sorted**, provided the newcomer's key
is new. -/
theorem sortedDown_insertDown {z : Record Γ α} : ∀ {s : St Γ α}, SortedDown s →
    (∀ y ∈ s, recKey y ≠ recKey z) → SortedDown (insertDown z s) := by
  intro s
  induction s with
  | nil => intro _ _; exact List.pairwise_singleton _ _
  | cons y Y ih =>
    intro hs hne
    simp only [insertDown]
    split_ifs with hlt
    · refine List.pairwise_cons.mpr ⟨?_, hs⟩
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw'
      · exact hlt
      · exact lexLt_trans _ _ _ (sortedDown_head hs w hw') hlt
    · refine List.pairwise_cons.mpr ⟨?_, ih (sortedDown_of_cons hs)
        (fun w hw => hne w (List.mem_cons_of_mem _ hw))⟩
      intro w hw
      rcases mem_insertDown.mp hw with rfl | hw'
      · rcases lexLt_total (hne y List.mem_cons_self) with h | h
        · exact absurd h hlt
        · exact h
      · exact sortedDown_head hs w hw'

/-! ## Filtering -/

theorem sortedDown_filter {s : St Γ α} (p : Record Γ α → Bool) (h : SortedDown s) :
    SortedDown (s.filter p) := List.Pairwise.filter p h

/-! ## The descending merge -/

theorem mem_mergeDown : ∀ (X Y : St Γ α) {x : Record Γ α},
    x ∈ mergeDown X Y ↔ x ∈ X ∨ x ∈ Y := by
  intro X
  induction X with
  | nil => intro Y x; simp [mergeDown]
  | cons u U ihU =>
    intro Y
    induction Y with
    | nil => intro x; simp [mergeDown]
    | cons v V ihV =>
      intro x
      simp only [mergeDown]
      split_ifs with h
      · simp only [List.mem_cons, ihU (v :: V), List.mem_cons]
        tauto
      · simp only [List.mem_cons, ihV, List.mem_cons]
        tauto

/-- **The descending merge keeps the list sorted**, provided the two sides
share no key. -/
theorem sortedDown_mergeDown : ∀ (X Y : St Γ α), SortedDown X → SortedDown Y →
    (∀ x ∈ X, ∀ y ∈ Y, recKey x ≠ recKey y) → SortedDown (mergeDown X Y) := by
  intro X
  induction X with
  | nil => intro Y _ hY _; simpa [mergeDown] using hY
  | cons u U ihU =>
    intro Y
    induction Y with
    | nil => intro hX _ _; simpa [mergeDown] using hX
    | cons v V ihV =>
      intro hX hY hcross
      simp only [mergeDown]
      split_ifs with h
      · refine List.pairwise_cons.mpr ⟨?_, ihU (v :: V) (sortedDown_of_cons hX) hY
          (fun x hx y hy => hcross x (List.mem_cons_of_mem _ hx) y hy)⟩
        intro w hw
        rcases (mem_mergeDown U (v :: V)).mp hw with hw' | hw'
        · exact sortedDown_head hX w hw'
        · rcases List.mem_cons.mp hw' with rfl | hw''
          · exact h
          · exact lexLt_trans _ _ _ (sortedDown_head hY w hw'') h
      · refine List.pairwise_cons.mpr ⟨?_, ihV hX (sortedDown_of_cons hY)
          (fun x hx y hy => hcross x hx y (List.mem_cons_of_mem _ hy))⟩
        intro w hw
        rcases (mem_mergeDown (u :: U) V).mp hw with hw' | hw'
        · rcases List.mem_cons.mp hw' with rfl | hw''
          · rcases lexLt_total (hcross w List.mem_cons_self v List.mem_cons_self) with h' | h'
            · exact h'
            · exact absurd h' h
          · exact lexLt_trans _ _ _ (sortedDown_head hX w hw'')
              (by rcases lexLt_total (hcross u List.mem_cons_self v List.mem_cons_self) with h' | h'
                  · exact h'
                  · exact absurd h' h)
        · exact sortedDown_head hY w hw'

/-! ## Where a record comes from

The sorted insert can only be forced to break a tie between records with
equal keys, and the merge can only produce a tie between its two sides. So
the invariant has to rule out ties, and that is a fact about the **events
the context observes**, not about the state alone. -/

/-- `z` is the record the insertion event `e` writes. -/
def Writes (e : Op (AppOp Γ α)) (z : Record Γ α) : Prop :=
  ∃ v p a g, e.op = AppOp.ins v p a g ∧ z = (e.time, v, p ++ Γ.code g (e.time - a))

/-- Every record of `s` is written by an insertion `C` observes. -/
def Sourced (C : Ctx (Dα Γ α Q)) (s : St Γ α) : Prop :=
  ∀ z ∈ s, ∃ e ∈ C.events, Writes e z

/-- **Distinct observed insertions carve out distinct coordinates.**

This is the context-level fact the whole invariant route turns on.
`Negative.lean` refutes it at an arbitrary pair of operations, which is why
no `rc` gives this row `Laws`. `Certificate.lean` derives it for the pairs a
certified execution observes, from issuance and `enc_append_cancel`. -/
def CoordHonest (C : Ctx (Dα Γ α Q)) : Prop :=
  ∀ e₁ ∈ C.events, ∀ e₂ ∈ C.events, ∀ z₁ z₂, Writes e₁ z₁ → Writes e₂ z₂ →
    z₁.2.2 = z₂.2.2 → z₁ = z₂

/-- **The state invariant.** Strictly descending in key order, and every
record traceable to an observed insertion. -/
def Valid (C : Ctx (Dα Γ α Q)) (s : St Γ α) : Prop := SortedDown s ∧ Sourced C s

/-- Under `CoordHonest`, distinct sourced records have distinct keys. This
is the only way the two halves of `Valid` are used together. -/
theorem key_ne_of_sourced {C : Ctx (Dα Γ α Q)} (hc : CoordHonest C) {s t : St Γ α}
    (hs : Sourced C s) (ht : Sourced C t) {x y : Record Γ α}
    (hx : x ∈ s) (hy : y ∈ t) (hne : x ≠ y) : recKey x ≠ recKey y := by
  intro hk
  obtain ⟨e₁, he₁, hw₁⟩ := hs x hx
  obtain ⟨e₂, he₂, hw₂⟩ := ht y hy
  exact hne (hc e₁ he₁ e₂ he₂ x y hw₁ hw₂ (Γ.key_inj hk))

/-! ## Closure

`InvariantOrder.Closed` asks for the invariant at the initial state, under
an update by an **observed** event, and under merge. The observed-event
premise is what lets the update case appeal to `CoordHonest`. -/

theorem valid_nil (C : Ctx (Dα Γ α Q)) : Valid C [] :=
  ⟨sortedDown_nil, fun _ hz => absurd hz (by simp)⟩

theorem valid_step {C : Ctx (Dα Γ α Q)} (hc : CoordHonest C) {s : St Γ α} (hs : Valid C s)
    {e : Op (AppOp Γ α)} (he : e ∈ C.events) : Valid C (step s e) := by
  obtain ⟨hsort, hsrc⟩ := hs
  cases hop : e.op with
  | ins v p a g =>
    simp only [step, hop]
    split_ifs with hmem
    · exact ⟨hsort, hsrc⟩
    · have hwz : Writes e (e.time, v, p ++ Γ.code g (e.time - a)) :=
        ⟨v, p, a, g, hop, rfl⟩
      refine ⟨sortedDown_insertDown hsort (fun y hy => ?_), fun w hw => ?_⟩
      · refine key_ne_of_sourced hc hsrc
          (fun u hu => by rcases List.mem_singleton.mp hu with rfl; exact ⟨e, he, hwz⟩)
          hy (List.mem_singleton_self _) (fun hyz => ?_)
        have hy1 : y.1 ∈ ids s := List.mem_map_of_mem hy
        rw [hyz] at hy1
        exact hmem hy1
      · rcases mem_insertDown.mp hw with rfl | hw'
        · exact ⟨e, he, hwz⟩
        · exact hsrc w hw'
  | del x =>
    refine ⟨?_, ?_⟩
    · simpa only [step, hop] using sortedDown_filter _ hsort
    · intro w hw
      simp only [step, hop, List.mem_filter] at hw
      exact hsrc w hw.1

theorem valid_merge {C : Ctx (Dα Γ α Q)} (hc : CoordHonest C) {l a b : St Γ α}
    (hl : Valid C l) (ha : Valid C a) (hb : Valid C b) :
    Valid C (mergeState l a b) := by
  obtain ⟨-, -⟩ := hl
  obtain ⟨hsa, hsrca⟩ := ha
  obtain ⟨hsb, hsrcb⟩ := hb
  set A : St Γ α := a.filter (fun z => z.1 ∈ ids b || !(z.1 ∈ ids l)) with hA
  set B : St Γ α := b.filter (fun z => !(z.1 ∈ ids l) && !(z.1 ∈ ids a)) with hB
  have hmemA : ∀ z ∈ A, z ∈ a := fun z hz => (List.mem_filter.mp hz).1
  have hmemB : ∀ z ∈ B, z ∈ b := fun z hz => (List.mem_filter.mp hz).1
  have hsrcA : Sourced C A := fun z hz => hsrca z (hmemA z hz)
  have hsrcB : Sourced C B := fun z hz => hsrcb z (hmemB z hz)
  have hcross : ∀ x ∈ A, ∀ y ∈ B, recKey x ≠ recKey y := by
    intro x hx y hy
    refine key_ne_of_sourced hc hsrcA hsrcB hx hy (fun hxy => ?_)
    have hyB := (List.mem_filter.mp hy).2
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hyB
    exact hyB.2 (by
      rw [← hxy]
      exact List.mem_map_of_mem (hmemA x hx))
  refine ⟨sortedDown_mergeDown A B (sortedDown_filter _ hsa)
    (sortedDown_filter _ hsb) hcross, fun w hw => ?_⟩
  rcases (mem_mergeDown A B).mp hw with hw' | hw'
  · exact hsrcA w hw'
  · exact hsrcB w hw'

/-- **The invariant is closed**, which is what the invariant-scoped replay
contract asks of it. -/
theorem closed (C : Ctx (Dα Γ α Q)) (hc : CoordHonest C) :
    InvariantOrder.Closed (Dα Γ α Q).toMRDTSig C (Valid C) where
  initial := valid_nil C
  update := fun _ hs e he => valid_step hc hs he
  merge := fun _ _ _ hl ha hb => valid_merge hc hl ha hb

end LeanProofs.NoSpecNonComm.Implementations.EmbeddedRGA
