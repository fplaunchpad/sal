import LeanProofs_no_spec_non_comm.Implementations.OptionalRegister.Definition
import LeanProofs_no_spec_non_comm.Metatheory.Adequacy
import LeanProofs_no_spec_non_comm.Soundness.RALinearizability

/-!
**A duplicate, plus one section.** Everything before the final section is
`Implementations/OptionalRegister/VCs.lean` with the namespace changed. The
last section is what this folder adds.

# The optional register: every obligation

`Laws(D_type)` of Section 4 and VC1 to VC5 of Section 5, for the tuple of
`Definition.lean`.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.OptionalRegister

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

/-! ## How `do` moves a cell -/

@[simp] theorem step_set_domain (s : State) (e : D.Event) {v : Nat} (h : e.op = .set v) :
    (step s e).domain = insert e.rep s.domain := by
  simp only [step, h]

@[simp] theorem step_set_cells (s : State) (e : D.Event) {v : Nat} (h : e.op = .set v)
    (r : Nat) :
    (step s e).cells r
      = if r = e.rep then (((s.cells r).1.1 + 1, true), (e.time, v)) else s.cells r := by
  simp only [step, h]

@[simp] theorem step_unset_domain (s : State) (e : D.Event) (h : e.op = .unset) :
    (step s e).domain = s.domain := by
  simp only [step, h]

@[simp] theorem step_unset_cells (s : State) (e : D.Event) (h : e.op = .unset) (r : Nat) :
    (step s e).cells r = (((s.cells r).1.1, false), (0, 0)) := by
  simp only [step, h]

/-- `do` is `step`. -/
theorem do_eq (s : State) (e : D.Event) : D.do_ s e = step s e := rfl

/-! ## Which pairs commute -/

/-- Two `set` events of different replicas commute: each writes only its own
cell, and neither reads the other's. -/
theorem commutes_set_set {e₁ e₂ : D.Event} {v₁ v₂ : Nat}
    (h₁ : e₁.op = .set v₁) (h₂ : e₂.op = .set v₂) (hr : e₁.rep ≠ e₂.rep) :
    D.Commutes e₁ e₂ := by
  intro s
  simp only [do_eq]
  refine State.ext ?_ ?_
  · simp only [step_set_domain _ _ h₁, step_set_domain _ _ h₂]
    exact Finset.insert_comm _ _ _
  · intro r
    simp only [step_set_cells _ _ h₁, step_set_cells _ _ h₂]
    by_cases hr₁ : r = e₁.rep <;> by_cases hr₂ : r = e₂.rep
    · exact absurd (hr₁.symm.trans hr₂) hr
    · simp [hr₁, hr₂, hr, Ne.symm hr]
    · simp [hr₁, hr₂, hr, Ne.symm hr]
    · simp [hr₁, hr₂]

/-- Two `unset` events commute: both clear every flag and payload and leave
every counter alone. -/
theorem commutes_unset_unset {e₁ e₂ : D.Event}
    (h₁ : e₁.op = .unset) (h₂ : e₂.op = .unset) : D.Commutes e₁ e₂ := by
  intro s
  simp only [do_eq]
  exact State.ext (by simp only [step_unset_domain _ _ h₁, step_unset_domain _ _ h₂])
    (by intro r; simp only [step_unset_cells _ _ h₁, step_unset_cells _ _ h₂])

/-- A `set` and an `unset` do not commute: performed in one order the
issuer's flag ends up raised, in the other it ends up clear. -/
theorem not_commutes_set_unset {e₁ e₂ : D.Event} {v : Nat}
    (h₁ : e₁.op = .set v) (h₂ : e₂.op = .unset) : ¬ D.Commutes e₁ e₂ := by
  intro hc
  have h := congrArg (fun t : State => (t.cells e₁.rep).1.2) (hc initial)
  simp only [do_eq, step_unset_cells _ _ h₂, step_set_cells _ _ h₁,
    step_unset_cells _ _ h₂, if_pos rfl] at h
  exact absurd h (by simp)

/-- Commutation is symmetric. -/
theorem commutes_symm {e₁ e₂ : D.Event} (h : D.Commutes e₁ e₂) : D.Commutes e₂ e₁ :=
  fun s => (h s).symm

/-- **What can fail to commute with a `set` issued by `r`.** Only an `unset`,
or another `set` issued by `r` itself. -/
theorem absorber_of_not_commutes {e e'' : D.Event} {v : Nat} (h : e.op = .set v)
    (hn : ¬ D.Commutes e e'') : e''.op = .unset ∨ e''.rep = e.rep := by
  by_cases hr : e''.rep = e.rep
  · exact Or.inr hr
  · rcases hop : e''.op with w | _
    · exact absurd (commutes_set_set h hop (Ne.symm hr)) hn
    · exact Or.inl rfl

/-! ## `rc` -/

/-- `rc` orders exactly an `unset` before a `set`. -/
theorem rcBefore_iff (o₁ o₂ : type.OType) :
    D.RcBefore o₁ o₂ ↔ o₁ = .unset ∧ ∃ v, o₂ = .set v := by
  cases o₁ <;> cases o₂ <;> simp [Impl.RcBefore, D, rcOf]

/-- The event-level reading of the same fact. -/
theorem eventRcBefore_iff (e₁ e₂ : D.Event) :
    D.EventRcBefore e₁ e₂ ↔ e₁.op = .unset ∧ ∃ v, e₂.op = .set v :=
  rcBefore_iff _ _

/-- **NO-RC-CHAIN.** An `unset` can only start an edge and a `set` can only
end one, so two edges never meet. -/
theorem no_rc_chain (o₁ o₂ o₃ : type.OType) :
    ¬ (D.RcBefore o₁ o₂ ∧ D.RcBefore o₂ o₃) := by
  rintro ⟨h₁, h₂⟩
  obtain ⟨-, v, hv⟩ := (rcBefore_iff _ _).mp h₁
  obtain ⟨hu, -⟩ := (rcBefore_iff _ _).mp h₂
  rw [hv] at hu
  exact Action.noConfusion hu

/-- **RC-NON-COMM**, at the concurrent pairs the paper's guards admit. Two
events of different replicas fail to commute exactly when one is a `set` and
the other an `unset`, and that is exactly the pair `rc` orders. -/
theorem rc_non_comm (e₁ e₂ : D.Event)
    (_ht : D.time e₁ ≠ D.time e₂) (hr : D.rep e₁ ≠ D.rep e₂) :
    ((¬ D.Commutes e₁ e₂ ∧ e₁.op ≠ e₂.op) ↔
      D.EventRcBefore e₁ e₂ ∨ D.EventRcBefore e₂ e₁) := by
  simp only [eventRcBefore_iff]
  rcases h₁ : e₁.op with v₁ | _ <;> rcases h₂ : e₂.op with v₂ | _
  · simp [commutes_set_set h₁ h₂ hr]
  · simp [not_commutes_set_unset h₁ h₂]
  · have hn : ¬ D.Commutes e₁ e₂ := fun hc => not_commutes_set_unset h₂ h₁ (commutes_symm hc)
    simp [hn]
  · simp

/-! ### The absorber argument for COND-COMM

Swapping an `unset` with a concurrent `set` changes the state only in the
cell of the `set`'s issuer, and never its counter. `unset` reads a cell's
counter alone, and `set` overwrites its issuer's cell outright, so no later
event can spread that one difference. An absorber is any event that rewrites
the cell: another `set` by the same replica, or an `unset`. -/

/-- Two states that agree on every counter, and on every cell but `r₀`. -/
structure AgreeOff (r₀ : Nat) (a b : State) : Prop where
  dom : a.domain = b.domain
  counts : ∀ r, (a.cells r).1.1 = (b.cells r).1.1
  off : ∀ r, r ≠ r₀ → a.cells r = b.cells r

/-- The relation is preserved by `do`. -/
theorem agreeOff_step {r₀ : Nat} {a b : State} (h : AgreeOff r₀ a b) (e : D.Event) :
    AgreeOff r₀ (step a e) (step b e) := by
  rcases hop : e.op with v | _
  · refine ⟨by simp only [step_set_domain _ _ hop, h.dom], ?_, ?_⟩
    · intro r
      simp only [step_set_cells _ _ hop]
      by_cases hr : r = e.rep
      · rw [if_pos hr, if_pos hr]
        show (a.cells r).1.1 + 1 = (b.cells r).1.1 + 1
        rw [h.counts r]
      · rw [if_neg hr, if_neg hr]
        exact h.counts r
    · intro r hr0
      simp only [step_set_cells _ _ hop]
      by_cases hr : r = e.rep
      · rw [if_pos hr, if_pos hr, h.counts r]
      · rw [if_neg hr, if_neg hr]
        exact h.off r hr0
  · exact ⟨by simp only [step_unset_domain _ _ hop, h.dom],
      by intro r; simp only [step_unset_cells _ _ hop, h.counts r],
      by intro r _; simp only [step_unset_cells _ _ hop, h.counts r]⟩

/-- And so by a whole replay. -/
theorem agreeOff_applyList {r₀ : Nat} {a b : State} (h : AgreeOff r₀ a b)
    (pi : List D.Event) : AgreeOff r₀ (D.applyList a pi) (D.applyList b pi) := by
  induction pi generalizing a b with
  | nil => exact h
  | cons e rest ih => exact ih (agreeOff_step h e)

/-- An absorber closes the gap: it rewrites the one cell that may differ. -/
theorem agreeOff_absorb {r₀ : Nat} {a b : State} (h : AgreeOff r₀ a b) {e : D.Event}
    (habs : e.op = .unset ∨ e.rep = r₀) : step a e = step b e := by
  rcases hop : e.op with v | _
  · have hr : e.rep = r₀ := by
      rcases habs with hu | hr
      · rw [hop] at hu; exact absurd hu (by simp)
      · exact hr
    refine State.ext (by simp only [step_set_domain _ _ hop, h.dom]) ?_
    intro r
    simp only [step_set_cells _ _ hop]
    by_cases hre : r = e.rep
    · simp [hre, h.counts]
    · exact by simp [hre, h.off r (by rw [← hr]; exact hre)]
  · exact State.ext (by simp only [step_unset_domain _ _ hop, h.dom])
      (by intro r; simp only [step_unset_cells _ _ hop, h.counts r])

/-- The two orders of a swapped `unset` and `set` differ only in the `set`
issuer's cell. -/
theorem agreeOff_base {sigma : State} {e e' : D.Event} {v : Nat}
    (he : e.op = .unset) (he' : e'.op = .set v) :
    AgreeOff e'.rep (step (step sigma e') e) (step (step sigma e) e') := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [step_unset_domain _ _ he, step_set_domain _ _ he']
  · intro r
    simp only [step_unset_cells _ _ he, step_set_cells _ _ he']
    by_cases hr : r = e'.rep
    · rw [if_pos hr, if_pos hr]
    · rw [if_neg hr, if_neg hr]
  · intro r hr
    simp only [step_unset_cells _ _ he, step_set_cells _ _ he']
    rw [if_neg hr, if_neg hr]

/-- **COND-COMM**, with the replica guard dropped: the argument never uses
it. `Laws.cond_comm` and `SameReplicaCondComm` are both instances. -/
theorem cond_comm_core (sigma : D.Sigma) (e e' e'' : D.Event) (pi : List D.Event)
    (hrc : D.EventRcBefore e e') (hnc : ¬ D.Commutes e' e'') :
    D.do_ (D.applyList (D.do_ (D.do_ sigma e') e) pi) e''
      = D.do_ (D.applyList (D.do_ (D.do_ sigma e) e') pi) e'' := by
  obtain ⟨he, v, he'⟩ := (eventRcBefore_iff e e').mp hrc
  exact agreeOff_absorb (agreeOff_applyList (agreeOff_base he he') pi)
    (absorber_of_not_commutes he' hnc)

/-- **COND-COMM** of Section 4. -/
theorem cond_comm (sigma : D.Sigma) (e e' e'' : D.Event) (pi : List D.Event)
    (_ht : D.time e ≠ D.time e') (_hr : D.rep e ≠ D.rep e')
    (hrc : D.EventRcBefore e e') (hnc : ¬ D.Commutes e' e'') :
    D.do_ (D.applyList (D.do_ (D.do_ sigma e') e) pi) e''
      = D.do_ (D.applyList (D.do_ (D.do_ sigma e) e') pi) e'' :=
  cond_comm_core sigma e e' e'' pi hrc hnc

/-- The same at a pair one replica issued, which is the case the paper's
COND-COMM exempts and the guarded contract still asks about. -/
theorem same_rep_cond_comm : SameReplicaCondComm D :=
  fun sigma e e' e'' pi _ _ hrc hnc => cond_comm_core sigma e e' e'' pi hrc hnc

/-- The case RC-NON-COMM's `o1 /= o2` conjunct excludes. Two events of
different replicas carrying one operation commute. -/
theorem equal_op_commutes : EqualOpCommutes D := by
  intro e₁ e₂ _ hr hop
  rcases h₁ : e₁.op with v | _
  · exact commutes_set_set h₁ (hop ▸ h₁) hr
  · exact commutes_unset_unset h₁ (hop ▸ h₁)

/-- **`Laws(D_type)`**: the three conditions of Section 4 that constrain
`rc` alone. -/
theorem laws : Laws D := ⟨rc_non_comm, no_rc_chain, cond_comm⟩

/-! ## VC1: MERGE-COMM

Cellwise, so it reduces to the symmetry of `mergeFlag` and `mergePayload`.
Both are symmetric by inspection: the flag merge asks "both raised", "both
clear", and otherwise reads the counter of whichever one is raised; the
payload merge takes the greater timestamp and averages a tie. -/

theorem mergeFlag_comm (l a b : Int × Bool) : mergeFlag l a b = mergeFlag l b a := by
  rcases a with ⟨ac, af⟩; rcases b with ⟨bc, bf⟩
  cases af <;> cases bf <;> simp [mergeFlag]

theorem mergePayload_comm (l a b : Payload) : mergePayload l a b = mergePayload l b a := by
  rcases a with ⟨at', av⟩; rcases b with ⟨bt, bv⟩
  simp only [mergePayload]
  by_cases h : at' = bt
  · subst h; simp [Nat.add_comm]
  · rcases Nat.lt_or_ge at' bt with hlt | hge
    · simp [h, Ne.symm h, Nat.not_lt.mpr (Nat.le_of_lt hlt), hlt]
    · have hgt : bt < at' := Nat.lt_of_le_of_ne hge (Ne.symm h)
      simp [h, Ne.symm h, hgt, Nat.not_lt.mpr (Nat.le_of_lt hgt)]

theorem mergeCell_comm (l a b : Cell) : mergeCell l a b = mergeCell l b a := by
  rcases a with ⟨⟨ac, af⟩, ap⟩; rcases b with ⟨⟨bc, bf⟩, bp⟩
  simp only [reduceIte, mergeCell, mergeFlag_comm l.1 (ac, af) (bc, bf)]
  cases af <;> cases bf <;>
    simp [mergeFlag, mergePayload_comm, Int.add_comm, Int.add_right_comm]

/-- **VC1** MERGE-COMM, over arbitrary states as the paper states it. -/
theorem vc1_merge_comm (l a b : D.Sigma) : D.merge l a b = D.merge l b a := by
  refine State.ext ?_ (fun r => mergeCell_comm _ _ _)
  show l.domain ∪ (a.domain ∪ b.domain) = l.domain ∪ (b.domain ∪ a.domain)
  rw [Finset.union_comm a.domain b.domain]

/-! ## The replay invariant

Three facts hold of every state a replay reaches from `sigma0`, and VC2
needs all three. A counter counts that replica's `set` events, so it is
never negative, and it is positive once the flag has ever been raised. A
cleared cell carries no payload, because `unset` clears both at once. -/

/-- What a replayed state looks like. -/
def WellFormed (s : State) : Prop :=
  ∀ r, 0 ≤ (s.cells r).1.1
     ∧ ((s.cells r).1.2 = true → 0 < (s.cells r).1.1)
     ∧ ((s.cells r).1.2 = false → (s.cells r).2 = (0, 0))

theorem wellFormed_initial : WellFormed initial := by
  intro r; exact ⟨le_refl 0, by simp [initial, zero], by simp [initial, zero]⟩

theorem wellFormed_step {s : State} (h : WellFormed s) (e : D.Event) :
    WellFormed (step s e) := by
  intro r
  rcases hop : e.op with v | _
  · simp only [step_set_cells _ _ hop]
    by_cases hr : r = e.rep
    · rw [if_pos hr]
      refine ⟨?_, fun _ => ?_, by simp⟩
      · show (0 : Int) ≤ (s.cells r).1.1 + 1
        have := (h r).1; omega
      · show (0 : Int) < (s.cells r).1.1 + 1
        have := (h r).1; omega
    · rw [if_neg hr]; exact h r
  · simp only [step_unset_cells _ _ hop]
    exact ⟨(h r).1, by simp, by simp⟩

theorem wellFormed_applyList {s : State} (h : WellFormed s) (pi : List D.Event) :
    WellFormed (D.applyList s pi) := by
  induction pi generalizing s with
  | nil => exact h
  | cons e rest ih => exact ih (wellFormed_step h e)

/-- Every canonical state is well formed: it is a replay from `sigma0`. -/
theorem wellFormed_of_isPaperCan {C : Ctx D} {E : Set D.Event} {s : D.Sigma}
    (hs : IsPaperCan D C E s) : WellFormed s := by
  obtain ⟨pi, -, -, hf⟩ := id hs
  exact hf ▸ wellFormed_applyList wellFormed_initial pi

/-! ## VC2: MERGE-INIT -/

/-- Merging a well-formed state against two empty states returns it. The
flag merge reads the counter, and well-formedness is what makes that read
agree with the flag already there. -/
theorem merge_init_of_wellFormed {s : State} (h : WellFormed s) :
    D.merge D.sigma0 D.sigma0 s = s := by
  refine State.ext ?_ ?_
  · show initial.domain ∪ (initial.domain ∪ s.domain) = s.domain
    simp [initial]
  · intro r
    obtain ⟨hnn, hpos, hzero⟩ := h r
    show mergeCell zero zero (s.cells r) = s.cells r
    rcases hc : s.cells r with ⟨⟨c, f⟩, p⟩
    rw [hc] at hnn hpos hzero
    cases f
    · have hp : p = (0, 0) := hzero rfl
      subst hp
      simp [mergeCell, mergeFlag, zero]
    · have hc0 : (0 : Int) < c := hpos rfl
      simp [mergeCell, mergeFlag, zero, hc0]

/-- **VC2** MERGE-INIT. -/
theorem vc2_merge_init (C : Ctx D) (E : Set D.Event) (s : D.Sigma)
    (_hsup : SupportedOn D C E) (hs : IsPaperCan D C E s) :
    D.merge D.sigma0 D.sigma0 s = s :=
  merge_init_of_wellFormed (wellFormed_of_isPaperCan hs)

/-! ## Which events write a cell

Cell `r` is written by `r`'s own `set` events and by every `unset`. A `set`
issued elsewhere leaves it alone. So the cell a replay reaches is fixed by
the **last** event of the replay that writes it, together with the number of
`set` events `r` issued, which is all the counter counts. -/

/-- `e` writes cell `r`. -/
def Touches (r : Nat) (e : D.Event) : Prop := e.op = .unset ∨ e.rep = r

/-- `e` is a `set` issued by `r`. There are two operations, so "not an
`unset`" is the decidable way to say it. -/
def SetAt (r : Nat) (e : D.Event) : Prop := e.rep = r ∧ e.op ≠ Action.unset

theorem isSet_iff {o : Action} : o ≠ Action.unset ↔ ∃ v, o = .set v := by
  cases o <;> simp

theorem not_touches {r : Nat} {e : D.Event} (h : ¬ Touches r e) :
    e.op ≠ .unset ∧ e.rep ≠ r := by
  simp only [Touches, not_or] at h; exact h

/-- No event of the list writes cell `r`. -/
def Untouched (r : Nat) (pi : List D.Event) : Prop := ∀ e ∈ pi, ¬ Touches r e

@[simp] theorem untouched_nil (r : Nat) : Untouched r [] := by simp [Untouched]

theorem untouched_append_singleton {r : Nat} {pi : List D.Event} {e : D.Event} :
    Untouched r (pi ++ [e]) ↔ Untouched r pi ∧ ¬ Touches r e := by
  constructor
  · exact fun h => ⟨fun a ha => h a (by simp [ha]), h e (by simp)⟩
  · rintro ⟨h, he⟩ a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact h a ha
    · rw [List.mem_singleton.mp ha]; exact he

/-! ## Counters -/

/-- The number of `set` events issued by `r`. -/
def setCount (r : Nat) (pi : List D.Event) : Nat :=
  pi.countP (fun e => decide (e.rep = r ∧ e.op ≠ Action.unset))

@[simp] theorem setCount_nil (r : Nat) : setCount r [] = 0 := rfl

theorem setCount_cons (r : Nat) (e : D.Event) (pi : List D.Event) :
    setCount r (e :: pi)
      = setCount r pi + if (e.rep = r ∧ e.op ≠ Action.unset) then 1 else 0 := by
  by_cases h : e.rep = r ∧ e.op ≠ Action.unset <;>
    simp [setCount, List.countP_cons, h]

/-- Replaying a list adds one to cell `r`'s counter for each `set` that `r`
issued, and changes no other counter. -/
theorem count_applyList (s : State) (pi : List D.Event) (r : Nat) :
    ((D.applyList s pi).cells r).1.1 = (s.cells r).1.1 + (setCount r pi : Int) := by
  induction pi generalizing s with
  | nil => simp [Impl.applyList]
  | cons e pi ih =>
      show ((D.applyList (D.do_ s e) pi).cells r).1.1 = _
      rw [ih, setCount_cons]
      rcases hop : e.op with v | _
      · simp only [do_eq, step_set_cells _ _ hop]
        by_cases hr : r = e.rep
        · rw [if_pos hr, if_pos (⟨hr.symm, by simp⟩ :
            e.rep = r ∧ Action.set v ≠ Action.unset)]
          show (s.cells r).1.1 + 1 + _ = _
          push_cast; ring
        · rw [if_neg hr, if_neg (by rintro ⟨h, -⟩; exact hr h.symm)]
          simp
      · simp only [do_eq, step_unset_cells _ _ hop]
        rw [if_neg (by rintro ⟨-, hv⟩; exact hv rfl)]
        simp

/-! ## The last writer -/

/-- A replay that never writes cell `r` leaves it exactly as it was. -/
theorem applyList_untouched {s : State} {pi : List D.Event} {r : Nat}
    (h : Untouched r pi) : (D.applyList s pi).cells r = s.cells r := by
  induction pi generalizing s with
  | nil => rfl
  | cons e pi ih =>
      obtain ⟨hu, hr⟩ := not_touches (h e (by simp))
      show (D.applyList (D.do_ s e) pi).cells r = _
      rw [ih (fun a ha => h a (by simp [ha]))]
      rcases hop : e.op with v | _
      · simp only [do_eq, step_set_cells _ _ hop]
        exact if_neg (fun h => hr h.symm)
      · exact absurd hop hu

/-- Splitting a replay at the last event that writes cell `r`. -/
theorem applyList_split {s : State} {pi pre post : List D.Event} {w : D.Event} {r : Nat}
    (hsplit : pi = pre ++ w :: post) (hpost : Untouched r post) :
    (D.applyList s pi).cells r = (D.do_ (D.applyList s pre) w).cells r := by
  subst hsplit
  show (D.applyList s (pre ++ w :: post)).cells r = _
  rw [show D.applyList s (pre ++ w :: post)
        = D.applyList (D.do_ (D.applyList s pre) w) post from by
      simp [Impl.applyList, List.foldl_append]]
  exact applyList_untouched hpost

/-- Every list either never writes cell `r`, or has a last event that does. -/
theorem exists_last_touch (r : Nat) (pi : List D.Event) :
    Untouched r pi ∨ ∃ pre w post, pi = pre ++ w :: post ∧ Touches r w
      ∧ Untouched r post := by
  induction pi using List.reverseRecOn with
  | nil => exact Or.inl (untouched_nil r)
  | append_singleton pi e ih =>
      by_cases he : Touches r e
      · exact Or.inr ⟨pi, e, [], rfl, he, untouched_nil r⟩
      · rcases ih with h | ⟨pre, w, post, hs, hw, hu⟩
        · exact Or.inl (untouched_append_singleton.mpr ⟨h, he⟩)
        · exact Or.inr ⟨pre, w, post ++ [e], by rw [hs]; simp, hw,
            untouched_append_singleton.mpr ⟨hu, he⟩⟩

/-! ## Edges

`loOn` is the framework's reading of `lo^C_E`, and `rcOrder D` is `rc` as an
`EventOrder`. The row-level reading of its `replayBefore` is just `rc`. -/

noncomputable instance : EventOrder D.toMRDTSig.toUpdateSig := Interface.rcOrder D

@[simp] theorem replayBefore_iff (a b : D.Event) :
    D.toMRDTSig.toUpdateSig.replayBefore a b
      ↔ a.op = Action.unset ∧ ∃ v, b.op = .set v := by
  refine Iff.trans ?_ (rcBefore_iff a.op b.op)
  exact @OperationPolicy.lift_replayOrder_iff D.toMRDTSig.toUpdateSig
    (Interface.policy D) a b

theorem not_edge_to_prefix {R : D.Event → D.Event → Prop}
    {pre post : List D.Event} {a x : D.Event}
    (hr : respects (pre ++ a :: post) R) (hm : x ∈ pre) : ¬ R a x :=
  (List.pairwise_append.mp hr).2.2 x hm a (by simp)

theorem not_edge_from_suffix {R : D.Event → D.Event → Prop}
    {pre post : List D.Event} {a x : D.Event}
    (hr : respects (pre ++ a :: post) R) (hm : x ∈ post) : ¬ R x a :=
  (List.pairwise_cons.mp (List.pairwise_append.mp hr).2.1).1 x hm

/-- `vis` is total on the events of one replica. -/
theorem vis_total {C : Ctx D} {a b : D.Event} (ha : a ∈ C.events) (hb : b ∈ C.events)
    (hne : a ≠ b) (hrep : a.rep = b.rep) : C.vis a b ∨ C.vis b a := by
  obtain ⟨p, t, hL, ht⟩ := ha
  obtain ⟨p', t', hL', ht'⟩ := hb
  exact C.vis_total_same_replica hL ht hL' ht' hne hrep

/-- Two `set` events of one replica never commute: the second overwrites the
first's payload, and a context gives them distinct timestamps. -/
theorem not_commutes_set_set_same {e₁ e₂ : D.Event} {v₁ v₂ : Nat}
    (h₁ : e₁.op = .set v₁) (h₂ : e₂.op = .set v₂) (hr : e₁.rep = e₂.rep)
    (ht : e₁.time ≠ e₂.time) : ¬ D.Commutes e₁ e₂ := by
  intro hc
  have h := congrArg (fun t : State => (t.cells e₁.rep).2.1) (hc initial)
  simp only [do_eq, step_set_cells _ _ h₂, step_set_cells _ _ h₁, hr, if_pos] at h
  exact ht h.symm

/-- Anything that writes cell `r` and is not `w` itself fails to commute with
a `set` `w` of `r`. -/
theorem not_commutes_of_touches {C : Ctx D} {r : Nat} {w x : D.Event} {v : Nat}
    (hw : w.op = .set v) (hwr : w.rep = r) (hx : Touches r x) (hne : x ≠ w)
    (hwC : w ∈ C.events) (hxC : x ∈ C.events) : ¬ D.Commutes w x := by
  rcases hop : x.op with u | _
  · have hxr : x.rep = r := by
      rcases hx with hu | hr
      · rw [hop] at hu; exact absurd hu (by simp)
      · exact hr
    exact not_commutes_set_set_same hw hop (hwr.trans hxr.symm)
      (fun h => hne (C.ts_unique hxC hwC h.symm))
  · exact not_commutes_set_unset hw hop

/-! ## Liveness

Cell `r` is raised exactly when some `set` of `r` in `E` is followed by
nothing that writes the cell: no `unset` of `E` and no later `set` of `r`
observes it. -/

variable {C : Ctx D}

/-- No event of `E` that writes cell `r` observes `a`. -/
def Survives (C : Ctx D) (E : Set D.Event) (r : Nat) (a : D.Event) : Prop :=
  ¬ ∃ x ∈ E, Touches r x ∧ C.vis a x

/-- Cell `r` is live in `E`: some `set` of `r` survives. -/
def Live (C : Ctx D) (E : Set D.Event) (r : Nat) : Prop :=
  ∃ w ∈ E, SetAt r w ∧ Survives C E r w

/-- **A surviving `set` is the last event of the replay that writes its
cell.** Anything of `E` writing the cell is either seen by `w`, which
`Survives` forbids, or `vis`-below it, or concurrent with it. In the last
case it cannot be a `set` of `r`, since one replica's events are never
concurrent, so it is an `unset`, and then `rc` orders it before `w` with no
absorber available, again by `Survives`. -/
theorem untouched_after_survivor {E : Set D.Event} {pi pre post : List D.Event}
    (hvs : VisStrict D C) (hsup : SupportedOn D C E)
    (hp : listPermOf pi E) (hr : respects pi (paperOrder (policy D) C E))
    {r : Nat} {w : D.Event} {v : Nat}
    (hwE : w ∈ E) (hwr : w.rep = r) (hwv : w.op = .set v) (hsv : Survives C E r w)
    (hpi : pi = pre ++ w :: post) : Untouched r post := by
  obtain ⟨htr, hirr⟩ := hvs
  intro x hx htouch
  have hxE : x ∈ E := (hp.2 x).mp (by rw [hpi]; simp [hx])
  have hne : x ≠ w := by
    have hnd := hp.1
    rw [hpi, List.nodup_append, List.nodup_cons] at hnd
    intro heq; exact hnd.2.1.1 (heq ▸ hx)
  have hnv : ¬ C.vis w x := fun hv => hsv ⟨x, hxE, htouch, hv⟩
  have hnc : ¬ D.Commutes w x :=
    not_commutes_of_touches hwv hwr htouch hne (hsup w hwE) (hsup x hxE)
  have hrp : (pre ++ w :: post).Pairwise
      (fun a b => ¬ paperOrder (policy D) C E b a) := by rw [← hpi]; exact hr
  have hno := (List.pairwise_cons.mp (List.pairwise_append.mp hrp).2.1).1 x hx
  by_cases hv2 : C.vis x w
  · exact hno (Or.inl ⟨hv2, fun hc => hnc (fun s => (hc s).symm)⟩)
  · rcases hxop : x.op with u | _
    · have hxr : x.rep = r := by
        rcases htouch with hu | hrr
        · rw [hxop] at hu; exact absurd hu (by simp)
        · exact hrr
      rcases vis_total (hsup x hxE) (hsup w hwE) hne (hxr.trans hwr.symm) with h | h
      · exact hv2 h
      · exact hnv h
    · have hpol : (policy D).before x.op w.op :=
        (rcBefore_iff x.op w.op).mpr ⟨hxop, v, hwv⟩
      refine hno (Or.inr ⟨hv2, hnv, hpol, ?_⟩)
      rintro ⟨c, hcE, hvc, hncc⟩
      exact hsv ⟨c, hcE, hwr ▸ absorber_of_not_commutes hwv hncc, hvc⟩

/-! ## The canonical cell

Three facts pin `can(E)` cellwise: the counter counts `r`'s `set` events,
the flag is liveness, and a live cell carries the surviving write. -/

/-- **A live cell holds its surviving write.** -/
theorem canonical_cell_live {E : Set D.Event} {s : D.Sigma}
    (hvs : VisStrict D C) (hsup : SupportedOn D C E) (hs : IsPaperCan D C E s)
    {r : Nat} {w : D.Event} {v : Nat}
    (hwE : w ∈ E) (hwr : w.rep = r) (hwv : w.op = .set v) (hsv : Survives C E r w) :
    (s.cells r).1.2 = true ∧ (s.cells r).2 = (w.time, v) := by
  obtain ⟨pi, hp, hr, hf⟩ := id hs
  obtain ⟨pre, post, hpi⟩ := List.mem_iff_append.mp ((hp.2 w).mpr hwE)
  have hu := untouched_after_survivor hvs hsup hp hr hwE hwr hwv hsv hpi
  have hcell : s.cells r = (D.do_ (D.applyList D.sigma0 pre) w).cells r := by
    rw [show s = D.applyList D.sigma0 pi from hf.symm]
    exact applyList_split hpi hu
  rw [hcell]
  simp only [do_eq, step_set_cells _ _ hwv, if_pos hwr.symm]
  exact ⟨trivial, trivial⟩

/-- **A cell that is not live is clear, and carries no payload.** -/
theorem canonical_cell_dead {E : Set D.Event} {s : D.Sigma}
    (hvs : VisStrict D C) (hsup : SupportedOn D C E) (hs : IsPaperCan D C E s)
    {r : Nat} (hdead : ¬ Live C E r) :
    (s.cells r).1.2 = false ∧ (s.cells r).2 = (0, 0) := by
  obtain ⟨htr, hirr⟩ := hvs
  obtain ⟨pi, hp, hr, hf⟩ := id hs
  have hsv : s = D.applyList D.sigma0 pi := hf.symm
  rcases exists_last_touch r pi with hun | ⟨pre, w, post, hpi, hw, hu⟩
  · rw [hsv, applyList_untouched hun]
    exact ⟨rfl, rfl⟩
  · have hcell : s.cells r = (D.do_ (D.applyList D.sigma0 pre) w).cells r := by
      rw [hsv]; exact applyList_split hpi hu
    rcases hop : w.op with v | _
    · exfalso
      have hwr : w.rep = r := by
        rcases hw with hun' | hrr
        · rw [hop] at hun'; exact absurd hun' (by simp)
        · exact hrr
      have hwE : w ∈ E := (hp.2 w).mp (by rw [hpi]; simp)
      refine hdead ⟨w, hwE, ⟨hwr, by rw [hop]; simp⟩, ?_⟩
      rintro ⟨x, hxE, htouch, hvwx⟩
      have hne : x ≠ w := fun heq => hirr w (heq ▸ hvwx)
      have hnc : ¬ D.Commutes w x :=
        not_commutes_of_touches hop hwr htouch hne (hsup w hwE) (hsup x hxE)
      have hxm : x ∈ pre ++ w :: post := by rw [← hpi]; exact (hp.2 x).mpr hxE
      have hrp : respects (pre ++ w :: post) (paperOrder (policy D) C E) := by
        rw [← hpi]; exact hr
      rcases List.mem_append.mp hxm with hxpre | hxrest
      · exact not_edge_to_prefix hrp hxpre (Or.inl ⟨hvwx, hnc⟩)
      · rcases List.mem_cons.mp hxrest with heq | hxpost
        · exact hne heq
        · exact hu x hxpost htouch
    · rw [hcell]
      simp only [do_eq, step_unset_cells _ _ hop]
      exact ⟨trivial, trivial⟩


/-- **The counter of a canonical state** counts `r`'s `set` events. -/
theorem canonical_count {E : Set D.Event} {s : D.Sigma}
    (hs : IsPaperCan D C E s) {pi : List D.Event} (hp : listPermOf pi E) (r : Nat) :
    (s.cells r).1.1 = (setCount r pi : Int) := by
  obtain ⟨rho, hq, -, hf⟩ := id hs
  rw [show s = D.applyList D.sigma0 rho from hf.symm, count_applyList]
  have hperm : rho.Perm pi :=
    (List.perm_ext_iff_of_nodup hq.1 hp.1).mpr (fun a => (hq.2 a).trans (hp.2 a).symm)
  rw [show setCount r rho = setCount r pi from List.Perm.countP_eq _ hperm]
  show (initial.cells r).1.1 + _ = _
  simp [initial, zero]

/-! ## The guard: causal monotonicity

The two orders this row confuses, timestamp and causal, agree inside a
configuration, because a `Configuration` carries `causal_mono`. That is the
side condition the five conditions need, and it costs nothing to discharge.
-/

/-- Visibility increases the timestamp. -/
def Monotone (C : Ctx D) : Prop := ∀ a b : D.Event, C.vis a b → a.time < b.time

theorem monotone_of_mintHonest (C : Configuration D.toMRDTSig)
    (_h : MintHonest D.toMRDTSig issuance.CanIssue C) :
    Monotone C.replayContext := fun _ _ h => C.causal_mono h

/-- **The surviving write of a replica is its latest.** Two `set` events of
one replica are `vis`-comparable, and the survivor is not observed by any
other writer of its cell, so every other `set` of that replica precedes it
and, by monotonicity, carries a smaller timestamp.

This is what reconciles the payload merge with canonicity: `mergePayload`
takes the greater timestamp, and inside a configuration that **is** the
causally later write. -/
theorem survivor_latest {C : Ctx D} (hvs : VisStrict D C) (hmono : Monotone C)
    {E : Set D.Event} (hsup : SupportedOn D C E) {r : Nat} {w w' : D.Event}
    (hwE : w ∈ E) (hwr : w.rep = r) {v : Nat} (hwv : w.op = .set v)
    (hsv : Survives C E r w)
    (hw'E : w' ∈ E) (hw'r : w'.rep = r) {v' : Nat} (hw'v : w'.op = .set v')
    (hne : w' ≠ w) : w'.time < w.time := by
  obtain ⟨htr, hirr⟩ := hvs
  have htouch : Touches r w' := Or.inr hw'r
  rcases vis_total (hsup w' hw'E) (hsup w hwE) hne (hw'r.trans hwr.symm) with h | h
  · exact hmono w' w h
  · exact absurd ⟨w', hw'E, htouch, h⟩ hsv

/-- A surviving write of a subset is still a write of the superset, and the
superset's own survivor is at least as late. -/
theorem survivor_mono {C : Ctx D} (hvs : VisStrict D C) (hmono : Monotone C)
    {E F : Set D.Event} (hEF : E ⊆ F) (hsup : SupportedOn D C F) {r : Nat}
    {w w' : D.Event} (hwE : w ∈ E) (hwr : w.rep = r) {v : Nat} (hwv : w.op = .set v)
    (hw'F : w' ∈ F) (hw'r : w'.rep = r) {v' : Nat} (hw'v : w'.op = .set v')
    (hsv' : Survives C F r w') : w.time ≤ w'.time := by
  by_cases hne : w = w'
  · exact le_of_eq (by rw [hne])
  · exact le_of_lt (survivor_latest hvs hmono hsup hw'F hw'r hw'v hsv'
      (hEF hwE) hwr hwv hne)

/-! ## A maximal `unset` observes every surviving write

This is the fact VC4's `unset` case turns on. `rc` orders an `unset` before
a `set`, so a `set` concurrent with a maximal `unset` would give `lo^C_E` an
edge out of it, unless the absorber clause cancels that edge. The absorber
can only be another writer of the same cell that observes the `set`, and
that is exactly what a surviving `set` does not have. -/

theorem survivor_vis_of_max_unset {C : Ctx D} (hvs : VisStrict D C)
    {U : Set D.Event} (hsup : SupportedOn D C U) {e : D.Event} {W : Finset Nat}
    (heU : e ∈ U) (heop : e.op = .unset)
    (hmax : PaperMaximalOn D C U e)
    {r : Nat} {w : D.Event} (hwU : w ∈ U) (hwr : w.rep = r) {v : Nat}
    (hwv : w.op = .set v) (hsv : Survives C U r w) : C.vis w e := by
  obtain ⟨htr, hirr⟩ := hvs
  by_contra hnv
  have hne : w ≠ e := by
    intro h; rw [h, heop] at hwv; exact absurd hwv (by simp)
  have hnc : ¬ D.Commutes e w := fun hc => not_commutes_set_unset hwv heop
    (fun s => (hc s).symm)
  by_cases hve : C.vis e w
  · exact hmax w hwU hne (Or.inl ⟨hve, hnc⟩)
  · refine hmax w hwU hne (Or.inr ⟨hve, hnv, ?_, ?_⟩)
    · exact (rcBefore_iff e.op w.op).mpr ⟨heop, v, hwv⟩
    · rintro ⟨c, hcU, hvc, hncc⟩
      exact hsv ⟨c, hcU, hwr ▸ absorber_of_not_commutes hwv hncc, hvc⟩

/-- Every other `set` of the replica precedes the survivor, so it precedes
anything the survivor precedes. -/
theorem other_set_vis {C : Ctx D} (hvs : VisStrict D C) {E : Set D.Event}
    (hsup : SupportedOn D C E) {r : Nat} {w w' : D.Event}
    (hwE : w ∈ E) (hwr : w.rep = r) {v : Nat} (hwv : w.op = .set v)
    (hsv : Survives C E r w)
    (hw'E : w' ∈ E) (hw'r : w'.rep = r) (hne : w' ≠ w) : C.vis w' w := by
  obtain ⟨htr, hirr⟩ := hvs
  rcases vis_total (hsup w' hw'E) (hsup w hwE) hne (hw'r.trans hwr.symm) with h | h
  · exact h
  · exact absurd ⟨w', hw'E, Or.inr hw'r, h⟩ hsv

/-! ## The domain of a canonical state

`State.ext` asks for the domain as well as the cells, so the conditions need
it. `set` inserts the issuer and `unset` leaves it alone, so the domain is
exactly the replicas that have issued a `set`. -/

instance decSetAt (r : Nat) (e : D.Event) : Decidable (SetAt r e) := by
  unfold SetAt; infer_instance

theorem mem_domain_step (s : State) (e : D.Event) (r : Nat) :
    r ∈ (D.do_ s e).domain ↔ r ∈ s.domain ∨ SetAt r e := by
  rcases hop : e.op with v | _
  · rw [do_eq, step_set_domain _ _ hop]
    simp only [Finset.mem_insert, SetAt, hop, ne_eq, reduceCtorEq,
      not_false_eq_true, and_true]
    exact ⟨fun h => h.elim (fun h => Or.inr h.symm) Or.inl,
      fun h => h.elim Or.inr (fun h => Or.inl h.symm)⟩
  · rw [do_eq, step_unset_domain _ _ hop]
    simp [SetAt, hop]

theorem mem_domain_applyList (s : State) (pi : List D.Event) (r : Nat) :
    r ∈ (D.applyList s pi).domain ↔ r ∈ s.domain ∨ ∃ e ∈ pi, SetAt r e := by
  induction pi generalizing s with
  | nil => simp [Impl.applyList]
  | cons e pi ih =>
      show r ∈ (D.applyList (D.do_ s e) pi).domain ↔ _
      rw [ih, mem_domain_step]
      constructor
      · rintro ((h | h) | ⟨a, ha, hsa⟩)
        · exact Or.inl h
        · exact Or.inr ⟨e, by simp, h⟩
        · exact Or.inr ⟨a, by simp [ha], hsa⟩
      · rintro (h | ⟨a, ha, hsa⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp ha with rfl | ha
          · exact Or.inl (Or.inr hsa)
          · exact Or.inr ⟨a, ha, hsa⟩

/-- **The domain of `can(E)`** is the replicas that have issued a `set`. -/
theorem canonical_domain {E : Set D.Event} {s : D.Sigma}
    (hs : IsPaperCan D C E s) (r : Nat) :
    r ∈ s.domain ↔ ∃ w ∈ E, SetAt r w := by
  obtain ⟨pi, hp, -, hf⟩ := id hs
  rw [show s = D.applyList D.sigma0 pi from hf.symm, mem_domain_applyList]
  constructor
  · rintro (h | ⟨w, hw, hsw⟩)
    · exact absurd h (by simp [show D.sigma0 = initial from rfl, initial])
    · exact ⟨w, (hp.2 w).mp hw, hsw⟩
  · rintro ⟨w, hw, hsw⟩
    exact Or.inr ⟨w, (hp.2 w).mpr hw, hsw⟩

/-! ## The causal delta sits inside the set

`down(e) \ {e}` is built from `vis` steps at non-commuting pairs, which is
exactly what `WeaklyClosed` pulls back, so it lies inside any admissible `E`
holding `e`. -/

theorem downset_diff_subset {E : Set D.Event} {e : D.Event}
    (hcl : WeaklyClosed D C E) (he : e ∈ E) :
    downset C e \ {e} ⊆ E \ {e} := by
  rintro x ⟨hx, hxe⟩
  refine ⟨?_, hxe⟩
  rcases hx with rfl | hx
  · exact he
  · clear hxe
    revert he
    induction hx with
    | single h => exact fun he => hcl _ _ h.1 h.2 he
    | tail _ h ih => exact fun he => ih (hcl _ _ h.1 h.2 he)

/-! ## Comparing counters

The counter of `can(E)` at `r` counts the `set` events of `r` in `E`, so one
canonical state's counter is at most another's as soon as every such event
of the first set is one of the second. -/

/-- The boolean `setCount` counts with. -/
def isSetAt (r : Nat) (e : D.Event) : Bool :=
  decide (e.rep = r ∧ e.op ≠ Action.unset)

@[simp] theorem isSetAt_iff {r : Nat} {e : D.Event} :
    isSetAt r e = true ↔ SetAt r e := by simp [isSetAt, SetAt]

theorem setCount_eq_length (r : Nat) (pi : List D.Event) :
    setCount r pi = (pi.filter (isSetAt r)).length :=
  List.countP_eq_length_filter

theorem canonical_count_le {E F : Set D.Event} {a b : D.Sigma}
    (ha : IsPaperCan D C E a) (hb : IsPaperCan D C F b) {r : Nat}
    (hsub : ∀ w ∈ E, SetAt r w → w ∈ F) :
    (a.cells r).1.1 ≤ (b.cells r).1.1 := by
  obtain ⟨pi, hp, -, -⟩ := id ha
  obtain ⟨rho, hq, -, -⟩ := id hb
  rw [canonical_count ha hp r, canonical_count hb hq r]
  refine Int.ofNat_le.mpr ?_
  rw [setCount_eq_length, setCount_eq_length]
  refine List.Subperm.length_le (List.subperm_of_subset (hp.1.filter _) ?_)
  intro x hx
  rw [List.mem_filter] at hx ⊢
  exact ⟨(hq.2 x).mpr (hsub x ((hp.2 x).mp hx.1) (isSetAt_iff.mp hx.2)), hx.2⟩

theorem canonical_count_eq {E F : Set D.Event} {a b : D.Sigma}
    (ha : IsPaperCan D C E a) (hb : IsPaperCan D C F b) {r : Nat}
    (h₁ : ∀ w ∈ E, SetAt r w → w ∈ F) (h₂ : ∀ w ∈ F, SetAt r w → w ∈ E) :
    (a.cells r).1.1 = (b.cells r).1.1 :=
  le_antisymm (canonical_count_le ha hb h₁) (canonical_count_le hb ha h₂)

/-- A canonical state of a subset has the strictly smaller counter as soon as
the superset holds a `set` of `r` the subset misses. -/
theorem canonical_count_lt {E F : Set D.Event} {a b : D.Sigma}
    (ha : IsPaperCan D C E a) (hb : IsPaperCan D C F b) {r : Nat} {w : D.Event}
    (hsub : ∀ x ∈ E, SetAt r x → x ∈ F) (hwF : w ∈ F) (hsw : SetAt r w)
    (hwE : w ∉ E) : (a.cells r).1.1 < (b.cells r).1.1 := by
  obtain ⟨pi, hp, -, -⟩ := id ha
  obtain ⟨rho, hq, -, -⟩ := id hb
  rw [canonical_count ha hp r, canonical_count hb hq r]
  refine Int.ofNat_lt.mpr ?_
  rw [setCount_eq_length, setCount_eq_length]
  have hmem : w ∈ rho.filter (isSetAt r) := by
    rw [List.mem_filter]
    exact ⟨(hq.2 w).mpr hwF, isSetAt_iff.mpr hsw⟩
  have hsp : (pi.filter (isSetAt r)).Subperm ((rho.filter (isSetAt r)).erase w) := by
    refine List.subperm_of_subset (hp.1.filter _) ?_
    intro x hx
    rw [List.mem_filter] at hx
    have hxE : x ∈ E := (hp.2 x).mp hx.1
    have hxne : x ≠ w := fun h => hwE (h ▸ hxE)
    rw [List.mem_erase_of_ne hxne, List.mem_filter]
    exact ⟨(hq.2 x).mpr (hsub x hxE (isSetAt_iff.mp hx.2)), hx.2⟩
  have hlen := hsp.length_le
  rw [List.length_erase_of_mem hmem] at hlen
  have hpos : 0 < (rho.filter (isSetAt r)).length := List.length_pos_of_mem hmem
  omega

/-! ## The flag is liveness

`canonical_cell_live` and `canonical_cell_dead` read in both directions. -/

theorem canonical_flag {E : Set D.Event} {s : D.Sigma}
    (hvs : VisStrict D C) (hsup : SupportedOn D C E) (hs : IsPaperCan D C E s)
    (r : Nat) : (s.cells r).1.2 = true ↔ Live C E r := by
  constructor
  · intro hf
    by_contra hdead
    exact absurd ((canonical_cell_dead hvs hsup hs hdead).1.symm.trans hf) (by simp)
  · rintro ⟨w, hwE, ⟨hwr, hwop⟩, hsv⟩
    obtain ⟨v, hv⟩ := isSet_iff.mp hwop
    exact (canonical_cell_live hvs hsup hs hwE hwr hv hsv).1

theorem canonical_payload_dead {E : Set D.Event} {s : D.Sigma}
    (hvs : VisStrict D C) (hsup : SupportedOn D C E) (hs : IsPaperCan D C E s)
    {r : Nat} (hf : (s.cells r).1.2 = false) : (s.cells r).2 = (0, 0) := by
  refine (canonical_cell_dead hvs hsup hs (fun hlive => ?_)).2
  exact absurd (((canonical_flag hvs hsup hs r).mpr hlive).symm.trans hf) (by simp)

/-- A survivor of a larger set survives in any subset that holds it. -/
theorem survives_mono {E F : Set D.Event} (hEF : E ⊆ F) {r : Nat} {a : D.Event}
    (h : Survives C F r a) : Survives C E r a :=
  fun ⟨x, hxE, ht, hv⟩ => h ⟨x, hEF hxE, ht, hv⟩

/-! ## A maximal `unset` observes every write that survives without it

The corrected form of the fact VC4's `unset` case turns on. A write cannot
survive the `unset` itself, since an `unset` touches every cell, so the
premise is survival in `E \ {e}`. -/

theorem survivor_vis_of_max_unset_diff {C : Ctx D} (hvs : VisStrict D C)
    {U : Set D.Event} (hsup : SupportedOn D C U) {e : D.Event}
    (heU : e ∈ U) (heop : e.op = .unset) (hmax : PaperMaximalOn D C U e)
    {r : Nat} {w : D.Event} (hwU : w ∈ U) (hwne : w ≠ e) {v : Nat}
    (hwv : w.op = .set v) (hwr : w.rep = r)
    (hsv : Survives C (U \ {e}) r w) : C.vis w e := by
  by_contra hnv
  have hnc : ¬ D.Commutes e w := fun hc => not_commutes_set_unset hwv heop
    (fun s => (hc s).symm)
  by_cases hve : C.vis e w
  · exact hmax w hwU hwne (Or.inl ⟨hve, hnc⟩)
  · refine hmax w hwU hwne (Or.inr ⟨hve, hnv, ?_, ?_⟩)
    · exact (rcBefore_iff e.op w.op).mpr ⟨heop, v, hwv⟩
    · rintro ⟨c, hcU, hvc, hncc⟩
      have hcne : c ≠ e := by
        rintro rfl; exact hnv hvc
      exact hsv ⟨c, ⟨hcU, hcne⟩, hwr ▸ absorber_of_not_commutes hwv hncc, hvc⟩

/-! ## Merging a cell against itself

VC4's off-cell case and the conditions' side cells all reduce to this: the
ancestor and one branch are the same cell, and the other branch wins. -/

theorem mergeCell_self (l a : Cell)
    (h1 : a.1.2 = true → l.1.2 = false → l.1.1 < a.1.1)
    (h2 : a.1.2 = true → l.1.2 = true → mergePayload l.2 a.2 l.2 = a.2)
    (h3 : a.1.2 = false → a.2 = (0, 0)) :
    mergeCell l a l = a := by
  obtain ⟨⟨cl, fl⟩, pl⟩ := l
  obtain ⟨⟨ca, fa⟩, pa⟩ := a
  simp only at h1 h2 h3
  cases fa <;> cases fl
  · simp [mergeCell, mergeFlag, h3 rfl]
  · simp [mergeCell, mergeFlag, h3 rfl]
  · simp [mergeCell, mergeFlag, h1 rfl rfl]
  · simp [mergeCell, mergeFlag, h2 rfl rfl]

/-- The issuer's cell under a `set`: both branches already carry the new
write, so the merge keeps it, provided the ancestor-side payload is older. -/
theorem mergeCell_issuer (l a : Cell) (t x : Nat)
    (hpay : a.1.2 = true → a.2.1 < t) :
    mergeCell l a (((l.1.1 + 1, true), (t, x)) : Cell)
      = (((a.1.1 + 1, true), (t, x)) : Cell) := by
  obtain ⟨⟨cl, fl⟩, pl⟩ := l
  obtain ⟨⟨ca, fa⟩, pa⟩ := a
  cases fa
  · simp [mergeCell, mergeFlag]
    omega
  · have h := hpay rfl
    simp only at h
    simp [mergeCell, mergeFlag, mergePayload, Nat.ne_of_lt h,
      Nat.not_lt.mpr (le_of_lt h)]
    omega

/-- Every cell under an `unset`: the branch is cleared, and the merge keeps
it cleared as long as the ancestor's counter is not the smaller one. -/
theorem mergeCell_clear (l a : Cell)
    (hcnt : a.1.2 = true → a.1.1 ≤ l.1.1) :
    mergeCell l a (((l.1.1, false), (0, 0)) : Cell)
      = (((a.1.1, false), (0, 0)) : Cell) := by
  obtain ⟨⟨cl, fl⟩, pl⟩ := l
  obtain ⟨⟨ca, fa⟩, pa⟩ := a
  cases fa
  · simp [mergeCell, mergeFlag]
  · have h := hcnt rfl
    simp only at h
    simp [mergeCell, mergeFlag, Int.not_lt.mpr h]

/-! ## VC4 CAUSAL-DELTA

`e` is maximal in `U`, `A` is `can(U \ {e})` and `B` is `can(down(e) \ {e})`.
Cell by cell, `B` is the ancestor of a merge whose branches are `A` and
`e(B)`, and the equation says that merge is `e(A)`.

The counter is the same arithmetic in every case. The flag and the payload
are where the guard is spent. Under a `set`, the issuer's cell needs the
new write to be the later one, which is `Monotone` applied to the `vis` edge
maximality forces. Under an `unset`, the cleared cell needs every surviving
`set` of the replica to lie in the causal delta, which is the same edge read
the other way. -/

theorem vc4_causal_delta (C : Ctx D) (U : Set D.Event) (A B : D.Sigma) (e : D.Event)
    (hmono : Monotone C) (hvs : VisStrict D C)
    (hsup : SupportedOn D C U) (hcl : WeaklyClosed D C U)
    (heU : e ∈ U) (hmax : PaperMaximalOn D C U e)
    (hA : IsPaperCan D C (U \ {e}) A)
    (hB : IsPaperCan D C (downset C e \ {e}) B) :
    D.merge B A (D.do_ B e) = D.do_ A e := by
  have hDU : downset C e \ {e} ⊆ U \ {e} := downset_diff_subset hcl heU
  have hsupA : SupportedOn D C (U \ {e}) := fun x hx => hsup x hx.1
  have hsupB : SupportedOn D C (downset C e \ {e}) := fun x hx => hsupA x (hDU hx)
  -- the three facts the off-cell merge needs
  have h3 : ∀ r, (A.cells r).1.2 = false → (A.cells r).2 = (0, 0) :=
    fun r hf => canonical_payload_dead hvs hsupA hA hf
  have h1 : ∀ r, (A.cells r).1.2 = true → (B.cells r).1.2 = false →
      (B.cells r).1.1 < (A.cells r).1.1 := by
    intro r hfa hfb
    obtain ⟨w, hwE, hsw, hsv⟩ := (canonical_flag hvs hsupA hA r).mp hfa
    have hwD : w ∉ downset C e \ {e} := fun hw =>
      absurd (((canonical_flag hvs hsupB hB r).mpr
        ⟨w, hw, hsw, survives_mono hDU hsv⟩).symm.trans hfb) (by simp)
    exact canonical_count_lt hB hA (fun x hx _ => hDU hx) hwE hsw hwD
  have h2 : ∀ r, (A.cells r).1.2 = true → (B.cells r).1.2 = true →
      mergePayload (B.cells r).2 (A.cells r).2 (B.cells r).2 = (A.cells r).2 := by
    intro r hfa hfb
    obtain ⟨wa, hwaE, ⟨hwar, hwaop⟩, hsva⟩ := (canonical_flag hvs hsupA hA r).mp hfa
    obtain ⟨wb, hwbE, ⟨hwbr, hwbop⟩, hsvb⟩ := (canonical_flag hvs hsupB hB r).mp hfb
    obtain ⟨va, hva⟩ := isSet_iff.mp hwaop
    obtain ⟨vb, hvb⟩ := isSet_iff.mp hwbop
    rw [(canonical_cell_live hvs hsupA hA hwaE hwar hva hsva).2,
      (canonical_cell_live hvs hsupB hB hwbE hwbr hvb hsvb).2]
    by_cases hts : wa.time = wb.time
    · obtain rfl : wa = wb := C.ts_unique (hsupA wa hwaE) (hsupB wb hwbE) hts
      obtain rfl : va = vb := by rw [hva] at hvb; injection hvb
      simp only [mergePayload, if_true, if_pos]
      refine Prod.ext rfl ?_
      show (va + va) / 2 = va
      omega
    · have hle : wb.time ≤ wa.time :=
        survivor_mono hvs hmono hDU hsupA hwbE hwbr hvb hwaE hwar hva hsva
      have hlt : wb.time < wa.time := lt_of_le_of_ne hle (fun h => hts h.symm)
      simp [mergePayload, fun h : wa.time = wb.time => hts h, hlt]
  refine State.ext ?_ ?_
  · ext r
    show r ∈ B.domain ∪ (A.domain ∪ (D.do_ B e).domain) ↔ r ∈ (D.do_ A e).domain
    rw [Finset.mem_union, Finset.mem_union, mem_domain_step, mem_domain_step,
      canonical_domain hA, canonical_domain hB]
    constructor
    · rintro (⟨w, hw, hsw⟩ | ⟨w, hw, hsw⟩ | ⟨w, hw, hsw⟩ | hse)
      · exact Or.inl ⟨w, hDU hw, hsw⟩
      · exact Or.inl ⟨w, hw, hsw⟩
      · exact Or.inl ⟨w, hDU hw, hsw⟩
      · exact Or.inr hse
    · rintro (⟨w, hw, hsw⟩ | hse)
      · exact Or.inr (Or.inl ⟨w, hw, hsw⟩)
      · exact Or.inr (Or.inr (Or.inr hse))
  · intro r
    show mergeCell (B.cells r) (A.cells r) ((D.do_ B e).cells r)
      = (D.do_ A e).cells r
    rcases hop : e.op with v | _
    · simp only [do_eq, step_set_cells _ _ hop]
      by_cases hr : r = e.rep
      · rw [if_pos hr, if_pos hr]
        refine mergeCell_issuer (B.cells r) (A.cells r) e.time v (fun hfa => ?_)
        obtain ⟨wa, hwaE, ⟨hwar, hwaop⟩, hsva⟩ :=
          (canonical_flag hvs hsupA hA r).mp hfa
        obtain ⟨va, hva⟩ := isSet_iff.mp hwaop
        rw [(canonical_cell_live hvs hsupA hA hwaE hwar hva hsva).2]
        have hne : wa ≠ e := hwaE.2
        have hrep : e.rep = wa.rep := by rw [hwar, hr]
        have hts : e.time ≠ wa.time := fun h =>
          hne (C.ts_unique (hsupA wa hwaE) (hsup e heU) h.symm)
        rcases vis_total (hsup e heU) (hsupA wa hwaE) (Ne.symm hne) hrep with hv | hv
        · exact absurd (hmax wa hwaE.1 hne
            (Or.inl ⟨hv, not_commutes_set_set_same hop hva hrep hts⟩)) (by simp)
        · exact hmono wa e hv
      · rw [if_neg hr, if_neg hr]
        exact mergeCell_self _ _ (h1 r) (h2 r) (h3 r)
    · simp only [do_eq, step_unset_cells _ _ hop]
      refine mergeCell_clear (B.cells r) (A.cells r) (fun hfa => ?_)
      refine canonical_count_le hA hB (fun w' hw' hsw' => ?_)
      obtain ⟨w, hwE, ⟨hwr, hwop⟩, hsv⟩ := (canonical_flag hvs hsupA hA r).mp hfa
      obtain ⟨vw, hvw⟩ := isSet_iff.mp hwop
      have hwe : C.vis w e := survivor_vis_of_max_unset_diff hvs hsup heU hop hmax
        hwE.1 hwE.2 hvw hwr hsv
      obtain ⟨vw', hvw'⟩ := isSet_iff.mp hsw'.2
      have hw'e : C.vis w' e := by
        by_cases hsame : w' = w
        · exact hsame ▸ hwe
        · exact hvs.1 (other_set_vis hvs hsupA hwE hwr hvw hsv hw' hsw'.1 hsame) hwe
      refine ⟨Or.inr (Relation.TransGen.single ⟨hw'e, ?_⟩), ?_⟩
      · exact not_commutes_set_unset hvw' hop
      · exact hw'.2

/-! ## The latest write of a cell

Every `set` of cell `r` is issued by replica `r`, so the writes of one cell
are pairwise `vis`-comparable and, inside a `Monotone` context, ordered by
timestamp. A cell is live exactly when its latest write is not followed by
an `unset`, which is the reading the join lemma below runs on. -/

theorem exists_time_max (l : List D.Event) (h : l ≠ []) :
    ∃ w ∈ l, ∀ x ∈ l, x.time ≤ w.time := by
  induction l with
  | nil => exact absurd rfl h
  | cons a t ih =>
      by_cases ht : t = []
      · subst ht
        exact ⟨a, by simp, by intro x hx; rw [List.mem_singleton.mp hx]⟩
      · obtain ⟨w, hw, hmax⟩ := ih ht
        by_cases h' : a.time ≤ w.time
        · refine ⟨w, List.mem_cons_of_mem _ hw, ?_⟩
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact h'
          · exact hmax x hx
        · refine ⟨a, by simp, ?_⟩
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact le_refl _
          · exact le_trans (hmax x hx) (Nat.not_le.mp h').le

/-- `w` is the last `set` of cell `r` in `E`. -/
def LatestSet (C : Ctx D) (E : Set D.Event) (r : Nat) (w : D.Event) : Prop :=
  w ∈ E ∧ SetAt r w ∧ ∀ w' ∈ E, SetAt r w' → w' ≠ w → C.vis w' w

/-- **A cell with a `set` has a latest one.** The writes of a cell come from
one replica, so they are `vis`-comparable, and the context makes `vis`
increase the timestamp, so the timestamp maximum is the `vis` maximum. -/
theorem exists_latestSet {E : Set D.Event} {s : D.Sigma}
    (hmono : Monotone C) (hsup : SupportedOn D C E) (hs : IsPaperCan D C E s)
    {r : Nat} {w₀ : D.Event} (hw₀ : w₀ ∈ E) (hsw₀ : SetAt r w₀) :
    ∃ w, LatestSet C E r w := by
  obtain ⟨pi, hp, -, -⟩ := id hs
  have hne : pi.filter (isSetAt r) ≠ [] := by
    intro hemp
    have hm : w₀ ∈ pi.filter (isSetAt r) :=
      List.mem_filter.mpr ⟨(hp.2 w₀).mpr hw₀, isSetAt_iff.mpr hsw₀⟩
    rw [hemp] at hm; exact absurd hm (by simp)
  obtain ⟨w, hw, hmax⟩ := exists_time_max _ hne
  rw [List.mem_filter] at hw
  have hwE : w ∈ E := (hp.2 w).mp hw.1
  have hsw : SetAt r w := isSetAt_iff.mp hw.2
  refine ⟨w, hwE, hsw, ?_⟩
  intro w' hw'E hsw' hne'
  have hw'l : w' ∈ pi.filter (isSetAt r) :=
    List.mem_filter.mpr ⟨(hp.2 w').mpr hw'E, isSetAt_iff.mpr hsw'⟩
  rcases vis_total (hsup w' hw'E) (hsup w hwE) hne'
    (hsw'.1.trans hsw.1.symm) with h | h
  · exact h
  · exact absurd (hmono w w' h) (Nat.not_lt.mpr (hmax w' hw'l))

/-- **A cell is live exactly when its latest write survives.** Any survivor
is the latest write, and the latest write is the only candidate. -/
theorem live_iff_latest_survives {E : Set D.Event}
    {r : Nat} {w : D.Event} (hlat : LatestSet C E r w) :
    Live C E r ↔ Survives C E r w := by
  constructor
  · rintro ⟨w', hw'E, hsw', hsv'⟩
    by_cases heq : w' = w
    · exact heq ▸ hsv'
    · exact absurd (hlat.2.2 w' hw'E hsw' heq) (fun hv => hsv'
        ⟨w, hlat.1, Or.inr hlat.2.1.1, hv⟩)
  · exact fun hsv => ⟨w, hlat.1, hlat.2.1, hsv⟩

/-- A survivor is the latest write. -/
theorem latestSet_of_survives {E : Set D.Event}
    (hvs : VisStrict D C) (hsup : SupportedOn D C E)
    {r : Nat} {w : D.Event} (hwE : w ∈ E) (hsw : SetAt r w)
    (hsv : Survives C E r w) : LatestSet C E r w := by
  refine ⟨hwE, hsw, fun w' hw'E hsw' hne => ?_⟩
  obtain ⟨v, hv⟩ := isSet_iff.mp hsw.2
  exact other_set_vis hvs hsup hwE hsw.1 hv hsv hw'E hsw'.1 hne

/-! ## Towards the join lemma

The row has no membership description of its state, so the conditions run on
its own join lemma, the way the enable-wins flag's do. These are the facts
that lemma needs. -/

theorem finite_of_listPermOf {pi : List D.Event} {E : Set D.Event}
    (h : listPermOf pi E) : E.Finite :=
  Set.Finite.subset (List.finite_toSet pi) (fun x hx => (h.2 x).mpr hx)

theorem survives_union_iff {E₁ E₂ : Set D.Event} {r : Nat} {w : D.Event} :
    Survives C (E₁ ∪ E₂) r w ↔ Survives C E₁ r w ∧ Survives C E₂ r w := by
  constructor
  · exact fun h => ⟨survives_mono Set.subset_union_left h,
      survives_mono Set.subset_union_right h⟩
  · rintro ⟨h₁, h₂⟩ ⟨x, hx, ht, hv⟩
    exact hx.elim (fun hx => h₁ ⟨x, hx, ht, hv⟩) (fun hx => h₂ ⟨x, hx, ht, hv⟩)

/-- **A write outside a weakly closed set survives it.** Anything of the set
that writes the cell and sees the write would drag the write in. -/
theorem survives_of_not_mem {E : Set D.Event} (hvs : VisStrict D C)
    (hsup : SupportedOn D C E) (hcl : WeaklyClosed D C E) {r : Nat} {w : D.Event}
    (hsw : SetAt r w) (hwC : w ∈ C.events) (hw : w ∉ E) : Survives C E r w := by
  rintro ⟨x, hxE, ht, hv⟩
  obtain ⟨v, hv'⟩ := isSet_iff.mp hsw.2
  exact hw (hcl w x hv
    (not_commutes_of_touches hv' hsw.1 ht (fun h => hvs.2 w (h ▸ hv)) hwC
      (hsup x hxE)) hxE)

/-- There is only one latest write. -/
theorem latestSet_unique {E : Set D.Event} (hvs : VisStrict D C) {r : Nat}
    {w w' : D.Event} (h : LatestSet C E r w) (h' : LatestSet C E r w') : w = w' := by
  by_contra hne
  exact hvs.2 w (hvs.1 (h'.2.2 w h.1 h.2.1 hne) (h.2.2 w' h'.1 h'.2.1 (Ne.symm hne)))

/-- The latest write of a union that lies in one side is that side's latest. -/
theorem latestSet_restrict {E F : Set D.Event} (hEF : E ⊆ F) {r : Nat}
    {w : D.Event} (hw : w ∈ E) (h : LatestSet C F r w) : LatestSet C E r w :=
  ⟨hw, h.2.1, fun w' hw' hsw' hne => h.2.2 w' (hEF hw') hsw' hne⟩

/-- **Inclusion and exclusion on the counters.** -/
theorem canonical_count_union {E₁ E₂ : Set D.Event} {l a b s : D.Sigma}
    (hl : IsPaperCan D C (E₁ ∩ E₂) l) (ha : IsPaperCan D C E₁ a)
    (hb : IsPaperCan D C E₂ b) (hs : IsPaperCan D C (E₁ ∪ E₂) s) (r : Nat) :
    (a.cells r).1.1 + (b.cells r).1.1 - (l.cells r).1.1 = (s.cells r).1.1 := by
  classical
  obtain ⟨pl, hpl, -, -⟩ := id hl
  obtain ⟨pa, hpa, -, -⟩ := id ha
  obtain ⟨pb, hpb, -, -⟩ := id hb
  obtain ⟨ps, hps, -, -⟩ := id hs
  rw [canonical_count hl hpl r, canonical_count ha hpa r,
    canonical_count hb hpb r, canonical_count hs hps r]
  have key : ∀ {pi : List D.Event} {E : Set D.Event}, listPermOf pi E →
      ∀ x, x ∈ (pi.filter (isSetAt r)).toFinset ↔ x ∈ E ∧ SetAt r x := by
    intro pi E hp x
    simp only [List.mem_toFinset, List.mem_filter, isSetAt_iff]
    exact ⟨fun h => ⟨(hp.2 x).mp h.1, h.2⟩, fun h => ⟨(hp.2 x).mpr h.1, h.2⟩⟩
  have hcard : ∀ {pi : List D.Event} {E : Set D.Event}, listPermOf pi E →
      (pi.filter (isSetAt r)).toFinset.card = setCount r pi := by
    intro pi E hp
    rw [setCount_eq_length, List.toFinset_card_of_nodup (hp.1.filter _)]
  have hu : (pa.filter (isSetAt r)).toFinset ∪ (pb.filter (isSetAt r)).toFinset
      = (ps.filter (isSetAt r)).toFinset := by
    ext x
    rw [Finset.mem_union, key hpa, key hpb, key hps]
    exact ⟨fun h => h.elim (fun h => ⟨Or.inl h.1, h.2⟩) (fun h => ⟨Or.inr h.1, h.2⟩),
      fun h => h.1.elim (fun h' => Or.inl ⟨h', h.2⟩) (fun h' => Or.inr ⟨h', h.2⟩)⟩
  have hi : (pa.filter (isSetAt r)).toFinset ∩ (pb.filter (isSetAt r)).toFinset
      = (pl.filter (isSetAt r)).toFinset := by
    ext x
    rw [Finset.mem_inter, key hpa, key hpb, key hpl]
    exact ⟨fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, h.2⟩⟩⟩
  have := Finset.card_union_add_card_inter
    (pa.filter (isSetAt r)).toFinset (pb.filter (isSetAt r)).toFinset
  rw [hu, hi, hcard hps, hcard hpl, hcard hpa, hcard hpb] at this
  omega

/-- **The latest write of a union survives it** as soon as each side's own
latest write survives that side. Inside a side the two latest writes agree,
and outside it the write survives for free. -/
theorem survives_union_of_latest {E₁ E₂ : Set D.Event} (hvs : VisStrict D C)
    (hs₁ : SupportedOn D C E₁) (hs₂ : SupportedOn D C E₂)
    (hc₁ : WeaklyClosed D C E₁) (hc₂ : WeaklyClosed D C E₂)
    (hsupU : SupportedOn D C (E₁ ∪ E₂))
    {r : Nat} {w : D.Event} (hlat : LatestSet C (E₁ ∪ E₂) r w)
    (h₁ : ∀ x, LatestSet C E₁ r x → Survives C E₁ r x)
    (h₂ : ∀ x, LatestSet C E₂ r x → Survives C E₂ r x) :
    Survives C (E₁ ∪ E₂) r w := by
  refine survives_union_iff.mpr ⟨?_, ?_⟩
  · by_cases hw : w ∈ E₁
    · exact h₁ w (latestSet_restrict Set.subset_union_left hw hlat)
    · exact survives_of_not_mem hvs hs₁ hc₁ hlat.2.1 (hsupU w hlat.1) hw
  · by_cases hw : w ∈ E₂
    · exact h₂ w (latestSet_restrict Set.subset_union_right hw hlat)
    · exact survives_of_not_mem hvs hs₂ hc₂ hlat.2.1 (hsupU w hlat.1) hw

/-- **When one side is dead, the union is live exactly when the other side's
latest write is not on the dead side.** This is the branch of `mergeFlag`
that compares counters, read as a statement about events. -/
theorem live_union_iff_not_mem {E₁ E₂ : Set D.Event} (hvs : VisStrict D C)
    (hs₁ : SupportedOn D C E₁) (hs₂ : SupportedOn D C E₂)
    (hc₂ : WeaklyClosed D C E₂) (hsupU : SupportedOn D C (E₁ ∪ E₂))
    {r : Nat} {wa : D.Event} (hlata : LatestSet C E₁ r wa)
    (hsva : Survives C E₁ r wa) (hLb : ¬ Live C E₂ r) :
    Live C (E₁ ∪ E₂) r ↔ wa ∉ E₂ := by
  constructor
  · rintro ⟨w, hwU, hsw, hsvU⟩
    obtain ⟨hsv₁, hsv₂⟩ := survives_union_iff.mp hsvU
    rcases hwU with hw | hw
    · have : w = wa := latestSet_unique hvs
        (latestSet_of_survives hvs hs₁ hw hsw hsv₁) hlata
      subst this
      exact fun hmem => hLb ⟨w, hmem, hsw, hsv₂⟩
    · exact absurd ⟨w, hw, hsw, hsv₂⟩ hLb
  · intro hwa
    refine ⟨wa, Or.inl hlata.1, hlata.2.1, survives_union_iff.mpr ⟨hsva, ?_⟩⟩
    exact survives_of_not_mem hvs hs₂ hc₂ hlata.2.1 (hs₁ wa hlata.1) hwa

/-- **And the counter comparison says the same thing.** If the latest write
of one side is on the other, so is every earlier write of that cell, and the
two counters agree; if it is not, the counter is strictly larger. -/
theorem count_lt_iff_not_mem {E₁ E₂ : Set D.Event} {l a : D.Sigma}
    (hvs : VisStrict D C) (hs₁ : SupportedOn D C E₁) (hc₂ : WeaklyClosed D C E₂)
    (hl : IsPaperCan D C (E₁ ∩ E₂) l) (ha : IsPaperCan D C E₁ a)
    {r : Nat} {wa : D.Event} (hlata : LatestSet C E₁ r wa) :
    (l.cells r).1.1 < (a.cells r).1.1 ↔ wa ∉ E₂ := by
  constructor
  · intro hlt hmem
    refine absurd (canonical_count_eq hl ha (fun x hx _ => hx.1) ?_) (ne_of_lt hlt)
    intro w' hw' hsw'
    refine ⟨hw', ?_⟩
    by_cases heq : w' = wa
    · exact heq ▸ hmem
    · obtain ⟨v, hv⟩ := isSet_iff.mp hlata.2.1.2
      exact hc₂ w' wa (hlata.2.2 w' hw' hsw' heq)
        (fun hcm => not_commutes_of_touches hv hlata.2.1.1 (Or.inr hsw'.1)
          (fun h => heq (h ▸ rfl)) (hs₁ wa hlata.1) (hs₁ w' hw')
          (fun s => (hcm s).symm)) hmem
  · intro hwa
    exact canonical_count_lt hl ha (fun x hx _ => hx.1) hlata.1 hlata.2.1
      (fun hmem => hwa hmem.2)

theorem mergePayload_self (X p : Payload) : mergePayload X p p = p := by
  obtain ⟨t, v⟩ := p
  simp only [mergePayload, if_true, if_pos]
  exact Prod.ext rfl (by show (v + v) / 2 = v; omega)

/-! ## The join lemma

Merging `can(E1 n E2)`, `can(E1)` and `can(E2)` gives `can(E1 u E2)`, at
every `Monotone` context. `Negative.lean` shows this fails without the
guard: the merge resolves a payload by timestamp and canonicity resolves it
by causal order, and only `causal_mono` ties the two together.

The counter is inclusion and exclusion. The flag is the enable-wins
comparison, which this proof reads as a statement about the latest write of
the cell. The payload follows the flag. -/

/-! ## The join lemma

Merging `can(E1 n E2)`, `can(E1)` and `can(E2)` gives `can(E1 u E2)`, at
every `Monotone` context. `Negative.lean` shows this fails without the
guard: the merge resolves a payload by timestamp and canonicity resolves it
by causal order, and only `causal_mono` ties the two together.

The counter is inclusion and exclusion. The flag is the enable-wins
comparison, which this proof reads as a statement about the latest write of
the cell. The payload follows the flag. -/

theorem joinCanonical (C : Ctx D) (E₁ E₂ : Set D.Event) (l a b : D.Sigma)
    (hmono : Monotone C) (hvs : VisStrict D C)
    (hs₁ : SupportedOn D C E₁) (hs₂ : SupportedOn D C E₂)
    (hc₁ : WeaklyClosed D C E₁) (hc₂ : WeaklyClosed D C E₂)
    (hl : IsPaperCan D C (E₁ ∩ E₂) l) (ha : IsPaperCan D C E₁ a)
    (hb : IsPaperCan D C E₂ b) :
    IsPaperCan D C (E₁ ∪ E₂) (D.merge l a b) := by
  have hsupU : SupportedOn D C (E₁ ∪ E₂) := fun x hx => hx.elim (hs₁ x) (hs₂ x)
  obtain ⟨pa, hpa, -, -⟩ := id ha
  obtain ⟨pb, hpb, -, -⟩ := id hb
  obtain ⟨sU, hsU⟩ := ConcreteMRDT.canonical_exists
    (guardedLaws laws equal_op_commutes same_rep_cond_comm) C (E₁ ∪ E₂)
    ((finite_of_listPermOf hpa).union (finite_of_listPermOf hpb)) hsupU
    (fun {_ _ _} h h' => hvs.1 h h') hvs.2
  have heq : D.merge l a b = sU := by
    refine State.ext ?_ ?_
    · ext r
      show r ∈ l.domain ∪ (a.domain ∪ b.domain) ↔ r ∈ sU.domain
      rw [Finset.mem_union, Finset.mem_union, canonical_domain hl,
        canonical_domain ha, canonical_domain hb, canonical_domain hsU]
      constructor
      · rintro (⟨w, hw, hsw⟩ | ⟨w, hw, hsw⟩ | ⟨w, hw, hsw⟩)
        · exact ⟨w, Or.inl hw.1, hsw⟩
        · exact ⟨w, Or.inl hw, hsw⟩
        · exact ⟨w, Or.inr hw, hsw⟩
      · rintro ⟨w, hw | hw, hsw⟩
        · exact Or.inr (Or.inl ⟨w, hw, hsw⟩)
        · exact Or.inr (Or.inr ⟨w, hw, hsw⟩)
    · intro r
      show mergeCell (l.cells r) (a.cells r) (b.cells r) = sU.cells r
      have hcnt := canonical_count_union hl ha hb hsU r
      have hdead : ¬ Live C (E₁ ∪ E₂) r → (sU.cells r).1.2 = false ∧
          (sU.cells r).2 = (0, 0) := fun h => canonical_cell_dead hvs hsupU hsU h
      by_cases hLa : Live C E₁ r <;> by_cases hLb : Live C E₂ r
      · -- both sides live
        have fa : (a.cells r).1.2 = true := (canonical_flag hvs hs₁ ha r).mpr hLa
        have fb : (b.cells r).1.2 = true := (canonical_flag hvs hs₂ hb r).mpr hLb
        obtain ⟨wa, hwaE, hswa, hsva⟩ := id hLa
        obtain ⟨wb, hwbE, hswb, hsvb⟩ := id hLb
        have hlata := latestSet_of_survives hvs hs₁ hwaE hswa hsva
        have hlatb := latestSet_of_survives hvs hs₂ hwbE hswb hsvb
        obtain ⟨w, hlatw⟩ := exists_latestSet hmono hsupU hsU (Or.inl hwaE) hswa
        have hsvw := survives_union_of_latest hvs hs₁ hs₂ hc₁ hc₂ hsupU hlatw
          (fun x hx => (live_iff_latest_survives hx).mp hLa)
          (fun x hx => (live_iff_latest_survives hx).mp hLb)
        have fs : (sU.cells r).1.2 = true :=
          (canonical_flag hvs hsupU hsU r).mpr ⟨w, hlatw.1, hlatw.2.1, hsvw⟩
        obtain ⟨va, hva⟩ := isSet_iff.mp hswa.2
        obtain ⟨vb, hvb⟩ := isSet_iff.mp hswb.2
        obtain ⟨vw, hvw⟩ := isSet_iff.mp hlatw.2.1.2
        have pa := (canonical_cell_live hvs hs₁ ha hwaE hswa.1 hva hsva).2
        have pb := (canonical_cell_live hvs hs₂ hb hwbE hswb.1 hvb hsvb).2
        have ps := (canonical_cell_live hvs hsupU hsU hlatw.1 hlatw.2.1.1 hvw hsvw).2
        have htime : ∀ x ∈ E₁ ∪ E₂, SetAt r x → x.time ≤ w.time := by
          intro x hx hsx
          by_cases hxw : x = w
          · exact le_of_eq (by rw [hxw])
          · exact le_of_lt (hmono x w (hlatw.2.2 x hx hsx hxw))
        have hwcase : w = wa ∨ w = wb := by
          rcases hlatw.1 with hw | hw
          · exact Or.inl (latestSet_unique hvs
              (latestSet_restrict Set.subset_union_left hw hlatw) hlata)
          · exact Or.inr (latestSet_unique hvs
              (latestSet_restrict Set.subset_union_right hw hlatw) hlatb)
        have hflag : mergeFlag (l.cells r).1 (a.cells r).1 (b.cells r).1 = true := by
          simp [mergeFlag, fa, fb]
        refine Prod.ext (Prod.ext hcnt (hflag.trans fs.symm)) ?_
        show (mergeCell (l.cells r) (a.cells r) (b.cells r)).2 = (sU.cells r).2
        simp only [reduceIte, mergeCell, hflag, fa, fb, Bool.not_true, if_false, ps, pa, pb]
        by_cases hab : wa.time = wb.time
        · have hwab : wa = wb := C.ts_unique (hs₁ wa hwaE) (hs₂ wb hwbE) hab
          have hvab : va = vb := by
            have hq : (Action.set va) = Action.set vb := by rw [← hva, ← hvb, hwab]
            injection hq
          have hww : w = wa := hwcase.elim id (fun h => h.trans hwab.symm)
          have hvwa : vw = va := by
            have hq : (Action.set vw) = Action.set va := by rw [← hvw, ← hva, hww]
            injection hq
          rw [← hwab, ← hvab, mergePayload_self, hww, hvwa]
          simp
        · rcases lt_or_gt_of_ne hab with hlt | hgt
          · have hww : w = wb := by
              rcases hwcase with h | h
              · exact absurd (htime wb (Or.inr hwbE) hswb)
                  (by rw [h]; exact Nat.not_le.mpr hlt)
              · exact h
            have hvwb : vw = vb := by
              have hq : (Action.set vw) = Action.set vb := by rw [← hvw, ← hvb, hww]
              injection hq
            rw [hww, hvwb]
            simp [mergePayload, hab, Nat.not_lt.mpr (le_of_lt hlt)]
          · have hww : w = wa := by
              rcases hwcase with h | h
              · exact h
              · exact absurd (htime wa (Or.inl hwaE) hswa)
                  (by rw [h]; exact Nat.not_le.mpr hgt)
            have hvwa : vw = va := by
              have hq : (Action.set vw) = Action.set va := by rw [← hvw, ← hva, hww]
              injection hq
            rw [hww, hvwa]
            simp [mergePayload, hab, hgt]
      · -- only `E₁` live
        have fa : (a.cells r).1.2 = true := (canonical_flag hvs hs₁ ha r).mpr hLa
        have fb : (b.cells r).1.2 = false := by
          by_contra h
          exact hLb ((canonical_flag hvs hs₂ hb r).mp (by simpa using h))
        obtain ⟨wa, hwaE, hswa, hsva⟩ := id hLa
        have hlata := latestSet_of_survives hvs hs₁ hwaE hswa hsva
        have hiff := live_union_iff_not_mem hvs hs₁ hs₂ hc₂ hsupU hlata hsva hLb
        have hcntiff := count_lt_iff_not_mem hvs hs₁ hc₂ hl ha hlata
        have hflag : mergeFlag (l.cells r).1 (a.cells r).1 (b.cells r).1
            = decide ((l.cells r).1.1 < (a.cells r).1.1) := by
          simp [mergeFlag, fa, fb]
        by_cases hLs : Live C (E₁ ∪ E₂) r
        · have hlt : (l.cells r).1.1 < (a.cells r).1.1 := hcntiff.mpr (hiff.mp hLs)
          have fs : (sU.cells r).1.2 = true := (canonical_flag hvs hsupU hsU r).mpr hLs
          obtain ⟨va, hva⟩ := isSet_iff.mp hswa.2
          have hsvw : Survives C (E₁ ∪ E₂) r wa :=
            survives_union_iff.mpr ⟨hsva, survives_of_not_mem hvs hs₂ hc₂ hswa
              (hs₁ wa hwaE) (hiff.mp hLs)⟩
          have ps := (canonical_cell_live hvs hsupU hsU (Or.inl hwaE) hswa.1 hva hsvw).2
          have pa := (canonical_cell_live hvs hs₁ ha hwaE hswa.1 hva hsva).2
          refine Prod.ext (Prod.ext hcnt
            (hflag.trans ((decide_eq_true hlt).trans fs.symm))) ?_
          · show (mergeCell (l.cells r) (a.cells r) (b.cells r)).2 = (sU.cells r).2
            simp only [reduceIte, mergeCell, hflag, decide_eq_true hlt, fa, fb, Bool.not_true,
              Bool.not_false, if_false, if_true, ps, pa]
            simp
        · have hnlt : ¬ (l.cells r).1.1 < (a.cells r).1.1 :=
            fun h => hLs (hiff.mpr (hcntiff.mp h))
          obtain ⟨fs, ps⟩ := hdead hLs
          refine Prod.ext (Prod.ext hcnt
            (hflag.trans ((decide_eq_false hnlt).trans fs.symm))) ?_
          · show (mergeCell (l.cells r) (a.cells r) (b.cells r)).2 = (sU.cells r).2
            simp only [reduceIte, mergeCell, hflag, decide_eq_false hnlt, Bool.not_false,
              if_true, ps]
      · -- only `E₂` live
        have fb : (b.cells r).1.2 = true := (canonical_flag hvs hs₂ hb r).mpr hLb
        have fa : (a.cells r).1.2 = false := by
          by_contra h
          exact hLa ((canonical_flag hvs hs₁ ha r).mp (by simpa using h))
        obtain ⟨wb, hwbE, hswb, hsvb⟩ := id hLb
        have hlatb := latestSet_of_survives hvs hs₂ hwbE hswb hsvb
        have hsupU' : SupportedOn D C (E₂ ∪ E₁) := fun x hx => hx.elim (hs₂ x) (hs₁ x)
        have hiff' := live_union_iff_not_mem hvs hs₂ hs₁ hc₁ hsupU' hlatb hsvb hLa
        have hiff : Live C (E₁ ∪ E₂) r ↔ wb ∉ E₁ := by
          rw [Set.union_comm]; exact hiff'
        have hl' : IsPaperCan D C (E₂ ∩ E₁) l := by rw [Set.inter_comm]; exact hl
        have hcntiff := count_lt_iff_not_mem hvs hs₂ hc₁ hl' hb hlatb
        have hflag : mergeFlag (l.cells r).1 (a.cells r).1 (b.cells r).1
            = decide ((l.cells r).1.1 < (b.cells r).1.1) := by
          simp [mergeFlag, fa, fb]
        by_cases hLs : Live C (E₁ ∪ E₂) r
        · have hlt : (l.cells r).1.1 < (b.cells r).1.1 := hcntiff.mpr (hiff.mp hLs)
          have fs : (sU.cells r).1.2 = true := (canonical_flag hvs hsupU hsU r).mpr hLs
          obtain ⟨vb, hvb⟩ := isSet_iff.mp hswb.2
          have hsvw : Survives C (E₁ ∪ E₂) r wb :=
            survives_union_iff.mpr ⟨survives_of_not_mem hvs hs₁ hc₁ hswb
              (hs₂ wb hwbE) (hiff.mp hLs), hsvb⟩
          have ps := (canonical_cell_live hvs hsupU hsU (Or.inr hwbE) hswb.1 hvb hsvw).2
          have pb := (canonical_cell_live hvs hs₂ hb hwbE hswb.1 hvb hsvb).2
          refine Prod.ext (Prod.ext hcnt
            (hflag.trans ((decide_eq_true hlt).trans fs.symm))) ?_
          · show (mergeCell (l.cells r) (a.cells r) (b.cells r)).2 = (sU.cells r).2
            simp only [reduceIte, mergeCell, hflag, decide_eq_true hlt, fa, fb, Bool.not_true,
              Bool.not_false, if_false, if_true, ps, pb]
            simp
        · have hnlt : ¬ (l.cells r).1.1 < (b.cells r).1.1 :=
            fun h => hLs (hiff.mpr (hcntiff.mp h))
          obtain ⟨fs, ps⟩ := hdead hLs
          refine Prod.ext (Prod.ext hcnt
            (hflag.trans ((decide_eq_false hnlt).trans fs.symm))) ?_
          · show (mergeCell (l.cells r) (a.cells r) (b.cells r)).2 = (sU.cells r).2
            simp only [reduceIte, mergeCell, hflag, decide_eq_false hnlt, Bool.not_false,
              if_true, ps]
      · -- neither side live
        have fa : (a.cells r).1.2 = false := by
          by_contra h
          exact hLa ((canonical_flag hvs hs₁ ha r).mp (by simpa using h))
        have fb : (b.cells r).1.2 = false := by
          by_contra h
          exact hLb ((canonical_flag hvs hs₂ hb r).mp (by simpa using h))
        have hLs : ¬ Live C (E₁ ∪ E₂) r := by
          rintro ⟨w, hwU, hsw, hsvU⟩
          obtain ⟨hsv₁, hsv₂⟩ := survives_union_iff.mp hsvU
          exact hwU.elim (fun h => hLa ⟨w, h, hsw, hsv₁⟩)
            (fun h => hLb ⟨w, h, hsw, hsv₂⟩)
        obtain ⟨fs, ps⟩ := hdead hLs
        have hflag : mergeFlag (l.cells r).1 (a.cells r).1 (b.cells r).1 = false := by
          simp [mergeFlag, fa, fb]
        refine Prod.ext (Prod.ext hcnt (hflag.trans fs.symm)) ?_
        show (mergeCell (l.cells r) (a.cells r) (b.cells r)).2 = (sU.cells r).2
        simp only [reduceIte, mergeCell, hflag, Bool.not_false, if_true, ps]
  rw [heq]; exact hsU

/-! ## VC3 and VC5, from the join lemma

Each side of each equation is a canonical state of `E1 u E2`, reached by a
different bracketing of the same three joins, and canonical states are
unique. This is the shape the enable-wins flag's conditions take, and for
the same reason: the row has no membership description of its state, so the
conditions run on its own join lemma. -/

/-- `e(can(down(e) \ {e})) = can(down(e))`. -/
theorem isCan_downset {C : Ctx D} {m : D.Sigma} {e : D.Event}
    (hvs : VisStrict D C) (hm : IsPaperCan D C (downset C e \ {e}) m) :
    IsPaperCan D C (downset C e) (D.do_ m e) :=
  isPaperCan_snoc self_mem_downset (paperMaximalOn_downset hvs e) hm

theorem peelI {C : Ctx D} {e : D.Event} (F : Set D.Event) (hsub : downset C e ⊆ F) :
    (F \ {e}) ∩ downset C e = downset C e \ {e} := by
  ext z; exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hsub h.1, h.2⟩, h.1⟩⟩

theorem peelU {C : Ctx D} {e : D.Event} (F : Set D.Event) (hsub : downset C e ⊆ F) :
    (F \ {e}) ∪ downset C e = F := by
  ext z; constructor
  · rintro (⟨hz, -⟩ | hz)
    · exact hz
    · exact hsub hz
  · intro hz
    by_cases hze : z = e
    · exact Or.inr (Or.inl hze)
    · exact Or.inl ⟨hz, hze⟩

/-- **VC3** LOCAL-REDISTRIBUTE. -/
theorem vc3_local_redistribute (C : Ctx D) (E₁ E₂ : Set D.Event)
    (l m x y : D.Sigma) (e : D.Event)
    (hmono : Monotone C) (hvs : VisStrict D C)
    (h₁ : SupportedOn D C E₁) (h₂ : SupportedOn D C E₂)
    (hc₁ : WeaklyClosed D C E₁) (hc₂ : WeaklyClosed D C E₂)
    (he₁ : e ∈ E₁) (he₂ : e ∉ E₂) (hmax : PaperMaximalOn D C (E₁ ∪ E₂) e)
    (hl : IsPaperCan D C (E₁ ∩ E₂) l)
    (hm : IsPaperCan D C (downset C e \ {e}) m)
    (hx : IsPaperCan D C (E₁ \ {e}) x)
    (hy : IsPaperCan D C E₂ y) :
    D.merge l (D.merge m x (D.do_ m e)) y
      = D.merge m (D.merge l x y) (D.do_ m e) := by
  have hdsub : downset C e ⊆ E₁ := downset_subset hc₁ he₁
  have hdm := isCan_downset hvs hm
  have hsupU : SupportedOn D C (E₁ ∪ E₂) := fun a ha => ha.elim (h₁ a) (h₂ a)
  have hdsupp : SupportedOn D C (downset C e) := fun a ha => h₁ a (hdsub ha)
  have hcld : WeaklyClosed D C (downset C e) :=
    fun a b => downset_closed (C := C) (e := e) a b
  have hclU : WeaklyClosed D C (E₁ ∪ E₂) := weaklyClosed_union hc₁ hc₂
  have hclx : WeaklyClosed D C (E₁ \ {e}) :=
    weaklyClosed_diff_of_max hc₁ Set.subset_union_left hmax
  have hclU' : WeaklyClosed D C ((E₁ ∪ E₂) \ {e}) :=
    weaklyClosed_diff_of_max hclU Set.Subset.rfl hmax
  have hdsubU : downset C e ⊆ E₁ ∪ E₂ := fun z hz => Or.inl (hdsub hz)
  have i₂ : (E₁ \ {e}) ∩ E₂ = E₁ ∩ E₂ := by
    ext z
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, fun hq => he₂ (hq ▸ h.2)⟩, h.2⟩⟩
  have u₂ : (E₁ \ {e}) ∪ E₂ = (E₁ ∪ E₂) \ {e} := by
    ext z; constructor
    · rintro (⟨hz, hn⟩ | hz)
      · exact ⟨Or.inl hz, hn⟩
      · exact ⟨Or.inr hz, fun hq => he₂ (hq ▸ hz)⟩
    · rintro ⟨hz | hz, hn⟩
      · exact Or.inl ⟨hz, hn⟩
      · exact Or.inr hz
  have hinner : IsPaperCan D C E₁ (D.merge m x (D.do_ m e)) := by
    have hj := joinCanonical C (E₁ \ {e}) (downset C e) m x (D.do_ m e) hmono hvs
      (fun a ha => h₁ a ha.1) hdsupp hclx hcld
      (by rw [peelI _ hdsub]; exact hm) hx hdm
    rwa [peelU _ hdsub] at hj
  have hL : IsPaperCan D C (E₁ ∪ E₂) (D.merge l (D.merge m x (D.do_ m e)) y) :=
    joinCanonical C E₁ E₂ l _ y hmono hvs h₁ h₂ hc₁ hc₂ hl hinner hy
  have hinner' : IsPaperCan D C ((E₁ ∪ E₂) \ {e}) (D.merge l x y) := by
    have hj := joinCanonical C (E₁ \ {e}) E₂ l x y hmono hvs
      (fun a ha => h₁ a ha.1) h₂ hclx hc₂ (by rw [i₂]; exact hl) hx hy
    rwa [u₂] at hj
  have hR : IsPaperCan D C (E₁ ∪ E₂) (D.merge m (D.merge l x y) (D.do_ m e)) := by
    have hj := joinCanonical C ((E₁ ∪ E₂) \ {e}) (downset C e) m (D.merge l x y)
      (D.do_ m e) hmono hvs (fun a ha => hsupU a ha.1) hdsupp hclU' hcld
      (by rw [peelI _ hdsubU]; exact hm) hinner' hdm
    rwa [peelU _ hdsubU] at hj
  exact ConcreteMRDT.canonical_unique
    (guardedLaws laws equal_op_commutes same_rep_cond_comm) C (E₁ ∪ E₂) hsupU hL hR

/-- **VC5** REDISTRIBUTE. -/
theorem vc5_redistribute (C : Ctx D) (E₁ E₂ : Set D.Event)
    (x₀ x₁ x₂ m : D.Sigma) (e : D.Event)
    (hmono : Monotone C) (hvs : VisStrict D C)
    (h₁ : SupportedOn D C E₁) (h₂ : SupportedOn D C E₂)
    (hc₁ : WeaklyClosed D C E₁) (hc₂ : WeaklyClosed D C E₂)
    (he₁ : e ∈ E₁) (he₂ : e ∈ E₂) (hmax : PaperMaximalOn D C (E₁ ∪ E₂) e)
    (hx₀ : IsPaperCan D C ((E₁ ∩ E₂) \ {e}) x₀)
    (hm : IsPaperCan D C (downset C e \ {e}) m)
    (hx₁ : IsPaperCan D C (E₁ \ {e}) x₁)
    (hx₂ : IsPaperCan D C (E₂ \ {e}) x₂) :
    D.merge (D.merge m x₀ (D.do_ m e)) (D.merge m x₁ (D.do_ m e))
        (D.merge m x₂ (D.do_ m e))
      = D.merge m (D.merge x₀ x₁ x₂) (D.do_ m e) := by
  have hdsub₁ : downset C e ⊆ E₁ := downset_subset hc₁ he₁
  have hdsub₂ : downset C e ⊆ E₂ := downset_subset hc₂ he₂
  have hdm := isCan_downset hvs hm
  have hsupU : SupportedOn D C (E₁ ∪ E₂) := fun a ha => ha.elim (h₁ a) (h₂ a)
  have hdsupp : SupportedOn D C (downset C e) := fun a ha => h₁ a (hdsub₁ ha)
  have hcld : WeaklyClosed D C (downset C e) :=
    fun a b => downset_closed (C := C) (e := e) a b
  have hclU : WeaklyClosed D C (E₁ ∪ E₂) := weaklyClosed_union hc₁ hc₂
  have hclI : WeaklyClosed D C (E₁ ∩ E₂) := by
    rintro a b hv hnc ⟨hb₁, hb₂⟩; exact ⟨hc₁ a b hv hnc hb₁, hc₂ a b hv hnc hb₂⟩
  have hcl₀ : WeaklyClosed D C ((E₁ ∩ E₂) \ {e}) :=
    weaklyClosed_diff_of_max hclI (fun z hz => Or.inl hz.1) hmax
  have hcl₁ : WeaklyClosed D C (E₁ \ {e}) :=
    weaklyClosed_diff_of_max hc₁ Set.subset_union_left hmax
  have hcl₂ : WeaklyClosed D C (E₂ \ {e}) :=
    weaklyClosed_diff_of_max hc₂ Set.subset_union_right hmax
  have hclU' : WeaklyClosed D C ((E₁ ∪ E₂) \ {e}) :=
    weaklyClosed_diff_of_max hclU Set.Subset.rfl hmax
  have hdsubI : downset C e ⊆ E₁ ∩ E₂ := fun z hz => ⟨hdsub₁ hz, hdsub₂ hz⟩
  have hdsubU : downset C e ⊆ E₁ ∪ E₂ := fun z hz => Or.inl (hdsub₁ hz)
  have hsup₀ : SupportedOn D C ((E₁ ∩ E₂) \ {e}) := fun a ha => h₁ a ha.1.1
  have hsup₁ : SupportedOn D C (E₁ \ {e}) := fun a ha => h₁ a ha.1
  have hsup₂ : SupportedOn D C (E₂ \ {e}) := fun a ha => h₂ a ha.1
  have iM : (E₁ \ {e}) ∩ (E₂ \ {e}) = (E₁ ∩ E₂) \ {e} := by
    ext z
    exact ⟨fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, h.2⟩⟩⟩
  have uM : (E₁ \ {e}) ∪ (E₂ \ {e}) = (E₁ ∪ E₂) \ {e} := by
    ext z; constructor
    · rintro (⟨hz, hn⟩ | ⟨hz, hn⟩)
      · exact ⟨Or.inl hz, hn⟩
      · exact ⟨Or.inr hz, hn⟩
    · rintro ⟨hz | hz, hn⟩
      · exact Or.inl ⟨hz, hn⟩
      · exact Or.inr ⟨hz, hn⟩
  have c₀ : IsPaperCan D C (E₁ ∩ E₂) (D.merge m x₀ (D.do_ m e)) := by
    have hj := joinCanonical C ((E₁ ∩ E₂) \ {e}) (downset C e) m x₀ (D.do_ m e)
      hmono hvs hsup₀ hdsupp hcl₀ hcld (by rw [peelI _ hdsubI]; exact hm) hx₀ hdm
    rwa [peelU _ hdsubI] at hj
  have c₁ : IsPaperCan D C E₁ (D.merge m x₁ (D.do_ m e)) := by
    have hj := joinCanonical C (E₁ \ {e}) (downset C e) m x₁ (D.do_ m e)
      hmono hvs hsup₁ hdsupp hcl₁ hcld (by rw [peelI _ hdsub₁]; exact hm) hx₁ hdm
    rwa [peelU _ hdsub₁] at hj
  have c₂ : IsPaperCan D C E₂ (D.merge m x₂ (D.do_ m e)) := by
    have hj := joinCanonical C (E₂ \ {e}) (downset C e) m x₂ (D.do_ m e)
      hmono hvs hsup₂ hdsupp hcl₂ hcld (by rw [peelI _ hdsub₂]; exact hm) hx₂ hdm
    rwa [peelU _ hdsub₂] at hj
  have hL : IsPaperCan D C (E₁ ∪ E₂)
      (D.merge (D.merge m x₀ (D.do_ m e)) (D.merge m x₁ (D.do_ m e))
        (D.merge m x₂ (D.do_ m e))) :=
    joinCanonical C E₁ E₂ _ _ _ hmono hvs h₁ h₂ hc₁ hc₂ c₀ c₁ c₂
  have hmid : IsPaperCan D C ((E₁ ∪ E₂) \ {e}) (D.merge x₀ x₁ x₂) := by
    have hj := joinCanonical C (E₁ \ {e}) (E₂ \ {e}) x₀ x₁ x₂ hmono hvs
      hsup₁ hsup₂ hcl₁ hcl₂ (by rw [iM]; exact hx₀) hx₁ hx₂
    rwa [uM] at hj
  have hR : IsPaperCan D C (E₁ ∪ E₂) (D.merge m (D.merge x₀ x₁ x₂) (D.do_ m e)) := by
    have hj := joinCanonical C ((E₁ ∪ E₂) \ {e}) (downset C e) m (D.merge x₀ x₁ x₂)
      (D.do_ m e) hmono hvs (fun a ha => hsupU a ha.1) hdsupp hclU' hcld
      (by rw [peelI _ hdsubU]; exact hm) hmid hdm
    rwa [peelU _ hdsubU] at hj
  exact ConcreteMRDT.canonical_unique
    (guardedLaws laws equal_op_commutes same_rep_cond_comm) C (E₁ ∪ E₂) hsupU hL hR

/-- **VC1 to VC5**, at the contexts in which `vis` increases the timestamp. -/
theorem joinLaws : PaperJoinLawsOn D Monotone where
  vc1_merge_comm := vc1_merge_comm
  vc2_merge_init := fun C E s _ hsup hs => vc2_merge_init C E s hsup hs
  vc3_local_redistribute := vc3_local_redistribute
  vc4_causal_delta := vc4_causal_delta
  vc5_redistribute := vc5_redistribute

/-! ## The execution order

`rc` is the implementation's, and the framework's execution induction needs
an order that relates **every** non-commuting pair. This is that order: `rc`
together with the one pair `rc` cannot describe, two `set` events of one
replica, taken in timestamp order. It is a proof device and appears nowhere
in the tuple, in `Laws(D_type)`, or in any of the five conditions. -/

/-- The relation the execution order carries. -/
def ExBefore (a b : D.Event) : Prop :=
  (a.op = Action.unset ∧ ∃ v, b.op = .set v) ∨
    (∃ v₁ v₂, a.op = .set v₁ ∧ b.op = .set v₂ ∧ a.rep = b.rep ∧ a.time < b.time)

open Classical in
/-- The execution order itself. -/
noncomputable def exEventOrder : EventOrder D.toMRDTSig.toUpdateSig where
  order a b :=
    if ExBefore a b then OrderResult.Fst_then_snd
    else if ExBefore b a then OrderResult.Snd_then_fst
    else OrderResult.Either

theorem exBefore_iff (a b : D.Event) :
    (exEventOrder).Before a b ↔ ExBefore a b := by
  simp only [EventOrder.Before, exEventOrder]
  split_ifs with h₁ h₂ <;> simp [h₁]

/-- Whatever the execution order relates does not commute. -/
theorem not_commutes_of_exBefore {a b : D.Event} (h : ExBefore a b) :
    ¬ D.Commutes a b := by
  rcases h with ⟨hu, v, hv⟩ | ⟨v₁, v₂, h₁, h₂, hr, ht⟩
  · exact fun hc => not_commutes_set_unset hv hu (fun s => (hc s).symm)
  · exact not_commutes_set_set_same h₁ h₂ hr (Nat.ne_of_lt ht)

/-- **The execution order is exact on observed events.** Every pair that
fails to commute is related, in one direction or the other, and nothing
else is. Two events of one replica carrying the same timestamp are the same
event, which is where the context is used. -/
theorem commutes_iff (C : Ctx D) (a b : D.Event)
    (ha : a ∈ C.events) (hb : b ∈ C.events) :
    ¬ D.Commutes a b ↔ ExBefore a b ∨ ExBefore b a := by
  constructor
  · intro hnc
    rcases hoa : a.op with va | _
    · rcases hob : b.op with vb | _
      · by_cases hr : a.rep = b.rep
        · have hne : a ≠ b := by
            rintro rfl; exact hnc (fun s => rfl)
          have hts : a.time ≠ b.time := fun h => hne (C.ts_unique ha hb h)
          rcases Nat.lt_or_ge a.time b.time with hlt | hge
          · exact Or.inl (Or.inr ⟨va, vb, hoa, hob, hr, hlt⟩)
          · exact Or.inr (Or.inr ⟨vb, va, hob, hoa, hr.symm,
              lt_of_le_of_ne hge (fun h => hts h.symm)⟩)
        · exact absurd (commutes_set_set hoa hob hr) hnc
      · exact Or.inr (Or.inl ⟨hob, va, hoa⟩)
    · rcases hob : b.op with vb | _
      · exact Or.inl (Or.inl ⟨hoa, vb, hob⟩)
      · exact absurd (commutes_unset_unset hoa hob) hnc
  · rintro (h | h)
    · exact not_commutes_of_exBefore h
    · exact fun hc => not_commutes_of_exBefore h (fun s => (hc s).symm)

/-- On concurrent pairs the execution order agrees with `rc`: two `set`
events of one replica are never concurrent. -/
theorem exBefore_iff_rc (C : Ctx D) (a b : D.Event)
    (ha : a ∈ C.events) (hb : b ∈ C.events)
    (hab : ¬ C.vis a b) (hba : ¬ C.vis b a) :
    ExBefore a b ↔ D.EventRcBefore a b := by
  rw [eventRcBefore_iff]
  constructor
  · rintro (h | ⟨v₁, v₂, h₁, h₂, hr, ht⟩)
    · exact h
    · have hne : a ≠ b := fun h => absurd ht (by rw [h]; exact lt_irrefl _)
      exact absurd (vis_total ha hb hne hr) (by rintro (h | h); exacts [hab h, hba h])
  · exact fun h => Or.inl h

/-- The execution order of this row. -/
noncomputable def exOrder : ExecutionOrder D where
  order := exEventOrder
  exact := fun C a b ha hb => by
    rw [exBefore_iff, exBefore_iff]
    exact commutes_iff C a b ha hb
  concurrent := fun C a b ha hb hab hba => by
    rw [exBefore_iff]
    exact exBefore_iff_rc C a b ha hb hab hba

/-- **The obligation bundle, at the contexts a configuration produces.**
`Monotone` is the one thing the five conditions need beyond the tuple, and
`monotone_of_mintHonest` discharges it. -/
theorem obligations : ObligationsOn D Monotone where
  laws := laws
  equal_op_commutes := equal_op_commutes
  same_rep_cond_comm := same_rep_cond_comm
  joinLaws := joinLaws
  executionOrder := ⟨exOrder⟩

#print axioms obligations
#print axioms joinCanonical

/-! ## SPEC-NON-COMM fails

The fourth law of Section 4, recorded for the same reason the other five
execution-scoped rows record it: the row does not satisfy it, and does not
need to. `certifiedRA_scoped_of_join_strict` never asks for it, because the
witness is the row's own history rather than the one clause 1 built, so
specification visibility is not established and Definition 4 does not ask
for it. -/

/-- `set 1` and `set 2` do not commute in `Spec`: the query at the end of
the history tells the two orders apart. -/
theorem not_spec_commutes :
    ¬ Interface.spec_commutes historySpec (.set 1) (.set 2) := by
  intro h
  have lhs : historySpec.admits
      ([SeqLabel.update (Action.set 1), .update (.set 2)]
        ++ [.query () (some 2)]) :=
    (specMachine.updates_query_iff [.set 1, .set 2] () (some 2)).mpr rfl
  have rhs := (h [] [SeqLabel.query () (some 2)]).mp (by simpa using lhs)
  have key : (some 2 : Option Nat) = some 1 :=
    (specMachine.updates_query_iff [Action.set 2, .set 1] () (some 2)).mp
      (by simpa using rhs)
  simp at key

/-- **SPEC-NON-COMM fails for the optional register.** Two writes by
different replicas land in different cells, so they commute in the
implementation; the register specification cannot see the cells, so they do
not commute in `Spec`. The row reaches Definition 4 through the
execution-scoped route, which does not ask for this law. -/
theorem not_spec_non_comm : ¬ Interface.spec_non_comm D historySpec := fun h =>
  h (1, 0, .set 1) (2, 1, .set 2) not_spec_commutes
    (commutes_set_set rfl rfl (by decide))

/-! ## What the specification says about a history

The specification is a plain register, so the value after a history is the
effect of its **last** update and nothing else. -/

theorem spec_fold_nil :
    ([] : List type.OType).foldl specMachine.update specMachine.initial = none := rfl

theorem spec_fold_append (ops : List type.OType) (o : type.OType) :
    (ops ++ [o]).foldl specMachine.update specMachine.initial
      = match o with | .set v => some v | .unset => none := by
  rw [List.foldl_append]
  cases o <;> rfl

/-! ## What the query says about a state -/

theorem candidates_unset {s : State} {e : D.Event} (h : e.op = .unset) :
    candidates (step s e) = ∅ := by
  simp only [candidates, step, h]
  refine Finset.image_eq_empty.mpr ?_
  refine Finset.filter_eq_empty_iff.mpr (fun r _ => ?_)
  simp

theorem readValue_unset {s : State} {e : D.Event} (h : e.op = .unset) :
    readValue (step s e) = none := by
  simp [readValue, winner, candidates_unset h]

theorem candidates_set {s : State} {e : D.Event} {v : Nat} (h : e.op = .set v) :
    (candidates (step s e)).Nonempty := by
  refine ⟨toLex (((step s e).cells e.rep).2.1,
    toLex (e.rep, ((step s e).cells e.rep).2.2)), ?_⟩
  refine Finset.mem_image.mpr ⟨e.rep, ?_, rfl⟩
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · simp only [step, h]
    exact Finset.mem_insert_self _ _
  · simp [step, h]

/-- The winner names a live cell, and reads its payload. -/
theorem winner_cell {s : State} {c : Write} (h : winner s = some c) :
    ∃ r, (s.cells r).1.2 = true ∧
      c = toLex ((s.cells r).2.1, toLex (r, (s.cells r).2.2)) := by
  unfold winner at h
  split_ifs at h with hne
  · have hmem : (candidates s).max' hne ∈ candidates s := Finset.max'_mem _ _
    have heq : (candidates s).max' hne = c := by injection h
    rw [heq] at hmem
    simp only [candidates, Finset.mem_image, Finset.mem_filter] at hmem
    obtain ⟨r, ⟨-, hflag⟩, hc⟩ := hmem
    exact ⟨r, hflag, hc.symm⟩

/-! ## A surviving write is maximal -/

variable {C : Ctx D}

/-- **A `set` that survives has no `lo^C_E` edge out of it.** A `set` starts
no `rc` edge, so the concurrent disjunct cannot fire; and a causal
non-commuting successor would write its cell, which surviving forbids. -/
theorem paperMaximal_of_survives {E : Set D.Event} {r : Nat} {w : D.Event}
    {v : Nat} (hwr : w.rep = r) (hwv : w.op = .set v)
    (hsv : Survives C E r w) : PaperMaximalOn D C E w := by
  intro x hxE _ hedge
  rcases hedge with ⟨hvis, hnc⟩ | ⟨-, -, hrc, -⟩
  · rcases absorber_of_not_commutes hwv hnc with hun | hrep
    · exact hsv ⟨x, hxE, Or.inl hun, hvis⟩
    · exact hsv ⟨x, hxE, Or.inr (hrep.trans hwr), hvis⟩
  · exact absurd ((eventRcBefore_iff w x).mp hrc).1 (by rw [hwv]; simp)

/-! # Specification visibility, without SPEC-NON-COMM

SPEC-NON-COMM is refuted above, so the usual route to specification
visibility is closed. The route taken here instead is to make the chosen
history respect `vis` as well as `lo^C_E`: every specification-visibility
arrow runs along `vis`, so the clause then follows in one line. Two facts
pay for it, `jointVis_acyclic` and `winner_no_vis_succ`.
-/

variable {E : Set D.Event}

/-! ## The two relations together, and no cycle -/

/-- **Both kinds of arrow at once.** `vis` and `lo^C_E`, inside `E`. A
history respecting this respects specification visibility, because every
specification-visibility arrow runs along `vis`. -/
def jointVis (C : Ctx D) (E : Set D.Event) (a b : D.Event) : Prop :=
  a ∈ E ∧ b ∈ E ∧ (C.vis a b ∨ paperOrder (policy D) C E a b)

/-- The target of a same-time arrow: a `set` of `E` with no non-commuting
visible successor in `E`. -/
def Blocked (C : Ctx D) (E : Set D.Event) (w : D.Event) : Prop :=
  w ∈ E ∧ (∃ v, w.op = Action.set v) ∧
    ¬ ∃ c ∈ E, C.vis w c ∧ ¬ D.Commutes w c

/-- A same-time arrow lands on a `Blocked` event. -/
theorem blocked_of_concurrent {a b : D.Event} (hbE : b ∈ E)
    (h : ¬ C.vis a b ∧ ¬ C.vis b a ∧ D.RcBefore a.op b.op ∧
      ¬ ∃ c ∈ E, C.vis b c ∧ ¬ D.Commutes b c) : Blocked C E b :=
  ⟨hbE, ((eventRcBefore_iff a b).mp h.2.2.1).2, h.2.2.2⟩

/-- **Nothing a `Blocked` event sees is an `unset`**, since an `unset` never
commutes with a `set`. -/
theorem succ_not_unset {w x : D.Event} (hw : Blocked C E w) (hxE : x ∈ E)
    (hvis : C.vis w x) : x.op ≠ Action.unset := by
  intro hx
  obtain ⟨v, hv⟩ := hw.2.1
  exact hw.2.2 ⟨x, hxE, hvis, not_commutes_set_unset hv hx⟩

/-- **A `Blocked` event starts no same-time arrow**, because `rc` only ever
starts one at an `unset`. -/
theorem no_concurrent_from_set {w z : D.Event} {v : Nat} (hwv : w.op = Action.set v)
    (h : ¬ C.vis w z ∧ ¬ C.vis z w ∧ D.RcBefore w.op z.op ∧
      ¬ ∃ c ∈ E, C.vis z c ∧ ¬ D.Commutes z c) : False := by
  have := ((eventRcBefore_iff w z).mp h.2.2.1).1
  rw [hwv] at this
  exact absurd this (by simp)

/-- **From a `Blocked` event every path is causal.** The absorber condition
forces each step to be a `vis` step, and `vis` is transitive, so the whole
path composes into one `vis` edge. -/
theorem vis_of_blocked_path (hvs : VisStrict D C) {w : D.Event}
    (hw : Blocked C E w) : ∀ {y}, Relation.TransGen (jointVis C E) w y → C.vis w y := by
  intro y h
  induction h with
  | single hedge =>
    rcases hedge.2.2 with hv | hp
    · exact hv
    · rcases hp with ⟨hv, -⟩ | hconc
      · exact hv
      · obtain ⟨v, hv⟩ := hw.2.1
        exact (no_concurrent_from_set hv hconc).elim
  | @tail y z _ hedge ih =>
    have hyE : y ∈ E := hedge.1
    have hyset : y.op ≠ Action.unset := succ_not_unset hw hyE ih
    rcases hedge.2.2 with hv | hp
    · exact hvs.1 ih hv
    · rcases hp with ⟨hv, -⟩ | hconc
      · exact hvs.1 ih hv
      · obtain ⟨v, hv⟩ := isSet_iff.mp hyset
        exact (no_concurrent_from_set hv hconc).elim

/-- Every path either composes into a `vis` edge, or has passed through a
`Blocked` event that it can still reach. -/
theorem path_cases (hvs : VisStrict D C) : ∀ {a b : D.Event},
    Relation.TransGen (jointVis C E) a b → C.vis a b ∨
      ∃ w, Blocked C E w ∧ Relation.ReflTransGen (jointVis C E) a w ∧
        (w = b ∨ C.vis w b) := by
  intro a b h
  induction h with
  | @single b hedge =>
    rcases hedge.2.2 with hv | hp
    · exact Or.inl hv
    · rcases hp with ⟨hv, -⟩ | hconc
      · exact Or.inl hv
      · exact Or.inr ⟨b, blocked_of_concurrent hedge.2.1 hconc,
          Relation.ReflTransGen.single hedge, Or.inl rfl⟩
  | @tail y z hpath hedge ih =>
    rcases ih with hv | ⟨w, hw, haw, hwy⟩
    · rcases hedge.2.2 with hv' | hp
      · exact Or.inl (hvs.1 hv hv')
      · rcases hp with ⟨hv', -⟩ | hconc
        · exact Or.inl (hvs.1 hv hv')
        · exact Or.inr ⟨z, blocked_of_concurrent hedge.2.1 hconc,
            (hpath.to_reflTransGen).tail hedge, Or.inl rfl⟩
    · refine Or.inr ⟨w, hw, haw, ?_⟩
      have hyE : y ∈ E := hedge.1
      have hwy' : C.vis w y ∨ w = y := hwy.symm
      have hyset : y.op ≠ Action.unset := by
        rcases hwy with rfl | hvwy
        · exact (isSet_iff.mpr hw.2.1)
        · exact succ_not_unset hw hyE hvwy
      have hvyz : C.vis y z := by
        rcases hedge.2.2 with hv' | hp
        · exact hv'
        · rcases hp with ⟨hv', -⟩ | hconc
          · exact hv'
          · obtain ⟨v, hv⟩ := isSet_iff.mp hyset
            exact (no_concurrent_from_set hv hconc).elim
      rcases hwy with rfl | hvwy
      · exact Or.inr hvyz
      · exact Or.inr (hvs.1 hvwy hvyz)

/-- **No loop.** The two kinds of arrow are each loop-free, and together they
stay loop-free: a same-time arrow lands on a `Blocked` event, from which
every path is causal, so a loop through one would make that event see
itself. -/
theorem jointVis_acyclic (hvs : VisStrict D C) (a : D.Event) :
    ¬ Relation.TransGen (jointVis C E) a a := by
  intro h
  rcases path_cases hvs h with hv | ⟨w, hw, haw, hwa⟩
  · exact hvs.2 a hv
  · rcases hwa with rfl | hvwa
    · exact hvs.2 w (vis_of_blocked_path hvs hw h)
    · rcases Relation.reflTransGen_iff_eq_or_transGen.mp haw with rfl | hpath
      · exact hvs.2 w hvwa
      · have haE : a ∈ E := by
          obtain ⟨b, hb, -⟩ := Relation.TransGen.head'_iff.mp h
          exact hb.1
        have hedge : jointVis C E w a := ⟨hw.1, haE, Or.inl hvwa⟩
        exact hvs.2 w (vis_of_blocked_path hvs hw (hpath.head hedge))

/-! ## The winning write is maximal for both

`paperMaximal_of_survives` of the main tree gives one half. This is the
other. -/

/-- **The winning write sees nothing.** Suppose cell `r` is live, holds the
surviving write `w`, and no live cell carries a later timestamp. Then `w`
has no visible successor in `E` at all.

An `unset` after `w` would write `w`'s own cell, which surviving forbids. A
`set` after `w` belongs to some cell `r'`, and either that cell is live, in
which case its own write is later than `w` and beats it, or it is not, in
which case its latest write is cleared by an `unset` that `w` also sees,
forbidden again. -/
theorem winner_no_vis_succ (hmono : Monotone C) (hvs : VisStrict D C)
    (hsup : SupportedOn D C E) {t : D.Sigma} (hs : IsPaperCan D C E t)
    {r : Nat} {w : D.Event} {v : Nat}
    (hwE : w ∈ E) (hwr : w.rep = r) (hwv : w.op = Action.set v)
    (hsv : Survives C E r w)
    (hmax : ∀ r'', (t.cells r'').1.2 = true → (t.cells r'').2.1 ≤ (t.cells r).2.1) :
    ∀ x ∈ E, ¬ C.vis w x := by
  intro x hxE hvis
  -- the payload of the winning cell is `w`'s
  have hpay : (t.cells r).2 = (w.time, v) :=
    (canonical_cell_live hvs hsup hs hwE hwr hwv hsv).2
  -- `x` cannot be an `unset`, since that writes `r`
  have hxset : x.op ≠ Action.unset := fun hx =>
    hsv ⟨x, hxE, Or.inl hx, hvis⟩
  obtain ⟨v', hv'⟩ := isSet_iff.mp hxset
  -- `x`'s cell has a latest write
  obtain ⟨w', hlat⟩ := exists_latestSet hmono hsup hs hxE ⟨rfl, hxset⟩
  have hvww' : C.vis w w' := by
    by_cases hxw : x = w'
    · exact hxw ▸ hvis
    · exact hvs.1 hvis (hlat.2.2 x hxE ⟨rfl, hxset⟩ hxw)
  by_cases hlive : Live C (E := E) x.rep
  · -- the other cell is live, so its write beats `w`
    have hsv' : Survives C E x.rep w' := (live_iff_latest_survives hlat).mp hlive
    obtain ⟨v'', hv''⟩ := isSet_iff.mp hlat.2.1.2
    obtain ⟨hflag', hpay'⟩ :=
      canonical_cell_live hvs hsup hs hlat.1 hlat.2.1.1 hv'' hsv'
    have hle := hmax x.rep hflag'
    rw [hpay', hpay] at hle
    exact absurd (hmono w w' hvww') (Nat.not_lt.mpr hle)
  · -- the other cell is dead, so an `unset` clears it, and `w` sees that too
    have hns : ¬ Survives C E x.rep w' := fun hsv' =>
      hlive ((live_iff_latest_survives hlat).mpr hsv')
    simp only [Survives, not_not] at hns
    obtain ⟨y, hyE, hty, hvy⟩ := hns
    rcases hty with hyun | hyrep
    · exact hsv ⟨y, hyE, Or.inl hyun, hvs.1 hvww' hvy⟩
    · by_cases hyset : y.op = Action.unset
      · exact hsv ⟨y, hyE, Or.inl hyset, hvs.1 hvww' hvy⟩
      · by_cases hyw : y = w'
        · exact hvs.2 w' (hyw ▸ hvy)
        · exact hvs.2 w' (hvs.1 hvy (hlat.2.2 y hyE ⟨hyrep, hyset⟩ hyw))

/-! ## Two facts about the winner -/

/-- A raised flag puts the replica in the domain, so its write is a
candidate. -/
theorem mem_candidates {t : State} {r : Nat} (h : (t.cells r).1.2 = true) :
    toLex ((t.cells r).2.1, toLex (r, (t.cells r).2.2)) ∈ candidates t := by
  refine Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨?_, h⟩, rfl⟩
  by_contra hr
  rw [t.outside r hr] at h
  exact absurd h (by simp [zero])

/-- The winning cell carries the greatest payload timestamp among live
cells. -/
theorem winner_time_max {t : State} {c : Write} (hc : winner t = some c)
    {r : Nat} (hcr : c = toLex ((t.cells r).2.1, toLex (r, (t.cells r).2.2)))
    (r'' : Nat) (h'' : (t.cells r'').1.2 = true) :
    (t.cells r'').2.1 ≤ (t.cells r).2.1 := by
  unfold winner at hc
  split_ifs at hc with hne
  · have heq : (candidates t).max' hne = c := by injection hc
    have hle := Finset.le_max' (candidates t) _ (mem_candidates h'')
    rw [heq, hcr] at hle
    rcases Prod.Lex.le_iff.mp hle with h | h
    · exact Nat.le_of_lt h
    · exact Nat.le_of_eq h.1

/-! ## The premise -/

theorem specChosenOrderSound :
    Soundness.SpecChosenOrderSound D historySpec issuance := by
  classical
  intro C hhon hvs E hsup hcl hfin q
  have hmono : Monotone C.replayContext := monotone_of_mintHonest C hhon
  have hl := guardedLaws laws equal_op_commutes same_rep_cond_comm
  obtain ⟨π₀, hp₀⟩ := hfin
  -- one enumeration respecting both relations at once
  obtain ⟨ρ₀, hperm, hrt⟩ := exists_respecting_perm
    (R := Relation.TransGen (jointVis C.replayContext E))
    (fun hab hbc => hab.trans hbc) (jointVis_acyclic hvs) π₀
  obtain ⟨ρ, hρ, hrj⟩ : ∃ ρ : List D.Event, listPermOf ρ E ∧
      respects ρ (jointVis C.replayContext E) :=
    ⟨ρ₀, ⟨hperm.nodup hp₀.1, fun a => (hperm.mem_iff (a := a)).symm.trans (hp₀.2 a)⟩,
      hrt.imp (fun {_ _} hno hedge => hno (Relation.TransGen.single hedge))⟩
  have hrvis : respects ρ (fun a b : D.Event => C.replayContext.vis a b) :=
    hrj.imp_of_mem (fun {a b} ha hb hno hv =>
      hno ⟨(hρ.2 b).mp hb, (hρ.2 a).mp ha, Or.inl hv⟩)
  have hrpo : respects ρ (paperOrder (policy D) C.replayContext E) :=
    hrj.imp_of_mem (fun {a b} ha hb hno hp =>
      hno ⟨(hρ.2 b).mp hb, (hρ.2 a).mp ha, Or.inr hp⟩)
  have hrspec : respects ρ (specVisibility historySpec C.replayContext) :=
    hrvis.imp (fun {_ _} hno hedge => hno hedge.1)
  have hcanρ : IsPaperCan D C.replayContext E (D.applyList D.sigma0 ρ) :=
    ⟨ρ, hρ, hrpo, rfl⟩
  have hlabels : ∀ π : List D.Event,
      projectedUpdates (D := D.toMRDTSig) π
        = DeterministicSpec.updateLabels (π.map Op.op) := by
    intro π
    simp [projectedUpdates, DeterministicSpec.updateLabels, List.map_map, Function.comp]
  by_cases hcand : (candidates (D.applyList D.sigma0 ρ)).Nonempty
  · have hc : winner (D.applyList D.sigma0 ρ)
        = some ((candidates (D.applyList D.sigma0 ρ)).max' hcand) := by
      simp [winner, hcand]
    obtain ⟨r, hflag, hcr⟩ := winner_cell hc
    obtain ⟨w, hwE, hsw, hsv⟩ := (canonical_flag hvs hsup hcanρ r).mp hflag
    obtain ⟨v, hwv⟩ := isSet_iff.mp hsw.2
    have hpay := (canonical_cell_live hvs hsup hcanρ hwE hsw.1 hwv hsv).2
    -- the winning write is maximal for both relations
    have hnovis := winner_no_vis_succ hmono hvs hsup hcanρ hwE hsw.1 hwv hsv
      (winner_time_max hc hcr)
    have hmaxpo : PaperMaximalOn D C.replayContext E w :=
      paperMaximal_of_survives hsw.1 hwv hsv
    have hmaxj : ∀ x ∈ E, ¬ jointVis C.replayContext E w x := by
      intro x hxE hedge
      rcases hedge.2.2 with hv | hp
      · exact hnovis x hxE hv
      · by_cases hxw : x = w
        · rw [hxw] at hp
          rcases hp with ⟨hv, -⟩ | ⟨-, -, hrc, -⟩
          · exact hvs.2 w hv
          · exact absurd ((eventRcBefore_iff w w).mp hrc).1 (by rw [hwv]; simp)
        · exact hmaxpo x hxE hxw hp
    have hwρ : w ∈ ρ := (hρ.2 w).mpr hwE
    set L : List D.Event := ρ.erase w ++ [w] with hL
    have hpermL : L.Perm ρ :=
      (List.perm_append_singleton w (ρ.erase w)).trans (List.perm_cons_erase hwρ).symm
    have hpL : listPermOf L E :=
      ⟨hpermL.symm.nodup hρ.1, fun x => (hpermL.mem_iff (a := x)).trans (hρ.2 x)⟩
    have hrjL : respects L (jointVis C.replayContext E) := by
      rw [hL]
      refine List.pairwise_append.mpr
        ⟨hrj.sublist List.erase_sublist, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton.mp hb]
      exact hmaxj a ((hρ.2 a).mp (List.mem_of_mem_erase ha))
    have hrpoL : respects L (paperOrder (policy D) C.replayContext E) :=
      hrjL.imp_of_mem (fun {a b} ha hb hno hp =>
        hno ⟨(hpL.2 b).mp hb, (hpL.2 a).mp ha, Or.inr hp⟩)
    have hrvisL : respects L (fun a b : D.Event => C.replayContext.vis a b) :=
      hrjL.imp_of_mem (fun {a b} ha hb hno hv =>
        hno ⟨(hpL.2 b).mp hb, (hpL.2 a).mp ha, Or.inl hv⟩)
    have hsame : D.applyList D.sigma0 L = D.applyList D.sigma0 ρ :=
      ConcreteMRDT.canonical_unique hl C.replayContext E hsup ⟨L, hpL, hrpoL, rfl⟩ hcanρ
    refine ⟨L, hpL, hrpoL, hrvisL.imp (fun {_ _} hno hedge => hno hedge.1), ?_⟩
    simp only [historySpec]
    rw [hlabels, specMachine.updates_query_iff]
    show readValue (D.applyList D.sigma0 L)
      = specMachine.query ((L.map Op.op).foldl specMachine.update specMachine.initial) q
    rw [hsame, hL, List.map_append, List.map_singleton, spec_fold_append]
    have hval : readValue (D.applyList D.sigma0 ρ) = some v := by
      simp only [readValue, hc, Option.map_some]
      rw [hcr]
      simp only [ofLex_toLex]
      rw [hpay]
    rw [hval, hwv]
    rfl
  · have hnone : readValue (D.applyList D.sigma0 ρ) = none := by
      simp [readValue, winner, Finset.not_nonempty_iff_eq_empty.mp hcand]
    refine ⟨ρ, hρ, hrpo, hrspec, ?_⟩
    simp only [historySpec]
    rw [hlabels, specMachine.updates_query_iff]
    show readValue (D.applyList D.sigma0 ρ)
      = specMachine.query ((ρ.map Op.op).foldl specMachine.update specMachine.initial) q
    rw [hnone]
    rcases hcase : ρ.reverse with _ | ⟨e, rest⟩
    · have hnil : ρ = [] := by
        have := congrArg List.reverse hcase
        simpa using this
      rw [hnil]; rfl
    · have hsplit : ρ = rest.reverse ++ [e] := by
        have := congrArg List.reverse hcase
        simpa using this
      have hunset : e.op = Action.unset := by
        by_contra hset
        obtain ⟨v, hv⟩ := isSet_iff.mp hset
        refine hcand ?_
        rw [hsplit, show D.applyList D.sigma0 (rest.reverse ++ [e])
            = step (D.applyList D.sigma0 rest.reverse) e from by
          simp [Impl.applyList, List.foldl_append, do_eq]]
        exact candidates_set hv
      rw [hsplit, List.map_append, List.map_singleton, spec_fold_append, hunset]
      rfl

end LeanProofs.NoSpecNonComm.Implementations.OptionalRegister
