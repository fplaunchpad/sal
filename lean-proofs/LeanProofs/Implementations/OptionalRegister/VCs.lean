import LeanProofs1.Implementations.OptionalRegister.Definition
import LeanProofs1.Metatheory.Adequacy

/-!
# The optional register: every obligation

`Laws(D_type)` of Section 4 and VC1 to VC5 of Section 5, for the tuple of
`Definition.lean`.
-/

namespace LeanProofs1.Implementations.OptionalRegister

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

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
  simp only [mergeCell, mergeFlag_comm l.1 (ac, af) (bc, bf)]
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

end LeanProofs1.Implementations.OptionalRegister
