import LeanProofs_no_spec_non_comm.Implementations.EmbeddedRGA.Commutation

/-!
# Embedded RGA: what a causal replay computes, and convergence

The representation the join induction runs on is the artifact's: a state
**is** a causal replay of an event set. This file gives that representation
its two defining properties.

`fold_live` says what a replay computes. Folding `step` along a `BirthFirst`
enumeration of observed events leaves precisely the records written by its
insertions whose identity it does not delete. `BirthFirst` asks only that
no insertion be preceded by the deletion of its own identity, which is
weaker than respecting `vis` and is what both the `vis`-respecting and the
`lo`-respecting enumerations of an observed set satisfy. The insertion case
is where the hypotheses are spent: the appended insertion is fresh, because
a record carrying its timestamp could only come from another event of the
prefix and observed events have distinct timestamps, and nothing in the
prefix deletes it, which is `BirthFirst` at the final split.

`fold_congr` is convergence. Two causal enumerations of the same event set
fold to the same state, since both folds are sorted, `fold_live` gives them
the same members, and `sortedDown_ext` says a sorted list is determined by
its members.

`DelBorn` replaces `DelHonest` of `Commutation.lean` as the primitive form
of the deletion premise, and `delHonest_of_delBorn` recovers the weaker one.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.EmbeddedRGA

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

variable {Γ : Scheme} {α : Type} [DecidableEq α] {Q : QueryOf Γ α}

/-- An insertion writes one record. -/
theorem writes_funct {e : Op (AppOp Γ α)} {z w : Record Γ α} (hz : Writes e z) (hw : Writes e w) :
    z = w := by
  obtain ⟨v, p, a, g, hop, rfl⟩ := hz
  obtain ⟨v', p', a', g', hop', rfl⟩ := hw
  rw [hop] at hop'
  cases hop'
  rfl

theorem writes_fst {e : Op (AppOp Γ α)} {z : Record Γ α} (h : Writes e z) : z.1 = e.time := by
  obtain ⟨v, p, a, g, -, rfl⟩ := h
  rfl

/-- `xs` deletes identity `t`. -/
def Deletes (xs : List (Op (AppOp Γ α))) (t : Nat) : Prop :=
  ∃ f ∈ xs, f.op = AppOp.del t

/-- The records a replay of `xs` leaves live: written by an insertion of
`xs`, and not deleted by `xs`. -/
def Live (xs : List (Op (AppOp Γ α))) (z : Record Γ α) : Prop :=
  (∃ e ∈ xs, Writes e z) ∧ ¬ Deletes xs z.1

/-- **Every observed deletion names an identity already born and visible.**

`CanIssue (del x)` asks for `x` to be live when the deletion is issued, so
the insertion allocating `x` lies in the deletion's causal past.
`Certificate.lean` discharges this from issuance; everything below takes it
as a hypothesis. -/
def DelBorn (C : Ctx (Dα Γ α Q)) : Prop :=
  ∀ f ∈ C.events, ∀ x, f.op = AppOp.del x →
    ∃ e ∈ C.events, e.time = x ∧ (∃ v p an g, e.op = AppOp.ins v p an g) ∧ C.vis e f

/-- `DelBorn` is the stronger reading: the pair `Negative.lean` uses is
ruled out because the birth is causally first. -/
theorem delHonest_of_delBorn {C : Ctx (Dα Γ α Q)} (hb : DelBorn C) : DelHonest C := by
  intro e he f hf v p an x g hope hopf hvef hvfe hx
  obtain ⟨g, hg, hgt, -, hvis⟩ := hb f hf x hopf
  have : g = e := by
    by_contra hne
    exact time_ne hg he hne (hgt.trans hx.symm)
  exact hvef (this ▸ hvis)

/-! ## A causal replay is exactly the live records

The engine of both convergence and the join: folding `step` along any
`vis`-respecting enumeration of a set of observed events leaves precisely
the records written by its insertions whose identity it does not delete. -/

/-- **No insertion is preceded by the deletion of its own identity.** This
is all the ordering `fold_live` needs, and both a `vis`-respecting and a
`lo`-respecting enumeration of observed events have it. -/
def BirthFirst (xs : List (Op (AppOp Γ α))) : Prop :=
  ∀ pre e post, xs = pre ++ e :: post → (∃ v p an g, e.op = AppOp.ins v p an g) →
    ¬ Deletes pre e.time

theorem birthFirst_append {xs : List (Op (AppOp Γ α))} {e : Op (AppOp Γ α)}
    (h : BirthFirst (xs ++ [e])) : BirthFirst xs := by
  intro pre u post hsplit hins
  exact h pre u (post ++ [e]) (by rw [hsplit]; simp) hins

theorem fold_live {C : Ctx (Dα Γ α Q)} :
    ∀ {xs : List (Op (AppOp Γ α))}, xs.Nodup → (∀ e ∈ xs, e ∈ C.events) →
      BirthFirst xs → ∀ z, z ∈ xs.foldl step [] ↔ Live xs z := by
  intro xs
  induction xs using List.reverseRecOn with
  | nil =>
    intro _ _ _ z
    simp [Live, Deletes]
  | append_singleton xs e ih =>
    intro hnd hsup hord z
    rw [List.nodup_append] at hnd
    obtain ⟨hndx, -, hdisj⟩ := hnd
    have hex : e ∉ xs := fun h => hdisj e h e List.mem_cons_self rfl
    have hsupx : ∀ u ∈ xs, u ∈ C.events := fun u hu => hsup u (List.mem_append_left _ hu)
    have hee : e ∈ C.events := hsup e (List.mem_append_right _ List.mem_cons_self)
    have hordx : BirthFirst xs := birthFirst_append hord
    have ihx := ih hndx hsupx hordx
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    -- membership in the appended list splits
    have hmem : ∀ w : Op (AppOp Γ α), w ∈ xs ++ [e] ↔ w ∈ xs ∨ w = e := by
      intro w; simp
    cases hop : e.op with
    | ins v p an g =>
      have hwe : Writes e (e.time, v, p ++ Γ.code g (e.time - an)) :=
        ⟨v, p, an, g, hop, rfl⟩
      -- `e` is fresh: a record with its timestamp would come from an event of `xs`
      have hfresh : e.time ∉ ids (xs.foldl step []) := by
        intro hin
        simp only [ids, List.mem_map] at hin
        obtain ⟨w, hw, hwt⟩ := hin
        obtain ⟨⟨u, hu, hwu⟩, -⟩ := (ihx w).mp hw
        exact time_ne (hsupx u hu) hee (fun h => hex (h ▸ hu))
          ((writes_fst hwu).symm.trans hwt)
      -- and nothing in `xs` deletes it
      have hnodel : ¬ Deletes xs e.time :=
        hord xs e [] rfl ⟨v, p, an, g, hop⟩
      simp only [step, hop, if_neg hfresh, mem_insertDown, ihx, Live, Deletes, hmem]
      constructor
      · rintro (rfl | ⟨⟨u, hu, hwu⟩, hnd'⟩)
        · refine ⟨⟨e, Or.inr rfl, hwe⟩, ?_⟩
          rintro ⟨f, hf | rfl, hfop⟩
          · exact hnodel ⟨f, hf, by simpa [writes_fst hwe] using hfop⟩
          · rw [hop] at hfop; exact absurd hfop (by simp)
        · refine ⟨⟨u, Or.inl hu, hwu⟩, ?_⟩
          rintro ⟨f, hf | rfl, hfop⟩
          · exact hnd' ⟨f, hf, hfop⟩
          · rw [hop] at hfop; exact absurd hfop (by simp)
      · rintro ⟨⟨u, hu | rfl, hwu⟩, hnd'⟩
        · exact Or.inr ⟨⟨u, hu, hwu⟩, fun ⟨f, hf, hfop⟩ => hnd' ⟨f, Or.inl hf, hfop⟩⟩
        · exact Or.inl (writes_funct hwu hwe)
    | del x =>
      simp only [step, hop, List.mem_filter, ihx, Live, Deletes, hmem,
        decide_eq_true_eq]
      constructor
      · rintro ⟨⟨⟨u, hu, hwu⟩, hnd'⟩, hzx⟩
        refine ⟨⟨u, Or.inl hu, hwu⟩, ?_⟩
        rintro ⟨f, hf | rfl, hfop⟩
        · exact hnd' ⟨f, hf, hfop⟩
        · rw [hop] at hfop
          cases hfop
          exact hzx rfl
      · rintro ⟨⟨u, hu | rfl, hwu⟩, hnd'⟩
        · refine ⟨⟨⟨u, hu, hwu⟩, fun ⟨f, hf, hfop⟩ => hnd' ⟨f, Or.inl hf, hfop⟩⟩, ?_⟩
          intro hzx
          exact hnd' ⟨e, Or.inr rfl, by rw [hop, hzx]⟩
        · obtain ⟨v, p, a, g', hbad, -⟩ := hwu
          rw [hop] at hbad
          exact absurd hbad (by simp)

/-! ## Sorted lists are determined by their members -/

theorem sortedDown_ext : ∀ {s t : St Γ α}, SortedDown s → SortedDown t →
    (∀ z, z ∈ s ↔ z ∈ t) → s = t := by
  intro s
  induction s with
  | nil =>
    intro t _ _ h
    cases t with
    | nil => rfl
    | cons y Y => exact absurd ((h y).mpr List.mem_cons_self) (by simp)
  | cons x X ih =>
    intro t hs ht h
    cases t with
    | nil => exact absurd ((h x).mp List.mem_cons_self) (by simp)
    | cons y Y =>
      have hxy : x = y := by
        by_contra hne
        have hxt : x ∈ y :: Y := (h x).mp List.mem_cons_self
        have hys : y ∈ x :: X := (h y).mpr List.mem_cons_self
        have hxY : x ∈ Y := (List.mem_cons.mp hxt).resolve_left hne
        have hyX : y ∈ X := (List.mem_cons.mp hys).resolve_left (Ne.symm hne)
        exact lexLt_not_of (sortedDown_head ht x hxY) (sortedDown_head hs y hyX)
      subst hxy
      refine congrArg _ (ih (sortedDown_of_cons hs) (sortedDown_of_cons ht) (fun z => ?_))
      constructor
      · intro hz
        rcases List.mem_cons.mp ((h z).mp (List.mem_cons_of_mem _ hz)) with rfl | hz'
        · exact absurd (sortedDown_head hs z hz) (by simp [lexLt_irrefl])
        · exact hz'
      · intro hz
        rcases List.mem_cons.mp ((h z).mpr (List.mem_cons_of_mem _ hz)) with rfl | hz'
        · exact absurd (sortedDown_head ht z hz) (by simp [lexLt_irrefl])
        · exact hz'

/-! ## Convergence

Two causal enumerations of the same observed event set fold to the same
state. This is the row's convergence theorem, and the uniqueness half of
the representation the join induction runs on. -/

/-- A causal replay of observed events is valid. -/
theorem valid_fold {C : Ctx (Dα Γ α Q)} (hc : CoordHonest C) {xs : List (Op (AppOp Γ α))}
    (hsup : ∀ e ∈ xs, e ∈ C.events) : Valid C (xs.foldl step []) :=
  (closed C hc).applySeq (valid_nil C) xs hsup

/-- **Convergence.** Both sides are sorted and have the same members, and a
sorted list is determined by its members. -/
theorem fold_congr {C : Ctx (Dα Γ α Q)} (hc : CoordHonest C)
    {xs ys : List (Op (AppOp Γ α))} (hndx : xs.Nodup) (hndy : ys.Nodup)
    (hsupx : ∀ e ∈ xs, e ∈ C.events) (hsupy : ∀ e ∈ ys, e ∈ C.events)
    (hordx : BirthFirst xs) (hordy : BirthFirst ys)
    (hsame : ∀ e, e ∈ xs ↔ e ∈ ys) :
    xs.foldl step [] = ys.foldl step [] := by
  refine sortedDown_ext (valid_fold hc hsupx).1 (valid_fold hc hsupy).1 (fun z => ?_)
  rw [fold_live (C := C) hndx hsupx hordx z, fold_live (C := C) hndy hsupy hordy z]
  constructor
  · rintro ⟨⟨u, hu, hwu⟩, hnd⟩
    exact ⟨⟨u, (hsame u).mp hu, hwu⟩,
      fun ⟨f, hf, hfop⟩ => hnd ⟨f, (hsame f).mpr hf, hfop⟩⟩
  · rintro ⟨⟨u, hu, hwu⟩, hnd⟩
    exact ⟨⟨u, (hsame u).mpr hu, hwu⟩,
      fun ⟨f, hf, hfop⟩ => hnd ⟨f, (hsame f).mp hf, hfop⟩⟩

end LeanProofs.NoSpecNonComm.Implementations.EmbeddedRGA
