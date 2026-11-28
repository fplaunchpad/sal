import LeanProofs_no_spec_non_comm.Implementations.EmbeddedRGA.Invariant
import Artifact.MRDTs.Paper1.InvariantReplay

/-!
# Embedded RGA: concurrent events commute at valid states

The single premise the invariant route consumes.
`InvariantReplay.laws_of_concurrent_commutation` and
`InvariantReplay.emptyPolicyLaws` both take exactly this hypothesis, and
between them they supply the replay contract and the policy contract at the
empty policy. So this file is the whole laws layer for the row.

Why it is true, in one line per operation pair.

* **Two deletions** commute at every state at all, valid or not.
* **An insertion and a deletion** commute once the deletion's target is not
  the identity the insertion allocates, which `DelHonest` supplies, and the
  state is sorted, which `Valid` supplies. Sortedness is not decoration:
  the sorted insert commutes with a filter only on a sorted list.
* **Two insertions** commute once their keys differ, which `CoordHonest`
  supplies through `Γ.key_inj`. Here the state needs nothing at all, as
  `insertDown_comm` records.

`DelHonest` is where the pair `Negative.lean` uses is ruled out.
`CanIssue (del x)` asks for `x` to be live when the deletion is issued, so
the insertion that allocated `x` is `vis`-before the deletion and the two
are never concurrent. That is the reason the invariant reading succeeds for
this row where no choice of `rc` can.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.EmbeddedRGA

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

variable {Γ : Scheme} {α : Type} [DecidableEq α] {Q : QueryOf Γ α}

theorem lexLt_not_of {u v : List Nat} (h : lexLt u v = true) : ¬ (lexLt v u = true) := by
  simp [lexLt_asymm u v h]

/-- **Two sorted inserts commute** as soon as their keys differ. No
sortedness of the list is needed: the record with the larger key is never a
stopper for the one with the smaller key, and the one with the smaller key
stops the larger one exactly where the list would have. -/
theorem insertDown_comm {z w : Record Γ α} (hne : recKey z ≠ recKey w) :
    ∀ s : St Γ α, insertDown w (insertDown z s) = insertDown z (insertDown w s) := by
  have hzw := lexLt_total hne
  intro s
  induction s with
  | nil =>
    simp only [insertDown]
    rcases hzw with h | h
    · rw [if_pos h, if_neg (lexLt_not_of h)]
    · rw [if_neg (lexLt_not_of h), if_pos h]
  | cons y Y ih =>
    by_cases hA : lexLt (recKey y) (recKey z) = true
    · by_cases hB : lexLt (recKey y) (recKey w) = true
      · rcases hzw with hP | hQ
        · simp only [insertDown, if_pos hA, if_pos hB, if_pos hP,
            if_neg (lexLt_not_of hP)]
        · simp only [insertDown, if_pos hA, if_pos hB, if_pos hQ,
            if_neg (lexLt_not_of hQ)]
      · rcases hzw with hP | hQ
        · exact absurd (lexLt_trans _ _ _ hA hP) hB
        · simp only [insertDown, if_pos hA, if_neg hB, if_pos hQ,
            if_neg (lexLt_not_of hQ)]
    · by_cases hB : lexLt (recKey y) (recKey w) = true
      · rcases hzw with hP | hQ
        · simp only [insertDown, if_neg hA, if_pos hB, if_pos hP,
            if_neg (lexLt_not_of hP)]
        · exact absurd (lexLt_trans _ _ _ hB hQ) hA
      · simp only [insertDown, if_neg hA, if_neg hB]
        exact congrArg _ ih

/-- A record whose key beats every key present goes to the front. -/
theorem insertDown_eq_cons {z : Record Γ α} : ∀ {t : St Γ α},
    (∀ w ∈ t, lexLt (recKey w) (recKey z) = true) → insertDown z t = z :: t := by
  intro t
  cases t with
  | nil => intro _; rfl
  | cons y Y => intro h; simp only [insertDown, if_pos (h y List.mem_cons_self)]

/-- **The sorted insert commutes with a filter the newcomer survives**, on a
sorted list. Sortedness is exactly what this needs: on `[v, u]` with `v`
below `u` in key order, inserting and then dropping `v` is not dropping `v`
and then inserting. -/
theorem insertDown_filter {z : Record Γ α} {p : Record Γ α → Bool} (hp : p z = true) :
    ∀ {s : St Γ α}, SortedDown s → (insertDown z s).filter p = insertDown z (s.filter p) := by
  intro s
  induction s with
  | nil => intro _; simp [insertDown, hp]
  | cons y Y ih =>
    intro hs
    by_cases hlt : lexLt (recKey y) (recKey z) = true
    · have hall : ∀ w ∈ (y :: Y), lexLt (recKey w) (recKey z) = true := by
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw'
        · exact hlt
        · exact lexLt_trans _ _ _ (sortedDown_head hs w hw') hlt
      have hallf : ∀ w ∈ (y :: Y).filter p, lexLt (recKey w) (recKey z) = true :=
        fun w hw => hall w (List.mem_of_mem_filter hw)
      rw [insertDown_eq_cons hall, insertDown_eq_cons hallf, List.filter_cons_of_pos hp]
    · simp only [insertDown, if_neg hlt]
      by_cases hpy : p y = true
      · rw [List.filter_cons_of_pos hpy, List.filter_cons_of_pos hpy,
          ih (sortedDown_of_cons hs)]
        simp only [insertDown, if_neg hlt]
      · rw [List.filter_cons_of_neg (by simpa using hpy),
          List.filter_cons_of_neg (by simpa using hpy), ih (sortedDown_of_cons hs)]

/-- Distinct observed events carry distinct timestamps. -/
theorem time_ne {C : Ctx (Dα Γ α Q)} {a b : Op (AppOp Γ α)} (ha : a ∈ C.events)
    (hb : b ∈ C.events) (hne : a ≠ b) : a.time ≠ b.time := by
  obtain ⟨r, t, hL, hm⟩ := ha
  obtain ⟨r', t', hL', hm'⟩ := hb
  exact C.timestamps_distinct hL hm hL' hm' hne

/-- A deletion does not change which other identities are present. -/
theorem ids_filter_ne {s : St Γ α} {t x : Nat} (h : t ≠ x) :
    t ∈ ids (s.filter (fun z => decide (z.1 ≠ x))) ↔ t ∈ ids s := by
  simp only [ids, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨z, ⟨hz, -⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, ⟨hz, decide_eq_true h⟩, rfl⟩

/-- Two deletions commute at every state. -/
theorem filter_ne_comm (s : St Γ α) (x y : Nat) :
    (s.filter (fun z => decide (z.1 ≠ x))).filter (fun z => decide (z.1 ≠ y))
      = (s.filter (fun z => decide (z.1 ≠ y))).filter (fun z => decide (z.1 ≠ x)) := by
  simp only [List.filter_filter]
  exact List.filter_congr (fun z _ => by simp [Bool.and_comm])

/-! ## The one premise the invariant route consumes

`InvariantReplay.laws_of_concurrent_commutation` and
`InvariantReplay.emptyPolicyLaws` take the same single hypothesis: observed
**concurrent** events commute at every valid state. Everything above exists
to discharge it. -/

/-- **A deletion's target is never the identity a concurrent insertion
allocates.**

`CanIssue (del x)` asks for `x` to be live when the deletion is issued, so
the insertion that allocated `x` is always `vis`-before the deletion. The
pair `Negative.lean` uses to refute RC-NON-COMM is therefore never
concurrent, which is the whole reason the invariant reading succeeds where
no `rc` can. `Certificate.lean` discharges this from issuance. -/
def DelHonest (C : Ctx (Dα Γ α Q)) : Prop :=
  ∀ e ∈ C.events, ∀ f ∈ C.events, ∀ (v : α) (p : List Γ.Sym) (an x : Nat) (g : Γ.Arg),
    e.op = AppOp.ins v p an g → f.op = AppOp.del x →
    ¬ C.vis e f → ¬ C.vis f e → e.time ≠ x

/-- An insertion and a deletion of another identity commute on a sorted
state. -/
theorem step_ins_del {s : St Γ α} (hsort : SortedDown s) {e f : Op (AppOp Γ α)}
    {v : α} {p : List Γ.Sym} {an x : Nat} {g : Γ.Arg}
    (hope : e.op = AppOp.ins v p an g) (hopf : f.op = AppOp.del x)
    (htx : e.time ≠ x) : step (step s e) f = step (step s f) e := by
  have hstepe : ∀ t : St Γ α, step t e
      = if e.time ∈ ids t then t else insertDown (e.time, v, p ++ Γ.code g (e.time - an)) t :=
    fun t => by simp [step, hope]
  have hstepf : ∀ t : St Γ α, step t f = t.filter (fun z => decide (z.1 ≠ x)) :=
    fun t => by simp [step, hopf]
  simp only [hstepe, hstepf]
  by_cases hm : e.time ∈ ids s
  · rw [if_pos hm, if_pos ((ids_filter_ne htx).mpr hm)]
  · rw [if_neg hm, if_neg (fun h => hm ((ids_filter_ne htx).mp h)),
      insertDown_filter (z := (e.time, v, p ++ Γ.code g (e.time - an)))
        (p := fun z => decide (z.1 ≠ x)) (decide_eq_true htx) hsort]

/-- **Observed concurrent events commute at every valid state.** -/
theorem concurrent_commutes {C : Ctx (Dα Γ α Q)} (hc : CoordHonest C) (hd : DelHonest C)
    {a b : Op (AppOp Γ α)} (ha : a ∈ C.events) (hb : b ∈ C.events)
    (hvab : ¬ C.vis a b) (hvba : ¬ C.vis b a) :
    InvariantOrder.Commutes (Dα Γ α Q).toMRDTSig.toUpdateSig (Valid C) a b := by
  intro s hs
  obtain ⟨hsort, -⟩ := hs
  by_cases hab : a = b
  · rw [hab]
  show step (step s a) b = step (step s b) a
  cases hopa : a.op with
  | ins va pa ana ga =>
    cases hopb : b.op with
    | ins vb pb anb gb =>
      have hta : a.time ≠ b.time := time_ne ha hb hab
      have hkey : recKey (a.time, va, pa ++ Γ.code ga (a.time - ana))
          ≠ recKey (b.time, vb, pb ++ Γ.code gb (b.time - anb)) := by
        refine recKey_ne (fun hco => ?_)
        have heq := hc a ha b hb _ _ ⟨va, pa, ana, ga, hopa, rfl⟩ ⟨vb, pb, anb, gb, hopb, rfl⟩ hco
        simp only [Prod.mk.injEq] at heq
        exact hta heq.1
      have hstepa : ∀ t : St Γ α, step t a
          = if a.time ∈ ids t then t
            else insertDown (a.time, va, pa ++ Γ.code ga (a.time - ana)) t :=
        fun t => by simp [step, hopa]
      have hstepb : ∀ t : St Γ α, step t b
          = if b.time ∈ ids t then t
            else insertDown (b.time, vb, pb ++ Γ.code gb (b.time - anb)) t :=
        fun t => by simp [step, hopb]
      simp only [hstepa, hstepb]
      by_cases hma : a.time ∈ ids s <;> by_cases hmb : b.time ∈ ids s
      · simp [hma, hmb]
      · simp [hma, hmb, ids_insertDown]
      · simp [hma, hmb, ids_insertDown]
      · rw [if_neg hma, if_neg hmb,
          if_neg (fun h => (ids_insertDown.mp h).elim (fun k => hta k.symm) hmb),
          if_neg (fun h => (ids_insertDown.mp h).elim hta hma)]
        exact insertDown_comm hkey s
    | del xb =>
      exact step_ins_del hsort hopa hopb
        (hd a ha b hb va pa ana xb ga hopa hopb hvab hvba)
  | del xa =>
    cases hopb : b.op with
    | ins vb pb anb gb =>
      exact (step_ins_del hsort hopb hopa
        (hd b hb a ha vb pb anb xa gb hopb hopa hvba hvab)).symm
    | del xb =>
      have hstepa : ∀ t : St Γ α, step t a = t.filter (fun z => decide (z.1 ≠ xa)) :=
        fun t => by simp [step, hopa]
      have hstepb : ∀ t : St Γ α, step t b = t.filter (fun z => decide (z.1 ≠ xb)) :=
        fun t => by simp [step, hopb]
      simp only [hstepa, hstepb]
      exact filter_ne_comm s xa xb

end LeanProofs.NoSpecNonComm.Implementations.EmbeddedRGA
