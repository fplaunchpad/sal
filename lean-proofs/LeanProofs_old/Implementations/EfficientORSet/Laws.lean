import LeanProofs.Implementations.EfficientORSet.Definition
import LeanProofs.Interface.PaperRoute

/-!
# The efficient OR-set: `Laws(D_type)` and VC1 to VC5

This row motivated the guard on RC-NON-COMM. Two `add x` events issued by
one replica do not commute, and they carry the same operation, so an
unguarded RC-NON-COMM would demand `add x --rc--> add x` and NO-RC-CHAIN
would refute it. With the guard the pair is out of scope, because one
replica's events are always causally ordered. Everything still in scope
behaves:

| pair, different replicas | commutes | `rc` edge |
| ------------------------ | -------- | --------- |
| `add x` / `add y`        | yes      | no        |
| `add x` / `remove x`     | no       | yes       |
| `remove x` / `remove y`  | yes      | no        |

So `Laws(D_type)` holds, and the five conditions are stated at `lo^C_E`
itself rather than at `rc`, which is the route of `Interface/PaperRoute.lean`.

## `can^C(E)` in closed form

`Represents` is this row's description of the canonical state: a record
`(r, t, x)` survives exactly when the `add x` that `r` issued at `t` is in
`E` and nothing in `E` visible to it kills the pair `(r, x)`. The file
proves that every linear extension of `lo^C_E` folds to that state, and the
five conditions follow by set algebra, because `Represents` determines the
state uniquely.
-/

namespace LeanProofs.Implementations.EfficientORSet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable {α : Type} [DecidableEq α]

/-! ## Which pairs commute -/

/-- An add never touches another replica's records, so two adds from
different replicas commute whatever they add. -/
theorem commutes_add_add {e₁ e₂ : Event α} {x y : α}
    (h₁ : e₁.2.2 = AppOp.add x) (h₂ : e₂.2.2 = AppOp.add y)
    (hr : e₁.2.1 ≠ e₂.2.1) : (D α).Commutes e₁ e₂ := by
  rcases e₁ with ⟨t₁, r₁, o₁⟩
  rcases e₂ with ⟨t₂, r₂, o₂⟩
  simp only at h₁ h₂
  subst h₁; subst h₂
  simp only at hr
  intro s
  ext p
  rcases p with ⟨r, t, z⟩
  simp [update, Finset.mem_insert, Finset.mem_filter, Prod.ext_iff]
  constructor
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨h, hk⟩) <;> tauto
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨h, hk⟩) <;> tauto

/-- Adds of **different elements** commute, whatever their replicas. -/
theorem commutes_add_add_ne {e₁ e₂ : Event α} {x y : α}
    (h₁ : e₁.2.2 = AppOp.add x) (h₂ : e₂.2.2 = AppOp.add y) (hxy : x ≠ y) :
    (D α).Commutes e₁ e₂ := by
  rcases e₁ with ⟨t₁, r₁, o₁⟩
  rcases e₂ with ⟨t₂, r₂, o₂⟩
  simp only at h₁ h₂
  subst h₁; subst h₂
  intro s
  ext p
  rcases p with ⟨r, t, z⟩
  simp [update, Finset.mem_insert, Finset.mem_filter, Prod.ext_iff]
  aesop

/-- Two removes are filters and commute. -/
theorem commutes_rem_rem {e₁ e₂ : Event α} {x y : α}
    (h₁ : e₁.2.2 = AppOp.remove x) (h₂ : e₂.2.2 = AppOp.remove y) :
    (D α).Commutes e₁ e₂ := by
  rcases e₁ with ⟨t₁, r₁, o₁⟩
  rcases e₂ with ⟨t₂, r₂, o₂⟩
  simp only at h₁ h₂
  subst h₁; subst h₂
  intro s
  ext p
  rcases p with ⟨r, t, z⟩
  simp [update, Finset.mem_filter]
  tauto

/-- An add and a remove of **different** elements commute. -/
theorem commutes_add_rem {e₁ e₂ : Event α} {x y : α}
    (h₁ : e₁.2.2 = AppOp.add x) (h₂ : e₂.2.2 = AppOp.remove y) (hxy : x ≠ y) :
    (D α).Commutes e₁ e₂ := by
  rcases e₁ with ⟨t₁, r₁, o₁⟩
  rcases e₂ with ⟨t₂, r₂, o₂⟩
  simp only at h₁ h₂
  subst h₁; subst h₂
  intro s
  ext p
  rcases p with ⟨r, t, z⟩
  simp [update, Finset.mem_insert, Finset.mem_filter, Prod.ext_iff]
  aesop

/-- An add and a remove of the **same** element do not commute. -/
theorem not_commutes_add_rem {e₁ e₂ : Event α} {x : α}
    (h₁ : e₁.2.2 = AppOp.add x) (h₂ : e₂.2.2 = AppOp.remove x) :
    ¬ (D α).Commutes e₁ e₂ := by
  rcases e₁ with ⟨t₁, r₁, o₁⟩
  rcases e₂ with ⟨t₂, r₂, o₂⟩
  simp only at h₁ h₂
  subst h₁; subst h₂
  intro h
  have := congrArg (fun S => ((r₁, t₁, x) : Record α) ∈ S) (h ∅)
  simp [update, Finset.mem_filter] at this

/-- **The pair the guard exists for.** Two adds of one element by one
replica do not commute: the second replaces the first's record. -/
theorem not_commutes_add_add_same {e₁ e₂ : Event α} {x : α}
    (h₁ : e₁.2.2 = AppOp.add x) (h₂ : e₂.2.2 = AppOp.add x)
    (hr : e₁.2.1 = e₂.2.1) (ht : e₁.1 ≠ e₂.1) : ¬ (D α).Commutes e₁ e₂ := by
  rcases e₁ with ⟨t₁, r₁, o₁⟩
  rcases e₂ with ⟨t₂, r₂, o₂⟩
  simp only at h₁ h₂ hr ht
  subst h₁; subst h₂; subst hr
  intro h
  have := congrArg (fun S => ((r₁, t₂, x) : Record α) ∈ S) (h ∅)
  simp [update, Finset.mem_insert, Finset.mem_filter, Prod.ext_iff,
    Ne.symm ht] at this

/-- **What can fail to commute with an `add x` issued by `r`.** Only a
`remove x`, or an `add x` issued by `r` itself. Both kill the pair
`(r, x)`, which is what the conditions below use. -/
theorem kills_of_not_commutes {e' e'' : Event α} {x : α} {r : Replica}
    (h' : e'.2.2 = AppOp.add x) (hr : e'.2.1 = r)
    (hn : ¬ (D α).Commutes e' e'') : kills r x e'' := by
  rcases e'' with ⟨t'', r'', o''⟩
  cases o'' with
  | add y =>
    by_cases hxy : x = y
    · subst hxy
      by_cases hrr : r'' = r
      · exact ⟨hrr, rfl⟩
      · exact absurd (commutes_add_add h' rfl (by
          simp only [hr]; exact fun h => hrr h.symm)) hn
    · exact absurd (commutes_add_add_ne h' rfl hxy) hn
  | remove y =>
    by_cases hxy : x = y
    · exact hxy.symm
    · exact absurd (commutes_add_rem h' rfl hxy) hn

/-- Conversely, whatever kills the pair `(r, x)` fails to commute with the
`add x` that created it, unless it **is** that event. -/
theorem not_commutes_of_kills {p : Record α} {e : Event α}
    (hne : e ≠ birth p) (hk : kills p.1 p.2.2 e) :
    ¬ (D α).Commutes (birth p) e := by
  rcases p with ⟨r, t, x⟩
  rcases e with ⟨te, re, oe⟩
  cases oe with
  | add y =>
    obtain ⟨hre, hyx⟩ := hk
    simp only at hre hyx
    subst hre; subst hyx
    refine not_commutes_add_add_same (x := y) rfl rfl rfl ?_
    simp only [birth_time]
    intro h
    exact hne (by simp [birth, h])
  | remove y =>
    simp only [kills] at hk
    subst hk
    exact not_commutes_add_rem (x := y) rfl rfl

/-! ## `Laws(D_type)` -/

/-- `rc` is empty on every pair except `remove x` against `add x`. -/
theorem rcOps_iff (o₁ o₂ : AppOp α) :
    (rcOps o₁ o₂ = OrderResult.Fst_then_snd ∨ rcOps o₂ o₁ = OrderResult.Fst_then_snd)
      ↔ (∃ x, (o₁ = .add x ∧ o₂ = .remove x) ∨ (o₁ = .remove x ∧ o₂ = .add x)) := by
  cases o₁ <;> cases o₂ <;>
    simp [rcOps, eq_comm] <;> aesop

/-- The single shape of `rc` edge, at events. -/
theorem rcBefore_iff (a b : Event α) :
    (D α).EventRcBefore a b ↔ ∃ x, a.2.2 = .remove x ∧ b.2.2 = .add x := by
  rcases a with ⟨ta, ra, oa⟩
  rcases b with ⟨tb, rb, ob⟩
  cases oa with
  | add x =>
    cases ob with
    | add y =>
      simp only [Impl.EventRcBefore, Impl.RcBefore, rcOps, Op.op]
      refine ⟨fun hcon => absurd hcon (by simp), ?_⟩
      rintro ⟨z, hz, -⟩
      exact absurd hz (by simp)
    | remove y =>
      simp only [Impl.EventRcBefore, Impl.RcBefore, rcOps, Op.op]
      refine ⟨fun hcon => ?_, ?_⟩
      · split_ifs at hcon
      · rintro ⟨z, hz, -⟩
        exact absurd hz (by simp)
  | remove x =>
    cases ob with
    | add y =>
      simp only [Impl.EventRcBefore, Impl.RcBefore, rcOps, Op.op]
      split_ifs with h
      · subst h; simp
      · refine ⟨fun hcon => absurd hcon (by simp), ?_⟩
        rintro ⟨z, hz, hz'⟩
        simp only [AppOp.remove.injEq] at hz
        simp only [AppOp.add.injEq] at hz'
        exact absurd (hz.trans hz'.symm) h
    | remove y =>
      simp only [Impl.EventRcBefore, Impl.RcBefore, rcOps, Op.op]
      refine ⟨fun hcon => absurd hcon (by simp), ?_⟩
      rintro ⟨z, -, hz⟩
      exact absurd hz (by simp)

/-- **RC-NON-COMM, over concurrent events.** The same-replica pair that
breaks the unguarded law is excluded by `hr`; every pair still in scope is
covered exactly. -/
theorem rc_non_comm : ConcurrentRcNonComm (D α) := by
  intro e₁ e₂ _ht hr
  obtain ⟨t₁, r₁, o₁⟩ := e₁
  obtain ⟨t₂, r₂, o₂⟩ := e₂
  simp only [Impl.rep, Op.rep] at hr
  cases o₁ with
  | add x =>
    cases o₂ with
    | add y =>
      have hc := commutes_add_add (e₁ := ((t₁, r₁, AppOp.add x) : Event α))
          (e₂ := ((t₂, r₂, AppOp.add y) : Event α)) (x := x) (y := y) rfl rfl hr
      simp [Impl.EventRcBefore, Impl.RcBefore, D, rcOps, Op.op, hc]
    | remove y =>
      by_cases hxy : x = y
      · subst hxy
        have hn := not_commutes_add_rem (e₁ := ((t₁, r₁, AppOp.add x) : Event α))
          (e₂ := ((t₂, r₂, AppOp.remove x) : Event α)) (x := x) rfl rfl
        simp [Impl.EventRcBefore, Impl.RcBefore, D, rcOps, Op.op, hn]
      · have hc := commutes_add_rem (e₁ := ((t₁, r₁, AppOp.add x) : Event α))
          (e₂ := ((t₂, r₂, AppOp.remove y) : Event α)) (x := x) (y := y) rfl rfl hxy
        simp [Impl.EventRcBefore, Impl.RcBefore, D, rcOps, Op.op, hc, hxy]
        exact fun h => hxy h.symm
  | remove x =>
    cases o₂ with
    | add y =>
      by_cases hxy : y = x
      · subst hxy
        have hn := not_commutes_add_rem
          (e₁ := ((t₂, r₂, AppOp.add y) : Event α))
          (e₂ := ((t₁, r₁, AppOp.remove y) : Event α)) (x := y) rfl rfl
        have hn' : ¬ (D α).Commutes (t₁, r₁, AppOp.remove y) (t₂, r₂, AppOp.add y) :=
          fun h => hn (fun s => (h s).symm)
        simp [Impl.EventRcBefore, Impl.RcBefore, D, rcOps, Op.op, hn']
      · have hc := commutes_add_rem
          (e₁ := ((t₂, r₂, AppOp.add y) : Event α))
          (e₂ := ((t₁, r₁, AppOp.remove x) : Event α)) (x := y) (y := x) rfl rfl hxy
        have hc' : (D α).Commutes (t₁, r₁, AppOp.remove x) (t₂, r₂, AppOp.add y) :=
          fun s => (hc s).symm
        simp only [Impl.EventRcBefore, Impl.RcBefore, D, rcOps, Op.op]
        simp [hc', hxy]
        exact fun h => hxy h.symm
    | remove y =>
      have hc := commutes_rem_rem (e₁ := ((t₁, r₁, AppOp.remove x) : Event α))
          (e₂ := ((t₂, r₂, AppOp.remove y) : Event α)) (x := x) (y := y) rfl rfl
      simp [Impl.EventRcBefore, Impl.RcBefore, D, rcOps, Op.op, hc]

/-- **NO-RC-CHAIN.** Every edge runs `remove x --rc--> add x`, and an `add`
has no outgoing edge, so two edges cannot meet. -/
theorem no_rc_chain (o₁ o₂ o₃ : (itype α).OType) :
    ¬ ((D α).RcBefore o₁ o₂ ∧ (D α).RcBefore o₂ o₃) := by
  rintro ⟨h₁, h₂⟩
  cases o₁ <;> cases o₂ <;> cases o₃ <;>
    simp [Impl.RcBefore, rcOps] at h₁ h₂ <;> aesop

/-! ## COND-COMM

`rc` has only one shape of edge, `remove x --rc--> add x`, so in COND-COMM
`e` is a remove and `e'` the matching add. Swapping them changes the state
by exactly the one record `e'` contributes, and the absorber `e''` is
whatever fails to commute with that add: another `remove x`, or an `add x`
from the issuer's own replica. Both wipe that record, so the two orders
agree once `e''` has run.

`EqOff` is the invariant that makes this precise: agreement outside one
replica's records for one element. -/

/-- Two states agree outside the records of replica `r` for element `x`. -/
def EqOff (r : Replica) (x : α) (a b : State α) : Prop :=
  ∀ p : Record α, ¬ (p.1 = r ∧ p.2.2 = x) → (p ∈ a ↔ p ∈ b)

theorem eqOff_update {r : Replica} {x : α} {a b : State α} (h : EqOff r x a b)
    (e : Event α) : EqOff r x (update a e) (update b e) := by
  intro p hp
  rcases p with ⟨pr, pt, pz⟩
  rcases e with ⟨t, er, o⟩
  cases o <;>
    simp [update, Finset.mem_insert, Finset.mem_filter, Prod.ext_iff, h _ hp]

theorem eqOff_applyList {r : Replica} {x : α} :
    ∀ (pi : List (Event α)) {a b : State α}, EqOff r x a b →
      EqOff r x ((D α).applyList a pi) ((D α).applyList b pi)
  | [], _, _, h => h
  | e :: rest, _, _, h => eqOff_applyList rest (eqOff_update h e)

/-- An absorber that settles replica `r`'s records for `x` collapses the
difference `EqOff` allows. -/
theorem update_eq_of_eqOff {r : Replica} {x : α} {a b : State α}
    (h : EqOff r x a b) {e'' : Event α}
    (hsettle : ∀ p : Record α, p.1 = r → p.2.2 = x →
      (p ∈ update a e'' ↔ p ∈ update b e'')) :
    update a e'' = update b e'' := by
  ext p
  by_cases hp : p.1 = r ∧ p.2.2 = x
  · exact hsettle p hp.1 hp.2
  · rcases p with ⟨pr, pt, pz⟩
    rcases e'' with ⟨t, er, o⟩
    cases o <;>
      simp [update, Finset.mem_insert, Finset.mem_filter, Prod.ext_iff, h _ hp]

/-- Swapping a `remove x` past the matching `add x` changes the state by
exactly the one record the add contributes. -/
theorem eqOff_swap {sigma : State α} {e e' : Event α} {x : α} {r : Replica}
    (he : e.2.2 = AppOp.remove x) (he' : e'.2.2 = AppOp.add x) (hr : e'.2.1 = r) :
    EqOff r x (update (update sigma e') e) (update (update sigma e) e') := by
  intro p hp
  rcases p with ⟨pr, pt, pz⟩
  rcases e with ⟨t, er, o⟩
  rcases e' with ⟨t', er', o'⟩
  simp only at he he' hr
  subst he; subst he'; subst hr
  simp [update, Finset.mem_insert, Finset.mem_filter, Prod.ext_iff] at hp ⊢
  aesop

/-- **COND-COMM**, with no guard. Once the absorber has run, the record that
the swap moved is settled identically on both sides. -/
theorem cond_comm : UniformCondComm (D α) := by
  intro sigma e e' e'' pi hrc hn
  obtain ⟨x, hex, he'x⟩ : ∃ x, e.2.2 = AppOp.remove x ∧ e'.2.2 = AppOp.add x := by
    obtain ⟨x, hx, hx'⟩ := (rcBefore_iff e e').mp hrc
    exact ⟨x, hx, hx'⟩
  have hswap := eqOff_swap (sigma := sigma) (r := e'.2.1) hex he'x rfl
  show update ((D α).applyList (update (update sigma e') e) pi) e''
      = update ((D α).applyList (update (update sigma e) e') pi) e''
  refine update_eq_of_eqOff (eqOff_applyList pi hswap) ?_
  intro p hp1 hp2
  have hk := kills_of_not_commutes (r := e'.2.1) he'x rfl hn
  rcases e'' with ⟨t'', r'', o''⟩
  rcases p with ⟨pr, pt, pz⟩
  simp only at hp1 hp2
  subst hp1; subst hp2
  cases o'' with
  | add y =>
    obtain ⟨hr'', hy⟩ := hk
    simp only at hr'' hy
    subst hy
    simp [update, Finset.mem_insert, Finset.mem_filter, Prod.ext_iff, hr'']
  | remove y =>
    simp only [kills] at hk
    subst hk
    simp [update, Finset.mem_filter]

/-- **`Laws(D_type)` for the efficient OR-set.** -/
theorem laws : Laws (D α) :=
  ⟨rcNonComm_of_exact no_rc_chain rc_non_comm, no_rc_chain,
    fun sigma e e' e'' pi _ _ => cond_comm sigma e e' e'' pi⟩

/-- **Concurrent events carrying one operation commute.** Two `add x` or
two `remove x` from different replicas do, and that is every such pair. This
is the one fact `Laws(D_type)` leaves out; the row has it already from the
exact equivalence it proved above. -/
theorem equal_op_commutes : EqualOpCommutes (D α) :=
  EqualOpCommutes.of_concurrent no_rc_chain rc_non_comm

/-! ## Canonical states contain exactly the live records

The OR-set's argument, with one clause added. A record `(r, t, x)` is born
by a single event, the `add x` that `r` issued at `t`, and it is killed by
anything in the set that birth observes which drops the pair `(r, x)`: a
`remove x`, as in the OR-set, **or a later `add x` from `r` itself**. That
second kind of killer is the whole difference between the two rows, and it
is why `kills` has two cases where the OR-set's `Survives` has one. -/

/-- `pi(sigma0)`, the state after replaying a list. -/
abbrev Run (ops : List (Event α)) : State α :=
  applySeq (D α).toMRDTSig.toUpdateSig (D α).toMRDTSig.init ops

/-- Something in `E` that the birth of `p` sees kills its pair. -/
def Killed (C : Ctx (D α)) (E : Set (Event α)) (p : Record α) : Prop :=
  ∃ z ∈ E, C.vis (birth p) z ∧ kills p.1 p.2.2 z

/-- Nothing in `E` that the birth of `p` sees kills its pair. -/
def Survives (C : Ctx (D α)) (E : Set (Event α)) (p : Record α) : Prop :=
  ¬ Killed C E p

/-- The record `p` is live in `E`: it was born by an event of `E` that no
killer in `E` observes. -/
def Live (C : Ctx (D α)) (E : Set (Event α)) (p : Record α) : Prop :=
  birth p ∈ E ∧ Survives C E p

theorem killed_union (C : Ctx (D α)) (A B : Set (Event α)) (p : Record α) :
    Killed C (A ∪ B) p ↔ Killed C A p ∨ Killed C B p := by
  simp only [Killed, Set.mem_union]
  aesop

theorem killed_mono {C : Ctx (D α)} {A B : Set (Event α)} (h : A ⊆ B)
    {p : Record α} (hk : Killed C A p) : Killed C B p := by
  obtain ⟨z, hz, hv, hkz⟩ := hk
  exact ⟨z, h hz, hv, hkz⟩

/-- A fold holds `p` exactly when the birth of `p` occurs in the list and
nothing after it kills the pair. -/
theorem mem_run_iff_suffix (p : Record α) (ops : List (Event α)) :
    p ∈ Run ops ↔ ∃ pre post, ops = pre ++ birth p :: post ∧
      ∀ e ∈ post, ¬ kills p.1 p.2.2 e := by
  show p ∈ ops.foldl update (∅ : State α) ↔ _
  induction ops using List.reverseRecOn with
  | nil => simp
  | append_singleton ops e ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, mem_update_iff, ih]
    constructor
    · rintro (he | ⟨⟨pre, post, hops, hpost⟩, hne⟩)
      · exact ⟨ops, [], by simp [he], by simp⟩
      · refine ⟨pre, post ++ [e], ?_, ?_⟩
        · simp [hops, List.append_assoc]
        · intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact hpost a ha
          · simpa using (List.mem_singleton.mp ha ▸ hne)
    · rintro ⟨pre, post, hops, hpost⟩
      by_cases hp : post = []
      · subst post
        have he := congrArg List.getLast? hops
        simp at he
        exact Or.inl he
      · let post' := post.dropLast
        let last := post.getLast hp
        have hsplit : post = post' ++ [last] := (List.dropLast_concat_getLast hp).symm
        rw [hsplit] at hops hpost
        have heq : ops = pre ++ birth p :: post' ∧ e = last := by
          have hh : ops ++ [e] = (pre ++ birth p :: post') ++ [last] := by
            simpa only [List.append_assoc, List.cons_append] using hops
          simpa using List.append_inj' hh (by simp)
        rcases heq with ⟨hop, he⟩
        subst e
        exact Or.inr ⟨⟨pre, post', hop, fun a ha => hpost a (List.mem_append_left _ ha)⟩,
          hpost last (by simp)⟩

/-- **Fact 1.** Any replay of `E` that respects `lo^C_E` contains exactly
the live records, so the state does not depend on which replay was taken.

Left to right: a killer the birth sees is `lo^C_E`-above the birth, so it
cannot have been replayed before it. Right to left: a killer replayed after
the birth is either seen by it, which contradicts liveness, or `vis`-below
it, or concurrent with it, and in the last case the killer must be a
`remove`, since one replica's events are never concurrent, so `rc` orders it
first with no absorber available. -/
theorem mem_run_iff_live {C : Ctx (D α)} {E : Set (Event α)}
    (hvs : VisStrict (D α) C) (hsup : SupportedOn (D α) C E)
    {ops : List (Event α)} (hp : listPermOf ops E)
    (hr : respects ops (paperOrder (policy (D α)) C E)) (p : Record α) :
    p ∈ Run ops ↔ Live C E p := by
  obtain ⟨htr, hirr⟩ := hvs
  rw [mem_run_iff_suffix]
  constructor
  · rintro ⟨pre, post, hπ, hpost⟩
    have hb : birth p ∈ E := (hp.2 _).mp (by rw [hπ]; simp)
    refine ⟨hb, ?_⟩
    rintro ⟨e, heE, hv, hk⟩
    have hne : e ≠ birth p := by
      intro heq; rw [heq] at hv; exact hirr _ hv
    have hpo : paperOrder (policy (D α)) C E (birth p) e :=
      Or.inl ⟨hv, not_commutes_of_kills hne hk⟩
    have hrp : (pre ++ birth p :: post).Pairwise
        (fun a b => ¬ paperOrder (policy (D α)) C E b a) := by
      rw [← hπ]; exact hr
    have hem : e ∈ pre ++ birth p :: post := by
      rw [← hπ]; exact (hp.2 e).mpr heE
    rcases List.mem_append.mp hem with hepre | hepost
    · exact (List.pairwise_append.mp hrp).2.2 e hepre (birth p) (by simp) hpo
    · rcases List.mem_cons.mp hepost with heq | hepost'
      · exact hne heq
      · exact hpost e hepost' hk
  · rintro ⟨hb, hnd⟩
    obtain ⟨pre, post, hπ⟩ := List.mem_iff_append.mp ((hp.2 _).mpr hb)
    refine ⟨pre, post, hπ, ?_⟩
    intro e hepost hk
    have heE : e ∈ E := (hp.2 e).mp (by rw [hπ]; simp [hepost])
    have hne : e ≠ birth p := by
      have hnd' := hp.1
      rw [hπ, List.nodup_append, List.nodup_cons] at hnd'
      intro heq
      exact hnd'.2.1.1 (heq ▸ hepost)
    have hnc : ¬ (D α).Commutes (birth p) e := not_commutes_of_kills hne hk
    have hnv : ¬ C.vis (birth p) e := fun hv => hnd ⟨e, heE, hv, hk⟩
    have hrp : (pre ++ birth p :: post).Pairwise
        (fun a b => ¬ paperOrder (policy (D α)) C E b a) := by
      rw [← hπ]; exact hr
    have hno := (List.pairwise_cons.mp (List.pairwise_append.mp hrp).2.1).1 e hepost
    by_cases hv2 : C.vis e (birth p)
    · exact hno (Or.inl ⟨hv2, fun hc => hnc (fun s => (hc s).symm)⟩)
    · cases hoe : e.2.2 with
      | add y =>
        have hk' : e.2.1 = p.1 ∧ y = p.2.2 := by
          simpa only [kills, hoe] using hk
        obtain ⟨re', se, hLe, hse⟩ := hsup e heE
        obtain ⟨rb, sb, hLb, hsb⟩ := hsup (birth p) hb
        rcases C.vis_total_same_replica hLe hse hLb hsb hne hk'.1 with h | h
        · exact hv2 h
        · exact hnv h
      | remove y =>
        have hy : y = p.2.2 := by simpa only [kills, hoe] using hk
        have hpol : (policy (D α)).before e.op (birth p).op := by
          refine (rcBefore_iff e (birth p)).mpr ⟨p.2.2, ?_, rfl⟩
          rw [hoe, hy]
        refine hno (Or.inr ⟨hv2, hnv, hpol, ?_⟩)
        rintro ⟨c, hcE, hvc, hncc⟩
        exact hnd ⟨c, hcE, hvc, kills_of_not_commutes rfl rfl hncc⟩

/-- The canonical state of a supported event set holds exactly its live
records. -/
theorem canonical_mem_iff {C : Ctx (D α)} {E : Set (Event α)} {s : State α}
    (hvs : VisStrict (D α) C) (hsup : SupportedOn (D α) C E)
    (hs : IsPaperCan (D α) C E s) (p : Record α) : p ∈ s ↔ Live C E p := by
  obtain ⟨ops, hp, hr, hf⟩ := hs
  rw [← show Run ops = s from hf]
  exact mem_run_iff_live hvs hsup hp hr p

/-- **Fact 2.** Nothing to prove. The record carries the replica and the
timestamp of its own `add`, so `birth` determines the event that made it;
the OR-set needs `live_iff_fixed_add` here because its records do not. -/
theorem live_iff_birth {C : Ctx (D α)} {E : Set (Event α)} (p : Record α) :
    Live C E p ↔ birth p ∈ E ∧ Survives C E p := Iff.rfl

/-- **Fact 3.** Liveness over the union is the Boolean that `merge`
computes. Causal closure is what is used: the killer of a live record never
commutes with its birth, so a branch that holds the killer holds the birth
too. -/
theorem live_join {C : Ctx (D α)} {E₁ E₂ : Set (Event α)}
    (hvs : VisStrict (D α) C)
    (c₁ : WeaklyClosed (D α) C E₁) (c₂ : WeaklyClosed (D α) C E₂)
    (p : Record α) :
    Live C (E₁ ∪ E₂) p ↔
      (Live C (E₁ ∩ E₂) p ∧ Live C E₁ p ∧ Live C E₂ p) ∨
      (Live C E₁ p ∧ ¬ Live C (E₁ ∩ E₂) p) ∨
      (Live C E₂ p ∧ ¬ Live C (E₁ ∩ E₂) p) := by
  have key : ∀ S : Set (Event α), WeaklyClosed (D α) C S →
      Killed C S p → birth p ∈ S := by
    rintro S hcl ⟨z, hz, hv, hk⟩
    have hne : z ≠ birth p := by
      intro heq; rw [heq] at hv; exact hvs.2 _ hv
    exact hcl _ z hv (not_commutes_of_kills hne hk) hz
  have k₁ := key E₁ c₁
  have k₂ := key E₂ c₂
  have ki₁ : Killed C (E₁ ∩ E₂) p → Killed C E₁ p :=
    killed_mono Set.inter_subset_left
  have ki₂ : Killed C (E₁ ∩ E₂) p → Killed C E₂ p :=
    killed_mono Set.inter_subset_right
  simp only [Live, Survives, Set.mem_union, Set.mem_inter_iff, killed_union]
  tauto

/-! ## VC1 and VC2

Two of the five hold at arbitrary states for this `merge`, so they are set
identities with no premises, exactly as the OR-set's are. -/

/-- `merge(l,a,b) = merge(l,b,a)` at any states. This is **VC1** exactly:
the paper states it over arbitrary states too. -/
theorem vc1_merge_comm (l a b : (D α).Sigma) :
    (D α).merge l a b = (D α).merge l b a := merge_comm l a b

/-- `merge(sigma0, sigma0, s) = s` at any `s`. **VC2** asks for it only at a
canonical `s`. -/
theorem vc2_merge_init (s : (D α).Sigma) :
    (D α).merge (D α).sigma0 (D α).sigma0 s = s := merge_init s

/-! ## The three canonical conditions

The states VC3, VC4 and VC5 mention are canonical for event sets built from
`E1`, `E2` and `down(e)`. Each nest of merges is read pointwise through
`canonical_mem_iff` and resolved by `live_join`, this row's description of
liveness over a union.

`mergeProp` below is the Boolean `merge` computes at a record. Writing both
`merge` and `live_join` in that one shape turns VC3 and VC5 into chains of
rewrites with no propositional search at all, exactly as in the OR-set. -/

/-- The Boolean `merge` computes at a single record: keep it when the base
and both branches have it, or when one branch has it and the base does
not. -/
def mergeProp (L B C : Prop) : Prop := (L ∧ B ∧ C) ∨ (B ∧ ¬ L) ∨ (C ∧ ¬ L)

theorem mem_merge (l a b : (D α).Sigma) (p : Record α) :
    p ∈ (D α).merge l a b ↔ mergeProp (p ∈ l) (p ∈ a) (p ∈ b) := by
  change p ∈ merge l a b ↔ _
  simp only [merge, mergeProp, Finset.mem_union, Finset.mem_inter,
    Finset.mem_sdiff]
  tauto

/-- `mem_update_iff` in the tuple's own notation. -/
theorem mem_do (s : (D α).Sigma) (e : Event α) (p : Record α) :
    p ∈ (D α).do_ s e ↔ e = birth p ∨ (p ∈ s ∧ ¬ kills p.1 p.2.2 e) :=
  mem_update_iff p s e

/-- `live_join` in `mergeProp` shape. -/
theorem live_merge {C : Ctx (D α)} {E₁ E₂ : Set (Event α)}
    (hvs : VisStrict (D α) C)
    (c₁ : WeaklyClosed (D α) C E₁) (c₂ : WeaklyClosed (D α) C E₂)
    (p : Record α) :
    Live C (E₁ ∪ E₂) p
      ↔ mergeProp (Live C (E₁ ∩ E₂) p) (Live C E₁ p) (Live C E₂ p) :=
  live_join hvs c₁ c₂ p

/-- `e(can(down(e) \ {e})) = can(down(e))`: the downset's own peel. -/
theorem isCan_downset {C : Ctx (D α)} {m : State α} {e : Event α}
    (hvs : VisStrict (D α) C)
    (hm : IsPaperCan (D α) C (downset C e \ {e}) m) :
    IsPaperCan (D α) C (downset C e) ((D α).do_ m e) :=
  isPaperCan_snoc self_mem_downset (paperMaximalOn_downset hvs e) hm

/-- **VC3** LOCAL-REDISTRIBUTE, proved for this row.

Both sides are liveness over `E1 u E2`. The left reaches it through
`E1 = (E1 \ {e}) u down(e)` and then `E1 u E2`; the right through
`(E1 u E2) \ {e} = (E1 \ {e}) u E2` and then
`(E1 u E2) = ((E1 u E2) \ {e}) u down(e)`. Four instances of `live_merge`,
and the equation falls out by rewriting. -/
theorem vc3_local_redistribute :
    ∀ (C : Ctx (D α)) (E₁ E₂ : Set (Event α)) (l m x y : (D α).Sigma)
      (e : Event α),
      VisStrict (D α) C →
      SupportedOn (D α) C E₁ → SupportedOn (D α) C E₂ →
      WeaklyClosed (D α) C E₁ → WeaklyClosed (D α) C E₂ →
      e ∈ E₁ → e ∉ E₂ → PaperMaximalOn (D α) C (E₁ ∪ E₂) e →
      IsPaperCan (D α) C (E₁ ∩ E₂) l →
      IsPaperCan (D α) C (downset C e \ {e}) m →
      IsPaperCan (D α) C (E₁ \ {e}) x →
      IsPaperCan (D α) C E₂ y →
      (D α).merge l ((D α).merge m x ((D α).do_ m e)) y
        = (D α).merge m ((D α).merge l x y) ((D α).do_ m e) := by
  intro C E₁ E₂ l m x y e hvs h₁ h₂ hc₁ hc₂ he₁ he₂ hmax hl hm hx hy
  have hdsub : downset C e ⊆ E₁ := downset_subset hc₁ he₁
  have hdm := isCan_downset hvs hm
  have hsupU : SupportedOn (D α) C (E₁ ∪ E₂) := fun a ha => ha.elim (h₁ a) (h₂ a)
  have hdsupp : SupportedOn (D α) C (downset C e) := fun a ha => h₁ a (hdsub ha)
  have hcld : WeaklyClosed (D α) C (downset C e) :=
    fun a b => downset_closed (C := C) (e := e) a b
  have hclU : WeaklyClosed (D α) C (E₁ ∪ E₂) := weaklyClosed_union hc₁ hc₂
  have hclx : WeaklyClosed (D α) C (E₁ \ {e}) :=
    weaklyClosed_diff_of_max hc₁ Set.subset_union_left hmax
  have hclU' : WeaklyClosed (D α) C ((E₁ ∪ E₂) \ {e}) :=
    weaklyClosed_diff_of_max hclU Set.Subset.rfl hmax
  have i₁ : (E₁ \ {e}) ∩ downset C e = downset C e \ {e} := by
    ext z; exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hdsub h.1, h.2⟩, h.1⟩⟩
  have u₁ : (E₁ \ {e}) ∪ downset C e = E₁ := by
    ext z; constructor
    · rintro (⟨hz, -⟩ | hz)
      · exact hz
      · exact hdsub hz
    · intro hz
      by_cases hze : z = e
      · exact Or.inr (Or.inl hze)
      · exact Or.inl ⟨hz, hze⟩
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
  have i₃ : ((E₁ ∪ E₂) \ {e}) ∩ downset C e = downset C e \ {e} := by
    ext z
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨Or.inl (hdsub h.1), h.2⟩, h.1⟩⟩
  have u₃ : ((E₁ ∪ E₂) \ {e}) ∪ downset C e = E₁ ∪ E₂ := by
    ext z; constructor
    · rintro (⟨hz, -⟩ | hz)
      · exact hz
      · exact Or.inl (hdsub hz)
    · intro hz
      by_cases hze : z = e
      · exact Or.inr (Or.inl hze)
      · exact Or.inl ⟨hz, hze⟩
  ext p
  have jA := live_merge hvs hclx hcld p
  rw [i₁, u₁] at jA
  have jB := live_merge hvs hc₁ hc₂ p
  have jC := live_merge hvs hclx hc₂ p
  rw [i₂, u₂] at jC
  have jD := live_merge hvs hclU' hcld p
  rw [i₃, u₃] at jD
  rw [mem_merge, mem_merge, mem_merge, mem_merge,
    canonical_mem_iff hvs (fun a ha => h₁ a ha.1) hl p,
    canonical_mem_iff hvs (fun a ha => hdsupp a ha.1) hm p,
    canonical_mem_iff hvs (fun a ha => h₁ a ha.1) hx p,
    canonical_mem_iff hvs h₂ hy p,
    canonical_mem_iff hvs hdsupp hdm p, ← jA, ← jB, ← jC, ← jD]

/-- The one fact about this row that **VC4** needs: a record that survives
`U \ {e}` and whose pair `e` kills also survives `down(e) \ {e}`.

Its birth must be seen by `e`. If `e` saw nothing of it, `lo^C_U` would have
an edge out of `e`: a visibility edge when `e` sees the birth, and otherwise
either `vis`-totality on one replica, when `e` is the replacing `add`, or
the `rc` edge `rem x --rc--> add x`, whose absorber clause can only be met
by a further killer in `U`, which would have killed the record in `U \ {e}`
as well. Either way `e` is not maximal. -/
theorem live_of_killed {C : Ctx (D α)} {U : Set (Event α)} {As Bs : State α}
    {e : Event α} (hvs : VisStrict (D α) C)
    (hUsub : SupportedOn (D α) C U) (hUcl : WeaklyClosed (D α) C U)
    (heU : e ∈ U) (hmax : PaperMaximalOn (D α) C U e)
    (hA : IsPaperCan (D α) C (U \ {e}) As)
    (hB : IsPaperCan (D α) C (downset C e \ {e}) Bs)
    (p : Record α) (hpA : p ∈ As) (hk : kills p.1 p.2.2 e) : p ∈ Bs := by
  have hdsub : downset C e ⊆ U := downset_subset hUcl heU
  obtain ⟨hbU, hsurv⟩ :=
    (canonical_mem_iff hvs (fun a ha => hUsub a ha.1) hA p).mp hpA
  have hne : e ≠ birth p := fun heq => hbU.2 heq.symm
  have hnc : ¬ (D α).Commutes (birth p) e := not_commutes_of_kills hne hk
  have hnv2 : ¬ C.vis e (birth p) := fun hv2 =>
    hmax (birth p) hbU.1 (fun heq => hne heq.symm)
      (Or.inl ⟨hv2, fun hc => hnc (fun s => (hc s).symm)⟩)
  have hvis : C.vis (birth p) e := by
    by_contra hnv
    cases hoe : e.2.2 with
    | add y =>
      have hk' : e.2.1 = p.1 ∧ y = p.2.2 := by
        simpa only [kills, hoe] using hk
      obtain ⟨re', se, hLe, hse⟩ := hUsub e heU
      obtain ⟨rb, sb, hLb, hsb⟩ := hUsub (birth p) hbU.1
      rcases C.vis_total_same_replica hLe hse hLb hsb hne hk'.1 with h | h
      · exact hnv2 h
      · exact hnv h
    | remove y =>
      have hy : y = p.2.2 := by simpa only [kills, hoe] using hk
      have hpol : (policy (D α)).before e.op (birth p).op := by
        refine (rcBefore_iff e (birth p)).mpr ⟨p.2.2, ?_, rfl⟩
        rw [hoe, hy]
      refine hmax (birth p) hbU.1 (fun heq => hne heq.symm)
        (Or.inr ⟨hnv2, hnv, hpol, ?_⟩)
      rintro ⟨c, hcU, hvc, hncc⟩
      have hcne : c ≠ e := fun heq => hnv (heq ▸ hvc)
      exact hsurv ⟨c, ⟨hcU, hcne⟩, hvc, kills_of_not_commutes rfl rfl hncc⟩
  refine (canonical_mem_iff hvs (fun a ha => hUsub a (hdsub ha.1)) hB p).mpr ?_
  refine ⟨⟨Or.inr (Relation.TransGen.single ⟨hvis, hnc⟩), hbU.2⟩, ?_⟩
  rintro ⟨z, hz, hv, hkz⟩
  exact hsurv ⟨z, ⟨hdsub hz.1, hz.2⟩, hv, hkz⟩

/-- **VC4** CAUSAL-DELTA, proved for this row rather than derived from the
join lemma. Two facts close it: `e` cannot already have contributed the
record it is about to add, and a record `e` kills that is live in
`U \ {e}` is live in `down(e) \ {e}` as well. -/
theorem vc4_causal_delta :
    ∀ (C : Ctx (D α)) (U : Set (Event α)) (As Bs : (D α).Sigma) (e : Event α),
      VisStrict (D α) C →
      SupportedOn (D α) C U → WeaklyClosed (D α) C U →
      e ∈ U → PaperMaximalOn (D α) C U e →
      IsPaperCan (D α) C (U \ {e}) As →
      IsPaperCan (D α) C (downset C e \ {e}) Bs →
      (D α).merge Bs As ((D α).do_ Bs e) = (D α).do_ As e := by
  intro C U As Bs e hvs hUsub hUcl heU hmax hA hB
  have hdsub : downset C e ⊆ U := downset_subset hUcl heU
  have hβ : ∀ p : Record α, e = birth p → p ∉ Bs := by
    intro p hβp hmem
    exact ((canonical_mem_iff hvs
      (fun a ha => hUsub a (hdsub ha.1)) hB p).mp hmem).1.2 hβp.symm
  have hkey : ∀ p : Record α, p ∈ As → kills p.1 p.2.2 e → p ∈ Bs :=
    fun p hpA hk => live_of_killed hvs hUsub hUcl heU hmax hA hB p hpA hk
  ext p
  have h1 := hβ p
  have h2 := hkey p
  rw [mem_merge, mem_do, mem_do]
  simp only [mergeProp]
  tauto

/-- **VC5** REDISTRIBUTE, proved for this row.

`e` lies in both branches, so each of `E1 n E2`, `E1` and `E2` is its own
`\ {e}` part joined with `down(e)`: three peels. The left side is then
liveness over `E1 u E2` directly. The right side reaches the same place
through `(E1 u E2) \ {e} = (E1 \ {e}) u (E2 \ {e})` and one further
peel. -/
theorem vc5_redistribute :
    ∀ (C : Ctx (D α)) (E₁ E₂ : Set (Event α)) (x₀ x₁ x₂ m : (D α).Sigma)
      (e : Event α),
      VisStrict (D α) C →
      SupportedOn (D α) C E₁ → SupportedOn (D α) C E₂ →
      WeaklyClosed (D α) C E₁ → WeaklyClosed (D α) C E₂ →
      e ∈ E₁ → e ∈ E₂ → PaperMaximalOn (D α) C (E₁ ∪ E₂) e →
      IsPaperCan (D α) C ((E₁ ∩ E₂) \ {e}) x₀ →
      IsPaperCan (D α) C (downset C e \ {e}) m →
      IsPaperCan (D α) C (E₁ \ {e}) x₁ →
      IsPaperCan (D α) C (E₂ \ {e}) x₂ →
      (D α).merge ((D α).merge m x₀ ((D α).do_ m e))
          ((D α).merge m x₁ ((D α).do_ m e))
          ((D α).merge m x₂ ((D α).do_ m e))
        = (D α).merge m ((D α).merge x₀ x₁ x₂) ((D α).do_ m e) := by
  intro C E₁ E₂ x₀ x₁ x₂ m e hvs h₁ h₂ hc₁ hc₂ he₁ he₂ hmax hx₀ hm hx₁ hx₂
  have hdsub₁ : downset C e ⊆ E₁ := downset_subset hc₁ he₁
  have hdsub₂ : downset C e ⊆ E₂ := downset_subset hc₂ he₂
  have hdm := isCan_downset hvs hm
  have hsupU : SupportedOn (D α) C (E₁ ∪ E₂) := fun a ha => ha.elim (h₁ a) (h₂ a)
  have hdsupp : SupportedOn (D α) C (downset C e) := fun a ha => h₁ a (hdsub₁ ha)
  have hcld : WeaklyClosed (D α) C (downset C e) :=
    fun a b => downset_closed (C := C) (e := e) a b
  have hclU : WeaklyClosed (D α) C (E₁ ∪ E₂) := weaklyClosed_union hc₁ hc₂
  have hclI : WeaklyClosed (D α) C (E₁ ∩ E₂) := by
    rintro a b hv hnc ⟨hb₁, hb₂⟩; exact ⟨hc₁ a b hv hnc hb₁, hc₂ a b hv hnc hb₂⟩
  have hcl₀ : WeaklyClosed (D α) C ((E₁ ∩ E₂) \ {e}) :=
    weaklyClosed_diff_of_max hclI (fun z hz => Or.inl hz.1) hmax
  have hcl₁ : WeaklyClosed (D α) C (E₁ \ {e}) :=
    weaklyClosed_diff_of_max hc₁ Set.subset_union_left hmax
  have hcl₂ : WeaklyClosed (D α) C (E₂ \ {e}) :=
    weaklyClosed_diff_of_max hc₂ Set.subset_union_right hmax
  have hclU' : WeaklyClosed (D α) C ((E₁ ∪ E₂) \ {e}) :=
    weaklyClosed_diff_of_max hclU Set.Subset.rfl hmax
  have peelI : ∀ F : Set (Event α), downset C e ⊆ F →
      (F \ {e}) ∩ downset C e = downset C e \ {e} := by
    intro F hsub; ext z
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hsub h.1, h.2⟩, h.1⟩⟩
  have peelU : ∀ F : Set (Event α), downset C e ⊆ F →
      (F \ {e}) ∪ downset C e = F := by
    intro F hsub; ext z; constructor
    · rintro (⟨hz, -⟩ | hz)
      · exact hz
      · exact hsub hz
    · intro hz
      by_cases hze : z = e
      · exact Or.inr (Or.inl hze)
      · exact Or.inl ⟨hz, hze⟩
  have hdsubI : downset C e ⊆ E₁ ∩ E₂ := fun z hz => ⟨hdsub₁ hz, hdsub₂ hz⟩
  have hdsubU : downset C e ⊆ E₁ ∪ E₂ := fun z hz => Or.inl (hdsub₁ hz)
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
  ext p
  have jP₀ := live_merge hvs hcl₀ hcld p
  rw [peelI _ hdsubI, peelU _ hdsubI] at jP₀
  have jP₁ := live_merge hvs hcl₁ hcld p
  rw [peelI _ hdsub₁, peelU _ hdsub₁] at jP₁
  have jP₂ := live_merge hvs hcl₂ hcld p
  rw [peelI _ hdsub₂, peelU _ hdsub₂] at jP₂
  have jU := live_merge hvs hc₁ hc₂ p
  have jM := live_merge hvs hcl₁ hcl₂ p
  rw [iM, uM] at jM
  have jD := live_merge hvs hclU' hcld p
  rw [peelI _ hdsubU, peelU _ hdsubU] at jD
  rw [mem_merge, mem_merge, mem_merge, mem_merge, mem_merge, mem_merge,
    canonical_mem_iff hvs (fun a ha => h₁ a ha.1.1) hx₀ p,
    canonical_mem_iff hvs (fun a ha => hdsupp a ha.1) hm p,
    canonical_mem_iff hvs (fun a ha => h₁ a ha.1) hx₁ p,
    canonical_mem_iff hvs (fun a ha => h₂ a ha.1) hx₂ p,
    canonical_mem_iff hvs hdsupp hdm p,
    ← jP₀, ← jP₁, ← jP₂, ← jU, ← jM, ← jD]

/-- **VC1 to VC5** of Section 5, read at `lo^C_E`. VC1 and VC2 are instances
of the two equations above; the other three are already stated
canonically. -/
theorem joinLaws : PaperJoinLaws (D α) where
  vc1_merge_comm := EfficientORSet.vc1_merge_comm
  vc2_merge_init := fun _ _ s _ _ _ => EfficientORSet.vc2_merge_init s
  vc3_local_redistribute := fun C E₁ E₂ l m x y e _ =>
    EfficientORSet.vc3_local_redistribute C E₁ E₂ l m x y e
  vc4_causal_delta := fun C U A B e _ =>
    EfficientORSet.vc4_causal_delta C U A B e
  vc5_redistribute := fun C E₁ E₂ x₀ x₁ x₂ m e _ =>
    EfficientORSet.vc5_redistribute C E₁ E₂ x₀ x₁ x₂ m e

/-! ## The execution order

`rc` is the implementation's, and the framework's execution induction needs
an order that relates **every** non-commuting pair. This is that order: `rc`
together with the one pair `rc` cannot describe, two `add x` events from one
replica, taken in timestamp order. It is a proof device and appears nowhere
in the tuple, in `Laws(D_type)`, or in any of the five conditions. -/

/-- The relation the execution order carries. -/
def ExBefore (a b : Event α) : Prop :=
  (∃ x, a.2.2 = .remove x ∧ b.2.2 = .add x) ∨
    (∃ x, a.2.2 = .add x ∧ b.2.2 = .add x ∧ a.2.1 = b.2.1 ∧ a.1 < b.1)

open Classical in
/-- The execution order itself. -/
noncomputable def exEventOrder : EventOrder (D α).toMRDTSig.toUpdateSig where
  order a b :=
    if ExBefore a b then OrderResult.Fst_then_snd
    else if ExBefore b a then OrderResult.Snd_then_fst
    else OrderResult.Either

theorem exBefore_iff (a b : Event α) :
    (exEventOrder (α := α)).Before a b ↔ ExBefore a b := by
  simp only [EventOrder.Before, exEventOrder]
  split_ifs with h₁ h₂ <;> simp [h₁]

/-- Whatever the execution order relates does not commute. -/
theorem not_commutes_of_exBefore {a b : Event α} (h : ExBefore a b) :
    ¬ (D α).Commutes a b := by
  rcases h with ⟨x, ha, hb⟩ | ⟨x, ha, hb, hr, ht⟩
  · intro hc
    exact not_commutes_add_rem (e₁ := b) (e₂ := a) hb ha (fun s => (hc s).symm)
  · exact not_commutes_add_add_same ha hb hr (ne_of_lt ht)

/-- **The execution order is exact on observed events.** Every pair that
fails to commute is related, in one direction or the other, and nothing
else is. Two events of one replica carrying the same timestamp are the same
event, which is where the context is used. -/
theorem commutes_iff (C : Ctx (D α)) (a b : Event α)
    (ha : a ∈ C.events) (hb : b ∈ C.events) :
    ¬ (D α).Commutes a b ↔ ExBefore a b ∨ ExBefore b a := by
  refine ⟨?_, ?_⟩
  · intro hnc
    cases hoa : a.2.2 with
    | add x =>
      cases hob : b.2.2 with
      | add y =>
        by_cases hxy : x = y
        · subst hxy
          by_cases hr : a.2.1 = b.2.1
          · by_cases ht : a.1 < b.1
            · exact Or.inl (Or.inr ⟨x, hoa, hob, hr, ht⟩)
            · by_cases ht' : b.1 < a.1
              · exact Or.inr (Or.inr ⟨x, hob, hoa, hr.symm, ht'⟩)
              · exfalso
                have hts : a.1 = b.1 := le_antisymm (not_lt.mp ht') (not_lt.mp ht)
                by_cases hab : a = b
                · exact hnc (by rw [hab]; intro s; rfl)
                · obtain ⟨ra, sa, hLa, hsa⟩ := ha
                  obtain ⟨rb, sb, hLb, hsb⟩ := hb
                  exact C.timestamps_distinct hLa hsa hLb hsb hab hts
          · exact absurd (commutes_add_add hoa hob hr) hnc
        · exact absurd (commutes_add_add_ne hoa hob hxy) hnc
      | remove y =>
        by_cases hxy : x = y
        · subst hxy
          exact Or.inr (Or.inl ⟨x, hob, hoa⟩)
        · exact absurd (commutes_add_rem hoa hob hxy) hnc
    | remove x =>
      cases hob : b.2.2 with
      | add y =>
        by_cases hxy : x = y
        · subst hxy
          exact Or.inl (Or.inl ⟨x, hoa, hob⟩)
        · refine absurd (fun s => ?_) hnc
          exact (commutes_add_rem (e₁ := b) (e₂ := a) hob hoa
            (fun h => hxy h.symm) s).symm
      | remove y => exact absurd (commutes_rem_rem hoa hob) hnc
  · rintro (h | h)
    · exact not_commutes_of_exBefore h
    · exact fun hc => not_commutes_of_exBefore h (fun s => (hc s).symm)

/-- **On concurrent events the execution order is `rc`.** The extra pair it
carries is two events of one replica, and those are never concurrent. -/
theorem exBefore_iff_rc (C : Ctx (D α)) (a b : Event α)
    (ha : a ∈ C.events) (hb : b ∈ C.events)
    (hab : ¬ C.vis a b) (hba : ¬ C.vis b a) :
    ExBefore a b ↔ (D α).EventRcBefore a b := by
  refine ⟨?_, fun h => Or.inl ((rcBefore_iff a b).mp h)⟩
  rintro (h | ⟨x, hoa, hob, hr, ht⟩)
  · exact (rcBefore_iff a b).mpr h
  · exfalso
    obtain ⟨ra, sa, hLa, hsa⟩ := ha
    obtain ⟨rb, sb, hLb, hsb⟩ := hb
    have hne : a ≠ b := fun heq => absurd (congrArg Prod.fst heq) (ne_of_lt ht)
    rcases C.vis_total_same_replica hLa hsa hLb hsb hne hr with h | h
    · exact hab h
    · exact hba h

/-- The execution order, packaged. -/
noncomputable def exOrder : ExecutionOrder (D α) where
  order := exEventOrder
  exact := fun C a b ha hb => by
    rw [exBefore_iff, exBefore_iff]
    exact commutes_iff C a b ha hb
  concurrent := fun C a b ha hb hab hba => by
    rw [exBefore_iff]
    exact exBefore_iff_rc C a b ha hb hab hba

/-- **The obligations of the efficient OR-set.** The row that cannot supply
an unguarded RC-NON-COMM supplies the three cases the paper's guards exclude
directly, where every other row gets them from `Obligations.ofUniform`. -/
theorem obligations : Obligations (D α) :=
  ⟨laws, equal_op_commutes, cond_comm.toSameReplica, joinLaws, ⟨exOrder⟩⟩

#print axioms laws
#print axioms joinLaws

end LeanProofs.Implementations.EfficientORSet
