import LeanProofs_no_spec_non_comm.Implementations.RemoveWinsSet.Definition
import LeanProofs_no_spec_non_comm.Metatheory.Adequacy
import LeanProofs_no_spec_non_comm.Soundness.RALinearizability

/-!
**A duplicate, plus one section.** Everything up to the last section is
`Implementations/RemoveWinsSet/VCs.lean` with the namespace changed. The last section
is what this folder adds: that `Soundness.joint` has no loop, which is all
`Soundness.certifiedSpecRA_any` asks of a row.

# The remove-wins set: every obligation

`Laws(D_type, Spec)` of Section 4 and VC1 to VC5 of Section 5, all four laws
and all five conditions, for the tuple of `Definition.lean`. `obligations`
bundles what the metatheory consumes; `spec_non_comm` and `anyOrderSound` are the
two further premises `Soundness.certifiedSpecRA` asks for.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.RemoveWinsSet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

variable {A : Type} [DecidableEq A] [Fintype A]

/-- `rc` relates exactly the pairs `add x`, `remove x`. -/
@[simp] theorem rcBefore_iff (o₁ o₂ : AppOp A) :
    (D A).RcBefore o₁ o₂ ↔ ∃ x, o₁ = .add x ∧ o₂ = .remove x := by
  cases o₁ with
  | remove x =>
      cases o₂ with
      | remove y => simp [Impl.RcBefore, rc]
      | add y => simp only [Impl.RcBefore, rc]; split <;> simp
  | add x =>
      cases o₂ with
      | remove y =>
          simp only [Impl.RcBefore, rc]
          by_cases h : x = y
          · subst h; simp
          · simp [h, Ne.symm h]
      | add y => simp [Impl.RcBefore, rc]

/-- The event-level reading of the same fact. -/
theorem eventRcBefore_iff (e₁ e₂ : (D A).Event) :
    (D A).EventRcBefore e₁ e₂ ↔ ∃ x, e₁.op = .add x ∧ e₂.op = .remove x :=
  rcBefore_iff _ _

@[simp] theorem mem_step (S : St A) (e : Event A) (p : A × Option Timestamp) :
    p ∈ step S e ↔ match e.op with
    | .remove x => p = (x, some e.time) ∨ p ∈ S
    | .add x => p ∈ S ∧ p.1 ≠ x := by
  rcases e with ⟨t, r, o⟩; cases o <;> simp [step, Op.op, Op.time]

/-- Everything `rc` leaves unordered really does commute. -/
theorem commute_of_no_rc (e₁ e₂ : (D A).Event)
    (h : ¬ ((D A).EventRcBefore e₁ e₂ ∨ (D A).EventRcBefore e₂ e₁)) :
    (D A).Commutes e₁ e₂ := by
  simp only [eventRcBefore_iff, not_or] at h
  intro S
  change St A at S
  rcases e₁ with ⟨t₁, r₁, o₁⟩; rcases e₂ with ⟨t₂, r₂, o₂⟩
  change step (step S _) _ = step (step S _) _
  cases o₁ <;> cases o₂ <;> ext p <;> simp [step, Op.op, Op.time] at h ⊢ <;> grind

/-- **RC-NON-COMM**. -/
theorem rc_non_comm (e₁ e₂ : (D A).Event) :
    ¬ (D A).Commutes e₁ e₂ ↔
      (D A).EventRcBefore e₁ e₂ ∨ (D A).EventRcBefore e₂ e₁ := by
  constructor
  · exact fun hn => Classical.byContradiction fun h => hn (commute_of_no_rc e₁ e₂ h)
  · intro hr hc
    rcases hr with hr | hr
    · obtain ⟨x, ha, hr'⟩ := (eventRcBefore_iff _ _).mp hr
      have h := Finset.ext_iff.mp (hc (∅ : St A)) (x, e₂.time)
      simp [step, ha, hr'] at h
    · obtain ⟨x, ha, hr'⟩ := (eventRcBefore_iff _ _).mp hr
      have h := Finset.ext_iff.mp (hc (∅ : St A)) (x, e₁.time)
      simp [step, ha, hr'] at h

/-- **NO-RC-CHAIN**. An `add` can only start an edge and a `remove` can only
end one, so two edges never meet. -/
theorem no_rc_chain (o₁ o₂ o₃ : AppOp A) :
    ¬ ((D A).RcBefore o₁ o₂ ∧ (D A).RcBefore o₂ o₃) := by
  rintro ⟨h₁, h₂⟩
  obtain ⟨x, -, hr⟩ := (rcBefore_iff _ _).mp h₁
  obtain ⟨y, ha, -⟩ := (rcBefore_iff _ _).mp h₂
  rw [hr] at ha; cases ha

/-! ### The absorber argument for COND-COMM -/

/-- Two states that agree away from `x`. -/
def EqExcept (x : A) (a b : St A) : Prop := ∀ p, p.1 ≠ x → (p ∈ a ↔ p ∈ b)

theorem eqExcept_step {x : A} {a b : St A} (h : EqExcept x a b) (e : Event A) :
    EqExcept x (step a e) (step b e) := by
  intro p hp
  rcases e with ⟨t, r, o⟩; cases o <;> simp [step, Op.op, h p hp]

theorem eqExcept_applyList {x : A} {a b : St A} (h : EqExcept x a b)
    (pi : List (D A).Event) :
    EqExcept x ((D A).applyList a pi) ((D A).applyList b pi) := by
  induction pi generalizing a b with
  | nil => exact h
  | cons e pi ih => exact ih (eqExcept_step h e)

/-- **COND-COMM**. -/
theorem cond_comm (S : (D A).Sigma) (e e' e'' : (D A).Event)
    (pi : List (D A).Event)
    (hrc : (D A).EventRcBefore e e') (hnc : ¬ (D A).Commutes e' e'') :
    (D A).do_ ((D A).applyList ((D A).do_ ((D A).do_ S e') e) pi) e''
      = (D A).do_ ((D A).applyList ((D A).do_ ((D A).do_ S e) e') pi) e'' := by
  obtain ⟨x, he, he'⟩ := (eventRcBefore_iff _ _).mp hrc
  have habs : e''.op = AppOp.add x := by
    rcases (rc_non_comm e' e'').mp hnc with h | h
    · obtain ⟨y, ha, -⟩ := (eventRcBefore_iff _ _).mp h
      rw [he'] at ha; cases ha
    · obtain ⟨y, ha, hr⟩ := (eventRcBefore_iff _ _).mp h
      rw [he'] at hr; injection hr with hxy; subst y; exact ha
  have hbase : EqExcept x (step (step S e') e) (step (step S e) e') := by
    intro p hp; simp [step, he, he', hp]
  have hfold := eqExcept_applyList hbase pi
  change step _ e'' = step _ e''
  ext p
  simp only [step, habs, Finset.mem_filter]
  by_cases hp : p.1 = x
  · simp [hp]
  · exact and_congr (hfold p hp) Iff.rfl

/-- `Laws(D_type)`: RC-NON-COMM over concurrent events, NO-RC-CHAIN and
COND-COMM. -/
theorem laws : Laws (D A) := ⟨rcNonComm_of_exact no_rc_chain (fun e₁ e₂ _ _ => rc_non_comm e₁ e₂),
  no_rc_chain,
  fun S e e' e'' pi _ _ => cond_comm S e e' e'' pi⟩


/-- The replay order of Section 4: `rc`, lifted to events. -/
noncomputable local instance rcOrder :
    EventOrder (D A).toMRDTSig.toUpdateSig := Interface.rcOrder (D A)

@[simp] theorem replayBefore_iff (a b : (D A).Event) :
    (D A).toMRDTSig.toUpdateSig.replayBefore a b
      ↔ ∃ x, a.op = AppOp.add x ∧ b.op = AppOp.remove x := by
  refine Iff.trans ?_ (rcBefore_iff a.op b.op)
  exact @OperationPolicy.lift_replayOrder_iff (D A).toMRDTSig.toUpdateSig
    (Interface.policy (D A)) a b

theorem noncomm_iff_replayBefore (a b : (D A).Event) :
    ¬ (D A).toMRDTSig.toUpdateSig.commutes a b ↔
      (D A).toMRDTSig.toUpdateSig.replayBefore a b
        ∨ (D A).toMRDTSig.toUpdateSig.replayBefore b a := by
  simpa only [replayBefore_iff] using
    (rc_non_comm a b).trans (by simp only [eventRcBefore_iff])

/-! ## Canonical states contain exactly the live tags -/

/-- `pi(sigma0)`, the state after replaying a list. -/
abbrev Run (ops : List (D A).Event) : St A :=
  applySeq (D A).toMRDTSig.toUpdateSig (D A).toMRDTSig.init ops

/-- No event in the list adds `x` back. -/
def NoAdd (ops : List (D A).Event) (x : A) : Prop :=
  ∀ e ∈ ops, e.op ≠ AppOp.add x

theorem noAdd_append_singleton {ops : List (D A).Event} {e : (D A).Event} {x : A} :
    NoAdd (ops ++ [e]) x ↔ NoAdd ops x ∧ e.op ≠ AppOp.add x := by
  constructor
  · exact fun h => ⟨fun a ha => h a (by simp [ha]), h e (by simp)⟩
  · rintro ⟨h, he⟩ a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact h a ha
    · rw [List.mem_singleton.mp ha]; exact he

/-- Splitting a list that ends in `e`. -/
theorem append_singleton_split {α : Type} {pi pre post : List α} {w e : α}
    (h : pi ++ [e] = pre ++ w :: post) :
    (w = e ∧ pi = pre)
      ∨ (∃ post', post = post' ++ [e] ∧ pi = pre ++ w :: post') := by
  cases post using List.reverseRecOn with
  | nil =>
      obtain ⟨hpre, hw⟩ := List.append_inj' (h : pi ++ [e] = pre ++ [w]) rfl
      have hew : e = w := by simpa using hw
      exact Or.inl ⟨hew.symm, hpre⟩
  | append_singleton post' x =>
      have h' : pi ++ [e] = (pre ++ w :: post') ++ [x] := by rw [h]; simp
      obtain ⟨hpi, hx⟩ := List.append_inj' h' rfl
      have hex : e = x := by simpa using hx
      exact Or.inr ⟨post', by rw [hex], hpi⟩

/-- A tag is in a replayed state exactly when some `remove` produced it and no
later event added its element back, or it is an initial tag that no `add`
removed. -/
theorem mem_run_iff_suffix (ops : List (D A).Event) (p : A × Option Timestamp) :
    p ∈ Run ops ↔
      (∃ pre w post, ops = pre ++ w :: post ∧ w.op = AppOp.remove p.1
        ∧ some w.time = p.2 ∧ NoAdd post p.1)
      ∨ (p.2 = none ∧ NoAdd ops p.1) := by
  induction ops using List.reverseRecOn with
  | nil =>
      constructor
      · intro hm
        exact Or.inr ⟨(mem_sigma0 p).mp hm, by simp [NoAdd]⟩
      · rintro (⟨pre, w, post, hs, -, -, -⟩ | ⟨h, -⟩)
        · exact absurd hs.symm (by simp)
        · exact (mem_sigma0 p).mpr h
  | append_singleton ops e ih =>
      have hrun : Run (ops ++ [e]) = step (Run ops) e := by
        simp [Run, applySeq, List.foldl_append]
        rfl
      rw [hrun]
      rcases hop : e.op with x | x
      · -- `add x`
        rw [mem_step, hop]
        constructor
        · rintro ⟨hm, hpx⟩
          have hne : e.op ≠ AppOp.add p.1 := by
            rw [hop]; intro h; injection h with h'; exact hpx h'.symm
          rcases ih.mp hm with ⟨pre, w, post, hs, hw, ht, hn⟩ | ⟨h0, hn⟩
          · exact Or.inl ⟨pre, w, post ++ [e], by rw [hs]; simp, hw, ht,
              noAdd_append_singleton.mpr ⟨hn, hne⟩⟩
          · exact Or.inr ⟨h0, noAdd_append_singleton.mpr ⟨hn, hne⟩⟩
        · rintro (⟨pre, w, post, hs, hw, ht, hn⟩ | ⟨h0, hn⟩)
          · rcases append_singleton_split hs with ⟨hwe, -⟩ | ⟨post', hpost, hops⟩
            · exact absurd (hwe ▸ hw) (by rw [hop]; simp)
            · obtain ⟨hn', hne⟩ := noAdd_append_singleton.mp (hpost ▸ hn)
              exact ⟨ih.mpr (Or.inl ⟨pre, w, post', hops, hw, ht, hn'⟩),
                fun hpx => hne (by rw [hop, hpx])⟩
          · obtain ⟨hn', hne⟩ := noAdd_append_singleton.mp hn
            exact ⟨ih.mpr (Or.inr ⟨h0, hn'⟩), fun hpx => hne (by rw [hop, hpx])⟩
      · -- `remove x`
        rw [mem_step, hop]
        constructor
        · rintro (heq | hm)
          · have hx : p.1 = x := congrArg Prod.fst heq
            refine Or.inl ⟨ops, e, [], rfl, ?_, (congrArg Prod.snd heq).symm,
              by simp [NoAdd]⟩
            rw [hop, hx]
          · rcases ih.mp hm with ⟨pre, w, post, hs, hw, ht, hn⟩ | ⟨h0, hn⟩
            · exact Or.inl ⟨pre, w, post ++ [e], by rw [hs]; simp, hw, ht,
                noAdd_append_singleton.mpr ⟨hn, by rw [hop]; simp⟩⟩
            · exact Or.inr ⟨h0, noAdd_append_singleton.mpr ⟨hn, by rw [hop]; simp⟩⟩
        · rintro (⟨pre, w, post, hs, hw, ht, hn⟩ | ⟨h0, hn⟩)
          · rcases append_singleton_split hs with ⟨hwe, -⟩ | ⟨post', hpost, hops⟩
            · subst hwe
              have hx : x = p.1 := by
                have h2 : AppOp.remove x = AppOp.remove p.1 := by rw [← hop]; exact hw
                simpa using h2
              exact Or.inl (Prod.ext hx.symm ht.symm)
            · exact Or.inr (ih.mpr (Or.inl ⟨pre, w, post', hops, hw, ht,
                (noAdd_append_singleton.mp (hpost ▸ hn)).1⟩))
          · exact Or.inr (ih.mpr (Or.inr ⟨h0, (noAdd_append_singleton.mp hn).1⟩))

/-! ## Liveness -/

theorem not_edge_to_prefix {R : (D A).Event → (D A).Event → Prop}
    {pre post : List (D A).Event} {a r : (D A).Event}
    (hr : respects (pre ++ a :: post) R) (hm : r ∈ pre) : ¬ R a r :=
  (List.pairwise_append.mp hr).2.2 r hm a (by simp)

theorem not_edge_from_suffix {R : (D A).Event → (D A).Event → Prop}
    {pre post : List (D A).Event} {a r : (D A).Event}
    (hr : respects (pre ++ a :: post) R) (hm : r ∈ post) : ¬ R r a :=
  (List.pairwise_cons.mp (List.pairwise_append.mp hr).2.1).1 r hm

/-- No `add` of `x` in `E` observes `a`. -/
def Survives (C : Ctx (D A))
    (E : Set (Event A)) (a : Event A) (x : A) : Prop :=
  ¬ ∃ b ∈ E, b.op = AppOp.add x ∧ C.vis a b

/-- The tag `p` is live in `E`: either the `remove` that created it is in `E`
and no `add` of `E` observes that `remove`, or it is an initial tag and `E`
holds no `add` for its element. -/
def Live (C : Ctx (D A))
    (E : Set (Event A)) (p : A × Option Timestamp) : Prop :=
  (∃ w ∈ E, w.op = AppOp.remove p.1 ∧ some w.time = p.2 ∧ Survives C E w p.1)
    ∨ (p.2 = none ∧ ¬ ∃ b ∈ E, b.op = AppOp.add p.1)

/-- **Fact 1.** A canonical state contains exactly the live tags. -/
theorem mem_run_iff_live {C : Ctx (D A)}
    {E : Set (Event A)} {ops : List (D A).Event}
    (hp : listPermOf ops E) (hr : respects ops (loOn C E)) (p : A × Option Timestamp) :
    p ∈ Run ops ↔ Live C E p := by
  rw [mem_run_iff_suffix]
  constructor
  · rintro (⟨pre, w, post, hs, hw, ht, hn⟩ | ⟨h0, hn⟩)
    · subst ops
      refine Or.inl ⟨w, (hp.2 w).mp (by simp), hw, ht, ?_⟩
      rintro ⟨b, hbe, hb, hvis⟩
      have hm : b ∈ pre ++ w :: post := (hp.2 b).mpr hbe
      rcases List.mem_append.mp hm with hm | hm
      · exact not_edge_to_prefix hr hm
          (Or.inl ⟨hvis, Or.inr ((replayBefore_iff b w).mpr ⟨p.1, hb, hw⟩)⟩)
      · rcases List.mem_cons.mp hm with heq | hm
        · rw [heq, hw] at hb; cases hb
        · exact hn b hm hb
    · exact Or.inr ⟨h0, fun ⟨b, hbe, hb⟩ => hn b ((hp.2 b).mpr hbe) hb⟩
  · rintro (⟨w, hwe, hw, ht, hsv⟩ | ⟨h0, hno⟩)
    · obtain ⟨pre, post, hs⟩ := List.append_of_mem ((hp.2 w).mpr hwe)
      refine Or.inl ⟨pre, w, post, hs, hw, ht, ?_⟩
      subst ops
      intro b hm hb
      refine not_edge_from_suffix hr hm ?_
      have hbe : b ∈ E := (hp.2 b).mp (by simp [hm])
      have hrc : (D A).toMRDTSig.toUpdateSig.replayBefore b w :=
        (replayBefore_iff b w).mpr ⟨p.1, hb, hw⟩
      by_cases hvb : C.vis b w
      · exact Or.inl ⟨hvb, Or.inl hrc⟩
      · refine Or.inr ⟨hvb, ?_, hrc, ?_⟩
        · exact fun hv => hsv ⟨b, hbe, hb, hv⟩
        · rintro ⟨c, hce, hvc, hc | hc⟩
          · obtain ⟨y, hwadd, -⟩ := (replayBefore_iff w c).mp hc
            rw [hw] at hwadd; cases hwadd
          · obtain ⟨y, hcadd, hwrem⟩ := (replayBefore_iff c w).mp hc
            rw [hw] at hwrem
            injection hwrem with hy
            subst y
            exact hsv ⟨c, hce, hcadd, hvc⟩
    · exact Or.inr ⟨h0, fun b hm hb => hno ⟨b, (hp.2 b).mp hm, hb⟩⟩

theorem canonical_mem_iff {C : Ctx (D A)}
    {E : Set (Event A)} {s : St A}
    (hs : Interface.IsCanOn (D A) C E s) (p : A × Option Timestamp) : p ∈ s ↔ Live C E p := by
  obtain ⟨ops, hp, hr, hf⟩ := hs
  rw [← hf]
  exact mem_run_iff_live hp hr p

/-- **Fact 2.** Timestamps identify events, and a seed tag carries `none`,
which no event's tag can equal, so a tag has one possible origin. -/
theorem live_iff_fixed_remove {C : Ctx (D A)}
    {E : Set (Event A)} (hsub : E ⊆ C.events)
    {p : A × Option Timestamp} {a : Event A} (hac : a ∈ C.events)
    (ha : a.op = AppOp.remove p.1) (ht : some a.time = p.2) :
    Live C E p ↔ a ∈ E ∧ Survives C E a p.1 := by
  constructor
  · rintro (⟨b, hb, -, hbt, hs⟩ | ⟨h0, -⟩)
    · have heq : b = a :=
        C.ts_unique (hsub hb) hac (Option.some.inj (hbt.trans ht.symm))
      subst b
      exact ⟨hb, hs⟩
    · exact absurd (ht.trans h0) (by simp)
  · rintro ⟨he, hs⟩
    exact Or.inl ⟨a, he, ha, ht, hs⟩

/-- **Fact 3.** Liveness over the union is the Boolean that `merge` computes.
The initial tags are handled separately, since no event creates them. -/
theorem live_join {C : Ctx (D A)}
    {E₁ E₂ : Set (Event A)}
    (hsub₁ : E₁ ⊆ C.events) (hsub₂ : E₂ ⊆ C.events)
    (hclosed₁ : ∀ a b, C.vis a b →
      ¬ (D A).toMRDTSig.toUpdateSig.commutes a b → b ∈ E₁ → a ∈ E₁)
    (hclosed₂ : ∀ a b, C.vis a b →
      ¬ (D A).toMRDTSig.toUpdateSig.commutes a b → b ∈ E₂ → a ∈ E₂)
    (p : A × Option Timestamp) :
    Live C (E₁ ∪ E₂) p ↔
      (Live C (E₁ ∩ E₂) p ∧ Live C E₁ p ∧ Live C E₂ p) ∨
      (Live C E₁ p ∧ ¬ Live C (E₁ ∩ E₂) p) ∨
      (Live C E₂ p ∧ ¬ Live C (E₁ ∩ E₂) p) := by
  have hint : E₁ ∩ E₂ ⊆ C.events := fun e he => hsub₁ he.1
  have huni : E₁ ∪ E₂ ⊆ C.events := fun e he => he.elim (fun h => hsub₁ h) (fun h => hsub₂ h)
  by_cases h0 : p.2 = none
  · -- an initial tag: no event creates it, so liveness is "no add for `p.1`"
    have key : ∀ E : Set (Event A), E ⊆ C.events →
        (Live C E p ↔ ¬ ∃ b ∈ E, b.op = AppOp.add p.1) := by
      intro E hsub
      constructor
      · rintro (⟨w, hw, -, hwt, -⟩ | ⟨-, h⟩)
        · exact absurd (hwt.trans h0) (by simp)
        · exact h
      · exact fun h => Or.inr ⟨h0, h⟩
    rw [key _ huni, key _ hsub₁, key _ hsub₂, key _ hint]
    constructor
    · intro h
      exact Or.inl ⟨fun ⟨b, hb, hba⟩ => h ⟨b, Or.inl hb.1, hba⟩,
        fun ⟨b, hb, hba⟩ => h ⟨b, Or.inl hb, hba⟩,
        fun ⟨b, hb, hba⟩ => h ⟨b, Or.inr hb, hba⟩⟩
    · rintro (⟨-, h₁, h₂⟩ | ⟨h₁, hn0⟩ | ⟨h₂, hn0⟩)
      · rintro ⟨b, hb | hb, hba⟩
        · exact h₁ ⟨b, hb, hba⟩
        · exact h₂ ⟨b, hb, hba⟩
      · exact absurd (fun ⟨b, hb, hba⟩ => h₁ ⟨b, hb.1, hba⟩) hn0
      · exact absurd (fun ⟨b, hb, hba⟩ => h₂ ⟨b, hb.2, hba⟩) hn0
  · -- a minted tag: the OR-set argument
    by_cases hex : ∃ a ∈ E₁ ∪ E₂, a.op = AppOp.remove p.1 ∧ some a.time = p.2
    · obtain ⟨a, hae, ha, ht⟩ := hex
      have hac : a ∈ C.events := huni hae
      rw [live_iff_fixed_remove huni hac ha ht,
        live_iff_fixed_remove hint hac ha ht,
        live_iff_fixed_remove hsub₁ hac ha ht,
        live_iff_fixed_remove hsub₂ hac ha ht]
      have hk₁ : ¬ Survives C E₁ a p.1 → a ∈ E₁ := by
        intro hn
        obtain ⟨b, hb, hba, hv⟩ := Classical.not_not.mp hn
        refine hclosed₁ a b hv ?_ hb
        exact (rc_non_comm a b).mpr (Or.inr ((eventRcBefore_iff b a).mpr ⟨p.1, hba, ha⟩))
      have hk₂ : ¬ Survives C E₂ a p.1 → a ∈ E₂ := by
        intro hn
        obtain ⟨b, hb, hba, hv⟩ := Classical.not_not.mp hn
        refine hclosed₂ a b hv ?_ hb
        exact (rc_non_comm a b).mpr (Or.inr ((eventRcBefore_iff b a).mpr ⟨p.1, hba, ha⟩))
      have hu : Survives C (E₁ ∪ E₂) a p.1 ↔
          Survives C E₁ a p.1 ∧ Survives C E₂ a p.1 := by
        simp only [Survives, Set.mem_union]
        constructor
        · intro h
          exact ⟨fun ⟨b, hb, hba, hv⟩ => h ⟨b, Or.inl hb, hba, hv⟩,
            fun ⟨b, hb, hba, hv⟩ => h ⟨b, Or.inr hb, hba, hv⟩⟩
        · rintro ⟨h₁, h₂⟩ ⟨b, hb | hb, hba, hv⟩
          · exact h₁ ⟨b, hb, hba, hv⟩
          · exact h₂ ⟨b, hb, hba, hv⟩
      have hi₁ : Survives C E₁ a p.1 → Survives C (E₁ ∩ E₂) a p.1 :=
        fun h ⟨b, hb, hba, hv⟩ => h ⟨b, hb.1, hba, hv⟩
      have hi₂ : Survives C E₂ a p.1 → Survives C (E₁ ∩ E₂) a p.1 :=
        fun h ⟨b, hb, hba, hv⟩ => h ⟨b, hb.2, hba, hv⟩
      rw [hu]
      simp only [Set.mem_union, Set.mem_inter_iff]
      tauto
    · have hn : ∀ E : Set (Event A), E ⊆ E₁ ∪ E₂ → ¬ Live C E p := by
        rintro E hs (⟨w, hw, hwr, hwt, -⟩ | ⟨hz, -⟩)
        · exact hex ⟨w, hs hw, hwr, hwt⟩
        · exact h0 hz
      have hnU := hn (E₁ ∪ E₂) Set.Subset.rfl
      have hnI := hn (E₁ ∩ E₂) (fun _ h => Or.inl h.1)
      have hn₁ := hn E₁ Set.subset_union_left
      have hn₂ := hn E₂ Set.subset_union_right
      simp [hnU, hnI, hn₁, hn₂]



/-! ## VC1 and VC2

Two of the five hold at arbitrary states for this `merge`, so they are set
identities with no premises at all, guard included. -/

/-- `merge(l,a,b) = merge(l,b,a)` at any states. This is **VC1** exactly:
the paper states it over arbitrary states too. -/
theorem vc1_merge_comm (l a b : (D A).Sigma) :
    (D A).merge l a b = (D A).merge l b a := by
  change mergeState l a b = mergeState l b a
  ext p
  simp only [mergeState, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

/-- `merge(sigma0, sigma0, s) = s` at any `s`. **VC2** asks for it only at a
canonical `s`. The seed tags of `sigma0` are kept by the first component and
everything else by the third, so the ancestor's own content is irrelevant. -/
theorem vc2_merge_init (s : (D A).Sigma) :
    (D A).merge (D A).sigma0 (D A).sigma0 s = s := by
  change mergeState (sigma0 A) (sigma0 A) s = s
  ext p
  simp only [mergeState, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

/-! ## The three canonical conditions

The states VC3, VC4 and VC5 mention are canonical for event sets built from
`E1`, `E2` and `down(e)`. Each nest of merges is read pointwise through
`canonical_mem_iff` and resolved by `live_join`, this row's own description
of liveness over a union.

`mergeProp` below is the Boolean `merge` computes at a tag. Writing both
`merge` and `live_join` in that one shape turns VC3 and VC5 into chains of
rewrites with no propositional search at all. -/

/-- The Boolean `merge` computes at a single tag: keep it when the ancestor
and both branches have it, or when one branch has it and the ancestor does
not. -/
def mergeProp (L B C : Prop) : Prop := (L ∧ B ∧ C) ∨ (B ∧ ¬ L) ∨ (C ∧ ¬ L)

theorem mem_merge (l a b : (D A).Sigma) (p : A × Option Timestamp) :
    p ∈ (D A).merge l a b ↔ mergeProp (p ∈ l) (p ∈ a) (p ∈ b) := by
  change p ∈ mergeState l a b ↔ _
  simp only [mergeState, mergeProp, Finset.mem_union, Finset.mem_inter,
    Finset.mem_sdiff]
  tauto

/-- `live_join` in `mergeProp` shape: liveness over a union is exactly the
Boolean `merge` computes from liveness over the intersection and over each
branch. -/
theorem live_merge {C : Ctx (D A)} {E₁ E₂ : Set (D A).Event}
    (h₁ : SupportedOn (D A) C E₁) (h₂ : SupportedOn (D A) C E₂)
    (c₁ : WeaklyClosed (D A) C E₁) (c₂ : WeaklyClosed (D A) C E₂)
    (p : A × Option Timestamp) :
    Live C (E₁ ∪ E₂) p
      ↔ mergeProp (Live C (E₁ ∩ E₂) p) (Live C E₁ p) (Live C E₂ p) :=
  live_join h₁ h₂ c₁ c₂ p

/-- `e(can(down(e) \ {e})) = can(down(e))`: the downset's own peel. -/
theorem isCan_downset {C : Ctx (D A)} {m : (D A).Sigma} {e : (D A).Event}
    (htr : ∀ {a b c : (D A).Event}, C.vis a b → C.vis b c → C.vis a c)
    (hir : ∀ a : (D A).Event, ¬ C.vis a a)
    (hm : IsCanOn (D A) C (downset C e \ {e}) m) :
    IsCanOn (D A) C (downset C e) ((D A).do_ m e) := by
  letI : EventOrder (D A).toMRDTSig.toUpdateSig := Interface.rcOrder (D A)
  exact isCanonicalState_snoc (Or.inl rfl) (downset_max htr hir) hm

/-- **VC3** LOCAL-REDISTRIBUTE, proved for this row.

Both sides are liveness over `E1 u E2`. The left reaches it through
`E1 = (E1 \ {e}) u down(e)` and then `E1 u E2`; the right through
`(E1 u E2) \ {e} = (E1 \ {e}) u E2` and then
`(E1 u E2) = ((E1 u E2) \ {e}) u down(e)`. Four instances of `live_merge`,
and the equation falls out by rewriting. -/
theorem vc3_local_redistribute :
    ∀ (C : Ctx (D A)) (E₁ E₂ : Set (D A).Event) (l m x y : (D A).Sigma)
      (e : (D A).Event),
      VisStrict (D A) C →
      SupportedOn (D A) C E₁ → SupportedOn (D A) C E₂ →
      WeaklyClosed (D A) C E₁ → WeaklyClosed (D A) C E₂ →
      e ∈ E₁ → e ∉ E₂ → MaximalOn (D A) C (E₁ ∪ E₂) e →
      IsCanOn (D A) C (E₁ ∩ E₂) l →
      IsCanOn (D A) C (downset C e \ {e}) m →
      IsCanOn (D A) C (E₁ \ {e}) x →
      IsCanOn (D A) C E₂ y →
      (D A).merge l ((D A).merge m x ((D A).do_ m e)) y
        = (D A).merge m ((D A).merge l x y) ((D A).do_ m e) := by
  letI : EventOrder (D A).toMRDTSig.toUpdateSig := Interface.rcOrder (D A)
  intro C E₁ E₂ l m x y e hvs h₁ h₂ hc₁ hc₂ he₁ he₂ hmax hl hm hx hy
  obtain ⟨htr, hir⟩ := hvs
  have hcov : ∀ a b : (D A).Event, ¬ (D A).toMRDTSig.toUpdateSig.commutes a b →
      ((D A).toMRDTSig.toUpdateSig.replayBefore a b ∨
        (D A).toMRDTSig.toUpdateSig.replayBefore b a) :=
    fun a b => (noncomm_iff_replayBefore a b).mp
  have hdsub : downset C e ⊆ E₁ := downset_subset hc₁ he₁
  have hdm := isCan_downset htr hir hm
  have hsupU : SupportedOn (D A) C (E₁ ∪ E₂) := fun a ha => ha.elim (h₁ a) (h₂ a)
  have hdsupp : SupportedOn (D A) C (downset C e) := fun a ha => h₁ a (hdsub ha)
  have hcld : WeaklyClosed (D A) C (downset C e) := fun a b => downset_closed a b
  have hclU : WeaklyClosed (D A) C (E₁ ∪ E₂) := weaklyClosed_union hc₁ hc₂
  have hclx : WeaklyClosed (D A) C (E₁ \ {e}) :=
    closure_diff_of_max hcov Set.subset_union_left hc₁ hmax
  have hclU' : WeaklyClosed (D A) C ((E₁ ∪ E₂) \ {e}) :=
    closure_diff_of_max hcov Set.Subset.rfl hclU hmax
  have i₁ : (E₁ \ {e}) ∩ downset C e = downset C e \ {e} := by
    ext z; exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hdsub h.1, h.2⟩, h.1⟩⟩
  have u₁ : (E₁ \ {e}) ∪ downset C e = E₁ := by
    ext z; constructor
    · rintro (⟨hz, -⟩ | hz); · exact hz
      · exact hdsub hz
    · intro hz; by_cases hze : z = e
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
    · rintro (⟨hz, -⟩ | hz); · exact hz
      · exact Or.inl (hdsub hz)
    · intro hz; by_cases hze : z = e
      · exact Or.inr (Or.inl hze)
      · exact Or.inl ⟨hz, hze⟩
  ext p
  have jA := live_merge (fun a ha => h₁ a ha.1) hdsupp hclx hcld p
  rw [i₁, u₁] at jA
  have jB := live_merge h₁ h₂ hc₁ hc₂ p
  have jC := live_merge (fun a ha => h₁ a ha.1) h₂ hclx hc₂ p
  rw [i₂, u₂] at jC
  have jD := live_merge (fun a ha => hsupU a ha.1) hdsupp hclU' hcld p
  rw [i₃, u₃] at jD
  rw [mem_merge, mem_merge, mem_merge, mem_merge,
    canonical_mem_iff hl p, canonical_mem_iff hm p, canonical_mem_iff hx p,
    canonical_mem_iff hy p, canonical_mem_iff hdm p, ← jA, ← jB, ← jC, ← jD]

/-- The one fact about this row that **VC4** needs in the `add` case: a tag
that is live in `U \ {e}` and carries the element `e` adds is already live
in `down(e) \ {e}`.

The `remove` that produced it must be seen by `e`. If `e` saw nothing of it,
`lo^C_U` would have an edge out of `e`: a visibility edge when `e` sees the
removal, and otherwise the `rc` edge `add x --rc--> rem x`, whose absorber
clause can only be met by an `add` of `x` in `U` that the removal sees,
which would have cleared the tag in `U \ {e}` as well. Either way `e` is not
maximal.

A seed tag takes the other branch of `Live` and needs none of this: no event
created it, so it survives wherever no `add` of its element does. -/
theorem live_of_added {C : Ctx (D A)} {U : Set (D A).Event}
    {As Bs : (D A).Sigma} {e : (D A).Event} {x : A}
    (hUsub : SupportedOn (D A) C U) (hUcl : WeaklyClosed (D A) C U)
    (heU : e ∈ U) (hmax : MaximalOn (D A) C U e) (hex : e.op = AppOp.add x)
    (hA : IsCanOn (D A) C (U \ {e}) As)
    (hB : IsCanOn (D A) C (downset C e \ {e}) Bs)
    (p : A × Option Timestamp) (hpA : p ∈ As) (hpx : p.1 = x) : p ∈ Bs := by
  letI : EventOrder (D A).toMRDTSig.toUpdateSig := Interface.rcOrder (D A)
  have hdsub : downset C e ⊆ U := downset_subset hUcl heU
  rw [canonical_mem_iff hB]
  rcases (canonical_mem_iff hA p).mp hpA with ⟨α, hαU, hαop, hαt, hαs⟩ | ⟨h0, hno⟩
  · have hrbe : (D A).toMRDTSig.toUpdateSig.replayBefore e α := by
      rw [replayBefore_iff]; exact ⟨x, hex, by rw [hαop, hpx]⟩
    have hvis : C.vis α e := by
      by_contra hnv
      by_cases hve : C.vis e α
      · exact hmax α hαU.1 hαU.2 (Or.inl ⟨hve, Or.inl hrbe⟩)
      · by_cases habs : ∃ e₃ ∈ U, C.vis α e₃ ∧
            ((D A).toMRDTSig.toUpdateSig.replayBefore α e₃ ∨
              (D A).toMRDTSig.toUpdateSig.replayBefore e₃ α)
        · obtain ⟨e₃, he₃U, hv₃, hrb₃⟩ := habs
          have he₃op : e₃.op = AppOp.add p.1 := by
            rcases hrb₃ with h | h
            · rw [replayBefore_iff] at h
              obtain ⟨y, hy, -⟩ := h; rw [hαop] at hy; cases hy
            · rw [replayBefore_iff] at h
              obtain ⟨y, hy, hy'⟩ := h
              rw [hαop] at hy'; injection hy' with hyx; exact hyx ▸ hy
          exact hαs ⟨e₃, ⟨he₃U, by rintro rfl; exact hnv hv₃⟩, he₃op, hv₃⟩
        · exact hmax α hαU.1 hαU.2 (Or.inr ⟨hve, hnv, hrbe, habs⟩)
    have hnc : ¬ (D A).toMRDTSig.toUpdateSig.commutes α e :=
      (noncomm_iff_replayBefore α e).mpr (Or.inr hrbe)
    refine Or.inl ⟨α, ⟨Or.inr (Relation.TransGen.single ⟨hvis, hnc⟩), hαU.2⟩,
      hαop, hαt, ?_⟩
    rintro ⟨b, hb, hbop, hv⟩
    exact hαs ⟨b, ⟨hdsub hb.1, hb.2⟩, hbop, hv⟩
  · exact Or.inr ⟨h0, fun ⟨b, hb, hbop⟩ =>
      hno ⟨b, ⟨hdsub hb.1, hb.2⟩, hbop⟩⟩

/-- **VC4** CAUSAL-DELTA, proved for this row rather than derived from the
join lemma. The two cases are the two shapes of `do`, and the guard is used
in exactly one of them.

For `remove x` the tag `e` mints cannot already be in the ancestor `B`: a
tag of `down(e) \ {e}` carrying that timestamp would be `e` itself by
`ts_unique`, and the only other way for a tag to sit there is as a seed,
which carries `none` and so cannot equal `some (time e)`.

For `add x` nothing is minted, and the work is `live_of_added`. -/
theorem vc4_causal_delta :
    ∀ (C : Ctx (D A)) (U : Set (D A).Event) (As Bs : (D A).Sigma)
      (e : (D A).Event),
      VisStrict (D A) C →
      SupportedOn (D A) C U → WeaklyClosed (D A) C U →
      e ∈ U → MaximalOn (D A) C U e →
      IsCanOn (D A) C (U \ {e}) As →
      IsCanOn (D A) C (downset C e \ {e}) Bs →
      (D A).merge Bs As ((D A).do_ Bs e) = (D A).do_ As e := by
  letI : EventOrder (D A).toMRDTSig.toUpdateSig := Interface.rcOrder (D A)
  intro C U As Bs e hvs hUsub hUcl heU hmax hA hB
  obtain ⟨htr, hir⟩ := hvs
  change St A at As Bs
  change mergeState Bs As (step Bs e) = step As e
  ext p
  cases hop : e.op with
  | remove x =>
      have hnB : (x, some e.time) ∉ Bs := by
        intro hmem
        rcases (canonical_mem_iff hB _).mp hmem with ⟨α, hα, -, hαt, -⟩ | ⟨h0, -⟩
        · exact hα.2 (C.ts_unique
            (hUsub α (downset_subset hUcl heU hα.1)) (hUsub e heU)
            (Option.some.inj hαt))
        · exact absurd h0 (by simp)
      have hkey : p = (x, some e.time) → p ∉ Bs := by rintro rfl; exact hnB
      simp only [mergeState, Finset.mem_union, Finset.mem_inter,
        Finset.mem_sdiff, mem_step, hop]
      tauto
  | add x =>
      have hkey : p ∈ As → p ∉ Bs → p.1 ≠ x := fun hpA hpB hq =>
        hpB (live_of_added hUsub hUcl heU hmax hop hA hB p hpA hq)
      simp only [mergeState, Finset.mem_union, Finset.mem_inter,
        Finset.mem_sdiff, mem_step, hop]
      tauto

/-- **VC5** REDISTRIBUTE, proved for this row.

`e` lies in both branches, so each of `E1 n E2`, `E1` and `E2` is its own
`\ {e}` part joined with `down(e)`: three peels. The left side is then
liveness over `E1 u E2` directly. The right side reaches the same place
through `(E1 u E2) \ {e} = (E1 \ {e}) u (E2 \ {e})` and one further
peel. -/
theorem vc5_redistribute :
    ∀ (C : Ctx (D A)) (E₁ E₂ : Set (D A).Event) (x₀ x₁ x₂ m : (D A).Sigma)
      (e : (D A).Event),
      VisStrict (D A) C →
      SupportedOn (D A) C E₁ → SupportedOn (D A) C E₂ →
      WeaklyClosed (D A) C E₁ → WeaklyClosed (D A) C E₂ →
      e ∈ E₁ → e ∈ E₂ → MaximalOn (D A) C (E₁ ∪ E₂) e →
      IsCanOn (D A) C ((E₁ ∩ E₂) \ {e}) x₀ →
      IsCanOn (D A) C (downset C e \ {e}) m →
      IsCanOn (D A) C (E₁ \ {e}) x₁ →
      IsCanOn (D A) C (E₂ \ {e}) x₂ →
      (D A).merge ((D A).merge m x₀ ((D A).do_ m e))
          ((D A).merge m x₁ ((D A).do_ m e))
          ((D A).merge m x₂ ((D A).do_ m e))
        = (D A).merge m ((D A).merge x₀ x₁ x₂) ((D A).do_ m e) := by
  letI : EventOrder (D A).toMRDTSig.toUpdateSig := Interface.rcOrder (D A)
  intro C E₁ E₂ x₀ x₁ x₂ m e hvs h₁ h₂ hc₁ hc₂ he₁ he₂ hmax hx₀ hm hx₁ hx₂
  obtain ⟨htr, hir⟩ := hvs
  have hcov : ∀ a b : (D A).Event, ¬ (D A).toMRDTSig.toUpdateSig.commutes a b →
      ((D A).toMRDTSig.toUpdateSig.replayBefore a b ∨
        (D A).toMRDTSig.toUpdateSig.replayBefore b a) :=
    fun a b => (noncomm_iff_replayBefore a b).mp
  have hdsub₁ : downset C e ⊆ E₁ := downset_subset hc₁ he₁
  have hdsub₂ : downset C e ⊆ E₂ := downset_subset hc₂ he₂
  have hdm := isCan_downset htr hir hm
  have hsupU : SupportedOn (D A) C (E₁ ∪ E₂) := fun a ha => ha.elim (h₁ a) (h₂ a)
  have hdsupp : SupportedOn (D A) C (downset C e) := fun a ha => h₁ a (hdsub₁ ha)
  have hcld : WeaklyClosed (D A) C (downset C e) := fun a b => downset_closed a b
  have hclU : WeaklyClosed (D A) C (E₁ ∪ E₂) := weaklyClosed_union hc₁ hc₂
  have hclI : WeaklyClosed (D A) C (E₁ ∩ E₂) := by
    rintro a b hv hnc ⟨hb₁, hb₂⟩; exact ⟨hc₁ a b hv hnc hb₁, hc₂ a b hv hnc hb₂⟩
  have hcl₀ : WeaklyClosed (D A) C ((E₁ ∩ E₂) \ {e}) :=
    closure_diff_of_max hcov (fun z hz => Or.inl hz.1) hclI hmax
  have hcl₁ : WeaklyClosed (D A) C (E₁ \ {e}) :=
    closure_diff_of_max hcov Set.subset_union_left hc₁ hmax
  have hcl₂ : WeaklyClosed (D A) C (E₂ \ {e}) :=
    closure_diff_of_max hcov Set.subset_union_right hc₂ hmax
  have hclU' : WeaklyClosed (D A) C ((E₁ ∪ E₂) \ {e}) :=
    closure_diff_of_max hcov Set.Subset.rfl hclU hmax
  have peelI : ∀ F : Set (D A).Event, downset C e ⊆ F →
      (F \ {e}) ∩ downset C e = downset C e \ {e} := by
    intro F hsub; ext z
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hsub h.1, h.2⟩, h.1⟩⟩
  have peelU : ∀ F : Set (D A).Event, downset C e ⊆ F →
      (F \ {e}) ∪ downset C e = F := by
    intro F hsub; ext z; constructor
    · rintro (⟨hz, -⟩ | hz); · exact hz
      · exact hsub hz
    · intro hz; by_cases hze : z = e
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
  have jP₀ := live_merge (fun a ha => h₁ a ha.1.1) hdsupp hcl₀ hcld p
  rw [peelI _ hdsubI, peelU _ hdsubI] at jP₀
  have jP₁ := live_merge (fun a ha => h₁ a ha.1) hdsupp hcl₁ hcld p
  rw [peelI _ hdsub₁, peelU _ hdsub₁] at jP₁
  have jP₂ := live_merge (fun a ha => h₂ a ha.1) hdsupp hcl₂ hcld p
  rw [peelI _ hdsub₂, peelU _ hdsub₂] at jP₂
  have jU := live_merge h₁ h₂ hc₁ hc₂ p
  have jM := live_merge (fun a ha => h₁ a ha.1) (fun a ha => h₂ a ha.1)
    hcl₁ hcl₂ p
  rw [iM, uM] at jM
  have jD := live_merge (fun a ha => hsupU a ha.1) hdsupp hclU' hcld p
  rw [peelI _ hdsubU, peelU _ hdsubU] at jD
  rw [mem_merge, mem_merge, mem_merge, mem_merge, mem_merge, mem_merge,
    canonical_mem_iff hx₀ p, canonical_mem_iff hm p, canonical_mem_iff hx₁ p,
    canonical_mem_iff hx₂ p, canonical_mem_iff hdm p,
    ← jP₀, ← jP₁, ← jP₂, ← jU, ← jM, ← jD]

/-- **VC1 to VC5** of Section 5. VC1 and VC2 are the two equations above;
the other three are already stated canonically. -/
theorem joinLaws : CanonicalJoinLawsOn (D A) (fun _ => True) where
  vc1_merge_comm := RemoveWinsSet.vc1_merge_comm
  vc2_merge_init := fun _ _ s _ _ _ => RemoveWinsSet.vc2_merge_init s
  vc3_local_redistribute := fun C E₁ E₂ l m x y e _ =>
    RemoveWinsSet.vc3_local_redistribute C E₁ E₂ l m x y e
  vc4_causal_delta := fun C U As Bs e _ =>
    RemoveWinsSet.vc4_causal_delta C U As Bs e
  vc5_redistribute := fun C E₁ E₂ x₀ x₁ x₂ m e _ =>
    RemoveWinsSet.vc5_redistribute C E₁ E₂ x₀ x₁ x₂ m e

variable {A : Type} [DecidableEq A] [Fintype A]

/-! ## `Spec` and the certificate -/

variable (A)

variable {A}

@[simp] theorem view_sigma0 : view (sigma0 A) = ∅ := by
  ext y
  simp [view, sigma0]

/-- Erasing the timestamps commutes with the update. -/
@[simp] theorem view_step (S : St A) (e : (D A).Event) :
    view (step S e) = (specMachine A).update (view S) e.op := by
  rcases e with ⟨t, r, o⟩
  cases o with
  | remove x =>
      ext y
      simp only [view, step, specMachine, Op.op, Op.time, Finset.mem_sdiff,
        Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_insert,
        Finset.mem_erase]
      constructor
      · intro h
        exact ⟨fun hy => h ⟨(x, t), Or.inl rfl, hy ▸ rfl⟩,
          fun ⟨q, hq, hqy⟩ => h ⟨q, Or.inr hq, hqy⟩⟩
      · rintro ⟨hyx, h⟩ ⟨q, hq | hq, hqy⟩
        · exact hyx (by rw [← hqy, hq])
        · exact h ⟨q, hq, hqy⟩
  | add x =>
      ext y
      simp only [view, step, specMachine, Op.op, Finset.mem_sdiff,
        Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_filter,
        Finset.mem_insert]
      constructor
      · intro h
        by_cases hyx : y = x
        · exact Or.inl hyx
        · exact Or.inr (fun ⟨q, hq, hqy⟩ => h ⟨q, ⟨hq, by rw [hqy]; exact hyx⟩, hqy⟩)
      · rintro (rfl | h) ⟨q, ⟨hq, hqx⟩, hqy⟩
        · exact hqx (by rw [hqy])
        · exact h ⟨q, hq, hqy⟩

theorem view_fold (S : St A) (ops : List (D A).Event) :
    view (applySeq (D A).toMRDTSig.toUpdateSig S ops)
      = (ops.map Op.op).foldl (specMachine A).update (view S) := by
  induction ops generalizing S with
  | nil => rfl
  | cons e ops ih => simpa [applySeq] using ih (step S e)

/-- The sequential premise, unrestricted. -/
theorem anyOrderSound : Soundness.AnyOrderSound (D A) (historySpec A) := by
  intro pi q
  have hlabels : projectedUpdates (D := (D A).toMRDTSig) pi
      = DeterministicSpec.updateLabels (pi.map Op.op) := by
    simp [projectedUpdates, DeterministicSpec.updateLabels, List.map_map,
      Function.comp]
  rw [hlabels, historySpec, (specMachine A).updates_query_iff]
  change decide (q ∈ view (applySeq (D A).toMRDTSig.toUpdateSig (sigma0 A) pi)) = _
  rw [view_fold, view_sigma0]
  rfl

/-! ## The join lemma -/

/-! ## `Laws(D_type, Spec)`: the fourth law

SPEC-NON-COMM is the one law of Section 4 that mentions `Spec`. In `Spec` an
`add` is an insertion and a `remove` is an erasure, so the only pair that
conflicts there is an `add x` against a `remove x`. That is exactly the pair
`rc` orders, so RC-NON-COMM read right to left says the implementation does
not commute it either. -/

/-- **SPEC-NON-COMM**: no implementation commutation erases a specification
conflict. -/
theorem spec_non_comm : Interface.spec_non_comm (D A) (historySpec A) := by
  intro e₁ e₂ hn hc
  refine hn (DeterministicSpec.language_commutes (specMachine A) _ _ ?_)
  have hno : ¬ ((D A).EventRcBefore e₁ e₂ ∨ (D A).EventRcBefore e₂ e₁) :=
    fun h => (rc_non_comm e₁ e₂).mpr h hc
  simp only [eventRcBefore_iff, not_or, not_exists, not_and] at hno
  intro S
  change Finset A at S
  rcases h₁ : e₁.op with x | x <;> rcases h₂ : e₂.op with y | y <;>
    simp only [specMachine]
  · exact Finset.insert_comm y x S
  · have hxy : x ≠ y := fun h => hno.1 x h₁ (by rw [h₂, h])
    exact Finset.erase_insert_of_ne hxy
  · have hxy : y ≠ x := fun h => hno.2 y h₂ (by rw [h₁, h])
    exact (Finset.erase_insert_of_ne hxy).symm
  · exact Finset.erase_right_comm

/-- **The bundle the specification route consumes**: the obligations of
Section 5 together with SPEC-NON-COMM, the one law of Section 4 that
mentions `Spec`. -/
theorem obligations : SpecObligations (D A) (historySpec A) :=
  SpecObligations.ofUniform laws rc_non_comm cond_comm joinLaws spec_non_comm

/-! # Specification visibility, without SPEC-NON-COMM

`Soundness.certifiedSpecRA_any` asks a row for one thing, that
`Soundness.joint` has no loop. For a row whose events all commute that is
immediate, `lo^C_E` being empty. This row's `rc` is **not** empty, so
`lo^C_E` carries same-time arrows between concurrent events, and such an
arrow is free to point backwards in time. The loop has to be ruled out.

It is ruled out because `rc` here runs an addition to a removal of the same element and nowhere else, so a
same-time arrow's target can start no further arrow, and it absorbs its
non-commuting visible successors by the side condition `lo^C_E` carries. Such
a target is therefore a **dead end**: no edge of `joint` leaves it at all.
Any loop would have to pass through one, and a loop with no same-time arrow
at all is a `vis` loop. That is `no_out` and `joint_acyclic`.

`edge_paperOrder` is where this row differs from the flags, and it is worth
being plain about it. For a row whose `rc` is indexed, like this one,
specification visibility cannot be absorbed into `vis` the way it can when
`rc` splits the alphabet globally: cross-index `vis` arrows would make that
relation loop. It is absorbed into `lo^C_E` instead, and that step is the
row's **own** SPEC-NON-COMM. So this row does not avoid the fourth law; what
it shows is that the law is not needed in the **adequacy theorem**, only in
the row, and that the criterion is reachable through the same `joint`
interface as everything else here.
-/

variable {C : Ctx (D A)} {E : Set (D A).Event}

/-- **Every edge of `joint` is a `lo^C_E` edge.** The right disjunct is one
already; the left is one by this row's SPEC-NON-COMM. -/
theorem edge_paperOrder {a b : (D A).Event} (h : Soundness.joint (D A) (historySpec A) C E a b) :
    paperOrder (policy (D A)) C E a b :=
  h.2.2.elim (fun hs => specVisibility_sub_paperOrder
    (Interface.spec_non_comm.covered spec_non_comm) _ E _ _ hs) id

/-- The target of a same-time arrow, with the side condition `lo^C_E`
carries. -/
def Blocked (C : Ctx (D A)) (E : Set (D A).Event) (w : (D A).Event) : Prop :=
  w ∈ E ∧ (∃ x, w.op = .remove x) ∧ ¬ ∃ c ∈ E, C.vis w c ∧ ¬ (D A).Commutes w c

/-- A same-time arrow lands on one. -/
theorem blocked_of_concurrent {a b : (D A).Event} (hbE : b ∈ E)
    (h : ¬ C.vis a b ∧ ¬ C.vis b a ∧ (D A).RcBefore a.op b.op ∧
      ¬ ∃ c ∈ E, C.vis b c ∧ ¬ (D A).Commutes b c) : Blocked C E b := by
  obtain ⟨x, -, hb⟩ := (eventRcBefore_iff a b).mp h.2.2.1
  exact ⟨hbE, ⟨x, hb⟩, h.2.2.2⟩

/-- **A `Blocked` event is a dead end.** Nothing leaves it: the absorber
kills the causal disjunct, and `rc` starts no arrow here. -/
theorem no_out {w z : (D A).Event} (hw : Blocked C E w) : ¬ Soundness.joint (D A) (historySpec A) C E w z := by
  intro hj
  rcases edge_paperOrder hj with ⟨hv, hnc⟩ | hconc
  · exact hw.2.2 ⟨z, hj.2.1, hv, hnc⟩
  · obtain ⟨x, hwx⟩ := hw.2.1
    obtain ⟨y, hw', -⟩ := (eventRcBefore_iff w z).mp hconc.2.2.1
    rw [hwx] at hw'
    exact absurd hw' (by simp)

/-- Every path is causal, or has reached a dead end. -/
theorem vis_or_blocked (hvs : VisStrict (D A) C) :
    ∀ {a b : (D A).Event}, Relation.TransGen (Soundness.joint (D A) (historySpec A) C E) a b →
      C.vis a b ∨ Blocked C E b := by
  intro a b h
  induction h with
  | @single b hedge =>
    rcases edge_paperOrder hedge with ⟨hv, -⟩ | hconc
    · exact Or.inl hv
    · exact Or.inr (blocked_of_concurrent hedge.2.1 hconc)
  | @tail y z _ hedge ih =>
    rcases ih with hv | hb
    · rcases edge_paperOrder hedge with ⟨hv', -⟩ | hconc
      · exact Or.inl (hvs.1 hv hv')
      · exact Or.inr (blocked_of_concurrent hedge.2.1 hconc)
    · exact absurd hedge (no_out hb)

/-- **No loop.** A causal loop is impossible, and a loop through a dead end
would have to leave it. -/
theorem joint_acyclic : Soundness.JointAcyclic (D A) (historySpec A) := by
  intro C E hvs a h
  rcases vis_or_blocked hvs h with hv | hb
  · exact hvs.2 a hv
  · obtain ⟨b, hb', -⟩ := Relation.TransGen.head'_iff.mp h
    exact no_out hb hb'

end LeanProofs.NoSpecNonComm.Implementations.RemoveWinsSet

