import LeanProofs.Implementations.ORSet.Definition
import LeanProofs.Interface.VCRoute
import LeanProofs.Soundness.LinearExtension

/-!
# The OR-set: discharging `Laws(D_type)`

The first row here with a nonempty `rc`, so the three conditions of Section 4
have real content. They are proved from one observation: `add x` and
`remove x` disagree only about records whose element is `x`, and every other
pair of operations commutes outright.

After the laws come this row's canonical states and then VC1 to VC5. The
OR-set cannot discharge the conditions the way a grow-only row does, by
proving an arbitrary-state equation and specialising it: its `merge` reads
its base, and the arbitrary-state VC3 is false here. The conditions are
therefore proved as
Section 5 states them, premises and all, from the closed description of
`can(E)` that `canonical_mem_iff` and `live_join` provide.

Because the conditions are proved here and not from `Join`, they can be
used to obtain it: `LinearExtension.lean` builds this row's join lemma by
handing `joinLaws` to `Metatheory.joinLemma_of_vcs`, the same metatheory
step a commuting row takes. The OR-set therefore travels the VC route end
to end, which the arbitrary-state form of the conditions did not allow.
-/

namespace LeanProofs.Implementations.ORSet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

variable {A : Type} [DecidableEq A]

/-- `rc` relates exactly the pairs `remove x`, `add x`. -/
@[simp] theorem rcBefore_iff (o₁ o₂ : AppOp A) :
    (D A).RcBefore o₁ o₂ ↔ ∃ x, o₁ = .remove x ∧ o₂ = .add x := by
  cases o₁ with
  | add x =>
      cases o₂ with
      | add y => simp [Impl.RcBefore, rc]
      | remove y => simp only [Impl.RcBefore, rc]; split <;> simp
  | remove x =>
      cases o₂ with
      | add y =>
          simp only [Impl.RcBefore, rc]
          by_cases h : x = y
          · subst h; simp
          · simp [h, Ne.symm h]
      | remove y => simp [Impl.RcBefore, rc]

/-- The event-level reading of the same fact. -/
theorem eventRcBefore_iff (e₁ e₂ : (D A).Event) :
    (D A).EventRcBefore e₁ e₂ ↔ ∃ x, e₁.op = .remove x ∧ e₂.op = .add x :=
  rcBefore_iff _ _

@[simp] theorem mem_step (S : St A) (e : Event A) (p : A × Timestamp) :
    p ∈ step S e ↔ match e.op with
    | .add x => p = (x, e.time) ∨ p ∈ S
    | .remove x => p ∈ S ∧ p.1 ≠ x := by
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
    · obtain ⟨x, ha, hb⟩ := (eventRcBefore_iff _ _).mp hr
      have h := Finset.ext_iff.mp (hc (∅ : St A)) (x, e₂.time)
      simp [step, ha, hb] at h
    · obtain ⟨x, hb, ha⟩ := (eventRcBefore_iff _ _).mp hr
      have h := Finset.ext_iff.mp (hc (∅ : St A)) (x, e₁.time)
      simp [step, ha, hb] at h

/-- **NO-RC-CHAIN**. A `remove` can only start an edge and an `add` can only
end one, so two edges never meet. -/
theorem no_rc_chain (o₁ o₂ o₃ : AppOp A) :
    ¬ ((D A).RcBefore o₁ o₂ ∧ (D A).RcBefore o₂ o₃) := by
  rintro ⟨h₁, h₂⟩
  obtain ⟨x, -, hb⟩ := (rcBefore_iff _ _).mp h₁
  obtain ⟨y, hb', -⟩ := (rcBefore_iff _ _).mp h₂
  rw [hb] at hb'; cases hb'

/-! ### The absorber argument for COND-COMM

Swapping `remove x` with a concurrent `add x` changes the state only in the
records whose element is `x`. The absorber of the pair is another `remove x`,
and it erases exactly those records, so the two orders agree after it. -/

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
  have habs : e''.op = AppOp.remove x := by
    rcases (rc_non_comm e' e'').mp hnc with h | h
    · obtain ⟨y, ha, -⟩ := (eventRcBefore_iff _ _).mp h
      rw [he'] at ha; cases ha
    · obtain ⟨y, hr, ha⟩ := (eventRcBefore_iff _ _).mp h
      rw [he'] at ha; injection ha with hxy; subst y; exact hr
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
      ↔ ∃ x, a.op = AppOp.remove x ∧ b.op = AppOp.add x := by
  refine Iff.trans ?_ (rcBefore_iff a.op b.op)
  exact @OperationPolicy.lift_replayOrder_iff (D A).toMRDTSig.toUpdateSig
    (Interface.policy (D A)) a b

theorem noncomm_iff_replayBefore (a b : (D A).Event) :
    ¬ (D A).toMRDTSig.toUpdateSig.commutes a b ↔
      (D A).toMRDTSig.toUpdateSig.replayBefore a b
        ∨ (D A).toMRDTSig.toUpdateSig.replayBefore b a := by
  simpa only [replayBefore_iff] using
    (rc_non_comm a b).trans (by simp only [eventRcBefore_iff])

/-! ## Canonical states contain exactly the live records -/

/-- `pi(sigma0)`, the state after replaying a list. -/
abbrev Run (ops : List (D A).Event) : St A :=
  applySeq (D A).toMRDTSig.toUpdateSig (D A).toMRDTSig.init ops

/-- No event in the list removes `x`. -/
def NoRemove (ops : List (D A).Event) (x : A) : Prop :=
  ∀ e ∈ ops, e.op ≠ AppOp.remove x

theorem pair_preserved {S : St A} {p : A × Timestamp} (hs : p ∈ S)
    (ops : List (D A).Event) (hn : NoRemove ops p.1) :
    p ∈ (show St A from applySeq (D A).toMRDTSig.toUpdateSig S ops) := by
  induction ops generalizing S with
  | nil => exact hs
  | cons e ops ih =>
      have he := hn e (by simp)
      have hn' : NoRemove ops p.1 := fun a ha => hn a (by simp [ha])
      apply ih (S := step S e) _ hn'
      rcases e with ⟨t, r, o⟩
      cases o with
      | add x => simp [step, Op.op, hs]
      | remove x =>
          have hx : p.1 ≠ x := by intro h; exact he (by simp [Op.op, h])
          simp [step, Op.op, hs, hx]

/-- A record is in a replayed state exactly when some add produced it and no
later event in the list removed its element. -/
theorem mem_run_iff_suffix (ops : List (D A).Event) (p : A × Timestamp) :
    p ∈ Run ops ↔ ∃ pre a post, ops = pre ++ a :: post ∧
      a.op = AppOp.add p.1 ∧ a.time = p.2 ∧ NoRemove post p.1 := by
  constructor
  · induction ops using List.reverseRecOn with
    | nil => simp [Run, applySeq, Impl.toMRDTSig]
    | append_singleton ops e ih =>
        intro hm
        change p ∈ (show St A from
          applySeq (D A).toMRDTSig.toUpdateSig (D A).toMRDTSig.init (ops ++ [e])) at hm
        rw [applySeq_append_single] at hm
        change p ∈ step (Run ops) e at hm
        rcases hop : e.op with x | x
        · simp only [step, hop, Finset.mem_insert] at hm
          rcases hm with h | h
          · have hx : x = p.1 := (congrArg Prod.fst h).symm
            have ht : e.time = p.2 := (congrArg Prod.snd h).symm
            exact ⟨ops, e, [], by simp, hx ▸ hop, ht, by simp [NoRemove]⟩
          · obtain ⟨pre, a, post, hsplit, ha, ht, hn⟩ := ih h
            refine ⟨pre, a, post ++ [e], by simp [hsplit, List.append_assoc], ha, ht, ?_⟩
            intro r hr
            rcases List.mem_append.mp hr with hr | hr
            · exact hn r hr
            · have hre : r = e := List.mem_singleton.mp hr
              subst r
              simp [hop]
        · simp only [step, hop, Finset.mem_filter] at hm
          obtain ⟨pre, a, post, hsplit, ha, ht, hn⟩ := ih hm.1
          refine ⟨pre, a, post ++ [e], by simp [hsplit, List.append_assoc], ha, ht, ?_⟩
          intro r hr
          rcases List.mem_append.mp hr with hr | hr
          · exact hn r hr
          · have hre : r = e := List.mem_singleton.mp hr
            subst r
            intro hrem
            rw [hop] at hrem
            injection hrem with hx
            exact hm.2 hx.symm
  · rintro ⟨pre, a, post, rfl, ha, ht, hn⟩
    have hp : p ∈ step (Run pre) a := by
      have heq : (p.1, a.time) = p := by rw [ht]
      simp [step, ha, heq]
    have hpost := pair_preserved hp post hn
    simpa [Run, applySeq, List.foldl_append] using hpost

/-- A relation edge cannot point from a suffix into a preceding position. -/
theorem not_edge_to_prefix {R : (D A).Event → (D A).Event → Prop}
    {pre post : List (D A).Event} {a r : (D A).Event}
    (hr : respects (pre ++ a :: post) R) (hm : r ∈ pre) : ¬ R a r :=
  (List.pairwise_append.mp hr).2.2 r hm a (by simp)

theorem not_edge_from_suffix {R : (D A).Event → (D A).Event → Prop}
    {pre post : List (D A).Event} {a r : (D A).Event}
    (hr : respects (pre ++ a :: post) R) (hm : r ∈ post) : ¬ R r a :=
  (List.pairwise_cons.mp (List.pairwise_append.mp hr).2.1).1 r hm

/-- No remove of `x` in `E` sees the add `a`. -/
def Survives (C : Ctx (D A))
    (E : Set (D A).Event) (a : (D A).Event) (x : A) : Prop :=
  ¬ ∃ r ∈ E, C.vis a r ∧ r.op = AppOp.remove x

/-- The record `p` is live in `E`: it was added by an event of `E` that no
remove of `E` observes. -/
def Live (C : Ctx (D A))
    (E : Set (D A).Event) (p : A × Timestamp) : Prop :=
  ∃ a ∈ E, a.op = AppOp.add p.1 ∧ a.time = p.2 ∧ Survives C E a p.1

/-- **Fact 1.** Any replay of `E` that respects `lo^C_E` contains exactly the
live records, so the state does not depend on which replay was taken. -/
theorem mem_run_iff_live {C : Ctx (D A)}
    {E : Set (D A).Event} {ops : List (D A).Event}
    (hp : listPermOf ops E) (hr : respects ops (loOn C E)) (p : A × Timestamp) :
    p ∈ Run ops ↔ Live C E p := by
  rw [mem_run_iff_suffix]
  constructor
  · rintro ⟨pre, a, post, hs, ha, ht, hn⟩
    subst ops
    refine ⟨a, (hp.2 a).mp (by simp), ha, ht, ?_⟩
    rintro ⟨r, hre, hv, hrem⟩
    have hm : r ∈ pre ++ a :: post := (hp.2 r).mpr hre
    rcases List.mem_append.mp hm with hm | hm
    · apply not_edge_to_prefix hr hm
      exact Or.inl ⟨hv, Or.inr ((replayBefore_iff r a).mpr ⟨p.1, hrem, ha⟩)⟩
    · rcases List.mem_cons.mp hm with heq | hm
      · rw [heq, ha] at hrem; cases hrem
      · exact hn r hm hrem
  · rintro ⟨a, hae, ha, ht, hn⟩
    obtain ⟨pre, post, hs⟩ := List.append_of_mem ((hp.2 a).mpr hae)
    refine ⟨pre, a, post, hs, ha, ht, ?_⟩
    subst ops
    intro r hm hrem
    apply not_edge_from_suffix hr hm
    have hre : r ∈ E := (hp.2 r).mp (by simp [hm])
    have hrc : (D A).toMRDTSig.toUpdateSig.replayBefore r a :=
      (replayBefore_iff r a).mpr ⟨p.1, hrem, ha⟩
    by_cases hva : C.vis r a
    · exact Or.inl ⟨hva, Or.inl hrc⟩
    · refine Or.inr ⟨hva, ?_, hrc, ?_⟩
      · exact fun hv => hn ⟨r, hre, hv, hrem⟩
      · rintro ⟨c, hce, hvc, hc⟩
        rcases hc with hc | hc
        · obtain ⟨x, ha', -⟩ := (replayBefore_iff a c).mp hc
          rw [ha] at ha'; cases ha'
        · obtain ⟨x, hc, ha'⟩ := (replayBefore_iff c a).mp hc
          rw [ha] at ha'; injection ha' with hx
          subst x
          exact hn ⟨c, hce, hvc, hc⟩

theorem canonical_mem_iff {C : Ctx (D A)}
    {E : Set (D A).Event} {s : St A}
    (hs : Interface.IsCanOn (D A) C E s) (p : A × Timestamp) : p ∈ s ↔ Live C E p := by
  obtain ⟨ops, hp, hr, hf⟩ := hs
  rw [← hf]
  exact mem_run_iff_live hp hr p

/-- **Fact 2.** Timestamps identify events, so only one event can add a given
record and liveness is a statement about that event alone. -/
theorem live_iff_fixed_add {C : Ctx (D A)}
    {E : Set (D A).Event} (hsub : E ⊆ C.events)
    {p : A × Timestamp} {a : (D A).Event}
    (hac : a ∈ C.events) (ha : a.op = AppOp.add p.1) (ht : a.time = p.2) :
    Live C E p ↔ a ∈ E ∧ Survives C E a p.1 := by
  constructor
  · rintro ⟨b, hb, -, hbt, hs⟩
    have heq : b = a := C.ts_unique (hsub hb) hac (hbt.trans ht.symm)
    subst b
    exact ⟨hb, hs⟩
  · rintro ⟨he, hs⟩
    exact ⟨a, he, ha, ht, hs⟩

/-- **Fact 3.** Liveness over the union is the Boolean that `merge` computes.
The two `hk` steps are where causal closure is used: a branch that observes a
remove covering the add must contain the add as well. -/
theorem live_join {C : Ctx (D A)}
    {E₁ E₂ : Set (D A).Event}
    (hsub₁ : E₁ ⊆ C.events) (hsub₂ : E₂ ⊆ C.events)
    (hclosed₁ : ∀ a b, C.vis a b →
      ¬ (D A).toMRDTSig.toUpdateSig.commutes a b → b ∈ E₁ → a ∈ E₁)
    (hclosed₂ : ∀ a b, C.vis a b →
      ¬ (D A).toMRDTSig.toUpdateSig.commutes a b → b ∈ E₂ → a ∈ E₂)
    (p : A × Timestamp) :
    Live C (E₁ ∪ E₂) p ↔
      (Live C (E₁ ∩ E₂) p ∧ Live C E₁ p ∧ Live C E₂ p) ∨
      (Live C E₁ p ∧ ¬ Live C (E₁ ∩ E₂) p) ∨
      (Live C E₂ p ∧ ¬ Live C (E₁ ∩ E₂) p) := by
  by_cases hex : ∃ a ∈ E₁ ∪ E₂, a.op = AppOp.add p.1 ∧ a.time = p.2
  · obtain ⟨a, hae, ha, ht⟩ := hex
    have hac : a ∈ C.events := hae.elim (fun h => hsub₁ h) (fun h => hsub₂ h)
    have huni : E₁ ∪ E₂ ⊆ C.events := fun e he => he.elim (fun h => hsub₁ h) (fun h => hsub₂ h)
    have hint : E₁ ∩ E₂ ⊆ C.events := fun e he => hsub₁ he.1
    rw [live_iff_fixed_add huni hac ha ht, live_iff_fixed_add hint hac ha ht,
      live_iff_fixed_add hsub₁ hac ha ht, live_iff_fixed_add hsub₂ hac ha ht]
    have hk₁ : ¬ Survives C E₁ a p.1 → a ∈ E₁ := by
      intro hn
      obtain ⟨r, hr, hv, hop⟩ := Classical.not_not.mp hn
      exact hclosed₁ a r hv ((noncomm_iff_replayBefore a r).mpr
        (Or.inr ((replayBefore_iff r a).mpr ⟨p.1, hop, ha⟩))) hr
    have hk₂ : ¬ Survives C E₂ a p.1 → a ∈ E₂ := by
      intro hn
      obtain ⟨r, hr, hv, hop⟩ := Classical.not_not.mp hn
      exact hclosed₂ a r hv ((noncomm_iff_replayBefore a r).mpr
        (Or.inr ((replayBefore_iff r a).mpr ⟨p.1, hop, ha⟩))) hr
    have hu : Survives C (E₁ ∪ E₂) a p.1 ↔
        Survives C E₁ a p.1 ∧ Survives C E₂ a p.1 := by
      simp only [Survives, Set.mem_union]
      constructor
      · intro h; exact ⟨fun ⟨r, hr, hv, ho⟩ => h ⟨r, Or.inl hr, hv, ho⟩,
          fun ⟨r, hr, hv, ho⟩ => h ⟨r, Or.inr hr, hv, ho⟩⟩
      · rintro ⟨h₁, h₂⟩ ⟨r, hr | hr, hv, ho⟩
        · exact h₁ ⟨r, hr, hv, ho⟩
        · exact h₂ ⟨r, hr, hv, ho⟩
    have hi₁ : Survives C E₁ a p.1 → Survives C (E₁ ∩ E₂) a p.1 :=
      fun h ⟨r, hr, hv, ho⟩ => h ⟨r, hr.1, hv, ho⟩
    have hi₂ : Survives C E₂ a p.1 → Survives C (E₁ ∩ E₂) a p.1 :=
      fun h ⟨r, hr, hv, ho⟩ => h ⟨r, hr.2, hv, ho⟩
    rw [hu]
    simp only [Set.mem_union, Set.mem_inter_iff]
    tauto
  · have hn (E : Set (D A).Event) (hs : E ⊆ E₁ ∪ E₂) : ¬ Live C E p := by
      rintro ⟨a, ha, hop, ht, -⟩
      exact hex ⟨a, hs ha, hop, ht⟩
    have hnU := hn (E₁ ∪ E₂) Set.Subset.rfl
    have hnI := hn (E₁ ∩ E₂) (fun _ h => Or.inl h.1)
    have hn₁ := hn E₁ Set.subset_union_left
    have hn₂ := hn E₂ Set.subset_union_right
    simp [hnU, hnI, hn₁, hn₂]

/-! ## VC1 and VC2

Two of the five hold at arbitrary states for this `merge`, so they are set
identities with no premises, exactly as a grow-only row's are. -/

/-- `merge(l,a,b) = merge(l,b,a)` at any states. This is **VC1** exactly:
the paper states it over arbitrary states too. -/
theorem vc1_merge_comm (l a b : (D A).Sigma) :
    (D A).merge l a b = (D A).merge l b a := by
  change mergeState l a b = mergeState l b a
  ext p
  simp only [mergeState, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

/-- `merge(sigma0, sigma0, s) = s` at any `s`. **VC2** asks for it only at a
canonical `s`. -/
theorem vc2_merge_init (s : (D A).Sigma) :
    (D A).merge (D A).sigma0 (D A).sigma0 s = s := by
  change mergeState ∅ ∅ s = s
  ext p
  simp only [mergeState, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  simp

/-! ## The three canonical conditions

The states VC3, VC4 and VC5 mention are canonical for event sets built from
`E1`, `E2` and `down(e)`. Each nest of merges is read pointwise through
`canonical_mem_iff` and resolved by `live_join`, the row's own description
of liveness over a union.

`mergeProp` below is the Boolean `merge` computes at a record. Writing both
`merge` and `live_join` in that one shape turns VC3 and VC5 into chains of
rewrites with no propositional search at all. -/

/-- The Boolean `merge` computes at a single record: keep it when the base
and both branches have it, or when one branch has it and the base does
not. -/
def mergeProp (L B C : Prop) : Prop := (L ∧ B ∧ C) ∨ (B ∧ ¬ L) ∨ (C ∧ ¬ L)

theorem mem_merge (l a b : (D A).Sigma) (p : A × Timestamp) :
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
    (p : A × Timestamp) :
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

/-- The one fact about this row that **VC4** needs: in the removal case, a
record that survives `U \ {e}` but not `down(e) \ {e}` cannot carry the
element `e` removes.

The add that produced it must be seen by `e`. If `e` saw nothing of it,
`lo^C_U` would have an edge out of `e`: a visibility edge when `e` sees the
add, and otherwise the `rc` edge `rem x --rc--> add x`, whose absorber
clause can only be met by a second removal of `x` in `U`, which would have
killed the record in `U \ {e}` as well. Either way `e` is not maximal. -/
theorem live_of_removed {C : Ctx (D A)} {U : Set (D A).Event}
    {As Bs : (D A).Sigma} {e : (D A).Event} {x : A}
    (hUsub : SupportedOn (D A) C U) (hUcl : WeaklyClosed (D A) C U)
    (heU : e ∈ U) (hmax : MaximalOn (D A) C U e) (hex : e.op = AppOp.remove x)
    (hA : IsCanOn (D A) C (U \ {e}) As)
    (hB : IsCanOn (D A) C (downset C e \ {e}) Bs)
    (p : A × Timestamp) (hpA : p ∈ As) (hpx : p.1 = x) : p ∈ Bs := by
  letI : EventOrder (D A).toMRDTSig.toUpdateSig := Interface.rcOrder (D A)
  have hdsub : downset C e ⊆ U := downset_subset hUcl heU
  obtain ⟨α, hαU, hαop, hαt, hαs⟩ := (canonical_mem_iff hA p).mp hpA
  have hrbe : (D A).toMRDTSig.toUpdateSig.replayBefore e α := by
    rw [replayBefore_iff]; exact ⟨x, hex, by rw [hαop, hpx]⟩
  have hvis : C.vis α e := by
    by_contra hnv
    by_cases hve : C.vis e α
    · exact hmax α hαU.1 hαU.2 (Or.inl ⟨hve, Or.inl hrbe⟩)
    · by_cases habs : ∃ e₃ ∈ U, C.vis α e₃ ∧
          ((D A).toMRDTSig.toUpdateSig.replayBefore α e₃ ∨
            (D A).toMRDTSig.toUpdateSig.replayBefore e₃ α)
      · obtain ⟨e₃, he₃U, hv₃, hrb₃⟩ := habs
        have he₃op : e₃.op = AppOp.remove p.1 := by
          rcases hrb₃ with h | h
          · rw [replayBefore_iff] at h
            obtain ⟨y, hy, -⟩ := h; rw [hαop] at hy; cases hy
          · rw [replayBefore_iff] at h
            obtain ⟨y, hy, hy'⟩ := h
            rw [hαop] at hy'; injection hy' with hyx; exact hyx ▸ hy
        exact hαs ⟨e₃, ⟨he₃U, by rintro rfl; exact hnv hv₃⟩, hv₃, he₃op⟩
      · exact hmax α hαU.1 hαU.2 (Or.inr ⟨hve, hnv, hrbe, habs⟩)
  have hnc : ¬ (D A).toMRDTSig.toUpdateSig.commutes α e :=
    (noncomm_iff_replayBefore α e).mpr (Or.inr hrbe)
  rw [canonical_mem_iff hB]
  refine ⟨α, ⟨Or.inr (Relation.TransGen.single ⟨hvis, hnc⟩), hαU.2⟩, hαop, hαt, ?_⟩
  rintro ⟨r, hr, hv, hop⟩
  exact hαs ⟨r, ⟨hdsub hr.1, hr.2⟩, hv, hop⟩

/-- **VC4** CAUSAL-DELTA, proved for this row rather than derived from the
join lemma. The two cases are the two shapes of `do`. -/
theorem vc4_causal_delta :
    @CausalDeltaLaw (D A).toMRDTSig (Interface.rcOrder (D A)) := by
  letI : EventOrder (D A).toMRDTSig.toUpdateSig := Interface.rcOrder (D A)
  intro C U As Bs e htr hir hUsub hUcl heU hmax hA hB
  change St A at As Bs
  change mergeState Bs As (step Bs e) = step As e
  ext p
  cases hop : e.op with
  | add x =>
      have hnB : (x, e.time) ∉ Bs := by
        intro hmem
        obtain ⟨α, hα, -, hαt, -⟩ := (canonical_mem_iff hB _).mp hmem
        exact hα.2 (C.ts_unique
          (hUsub α (downset_subset hUcl heU hα.1)) (hUsub e heU) hαt)
      have hkey : p = (x, e.time) → p ∉ Bs := by rintro rfl; exact hnB
      simp only [mergeState, Finset.mem_union, Finset.mem_inter,
        Finset.mem_sdiff, mem_step, hop]
      tauto
  | remove x =>
      have hkey : p ∈ As → p ∉ Bs → p.1 ≠ x := fun hpA hpB hq =>
        hpB (live_of_removed hUsub hUcl heU hmax hop hA hB p hpA hq)
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
  have jM := live_merge (fun a ha => h₁ a ha.1) (fun a ha => h₂ a ha.1) hcl₁ hcl₂ p
  rw [iM, uM] at jM
  have jD := live_merge (fun a ha => hsupU a ha.1) hdsupp hclU' hcld p
  rw [peelI _ hdsubU, peelU _ hdsubU] at jD
  rw [mem_merge, mem_merge, mem_merge, mem_merge, mem_merge, mem_merge,
    canonical_mem_iff hx₀ p, canonical_mem_iff hm p, canonical_mem_iff hx₁ p,
    canonical_mem_iff hx₂ p, canonical_mem_iff hdm p,
    ← jP₀, ← jP₁, ← jP₂, ← jU, ← jM, ← jD]

/-- **VC1 to VC5** of Section 5, in the paper's form. VC1 and VC2 are
instances of the two equations above; the other three are already stated
canonically. -/
theorem joinLaws : CanonicalJoinLaws (D A) where
  vc1_merge_comm := ORSet.vc1_merge_comm
  vc2_merge_init := fun _ _ s _ _ => ORSet.vc2_merge_init s
  vc3_local_redistribute := ORSet.vc3_local_redistribute
  vc4_causal_delta := ORSet.vc4_causal_delta
  vc5_redistribute := ORSet.vc5_redistribute

/-- **Everything the metatheory consumes.** The same bundle a commuting row
supplies. The OR-set's operations do not commute, and `Obligations` does not
ask them to: what it asks for is `Laws(D_type)` and the five conditions of
Section 5, both of which this row proves above. -/
theorem obligations : Obligations (D A) :=
  ⟨laws, rc_non_comm, cond_comm, joinLaws⟩

end LeanProofs.Implementations.ORSet
