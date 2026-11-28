import LeanProofs_no_spec_non_comm.Implementations.DisableWinsFlag.Definition
import LeanProofs_no_spec_non_comm.Metatheory.Adequacy
import LeanProofs_no_spec_non_comm.Soundness.RALinearizability

/-!
**A duplicate, plus one section.** Everything up to the last section is
`Implementations/DisableWinsFlag/VCs.lean` with the namespace changed. The last section
is what this folder adds: one witness respecting `vis` and `lo^C_E` at once,
which gives **specification visibility** with no appeal to SPEC-NON-COMM
although this row proves that law.

# The disable-wins flag: every obligation

`Laws(D_type, Spec)` of Section 4 and VC1 to VC5 of Section 5, all four laws
and all five conditions, for the tuple of `Definition.lean`. `obligations`
bundles what the metatheory consumes; `spec_non_comm` and `anyOrderSound` are the
two further premises `Soundness.certifiedSpecRA` asks for.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.DisableWinsFlag

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

/-! ### Unfolding `do` -/

theorem step_winning (s : St) (e : Event) (h : e.op = .winning) :
    step s e = fun r => if r = e.rep then ((s r).1 + 1, true) else s r := by
  simp only [step, h]

theorem step_reset (s : St) (e : Event) (h : e.op = .reset) :
    step s e = fun r => ((s r).1, false) := by
  simp only [step, h]

/-! ### `rc` -/

/-- `rc` relates exactly the pair `reset`, `winning`. -/
@[simp] theorem rcBefore_iff (o₁ o₂ : AppOp) :
    D.RcBefore o₁ o₂ ↔ o₁ = .reset ∧ o₂ = .winning := by
  cases o₁ <;> cases o₂ <;> simp [Impl.RcBefore, rc]

/-- The event-level reading. -/
theorem eventRcBefore_iff (e₁ e₂ : D.Event) :
    D.EventRcBefore e₁ e₂ ↔
      e₁.op = .reset ∧ e₂.op = .winning :=
  rcBefore_iff _ _

/-! ### Commutation -/

theorem commutes_symm {e₁ e₂ : D.Event}
    (h : D.Commutes e₁ e₂) :
    D.Commutes e₂ e₁ := fun s => (h s).symm

/-- Equal requests commute, whatever their issuers. Two `winning` events add
to their own rows and agree on the bit; two `reset` events agree outright. -/
theorem commutes_of_same_op (e₁ e₂ : D.Event)
    (h : e₁.op = e₂.op) : D.Commutes e₁ e₂ := by
  intro s
  change step (step s e₁) e₂ = step (step s e₂) e₁
  cases h₁ : e₁.op with
  | winning =>
      have h₂ : e₂.op = AppOp.winning := h.symm.trans h₁
      simp only [step, h₁, h₂]
      funext r
      by_cases hp : r = e₁.rep
      · by_cases hq : r = e₂.rep
        · have hpq : e₁.rep = e₂.rep := hp ▸ hq
          simp [hp, hq, hpq]
        · have hne : ¬ (e₁.rep = e₂.rep) := hp ▸ hq
          simp [hp, hq, hne]
      · by_cases hq : r = e₂.rep
        · have hne : ¬ (e₂.rep = e₁.rep) := hq ▸ hp
          simp [hp, hq, hne]
        · simp [hp, hq]
  | reset =>
      have h₂ : e₂.op = AppOp.reset := h.symm.trans h₁
      simp only [step, h₁, h₂]

/-- A `reset` and a `winning` do not commute: performed in one order the
issuer's bit ends up set, in the other it ends up clear. -/
theorem not_commutes_reset_winning (e₁ e₂ : D.Event)
    (h₁ : e₁.op = .reset) (h₂ : e₂.op = .winning) :
    ¬ D.Commutes e₁ e₂ := by
  intro hc
  have h := congrFun (hc (fun _ => (0, false))) e₂.rep
  simp only [step, h₁, h₂] at h
  simp at h

/-- **RC-NON-COMM**. -/
theorem rc_non_comm (e₁ e₂ : D.Event) :
    ¬ D.Commutes e₁ e₂ ↔
      D.EventRcBefore e₁ e₂
        ∨ D.EventRcBefore e₂ e₁ := by
  simp only [eventRcBefore_iff]
  cases h₁ : e₁.op with
  | winning =>
      cases h₂ : e₂.op with
      | winning => simp [commutes_of_same_op e₁ e₂ (h₁.trans h₂.symm)]
      | reset =>
          have hn : ¬ D.Commutes e₁ e₂ := fun hc =>
            not_commutes_reset_winning e₂ e₁ h₂ h₁ (commutes_symm hc)
          simp [hn, h₁, h₂]
  | reset =>
      cases h₂ : e₂.op with
      | winning => simp [not_commutes_reset_winning e₁ e₂ h₁ h₂, h₁, h₂]
      | reset => simp [commutes_of_same_op e₁ e₂ (h₁.trans h₂.symm)]

/-- **NO-RC-CHAIN**. A `reset` can only start an edge and a `winning` can only
end one, so two edges never meet. -/
theorem no_rc_chain (o₁ o₂ o₃ : AppOp) :
    ¬ (D.RcBefore o₁ o₂ ∧ D.RcBefore o₂ o₃) := by
  cases o₂ <;> simp

/-! ### The absorber argument for COND-COMM -/

/-- Two states with the same counters everywhere. Bits may differ. -/
def EqCounters (a b : St) : Prop := ∀ r, (a r).1 = (b r).1

theorem eqCounters_step {a b : St} (h : EqCounters a b) (e : Event) :
    EqCounters (step a e) (step b e) := by
  intro r
  cases he : e.op with
  | winning =>
      simp only [step, he]
      by_cases hr : r = e.rep
      · simp [hr, h e.rep]
      · simp [hr, h r]
  | reset =>
      simp only [step, he]
      exact h r

theorem eqCounters_foldl {a b : St} (h : EqCounters a b) (pi : List (Event)) :
    EqCounters (pi.foldl step a) (pi.foldl step b) := by
  induction pi generalizing a b with
  | nil => exact h
  | cons e pi ih => exact ih (eqCounters_step h e)

/-- A `reset` rebuilds every bit from the counters, so it maps states with
equal counters to the same state. -/
theorem reset_eq_of_eqCounters {a b : St} (h : EqCounters a b) {e : Event}
    (he : e.op = .reset) : step a e = step b e := by
  simp only [step, he]
  funext r
  rw [h r]

/-- **COND-COMM**. -/
theorem cond_comm (S : D.Sigma)
    (e e' e'' : D.Event) (pi : List D.Event)
    (hrc : D.EventRcBefore e e')
    (hnc : ¬ D.Commutes e' e'') :
    D.do_ (D.applyList
        (D.do_ (D.do_ S e') e) pi) e''
      = D.do_ (D.applyList
          (D.do_ (D.do_ S e) e') pi) e'' := by
  obtain ⟨he, he'⟩ := (eventRcBefore_iff e e').mp hrc
  have habs : e''.op = AppOp.reset := by
    rcases (rc_non_comm e' e'').mp hnc with h | h
    · exact absurd (((eventRcBefore_iff _ _).mp h).1.symm.trans he') (by simp)
    · exact ((eventRcBefore_iff _ _).mp h).1
  have hbase : EqCounters (step (step S e') e) (step (step S e) e') := by
    intro r
    simp only [step, he, he']
    by_cases hr : r = e'.rep <;> simp [hr]
  exact reset_eq_of_eqCounters (eqCounters_foldl hbase pi) habs

/-- `Laws(D_type)`: RC-NON-COMM over concurrent events, NO-RC-CHAIN and
COND-COMM. -/
theorem laws : Laws D := ⟨rcNonComm_of_exact no_rc_chain (fun e₁ e₂ _ _ => rc_non_comm e₁ e₂),
  no_rc_chain,
  fun S e e' e'' pi _ _ => cond_comm S e e' e'' pi⟩

/-- The replay order of Section 4: `rc`, lifted to events. -/
noncomputable local instance rcOrder :
    EventOrder D.toMRDTSig.toUpdateSig :=
  Interface.rcOrder D

@[simp] theorem replayBefore_iff (a b : D.Event) :
    D.toMRDTSig.toUpdateSig.replayBefore a b
      ↔ a.op = AppOp.reset ∧ b.op = AppOp.winning := by
  refine Iff.trans ?_ (rcBefore_iff a.op b.op)
  exact @OperationPolicy.lift_replayOrder_iff D.toMRDTSig.toUpdateSig
    (Interface.policy D) a b

/-- A `reset` and a `winning` are exactly the pairs `loOn` can order. -/
theorem replayBefore_or_iff (a b : D.Event) :
    (D.toMRDTSig.toUpdateSig.replayBefore a b
        ∨ D.toMRDTSig.toUpdateSig.replayBefore b a)
      ↔ (a.op = AppOp.reset ∧ b.op = AppOp.winning)
        ∨ (b.op = AppOp.reset ∧ a.op = AppOp.winning) := by
  simp only [replayBefore_iff]

/-! ## Counters -/

/-- The number of `winning` events issued by `r`. -/
def winCount (r : Replica) (pi : List (Event)) : Nat :=
  pi.countP (fun e => decide (e.op = AppOp.winning ∧ e.rep = r))

@[simp] theorem winCount_nil (r : Replica) : winCount r [] = 0 := rfl

theorem winCount_cons (r : Replica) (e : Event) (pi : List (Event)) :
    winCount r (e :: pi) =
      winCount r pi + if e.op = AppOp.winning ∧ e.rep = r then 1 else 0 := by
  by_cases h : e.op = AppOp.winning ∧ e.rep = r <;>
    simp [winCount, List.countP_cons, h]

/-- Replaying a list adds one to row `r` for each `winning` it issued. -/
theorem foldl_counter (s : St) (pi : List (Event)) (r : Replica) :
    ((pi.foldl step s) r).1 = (s r).1 + (winCount r pi : Int) := by
  induction pi generalizing s with
  | nil => simp
  | cons e pi ih =>
      rw [List.foldl_cons, ih, winCount_cons]
      cases he : e.op with
      | winning =>
          simp only [step, he]
          by_cases hr : r = e.rep
          · simp [hr]; omega
          · have hr' : ¬ (e.rep = r) := Ne.symm hr
            simp [hr, hr']
      | reset =>
          simp only [step, he]
          simp [he]

/-! ## Bits

The bit of row `r` is set exactly when the list holds a `winning` at `r` with
no `reset` after it, or holds no `reset` at all and started set. -/

/-- No event in the list is a `reset`. -/
def NoReset (pi : List (Event)) : Prop := ∀ e ∈ pi, e.op ≠ AppOp.reset

@[simp] theorem noReset_nil : NoReset [] := by simp [NoReset]

theorem noReset_append_singleton {pi : List (Event)} {e : Event} :
    NoReset (pi ++ [e]) ↔ NoReset pi ∧ e.op ≠ AppOp.reset := by
  constructor
  · exact fun h => ⟨fun a ha => h a (by simp [ha]), h e (by simp)⟩
  · rintro ⟨h, he⟩ a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact h a ha
    · rw [List.mem_singleton.mp ha]; exact he

/-- Splitting a list that ends in `e`: either the marked element is `e`
itself, or the split lies entirely inside the prefix. -/
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

/-- The list-level reading of the bit. -/
theorem foldl_bit_iff (s : St) (pi : List (Event)) (r : Replica) :
    ((pi.foldl step s) r).2 = true ↔
      (∃ pre w post, pi = pre ++ w :: post ∧ w.op = AppOp.winning ∧ w.rep = r
        ∧ NoReset post)
      ∨ ((s r).2 = true ∧ NoReset pi) := by
  induction pi using List.reverseRecOn with
  | nil =>
      constructor
      · exact fun h => Or.inr ⟨h, noReset_nil⟩
      · rintro (⟨pre, w, post, hs, -, -, -⟩ | ⟨h, -⟩)
        · exact absurd hs.symm (by simp)
        · exact h
  | append_singleton pi e ih =>
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      cases he : e.op with
      | winning =>
          simp only [step, he]
          by_cases hr : r = e.rep
          · subst hr
            simp only [if_pos rfl]
            constructor
            · exact fun _ => Or.inl ⟨pi, e, [], rfl, he, rfl, noReset_nil⟩
            · exact fun _ => rfl
          · simp only [if_neg hr]
            rw [ih]
            constructor
            · rintro (⟨pre, w, post, hs, hw, hwr, hn⟩ | ⟨h, hn⟩)
              · exact Or.inl ⟨pre, w, post ++ [e], by rw [hs]; simp, hw, hwr,
                  noReset_append_singleton.mpr ⟨hn, by rw [he]; simp⟩⟩
              · exact Or.inr ⟨h, noReset_append_singleton.mpr ⟨hn, by rw [he]; simp⟩⟩
            · rintro (⟨pre, w, post, hs, hw, hwr, hn⟩ | ⟨h, hn⟩)
              · rcases append_singleton_split hs with ⟨hwe, -⟩ | ⟨post', hpost, hpi⟩
                · exact absurd (hwe ▸ hwr) (Ne.symm hr)
                · exact Or.inl ⟨pre, w, post', hpi, hw, hwr,
                    (noReset_append_singleton.mp (hpost ▸ hn)).1⟩
              · exact Or.inr ⟨h, (noReset_append_singleton.mp hn).1⟩
      | reset =>
          simp only [step, he]
          constructor
          · exact fun h => absurd h (by simp)
          · rintro (⟨pre, w, post, hs, hw, hwr, hn⟩ | ⟨-, hn⟩)
            · exfalso
              rcases append_singleton_split hs with ⟨hwe, -⟩ | ⟨post', hpost, -⟩
              · exact absurd (hwe ▸ hw) (by rw [he]; simp)
              · exact absurd he (hn e (by rw [hpost]; simp))
            · exact absurd he (hn e (by simp))

/-! ## Liveness

The bit of row `r` is set exactly when some `winning` at `r` survives, which
is the OR-set's liveness predicate with `reset` in the role of `remove`. -/

variable {C : Ctx D}

/-- No `reset` of `E` observes `a`. -/
def Survives (C : Ctx D)
    (E : Set (Event)) (a : Event) : Prop :=
  ¬ ∃ rho ∈ E, rho.op = AppOp.reset ∧ C.vis a rho

/-- Row `r` is live in `E`: some `winning` at `r` survives, or the initial
bit was set and `E` holds no `reset` at all. -/
def Live (C : Ctx D)
    (E : Set (Event)) (flag : Bool) (r : Replica) : Prop :=
  (∃ w ∈ E, w.op = AppOp.winning ∧ w.rep = r ∧ Survives C E w)
    ∨ (flag = true ∧ ¬ ∃ rho ∈ E, rho.op = AppOp.reset)

theorem survives_union {E₁ E₂ : Set (Event)} {a : Event} :
    Survives C (E₁ ∪ E₂) a ↔ Survives C E₁ a
      ∧ Survives C E₂ a := by
  constructor
  · exact fun h => ⟨fun ⟨p, hp, hr, hv⟩ => h ⟨p, Or.inl hp, hr, hv⟩,
      fun ⟨p, hp, hr, hv⟩ => h ⟨p, Or.inr hp, hr, hv⟩⟩
  · rintro ⟨h₁, h₂⟩ ⟨p, hp | hp, hr, hv⟩
    · exact h₁ ⟨p, hp, hr, hv⟩
    · exact h₂ ⟨p, hp, hr, hv⟩

theorem survives_subset {E F : Set (Event)} {a : Event} (hsub : E ⊆ F)
    (h : Survives C F a) :
    Survives C E a :=
  fun ⟨p, hp, hr, hv⟩ => h ⟨p, hsub hp, hr, hv⟩

/-- A `winning` and a `reset` never commute. -/
theorem not_commutes_winning_reset {a b : Event} (ha : a.op = AppOp.winning)
    (hb : b.op = AppOp.reset) :
    ¬ D.toMRDTSig.toUpdateSig.commutes a b :=
  fun hc => not_commutes_reset_winning
    b a hb ha (commutes_symm hc)

/-- A `winning` a branch does not contain is observed by no `reset` of that
branch: causal closure would otherwise force it in. This is where the
closure premises of `JoinAt` are used. -/
theorem survives_of_not_mem {E : Set (Event)} {w : Event}
    (hclosed : ∀ a b, C.vis a b →
      ¬ D.toMRDTSig.toUpdateSig.commutes a b → b ∈ E → a ∈ E)
    (hw : w.op = AppOp.winning) (hnm : w ∉ E) : Survives C E w := by
  rintro ⟨rho, hrho, hres, hvis⟩
  exact hnm (hclosed w rho hvis (not_commutes_winning_reset hw hres) hrho)

/-- Survival passes to later `winning` events of the same replica: a `reset`
observing the later one observes the earlier one too. -/
theorem survives_mono {E : Set (Event)} {w w' : Event}
    (htr : ∀ {a b c : Event}, C.vis a b → C.vis b c → C.vis a c)
    (hvis : C.vis w w')
    (h : Survives C E w) :
    Survives C E w' :=
  fun ⟨rho, hrho, hres, hv⟩ => h ⟨rho, hrho, hres, htr hvis hv⟩

/-- `vis` is total on the events of one replica. -/
theorem vis_total {a b : Event} (ha : a ∈ C.events) (hb : b ∈ C.events)
    (hne : a ≠ b) (hrep : a.rep = b.rep) : C.vis a b ∨ C.vis b a := by
  obtain ⟨p, s, hL, hs⟩ := ha
  obtain ⟨p', s', hL', hs'⟩ := hb
  exact C.vis_total_same_replica hL hs hL' hs' hne hrep

/-! ### Edges and list positions -/

theorem not_edge_to_prefix {R : Event → Event → Prop}
    {pre post : List (Event)} {a r : Event}
    (hr : respects (pre ++ a :: post) R) (hm : r ∈ pre) : ¬ R a r :=
  (List.pairwise_append.mp hr).2.2 r hm a (by simp)

theorem not_edge_from_suffix {R : Event → Event → Prop}
    {pre post : List (Event)} {a r : Event}
    (hr : respects (pre ++ a :: post) R) (hm : r ∈ post) : ¬ R r a :=
  (List.pairwise_cons.mp (List.pairwise_append.mp hr).2.1).1 r hm

/-- **The bit of a canonical state is liveness.** Every replay of `E` that
respects `lo^C_E` agrees, so the bit depends on the event set alone. -/
theorem run_bit_iff_live {E : Set (Event)} {pi : List (Event)}
    (hp : listPermOf pi E) (hr : respects pi (loOn C E)) (r : Replica) :
    ((pi.foldl step (fun _ => (0, true))) r).2 = true
      ↔ Live C E true r := by
  rw [foldl_bit_iff]
  constructor
  · rintro (⟨pre, w, post, hs, hw, hwr, hn⟩ | ⟨hb, hn⟩)
    · subst pi
      refine Or.inl ⟨w, (hp.2 w).mp (by simp), hw, hwr, ?_⟩
      rintro ⟨rho, hrho, hres, hvis⟩
      have hm : rho ∈ pre ++ w :: post := (hp.2 rho).mpr hrho
      rcases List.mem_append.mp hm with hm | hm
      · exact not_edge_to_prefix hr hm
          (Or.inl ⟨hvis, Or.inr ((replayBefore_iff rho w).mpr ⟨hres, hw⟩)⟩)
      · rcases List.mem_cons.mp hm with heq | hm
        · rw [heq, hw] at hres; cases hres
        · exact hn rho hm hres
    · exact Or.inr ⟨hb, fun ⟨rho, hrho, hres⟩ => hn rho ((hp.2 rho).mpr hrho) hres⟩
  · rintro (⟨w, hwe, hw, hwr, hsv⟩ | ⟨hb, hno⟩)
    · obtain ⟨pre, post, hs⟩ := List.append_of_mem ((hp.2 w).mpr hwe)
      refine Or.inl ⟨pre, w, post, hs, hw, hwr, ?_⟩
      subst pi
      intro rho hm hres
      refine not_edge_from_suffix hr hm ?_
      have hre : rho ∈ E := (hp.2 rho).mp (by simp [hm])
      have hrc : D.toMRDTSig.toUpdateSig.replayBefore rho w :=
        (replayBefore_iff rho w).mpr ⟨hres, hw⟩
      by_cases hvw : C.vis rho w
      · exact Or.inl ⟨hvw, Or.inl hrc⟩
      · refine Or.inr ⟨hvw, ?_, hrc, ?_⟩
        · exact fun hv => hsv ⟨rho, hre, hres, hv⟩
        · rintro ⟨c, hce, hvc, hc | hc⟩
          · obtain ⟨hwres, -⟩ := (replayBefore_iff w c).mp hc
            rw [hw] at hwres; cases hwres
          · obtain ⟨hcres, -⟩ := (replayBefore_iff c w).mp hc
            exact hsv ⟨c, hce, hcres, hvc⟩
    · exact Or.inr ⟨hb, fun rho hm hres => hno ⟨rho, (hp.2 rho).mp hm, hres⟩⟩

/-! ### How liveness behaves under union

These four lemmas are the whole content of the bit half of the merge. -/

/-- A row live in the union is live in one of the branches. -/
theorem live_of_live_union {E₁ E₂ : Set (Event)} {flag : Bool} {r : Replica}
    (h : Live C (E₁ ∪ E₂) flag r) : Live C E₁ flag r ∨ Live C E₂ flag r := by
  rcases h with ⟨w, hwe, hw, hwr, hsv⟩ | ⟨hb, hno⟩
  · obtain ⟨hs₁, hs₂⟩ := survives_union.mp hsv
    rcases hwe with hwe | hwe
    · exact Or.inl (Or.inl ⟨w, hwe, hw, hwr, hs₁⟩)
    · exact Or.inr (Or.inl ⟨w, hwe, hw, hwr, hs₂⟩)
  · exact Or.inl (Or.inr ⟨hb, fun ⟨rho, hrho, hres⟩ => hno ⟨rho, Or.inl hrho, hres⟩⟩)

/-- A row live in both branches is live in the union. The two surviving
`winning` events are issued by the same replica, so `vis` compares them, and
the later one survives both branches. -/
theorem live_union_of_both {E₁ E₂ : Set (Event)} {flag : Bool} {r : Replica}
    (htr : ∀ {a b c : Event}, C.vis a b → C.vis b c → C.vis a c)
    (hsub₁ : ∀ a ∈ E₁, a ∈ C.events) (hsub₂ : ∀ a ∈ E₂, a ∈ C.events)
    (h₁ : Live C E₁ flag r) (h₂ : Live C E₂ flag r) : Live C (E₁ ∪ E₂) flag r := by
  rcases h₁ with ⟨w₁, hw₁e, hw₁, hw₁r, hs₁⟩ | ⟨hb₁, hno₁⟩
  · rcases h₂ with ⟨w₂, hw₂e, hw₂, hw₂r, hs₂⟩ | ⟨hb₂, hno₂⟩
    · by_cases heq : w₁ = w₂
      · subst heq
        exact Or.inl ⟨w₁, Or.inl hw₁e, hw₁, hw₁r, survives_union.mpr ⟨hs₁, hs₂⟩⟩
      · rcases vis_total (hsub₁ w₁ hw₁e) (hsub₂ w₂ hw₂e) heq (hw₁r.trans hw₂r.symm)
          with hv | hv
        · exact Or.inl ⟨w₂, Or.inr hw₂e, hw₂, hw₂r,
            survives_union.mpr ⟨survives_mono htr hv hs₁, hs₂⟩⟩
        · exact Or.inl ⟨w₁, Or.inl hw₁e, hw₁, hw₁r,
            survives_union.mpr ⟨hs₁, survives_mono htr hv hs₂⟩⟩
    · exact Or.inl ⟨w₁, Or.inl hw₁e, hw₁, hw₁r, survives_union.mpr
        ⟨hs₁, fun ⟨rho, hrho, hres, _⟩ => hno₂ ⟨rho, hrho, hres⟩⟩⟩
  · rcases h₂ with ⟨w₂, hw₂e, hw₂, hw₂r, hs₂⟩ | ⟨hb₂, hno₂⟩
    · exact Or.inl ⟨w₂, Or.inr hw₂e, hw₂, hw₂r, survives_union.mpr
        ⟨fun ⟨rho, hrho, hres, _⟩ => hno₁ ⟨rho, hrho, hres⟩, hs₂⟩⟩
    · refine Or.inr ⟨hb₁, ?_⟩
      rintro ⟨rho, hrho | hrho, hres⟩
      · exact hno₁ ⟨rho, hrho, hres⟩
      · exact hno₂ ⟨rho, hrho, hres⟩

/-- A branch that is live and holds a `winning` the other branch does not
makes the union live. -/
theorem live_union_of_fresh {E₁ E₂ : Set (Event)} {flag : Bool} {r : Replica}
    (htr : ∀ {a b c : Event}, C.vis a b → C.vis b c → C.vis a c)
    (hsub₁ : ∀ a ∈ E₁, a ∈ C.events)
    (hclosed₂ : ∀ a b, C.vis a b →
      ¬ D.toMRDTSig.toUpdateSig.commutes a b → b ∈ E₂ → a ∈ E₂)
    (h₁ : Live C E₁ flag r)
    {w : Event} (hwe : w ∈ E₁) (hnm : w ∉ E₂)
    (hw : w.op = AppOp.winning) (hwr : w.rep = r) : Live C (E₁ ∪ E₂) flag r := by
  have hw₂ : Survives C E₂ w := survives_of_not_mem hclosed₂ hw hnm
  rcases h₁ with ⟨w₁, hw₁e, hw₁, hw₁r, hs₁⟩ | ⟨-, hno₁⟩
  · by_cases heq : w = w₁
    · subst heq
      exact Or.inl ⟨w, Or.inl hwe, hw, hwr, survives_union.mpr ⟨hs₁, hw₂⟩⟩
    · rcases vis_total (hsub₁ w hwe) (hsub₁ w₁ hw₁e) heq (hwr.trans hw₁r.symm) with hv | hv
      · exact Or.inl ⟨w₁, Or.inl hw₁e, hw₁, hw₁r,
          survives_union.mpr ⟨hs₁, survives_mono htr hv hw₂⟩⟩
      · exact Or.inl ⟨w, Or.inl hwe, hw, hwr,
          survives_union.mpr ⟨survives_mono htr hv hs₁, hw₂⟩⟩
  · exact Or.inl ⟨w, Or.inl hwe, hw, hwr, survives_union.mpr
      ⟨fun ⟨rho, hrho, hres, _⟩ => hno₁ ⟨rho, hrho, hres⟩, hw₂⟩⟩

/-- If the union is live but one branch is not, the other branch holds a
`winning` the first does not. -/
theorem fresh_of_live_union {E₁ E₂ : Set (Event)} {flag : Bool} {r : Replica}
    (h : Live C (E₁ ∪ E₂) flag r) (hn₂ : ¬ Live C E₂ flag r) :
    ∃ w ∈ E₁, w ∉ E₂ ∧ w.op = AppOp.winning ∧ w.rep = r := by
  rcases h with ⟨w, hwe, hw, hwr, hsv⟩ | ⟨hb, hno⟩
  · obtain ⟨hs₁, hs₂⟩ := survives_union.mp hsv
    rcases hwe with hwe | hwe
    · refine ⟨w, hwe, ?_, hw, hwr⟩
      exact fun hm => hn₂ (Or.inl ⟨w, hm, hw, hwr, hs₂⟩)
    · exact absurd (Or.inl ⟨w, hwe, hw, hwr, hs₂⟩) hn₂
  · exact absurd (Or.inr ⟨hb, fun ⟨rho, hrho, hres⟩ => hno ⟨rho, Or.inr hrho, hres⟩⟩) hn₂

/-! ## Counting the `winning` events

The counter half of the merge is inclusion-exclusion, and the comparison
`a.1 > l.1` that the bit half consults says the branch holds a `winning` the
ancestor did not. Both are read off one finite set. -/

/-- The `winning` events of `r` in an enumeration. -/
def winOf (r : Replica) (pi : List (Event)) : Finset (Event) :=
  pi.toFinset.filter (fun e => e.op = AppOp.winning ∧ e.rep = r)

theorem mem_winOf_set {r : Replica} {pi : List (Event)} {E : Set (Event)}
    (hp : listPermOf pi E) {e : Event} :
    e ∈ winOf r pi ↔ e ∈ E ∧ e.op = AppOp.winning ∧ e.rep = r := by
  rw [winOf, Finset.mem_filter, List.mem_toFinset, hp.2 e]

theorem card_winOf {r : Replica} {pi : List (Event)} (h : pi.Nodup) :
    (winOf r pi).card = winCount r pi := by
  have hfilter : winOf r pi
      = (pi.filter (fun e => decide (e.op = AppOp.winning ∧ e.rep = r))).toFinset := by
    ext e
    simp [winOf, List.mem_toFinset, List.mem_filter]
  rw [hfilter, List.toFinset_card_of_nodup (h.filter _), winCount,
    List.countP_eq_length_filter]

/-- The counters obey inclusion-exclusion, which is the counter half of the
merge equation. -/
theorem count_union_inter {E₁ E₂ : Set (Event)}
    {pi₀ pi₁ pi₂ piU : List (Event)}
    (hp₀ : listPermOf pi₀ (E₁ ∩ E₂)) (hp₁ : listPermOf pi₁ E₁)
    (hp₂ : listPermOf pi₂ E₂) (hpU : listPermOf piU (E₁ ∪ E₂)) (r : Replica) :
    winCount r piU + winCount r pi₀ = winCount r pi₁ + winCount r pi₂ := by
  have hU : winOf r pi₁ ∪ winOf r pi₂ = winOf r piU := by
    ext e
    simp only [Finset.mem_union, mem_winOf_set hp₁, mem_winOf_set hp₂,
      mem_winOf_set hpU, Set.mem_union]
    constructor
    · rintro (⟨h, hw⟩ | ⟨h, hw⟩)
      · exact ⟨Or.inl h, hw⟩
      · exact ⟨Or.inr h, hw⟩
    · rintro ⟨h | h, hw⟩
      · exact Or.inl ⟨h, hw⟩
      · exact Or.inr ⟨h, hw⟩
  have hI : winOf r pi₁ ∩ winOf r pi₂ = winOf r pi₀ := by
    ext e
    simp only [Finset.mem_inter, mem_winOf_set hp₁, mem_winOf_set hp₂,
      mem_winOf_set hp₀, Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨h1, hw⟩, ⟨h2, -⟩⟩
      exact ⟨⟨h1, h2⟩, hw⟩
    · rintro ⟨⟨h1, h2⟩, hw⟩
      exact ⟨⟨h1, hw⟩, ⟨h2, hw⟩⟩
  rw [← card_winOf hpU.1, ← card_winOf hp₀.1, ← card_winOf hp₁.1,
    ← card_winOf hp₂.1, ← hU, ← hI]
  exact Finset.card_union_add_card_inter _ _

/-- A branch's counter exceeds the ancestor's exactly when the branch holds a
`winning` the other branch does not. -/
theorem count_lt_iff {E₁ E₂ : Set (Event)} {pi₀ pi₁ : List (Event)}
    (hp₀ : listPermOf pi₀ (E₁ ∩ E₂)) (hp₁ : listPermOf pi₁ E₁) (r : Replica) :
    winCount r pi₀ < winCount r pi₁
      ↔ ∃ w ∈ E₁, w ∉ E₂ ∧ w.op = AppOp.winning ∧ w.rep = r := by
  have hsub : winOf r pi₀ ⊆ winOf r pi₁ := by
    intro e he
    rw [mem_winOf_set hp₀] at he
    exact (mem_winOf_set hp₁).mpr ⟨he.1.1, he.2⟩
  rw [← card_winOf hp₀.1, ← card_winOf hp₁.1]
  constructor
  · intro hlt
    by_contra hcon
    have hsub2 : winOf r pi₁ ⊆ winOf r pi₀ := by
      intro e he
      rw [mem_winOf_set hp₁] at he
      refine (mem_winOf_set hp₀).mpr ⟨⟨he.1, ?_⟩, he.2⟩
      by_contra hm
      exact hcon ⟨e, he.1, hm, he.2.1, he.2.2⟩
    have := Finset.card_le_card hsub2
    omega
  · rintro ⟨w, hw₁, hw₂, hww, hwr⟩
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨w, ?_, ?_⟩)
    · exact (mem_winOf_set hp₁).mpr ⟨hw₁, hww, hwr⟩
    · intro hm
      rw [mem_winOf_set hp₀] at hm
      exact hw₂ hm.1.2

/-! ## The join lemma -/

/-- **The join lemma** for this row, proved from the description of
canonical states above. Merging canonical states of the branches yields a
canonical state of the union of their event sets. The
counter half is inclusion-exclusion; the bit half is the four-way case
analysis of `mergeFlag`, in which the counter comparison stands for "this
branch holds a `winning` the ancestor did not". -/
theorem joinCanonical : @Join D.toMRDTSig (Interface.rcOrder D) := by
  intro C E₁ E₂ s₀ s₁ s₂ htr hir hsub₁ hsub₂ hclosed₁ hclosed₂ hs₀ hs₁ hs₂
  obtain ⟨pi₀, hp₀, hr₀, hf₀⟩ := id hs₀
  obtain ⟨pi₁, hp₁, hr₁, hf₁⟩ := id hs₁
  obtain ⟨pi₂, hp₂, hr₂, hf₂⟩ := id hs₂
  have hsubU : ∀ a ∈ E₁ ∪ E₂, a ∈ C.events :=
    fun a ha => ha.elim (hsub₁ a) (hsub₂ a)
  obtain ⟨sU, hsU⟩ := isCanonicalState_exists_of_replayLaws
    (Metatheory.replayLaws laws rc_non_comm cond_comm)
    htr hir
    (listPermOf_union (D := D.toMRDTSig.toUpdateSig) hp₁ hp₂) hsubU
  obtain ⟨piU, hpU, hrU, hfU⟩ := id hsU
  have hcount : ∀ (pi : List (Event)) (s : St),
      applySeq D.toMRDTSig.toUpdateSig
        D.toMRDTSig.init pi = s →
      ∀ r, (s r).1 = (winCount r pi : Int) := by
    intro pi s hfs r
    rw [← hfs]
    simpa using foldl_counter (fun _ => ((0 : Int), true)) pi r
  have hbit : ∀ (pi : List (Event)) (s : St) (E : Set (Event)),
      listPermOf pi E → respects pi (loOn C E) →
      applySeq D.toMRDTSig.toUpdateSig
        D.toMRDTSig.init pi = s →
      ∀ r, ((s r).2 = true ↔ Live C E true r) := by
    intro pi s E hp hr hfs r
    rw [← hfs]
    exact run_bit_iff_live hp hr r
  have heq : D.toMRDTSig.merge s₀ s₁ s₂ = sU := by
    funext r
    have hc₀ := hcount pi₀ s₀ hf₀ r
    have hc₁ := hcount pi₁ s₁ hf₁ r
    have hc₂ := hcount pi₂ s₂ hf₂ r
    have hcU := hcount piU sU hfU r
    have hb₀ := hbit pi₀ s₀ _ hp₀ hr₀ hf₀ r
    have hb₁ := hbit pi₁ s₁ _ hp₁ hr₁ hf₁ r
    have hb₂ := hbit pi₂ s₂ _ hp₂ hr₂ hf₂ r
    have hbU := hbit piU sU _ hpU hrU hfU r
    have hcounter : (s₁ r).1 + (s₂ r).1 - (s₀ r).1 = (sU r).1 := by
      have := count_union_inter hp₀ hp₁ hp₂ hpU r
      rw [hc₀, hc₁, hc₂, hcU]
      omega
    have hflag : mergeFlag (s₀ r) (s₁ r) (s₂ r) = (sU r).2 := by
      cases hv₁ : (s₁ r).2 with
      | true =>
          cases hv₂ : (s₂ r).2 with
          | true =>
              have := (hbU).mpr (live_union_of_both htr hsub₁ hsub₂
                (hb₁.mp hv₁) (hb₂.mp hv₂))
              simp [mergeFlag, hv₁, hv₂, this]
          | false =>
              have hn₂ : ¬ Live C E₂ true r := by
                intro h
                rw [hb₂.mpr h] at hv₂
                exact Bool.noConfusion hv₂
              simp only [mergeFlag, hv₁, hv₂, Bool.and_false, if_false,
                Bool.not_true, Bool.false_and, Bool.not_false, if_true]
              rw [hc₀, hc₁]
              cases hvU : (sU r).2 with
              | true =>
                  obtain ⟨w, hw₁, hw₂, hww, hwr⟩ :=
                    fresh_of_live_union (hbU.mp hvU) hn₂
                  have : winCount r pi₀ < winCount r pi₁ :=
                    (count_lt_iff hp₀ hp₁ r).mpr ⟨w, hw₁, hw₂, hww, hwr⟩
                  simp
                  omega
              | false =>
                  have hnf : ¬ ∃ w ∈ E₁, w ∉ E₂ ∧ w.op = AppOp.winning ∧ w.rep = r := by
                    rintro ⟨w, hw₁, hw₂, hww, hwr⟩
                    have := hbU.mpr (live_union_of_fresh htr hsub₁ hclosed₂
                      (hb₁.mp hv₁) hw₁ hw₂ hww hwr)
                    rw [this] at hvU
                    exact Bool.noConfusion hvU
                  have hle : ¬ (winCount r pi₀ < winCount r pi₁) :=
                    fun h => hnf ((count_lt_iff hp₀ hp₁ r).mp h)
                  simp
                  omega
      | false =>
          cases hv₂ : (s₂ r).2 with
          | true =>
              have hn₁ : ¬ Live C E₁ true r := by
                intro h
                rw [hb₁.mpr h] at hv₁
                exact Bool.noConfusion hv₁
              simp only [mergeFlag, hv₁, hv₂, Bool.false_and, if_false,
                Bool.not_false, Bool.not_true, Bool.and_false, if_true, if_false]
              rw [hc₀, hc₂]
              cases hvU : (sU r).2 with
              | true =>
                  obtain ⟨w, hw₂, hw₁, hww, hwr⟩ :=
                    fresh_of_live_union (E₁ := E₂) (E₂ := E₁)
                      (by rw [Set.union_comm]; exact hbU.mp hvU) hn₁
                  have : winCount r pi₀ < winCount r pi₂ :=
                    (count_lt_iff (E₂ := E₁) (by rw [Set.inter_comm]; exact hp₀) hp₂ r).mpr
                      ⟨w, hw₂, hw₁, hww, hwr⟩
                  simp
                  omega
              | false =>
                  have hnf : ¬ ∃ w ∈ E₂, w ∉ E₁ ∧ w.op = AppOp.winning ∧ w.rep = r := by
                    rintro ⟨w, hw₂, hw₁, hww, hwr⟩
                    have := hbU.mpr (by
                      rw [Set.union_comm]
                      exact live_union_of_fresh htr hsub₂ hclosed₁
                        (hb₂.mp hv₂) hw₂ hw₁ hww hwr)
                    rw [this] at hvU
                    exact Bool.noConfusion hvU
                  have hle : ¬ (winCount r pi₀ < winCount r pi₂) :=
                    fun h => hnf ((count_lt_iff (E₂ := E₁)
                      (by rw [Set.inter_comm]; exact hp₀) hp₂ r).mp h)
                  simp
                  omega
          | false =>
              have hnU : (sU r).2 = false := by
                cases hvU : (sU r).2 with
                | false => rfl
                | true =>
                    exfalso
                    rcases live_of_live_union (hbU.mp hvU) with h | h
                    · rw [hb₁.mpr h] at hv₁; exact Bool.noConfusion hv₁
                    · rw [hb₂.mpr h] at hv₂; exact Bool.noConfusion hv₂
              simp [mergeFlag, hv₁, hv₂, hnU]
    exact Prod.ext hcounter hflag
  rw [heq]
  exact hsU

variable {C : Ctx D}

/-- Two enumerations of the same event set have the same `winning` count. -/
theorem winCount_congr {E : Set Event} {π ρ : List Event}
    (hp : listPermOf π E) (hq : listPermOf ρ E) (r : Replica) :
    winCount r π = winCount r ρ := by
  rw [← card_winOf hp.1, ← card_winOf hq.1]
  congr 1
  ext e
  rw [mem_winOf_set hp, mem_winOf_set hq]

/-- **The counter half of a canonical state**: row `r` counts the `winning`
events of `r` in `E`. -/
theorem canonical_count {E : Set Event} {s : St}
    (hs : IsCanOn D C E s) {π : List Event} (hp : listPermOf π E) (r : Replica) :
    (s r).1 = (winCount r π : Int) := by
  obtain ⟨ρ, hq, -, hf⟩ := hs
  have : s = ρ.foldl step (fun _ => (0, true)) := hf.symm
  rw [this, foldl_counter, winCount_congr hq hp r]
  simp

/-- **The bit half of a canonical state**: row `r` is set exactly when it is
live in `E`. -/
theorem canonical_bit {E : Set Event} {s : St}
    (hs : IsCanOn D C E s) (r : Replica) :
    (s r).2 = true ↔ Live C E true r := by
  obtain ⟨ρ, hq, hrs, hf⟩ := hs
  have : s = ρ.foldl step (fun _ => (0, true)) := hf.symm
  rw [this]
  exact run_bit_iff_live hq hrs r

/-- **VC1** MERGE-COMM, over arbitrary states as the paper has it. -/
theorem vc1_merge_comm (l a b : D.Sigma) : D.merge l a b = D.merge l b a := by
  funext r
  show mergeCell (l r) (a r) (b r) = mergeCell (l r) (b r) (a r)
  rcases hl : l r with ⟨lc, lb⟩
  rcases ha : a r with ⟨ac, ab⟩
  rcases hb : b r with ⟨bc, bb⟩
  cases ab <;> cases bb <;>
    simp [mergeCell, mergeFlag, Int.add_comm]

/-- **VC2** MERGE-INIT. The initial bits are set, so an initial ancestor and
an initial branch settle `mergeFlag` by its first two clauses, and no
invariant on the counters is needed. -/
theorem vc2_merge_init :
    ∀ (C : Ctx D) (E : Set Event) (s : D.Sigma),
      SupportedOn D C E → IsCanOn D C E s →
      D.merge D.sigma0 D.sigma0 s = s := by
  intro C E s _ _
  funext r
  show mergeCell ((0 : Int), true) ((0 : Int), true) (s r) = s r
  rcases hb : (s r) with ⟨n, b⟩
  cases b <;> simp [mergeCell, mergeFlag]

/-- **The key fact behind VC4's `reset` case.**

Let `e` be a `reset` maximal in `U`, and suppose row `r` is live in
`U \ {e}`, witnessed by a surviving `winning` `w0`. Then *every* `winning`
of `r` in `U \ {e}` is seen by `e`.

For a single `w`, maximality all but settles it: `rc` orders `reset` before
`winning`, so an unseen `w` would give `lo^C_U` an edge out of `e` unless
the absorber clause cancels it, and the absorber can only be another
`reset` in `U` that `w` sees. That is where `w0` comes in. Two events of
one replica are always `vis`-comparable, so `w` and `w0` are ordered: if
`w0` sees `w` it also sees that absorber, which contradicts `w0`
surviving; and if `w` sees `w0` then, since `w0` is seen by `e`,
transitivity makes `e` see `w` after all. -/
theorem winning_vis_of_max_reset {U : Set Event} {e w : Event} {r : Replica}
    (htr : ∀ {a b c : Event}, C.vis a b → C.vis b c → C.vis a c)
    (hUsub : ∀ a ∈ U, a ∈ C.events) (heU : e ∈ U)
    (hmax : ∀ x ∈ U, x ≠ e → ¬ loOn C U e x)
    (hres : e.op = AppOp.reset)
    (hlive : Live C (U \ {e}) true r)
    (hwU : w ∈ U \ {e}) (hw : w.op = AppOp.winning) (hwr : w.rep = r) :
    C.vis w e := by
  -- first: `e` sees `w0`
  have seen : ∀ v : Event, v ∈ U \ {e} → v.op = AppOp.winning →
      (¬ C.vis v e → ∃ ρ ∈ U \ {e}, ρ.op = AppOp.reset ∧ C.vis v ρ) := by
    intro v hvU hv hnv
    by_cases hev : C.vis e v
    · exact absurd (Or.inl ⟨hev, Or.inl ((replayBefore_iff e v).mpr ⟨hres, hv⟩)⟩)
        (hmax v hvU.1 hvU.2)
    · by_cases habs : ∃ e₃ ∈ U, C.vis v e₃ ∧
          (D.toMRDTSig.toUpdateSig.replayBefore v e₃ ∨
            D.toMRDTSig.toUpdateSig.replayBefore e₃ v)
      · obtain ⟨e₃, h₃U, h₃v, h₃r⟩ := habs
        refine ⟨e₃, ⟨h₃U, ?_⟩, ?_, h₃v⟩
        · rintro rfl; exact hnv h₃v
        · rcases (replayBefore_or_iff v e₃).mp h₃r with ⟨hvr, -⟩ | ⟨h₃res, -⟩
          · rw [hv] at hvr; cases hvr
          · exact h₃res
      · exact absurd (Or.inr ⟨hev, hnv, (replayBefore_iff e v).mpr ⟨hres, hv⟩, habs⟩)
          (hmax v hvU.1 hvU.2)
  rcases hlive with ⟨w0, hw0U, hw0, hw0r, hsv⟩ | ⟨-, hnores⟩
  · have hw0e : C.vis w0 e := by
      by_contra hnv
      obtain ⟨ρ, hρU, hρ, hvρ⟩ := seen w0 hw0U hw0 hnv
      exact hsv ⟨ρ, hρU, hρ, hvρ⟩
    by_contra hnv
    obtain ⟨ρ, hρU, hρ, hvρ⟩ := seen w hwU hw hnv
    by_cases heq : w = w0
    · exact hsv ⟨ρ, hρU, hρ, heq ▸ hvρ⟩
    · rcases vis_total (hUsub w hwU.1) (hUsub w0 hw0U.1) heq
        (hwr.trans hw0r.symm) with hvis | hvis
      · exact hnv (htr hvis hw0e)
      · exact hsv ⟨ρ, hρU, hρ, htr hvis hvρ⟩
  · by_contra hnv
    obtain ⟨ρ, hρU, hρ, -⟩ := seen w hwU hw hnv
    exact hnores ⟨ρ, hρU, hρ⟩

/-- Counting `winning` events of `r` is monotone in the event set. -/
theorem count_le_of_subset {E F : Set Event} {πE πF : List Event}
    (hpE : listPermOf πE E) (hpF : listPermOf πF F) (hsub : E ⊆ F) (r : Replica) :
    winCount r πE ≤ winCount r πF := by
  rw [← card_winOf hpE.1, ← card_winOf hpF.1]
  refine Finset.card_le_card ?_
  intro z hz
  rw [mem_winOf_set hpE] at hz
  exact (mem_winOf_set hpF).mpr ⟨hsub hz.1, hz.2⟩

/-- A closed form for `mergeFlag`, with no nested conditionals: a merged bit
is set when both branches have it, or when a branch that has it has grown
since the ancestor. This is what makes VC3 and VC5 tractable, since there
the flag is applied to the result of another merge. -/
theorem mergeFlag_eq (l a b : Cell) :
    mergeFlag l a b
      = (a.2 && b.2) || (a.2 && decide (a.1 > l.1)) || (b.2 && decide (b.1 > l.1)) := by
  rcases a with ⟨ac, ab⟩; rcases b with ⟨bc, bb⟩
  cases ab <;> cases bb <;> simp [mergeFlag] <;> omega

/-- **VC4** CAUSAL-DELTA, proved for this row. The counters need no
premises; the bits need `winning_vis_of_max_reset` in the `reset` case and
a fresh surviving `winning` in the other. -/
theorem vc4_causal_delta :
    ∀ (C : Ctx D) (U : Set D.Event) (A B : D.Sigma) (e : D.Event),
      VisStrict D C →
      SupportedOn D C U → WeaklyClosed D C U →
      e ∈ U → MaximalOn D C U e →
      IsCanOn D C (U \ {e}) A →
      IsCanOn D C (downset C e \ {e}) B →
      D.merge B A (D.do_ B e) = D.do_ A e := by
  intro C U A B e hvs hUsub hUcl heU hmax hA hB
  obtain ⟨htr, hir⟩ := hvs
  have hdsub : downset C e ⊆ U := downset_subset hUcl heU
  have hBA : downset C e \ {e} ⊆ U \ {e} := fun z hz => ⟨hdsub hz.1, hz.2⟩
  obtain ⟨ρA, hpA, -, -⟩ := id hA
  obtain ⟨ρB, hpB, -, -⟩ := id hB
  funext r
  have hcA := canonical_count hA hpA r
  have hcB := canonical_count hB hpB r
  have hle : (B r).1 ≤ (A r).1 := by
    rw [hcA, hcB]; exact_mod_cast count_le_of_subset hpB hpA hBA r
  show mergeCell (B r) (A r) (step B e r) = step A e r
  cases hop : e.op with
  | winning =>
      have hsB : step B e r = if r = e.rep then ((B r).1 + 1, true) else B r := by
        simp only [step, hop]
      have hsA : step A e r = if r = e.rep then ((A r).1 + 1, true) else A r := by
        simp only [step, hop]
      rw [hsA, hsB]
      by_cases hr : r = e.rep
      · rw [if_pos hr, if_pos hr]
        refine Prod.ext ?_ ?_
        · show (A r).1 + ((B r).1 + 1) - (B r).1 = (A r).1 + 1; omega
        · show mergeFlag (B r) (A r) ((B r).1 + 1, true) = true
          rcases h2 : (A r).2 with _ | _ <;> simp [mergeFlag, h2]
      · rw [if_neg hr, if_neg hr]
        have hfresh : (A r).2 = true → (B r).2 = false → (B r).1 < (A r).1 := by
          intro hA2 hB2
          rcases (canonical_bit hA r).mp hA2 with ⟨w, hwU, hw, hwr, hsv⟩ | ⟨-, hnores⟩
          · have hnot : w ∉ downset C e \ {e} := by
              intro hmem
              rw [(canonical_bit hB r).mpr
                (Or.inl ⟨w, hmem, hw, hwr, survives_subset hBA hsv⟩)] at hB2
              cases hB2
            rw [hcA, hcB]
            have hss : winOf r ρB ⊂ winOf r ρA := by
              refine Finset.ssubset_iff_of_subset (fun z hz => ?_) |>.mpr
                ⟨w, (mem_winOf_set hpA).mpr ⟨hwU, hw, hwr⟩,
                  fun hmem => hnot ((mem_winOf_set hpB).mp hmem).1⟩
              rw [mem_winOf_set hpB] at hz
              exact (mem_winOf_set hpA).mpr ⟨hBA hz.1, hz.2⟩
            have hc := Finset.card_lt_card hss
            rw [card_winOf hpB.1, card_winOf hpA.1] at hc
            exact_mod_cast hc
          · exfalso
            rw [(canonical_bit hB r).mpr
              (Or.inr ⟨rfl, fun hx => hnores ⟨hx.choose, hBA hx.choose_spec.1,
                hx.choose_spec.2⟩⟩)] at hB2
            cases hB2
        refine Prod.ext ?_ ?_
        · show (A r).1 + (B r).1 - (B r).1 = (A r).1; omega
        · show mergeFlag (B r) (A r) (B r) = (A r).2
          rcases h2 : (A r).2 with _ | _ <;> rcases h3 : (B r).2 with _ | _
          · simp [mergeFlag, h2, h3]
          · simp [mergeFlag, h2, h3]
          · have h := hfresh h2 h3
            simp [mergeFlag, h2, h3, h]
          · simp [mergeFlag, h2, h3]
  | reset =>
      have hsB : step B e r = ((B r).1, false) := by simp only [step, hop]
      have hsA : step A e r = ((A r).1, false) := by simp only [step, hop]
      rw [hsA, hsB]
      have hcap : (A r).2 = true → (A r).1 ≤ (B r).1 := by
        intro hA2
        have hlive := (canonical_bit hA r).mp hA2
        rw [hcA, hcB]
        have hss : winOf r ρA ⊆ winOf r ρB := by
          intro z hz
          rw [mem_winOf_set hpA] at hz
          refine (mem_winOf_set hpB).mpr ⟨⟨?_, hz.1.2⟩, hz.2⟩
          exact Or.inr (Relation.TransGen.single
            ⟨winning_vis_of_max_reset htr hUsub heU hmax hop hlive
              hz.1 hz.2.1 hz.2.2,
             not_commutes_winning_reset hz.2.1 hop⟩)
        have hc := Finset.card_le_card hss
        rw [card_winOf hpA.1, card_winOf hpB.1] at hc
        exact_mod_cast hc
      refine Prod.ext ?_ ?_
      · show (A r).1 + (B r).1 - (B r).1 = (A r).1; omega
      · show mergeFlag (B r) (A r) ((B r).1, false) = false
        rcases h2 : (A r).2 with _ | _
        · simp [mergeFlag, h2]
        · have h := hcap h2
          simp [mergeFlag, h2, h]

/-! ## VC3 and VC5

Unlike VC1, VC2 and VC4, these two do not reduce to facts about a single
row. Each side of VC3 merges three canonical states whose event sets unite
to `E1 u E2`, so each step **is** the join lemma, applied pointwise; VC3
needs four such steps and VC5 six.

For a row whose canonical state has a closed description independent of
`merge` -- the OR-set's `live_join`, say -- that description carries the
argument and the conditions are genuinely cheaper than the join lemma. This
row has no such description: its state is a counter and a bit, and its join
proof settles both together. So the two proofs below run on `joinCanonical`,
the row's own join lemma. They are honest proofs of the conditions, but they
are not an independent route to convergence for this row. -/

/-- `e(can(down(e) \ {e})) = can(down(e))`. -/
theorem isCan_downset {C : Ctx D} {m : D.Sigma} {e : Event}
    (htr : ∀ {a b c : Event}, C.vis a b → C.vis b c → C.vis a c)
    (hir : ∀ a : Event, ¬ C.vis a a)
    (hm : IsCanOn D C (downset C e \ {e}) m) :
    IsCanOn D C (downset C e) (D.do_ m e) :=
  isCanonicalState_snoc (Or.inl rfl) (downset_max htr hir) hm

/-- **VC3** LOCAL-REDISTRIBUTE. -/
theorem vc3_local_redistribute :
    ∀ (C : Ctx D) (E₁ E₂ : Set Event) (l m x y : D.Sigma) (e : Event),
      VisStrict D C →
      SupportedOn D C E₁ → SupportedOn D C E₂ →
      WeaklyClosed D C E₁ → WeaklyClosed D C E₂ →
      e ∈ E₁ → e ∉ E₂ → MaximalOn D C (E₁ ∪ E₂) e →
      IsCanOn D C (E₁ ∩ E₂) l →
      IsCanOn D C (downset C e \ {e}) m →
      IsCanOn D C (E₁ \ {e}) x →
      IsCanOn D C E₂ y →
      D.merge l (D.merge m x (D.do_ m e)) y
        = D.merge m (D.merge l x y) (D.do_ m e) := by
  have hrl := Metatheory.replayLaws laws rc_non_comm cond_comm
  intro C E₁ E₂ l m x y e hvs h₁ h₂ hc₁ hc₂ he₁ he₂ hmax hl hm hx hy
  obtain ⟨htr, hir⟩ := hvs
  have hdsub : downset C e ⊆ E₁ := downset_subset hc₁ he₁
  have hdm := isCan_downset htr hir hm
  have hsupU : SupportedOn D C (E₁ ∪ E₂) := fun a ha => ha.elim (h₁ a) (h₂ a)
  have hdsupp : SupportedOn D C (downset C e) := fun a ha => h₁ a (hdsub ha)
  have hcld : WeaklyClosed D C (downset C e) := fun a b => downset_closed a b
  have hclU : WeaklyClosed D C (E₁ ∪ E₂) := weaklyClosed_union hc₁ hc₂
  have hclx : WeaklyClosed D C (E₁ \ {e}) :=
    closure_diff_of_max hrl.noncomm_covered Set.subset_union_left hc₁ hmax
  have hclU' : WeaklyClosed D C ((E₁ ∪ E₂) \ {e}) :=
    closure_diff_of_max hrl.noncomm_covered Set.Subset.rfl hclU hmax
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
  have hinner : IsCanOn D C E₁ (D.merge m x (D.do_ m e)) := by
    have := joinCanonical C (E₁ \ {e}) (downset C e) m x (D.do_ m e) htr hir
      (fun a ha => h₁ a ha.1) hdsupp hclx hcld (by rw [i₁]; exact hm) hx hdm
    rwa [u₁] at this
  have hL : IsCanOn D C (E₁ ∪ E₂) (D.merge l (D.merge m x (D.do_ m e)) y) :=
    joinCanonical C E₁ E₂ l _ y htr hir h₁ h₂ hc₁ hc₂ hl hinner hy
  have hinner' : IsCanOn D C ((E₁ ∪ E₂) \ {e}) (D.merge l x y) := by
    have := joinCanonical C (E₁ \ {e}) E₂ l x y htr hir (fun a ha => h₁ a ha.1) h₂
      hclx hc₂ (by rw [i₂]; exact hl) hx hy
    rwa [u₂] at this
  have hR : IsCanOn D C (E₁ ∪ E₂) (D.merge m (D.merge l x y) (D.do_ m e)) := by
    have := joinCanonical C ((E₁ ∪ E₂) \ {e}) (downset C e) m (D.merge l x y)
      (D.do_ m e) htr hir (fun a ha => hsupU a ha.1) hdsupp hclU' hcld
      (by rw [i₃]; exact hm) hinner' hdm
    rwa [u₃] at this
  exact isCanonicalState_unique_of_replayLaws hrl hsupU hL hR

/-- **VC5** REDISTRIBUTE. -/
theorem vc5_redistribute :
    ∀ (C : Ctx D) (E₁ E₂ : Set Event) (x₀ x₁ x₂ m : D.Sigma) (e : Event),
      VisStrict D C →
      SupportedOn D C E₁ → SupportedOn D C E₂ →
      WeaklyClosed D C E₁ → WeaklyClosed D C E₂ →
      e ∈ E₁ → e ∈ E₂ → MaximalOn D C (E₁ ∪ E₂) e →
      IsCanOn D C ((E₁ ∩ E₂) \ {e}) x₀ →
      IsCanOn D C (downset C e \ {e}) m →
      IsCanOn D C (E₁ \ {e}) x₁ →
      IsCanOn D C (E₂ \ {e}) x₂ →
      D.merge (D.merge m x₀ (D.do_ m e)) (D.merge m x₁ (D.do_ m e))
          (D.merge m x₂ (D.do_ m e))
        = D.merge m (D.merge x₀ x₁ x₂) (D.do_ m e) := by
  have hrl := Metatheory.replayLaws laws rc_non_comm cond_comm
  intro C E₁ E₂ x₀ x₁ x₂ m e hvs h₁ h₂ hc₁ hc₂ he₁ he₂ hmax hx₀ hm hx₁ hx₂
  obtain ⟨htr, hir⟩ := hvs
  have hdsub₁ : downset C e ⊆ E₁ := downset_subset hc₁ he₁
  have hdsub₂ : downset C e ⊆ E₂ := downset_subset hc₂ he₂
  have hdm := isCan_downset htr hir hm
  have hsupU : SupportedOn D C (E₁ ∪ E₂) := fun a ha => ha.elim (h₁ a) (h₂ a)
  have hdsupp : SupportedOn D C (downset C e) := fun a ha => h₁ a (hdsub₁ ha)
  have hcld : WeaklyClosed D C (downset C e) := fun a b => downset_closed a b
  have hclU : WeaklyClosed D C (E₁ ∪ E₂) := weaklyClosed_union hc₁ hc₂
  have hclI : WeaklyClosed D C (E₁ ∩ E₂) := by
    rintro a b hv hnc ⟨hb₁, hb₂⟩; exact ⟨hc₁ a b hv hnc hb₁, hc₂ a b hv hnc hb₂⟩
  have hcl₀ : WeaklyClosed D C ((E₁ ∩ E₂) \ {e}) :=
    closure_diff_of_max hrl.noncomm_covered (fun z hz => Or.inl hz.1) hclI hmax
  have hcl₁ : WeaklyClosed D C (E₁ \ {e}) :=
    closure_diff_of_max hrl.noncomm_covered Set.subset_union_left hc₁ hmax
  have hcl₂ : WeaklyClosed D C (E₂ \ {e}) :=
    closure_diff_of_max hrl.noncomm_covered Set.subset_union_right hc₂ hmax
  have hclU' : WeaklyClosed D C ((E₁ ∪ E₂) \ {e}) :=
    closure_diff_of_max hrl.noncomm_covered Set.Subset.rfl hclU hmax
  have peelI : ∀ F : Set Event, downset C e ⊆ F →
      (F \ {e}) ∩ downset C e = downset C e \ {e} := by
    intro F hsub; ext z
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hsub h.1, h.2⟩, h.1⟩⟩
  have peelU : ∀ F : Set Event, downset C e ⊆ F →
      (F \ {e}) ∪ downset C e = F := by
    intro F hsub; ext z; constructor
    · rintro (⟨hz, -⟩ | hz); · exact hz
      · exact hsub hz
    · intro hz; by_cases hze : z = e
      · exact Or.inr (Or.inl hze)
      · exact Or.inl ⟨hz, hze⟩
  have hdsubI : downset C e ⊆ E₁ ∩ E₂ := fun z hz => ⟨hdsub₁ hz, hdsub₂ hz⟩
  have hdsubU : downset C e ⊆ E₁ ∪ E₂ := fun z hz => Or.inl (hdsub₁ hz)
  have peel : ∀ (F : Set Event) (t : D.Sigma), downset C e ⊆ F →
      SupportedOn D C F → WeaklyClosed D C (F \ {e}) →
      IsCanOn D C (F \ {e}) t → IsCanOn D C F (D.merge m t (D.do_ m e)) := by
    intro F t hsub hsup hcl ht
    have := joinCanonical C (F \ {e}) (downset C e) m t (D.do_ m e) htr hir
      (fun a ha => hsup a ha.1) (fun a ha => hsup a (hsub ha)) hcl hcld
      (by rw [peelI F hsub]; exact hm) ht hdm
    rwa [peelU F hsub] at this
  have hb₀ := peel (E₁ ∩ E₂) x₀ hdsubI (fun a ha => h₁ a ha.1) hcl₀ hx₀
  have hb₁ := peel E₁ x₁ hdsub₁ h₁ hcl₁ hx₁
  have hb₂ := peel E₂ x₂ hdsub₂ h₂ hcl₂ hx₂
  have hL : IsCanOn D C (E₁ ∪ E₂)
      (D.merge (D.merge m x₀ (D.do_ m e)) (D.merge m x₁ (D.do_ m e))
        (D.merge m x₂ (D.do_ m e))) :=
    joinCanonical C E₁ E₂ _ _ _ htr hir h₁ h₂ hc₁ hc₂ hb₀ hb₁ hb₂
  have i₀ : (E₁ \ {e}) ∩ (E₂ \ {e}) = (E₁ ∩ E₂) \ {e} := by
    ext z
    exact ⟨fun h => ⟨⟨h.1.1, h.2.1⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, ⟨h.1.2, h.2⟩⟩⟩
  have u₀ : (E₁ \ {e}) ∪ (E₂ \ {e}) = (E₁ ∪ E₂) \ {e} := by
    ext z; constructor
    · rintro (⟨hz, hn⟩ | ⟨hz, hn⟩)
      · exact ⟨Or.inl hz, hn⟩
      · exact ⟨Or.inr hz, hn⟩
    · rintro ⟨hz | hz, hn⟩
      · exact Or.inl ⟨hz, hn⟩
      · exact Or.inr ⟨hz, hn⟩
  have hmid : IsCanOn D C ((E₁ ∪ E₂) \ {e}) (D.merge x₀ x₁ x₂) := by
    have := joinCanonical C (E₁ \ {e}) (E₂ \ {e}) x₀ x₁ x₂ htr hir
      (fun a ha => h₁ a ha.1) (fun a ha => h₂ a ha.1) hcl₁ hcl₂
      (by rw [i₀]; exact hx₀) hx₁ hx₂
    rwa [u₀] at this
  have hR := peel (E₁ ∪ E₂) (D.merge x₀ x₁ x₂) hdsubU hsupU hclU' hmid
  exact isCanonicalState_unique_of_replayLaws hrl hsupU hL hR

/-- **VC1 to VC5** of Section 5, in the paper's form. -/
theorem joinLaws : CanonicalJoinLawsOn D (fun _ => True) where
  vc1_merge_comm := vc1_merge_comm
  vc2_merge_init := fun C E s _ => vc2_merge_init C E s
  vc3_local_redistribute := fun C E₁ E₂ l m x y e _ =>
    vc3_local_redistribute C E₁ E₂ l m x y e
  vc4_causal_delta := fun C U A B e _ => vc4_causal_delta C U A B e
  vc5_redistribute := fun C E₁ E₂ x₀ x₁ x₂ m e _ =>
    vc5_redistribute C E₁ E₂ x₀ x₁ x₂ m e

/-- The client reading of the physical bit. -/
theorem machine_fold (invert : Bool) (ops : List AppOp) (b : Bool) :
    ops.foldl (boolStep invert) (if invert then !b else b)
      = if invert then !(ops.foldl flagStep b) else ops.foldl flagStep b := by
  induction ops generalizing b with
  | nil => rfl
  | cons o ops ih =>
      cases o with
      | winning =>
          have hb : boolStep invert (if invert then !b else b) AppOp.winning
              = if invert then !(flagStep b AppOp.winning) else flagStep b AppOp.winning := by
            cases invert <;> simp [boolStep, flagStep]
          rw [List.foldl_cons, List.foldl_cons, hb, ih]
      | reset =>
          have hb : boolStep invert (if invert then !b else b) AppOp.reset
              = if invert then !(flagStep b AppOp.reset) else flagStep b AppOp.reset := by
            cases invert <;> simp [boolStep, flagStep]
          rw [List.foldl_cons, List.foldl_cons, hb, ih]

/-- After a replay the physical reading depends only on the last request. -/
theorem active_foldl (pi : List (Event)) :
    active (pi.foldl step (fun _ => (0, true)))
      = (pi.map Op.op).foldl flagStep true := by
  induction pi using List.reverseRecOn with
  | nil => simp [active]
  | append_singleton pi e ih =>
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, List.map_append,
        List.foldl_append]
      cases he : e.op with
      | winning =>
          have hact : active (step (pi.foldl step (fun _ => (0, true))) e) = true := by
            rw [active]
            simp only [decide_eq_true_eq]
            exact ⟨e.rep, by simp [step, he]⟩
          rw [hact]
          simp [flagStep, he]
      | reset =>
          have hact : active (step (pi.foldl step (fun _ => (0, true))) e) = false := by
            rw [active]
            simp [step, he]
          rw [hact]
          simp [flagStep, he]

/-- The sequential premise, in its unrestricted form: every replay of the
implementation is explained by the one-Boolean language. -/
theorem anyOrderSound :
    Soundness.AnyOrderSound D historySpec := by
  intro pi q
  have hlabels : projectedUpdates (D := D.toMRDTSig) pi
      = DeterministicSpec.updateLabels (pi.map Op.op) := by
    simp [projectedUpdates, DeterministicSpec.updateLabels, List.map_map,
      Function.comp]
  rw [hlabels, historySpec, specMachine.updates_query_iff]
  show (if true then !active (pi.foldl step (fun _ => (0, true)))
      else active (pi.foldl step (fun _ => (0, true)))) = _
  rw [active_foldl]
  exact (machine_fold true (pi.map Op.op) true).symm

/-! ## `Laws(D_type, Spec)`: the fourth law

SPEC-NON-COMM is the one law of Section 4 that mentions `Spec`. `boolStep`
ignores the Boolean it is handed, so in `Spec` two requests commute exactly
when they are the same request. The implementation agrees: equal requests
commute by `commutes_of_same_op`, and a `reset` against a `winning` does not
commute by `not_commutes_reset_winning`. So there is no specification
conflict for the implementation to erase. -/

/-- Equal requests commute in `Spec`. -/
theorem spec_commutes_of_same_op {o₁ o₂ : type.OType} (h : o₁ = o₂) :
    Interface.spec_commutes historySpec o₁ o₂ :=
  specMachine.language_commutes o₁ o₂ (fun _ => by rw [h])

/-- **SPEC-NON-COMM**: a pair that conflicts in `Spec` carries two different
requests, and such a pair does not commute in the implementation either. -/
theorem spec_non_comm : Interface.spec_non_comm D historySpec := by
  intro e₁ e₂ hn
  cases h₁ : e₁.op with
  | winning =>
      cases h₂ : e₂.op with
      | winning => exact absurd (spec_commutes_of_same_op (h₁.trans h₂.symm)) hn
      | reset =>
          exact fun hc => not_commutes_reset_winning e₂ e₁ h₂ h₁ (commutes_symm hc)
  | reset =>
      cases h₂ : e₂.op with
      | winning => exact not_commutes_reset_winning e₁ e₂ h₁ h₂
      | reset => exact absurd (spec_commutes_of_same_op (h₁.trans h₂.symm)) hn

/-- **The bundle the specification route consumes**: the obligations of
Section 5 together with SPEC-NON-COMM, the one law of Section 4 that
mentions `Spec`. -/
theorem obligations : SpecObligations D historySpec :=
  SpecObligations.ofUniform laws rc_non_comm cond_comm joinLaws spec_non_comm

/-! # Specification visibility, without SPEC-NON-COMM

This row proves SPEC-NON-COMM, so it does not **need** the route below. What
the section shows is that the route is available anyway, on its own terms.

Unlike the commuting rows, this one cannot just take the chronological
witness. Its `rc` is not empty, so `lo^C_E` carries same-time arrows between
concurrent events, and a same-time arrow is free to point backwards in time:
the timestamp order together with one such arrow is already a loop. The
witness has to be a genuine linear extension of `vis` and `lo^C_E` **at
once**, which exists exactly when the two have no loop between them.

They have none, because `rc` splits this alphabet cleanly. A same-time arrow
runs `reset` to `winning` and nowhere else, so

* no same-time arrow leaves a `winning`, which is `no_concurrent_from_winning`;
* nothing such an arrow's target sees is a `reset`, because a `reset` never
  commutes with a `winning` and the target absorbs its non-commuting visible
  successors, which is `succ_not_reset`.

Together those make every path out of such a target a single `vis` edge, so
a loop through one would make it see itself. That is `jointVis_acyclic`, and
with it the witness respects `vis` as well as `lo^C_E`, which is all
specification visibility asks, since every specification-visibility arrow
runs along `vis`.

The sequential premise stays `AnyOrderSound`, the unrestricted one the main
tree already proves for this row, and the row states no chosen-order premise
of its own. `Soundness.certifiedSpecRA_any` takes `joint` and the acyclicity
below and picks the witness itself. Only the **choice of witness** is
constrained here, not what the specification must admit. -/

variable {E : Set D.Event}

def jointVis (C : Ctx D) (E : Set D.Event) (a b : D.Event) : Prop :=
  a ∈ E ∧ b ∈ E ∧ (C.vis a b ∨ paperOrder (policy D) C E a b)

def Blocked (C : Ctx D) (E : Set D.Event) (w : D.Event) : Prop :=
  w ∈ E ∧ w.op = AppOp.winning ∧ ¬ ∃ c ∈ E, C.vis w c ∧ ¬ D.Commutes w c

theorem blocked_of_concurrent {a b : D.Event} (hbE : b ∈ E)
    (h : ¬ C.vis a b ∧ ¬ C.vis b a ∧ D.RcBefore a.op b.op ∧
      ¬ ∃ c ∈ E, C.vis b c ∧ ¬ D.Commutes b c) : Blocked C E b :=
  ⟨hbE, ((eventRcBefore_iff a b).mp h.2.2.1).2, h.2.2.2⟩

theorem succ_not_reset {w x : D.Event} (hw : Blocked C E w) (hxE : x ∈ E)
    (hvis : C.vis w x) : x.op ≠ AppOp.reset := by
  intro hx
  exact hw.2.2 ⟨x, hxE, hvis,
    (rc_non_comm w x).mpr (Or.inr ((eventRcBefore_iff x w).mpr ⟨hx, hw.2.1⟩))⟩

theorem no_concurrent_from_winning {w z : D.Event} (hwv : w.op = AppOp.winning)
    (h : ¬ C.vis w z ∧ ¬ C.vis z w ∧ D.RcBefore w.op z.op ∧
      ¬ ∃ c ∈ E, C.vis z c ∧ ¬ D.Commutes z c) : False := by
  have := ((eventRcBefore_iff w z).mp h.2.2.1).1
  rw [hwv] at this
  exact absurd this (by simp)

theorem vis_of_blocked_path (hvs : VisStrict D C) {w : D.Event}
    (hw : Blocked C E w) : ∀ {y}, Relation.TransGen (jointVis C E) w y → C.vis w y := by
  intro y h
  induction h with
  | single hedge =>
    rcases hedge.2.2 with hv | hp
    · exact hv
    · rcases hp with ⟨hv, -⟩ | hconc
      · exact hv
      · exact (no_concurrent_from_winning hw.2.1 hconc).elim
  | @tail y z _ hedge ih =>
    have hyres : y.op ≠ AppOp.reset := succ_not_reset hw hedge.1 ih
    rcases hedge.2.2 with hv | hp
    · exact hvs.1 ih hv
    · rcases hp with ⟨hv, -⟩ | hconc
      · exact hvs.1 ih hv
      · exact absurd ((eventRcBefore_iff y z).mp hconc.2.2.1).1 hyres

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
      have hyres : y.op ≠ AppOp.reset := by
        rcases hwy with rfl | hvwy
        · rw [hw.2.1]; simp
        · exact succ_not_reset hw hedge.1 hvwy
      have hvyz : C.vis y z := by
        rcases hedge.2.2 with hv' | hp
        · exact hv'
        · rcases hp with ⟨hv', -⟩ | hconc
          · exact hv'
          · exact absurd ((eventRcBefore_iff y z).mp hconc.2.2.1).1 hyres
      rcases hwy with rfl | hvwy
      · exact Or.inr hvyz
      · exact Or.inr (hvs.1 hvwy hvyz)

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

/-! ## The uniform interface

`Soundness.certifiedSpecRA_any` asks for one fact, that `Soundness.joint`
has no loop. That relation is specification visibility together with
`lo^C_E`, weaker than the `vis` version above, so the acyclicity carries
over by monotonicity. -/

/-- **No loop.** Every specification-visibility arrow runs along `vis`, so
`Soundness.joint` is a subrelation of `jointVis`, which `jointVis_acyclic`
shows has none. -/
theorem joint_acyclic : Soundness.JointAcyclic D historySpec :=
  fun _ _ hvs a h => jointVis_acyclic hvs a
    (h.mono (fun {_ _} he => ⟨he.1, he.2.1, he.2.2.imp (fun hs => hs.1) id⟩))

end LeanProofs.NoSpecNonComm.Implementations.DisableWinsFlag
