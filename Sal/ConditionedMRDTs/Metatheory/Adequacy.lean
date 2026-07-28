import Sal.ConditionedMRDTs.Framework.VC_Set
import Sal.ConditionedMRDTs.Metatheory.LCA_Lemma
import Sal.CRDTs.Metatheory.RA_Lin_Of_Join

/-!
# ADEQUACY: the VC set suffices for RA-linearizability

The generic theorems, quantifying over every configuration reachable in the
ternary transition system `Step3` (from `initConfig`), concluding
**per-version** RA-linearizability (`IsRALinearizable3` — the paper's Def-lin
for every version in the store, LCAs included):

* `GoodConfig3` — the reachability invariant (every version canonical, plus
  the store closure facts) and its per-transition preservation;
* `join_lemma3_of_cd` / `join_lemma3_of_cd_feasible` — the master inductions
  from the (feasible) delta contract + the CD equation to `JoinLemma3`;
* `ra_linearizable3_of_join` / `ra_linearizable_of_core_delta_cd3` /
  `ra_linearizable_of_core_feasible_cd3` — the end-to-end bridges;
* `cdVC3_of_all_comm` — the commuting class gets `CDVC3` for free;
* `goodConfig3_mergeF` / `ra_linearizable3_of_joinF` — the **full-closure**
  bridge consumed by the Enable-wins route (`JoinLemma3F`).
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

section
variable {D : ConditionedMRDTSig}

/-- **Per-version RA-linearizability** of a ternary configuration (paper Def. lin
over versions), with the witness respecting the (unconditioned) `lo` of the
replica-keyed core. -/
def IsRALinearizable3 (C : Configuration D) : Prop :=
  ∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
    C.ver v = some (s, E) →
    ∃ π : List (Op D.AppOp),
      listPermOf π E ∧
      respects π (Sal.Emulation.lo (Configuration.core C)) ∧
      applySeq D.toCRDTSig D.init π = s

/-- The reachability invariant: **every allocated version** holds the canonical
state of its event set (LCAs are historical versions, so replica heads are not
enough), plus `vis` transitivity/irreflexivity and the two facts historical
versions need — their event sets stay inside the replica-observed universe
(feeds Apply-freshness) and stay causally closed (feeds the Join Lemma's
backward-closure premises). -/
structure GoodConfig3 (C : Configuration D) : Prop where
  canonical : ∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
    C.ver v = some (s, E) → IsCanonicalState (Configuration.core C) E s
  vis_trans : ∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c
  vis_irrefl : ∀ a : Op D.AppOp, ¬ C.vis a a
  ver_events_sub : ∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
    C.ver v = some (s, E) → ∀ a ∈ E, a ∈ C.events
  ver_causal : ∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
    C.ver v = some (s, E) → ∀ a b, C.vis a b → b ∈ E → a ∈ E

/-- The strengthened invariant delivers per-version Def-lin
(`isCanonicalState_lo_witness`, reused). -/
theorem isRALinearizable3_of_good {C : Configuration D}
    (h : GoodConfig3 C) : IsRALinearizable3 C :=
  fun v s E hv => isCanonicalState_lo_witness (h.canonical v s E hv)

/-- The invariant holds initially: the only allocated version is `0 = (σ₀, ∅)`. -/
theorem goodConfig3_init (hInit : D.Inv D.init) :
    GoodConfig3 (initConfig D hInit) := by
  have hver : ∀ v, (initConfig D hInit).ver v
      = if v = 0 then some (D.init, (∅ : Set (Op D.AppOp))) else none :=
    fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v s E hv
    rw [hver] at hv
    by_cases h : v = 0
    · rw [if_pos h, Option.some.injEq, Prod.mk.injEq] at hv
      rw [← hv.1, ← hv.2]
      exact ⟨[], ⟨List.nodup_nil, fun a => by simp⟩, List.Pairwise.nil, rfl⟩
    · rw [if_neg h] at hv
      simp at hv
  · intro a b c h _
    exact absurd h id
  · intro a h
    exact absurd h id
  · intro v s E hv a ha
    rw [hver] at hv
    by_cases h : v = 0
    · rw [if_pos h, Option.some.injEq, Prod.mk.injEq] at hv
      rw [← hv.2] at ha
      exact absurd ha (Set.notMem_empty a)
    · rw [if_neg h] at hv
      simp at hv
  · intro v s E hv a b hab _
    exact absurd hab id

/-- **CreateReplica preserves the invariant** (store and `vis` unchanged; the
fresh replica cannot shrink the event universe because it was inactive). -/
theorem goodConfig3_createReplica {C C' : Configuration D} {r : Replica}
    (h_fresh : C.N r = none)
    (hL : C'.L = updateRep C.L r ∅)
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = C.ver)
    (h : GoodConfig3 C) : GoodConfig3 C' := by
  have h_events : ∀ x, x ∈ C.events → x ∈ C'.events := by
    rintro x ⟨r'', s'', hLr'', hx⟩
    by_cases hr'' : r'' = r
    · subst hr''
      have hnone := (C.dom_eq r'').mp h_fresh
      rw [hnone] at hLr''
      simp at hLr''
    · refine ⟨r'', s'', ?_, hx⟩
      rw [hL]
      simp only [updateRep, if_neg hr'']
      exact hLr''
  have h_same : ∀ (E' : Set (Op D.AppOp)) (s' : D.State),
      IsCanonicalState (Configuration.core C) E' s' →
      IsCanonicalState (Configuration.core C') E' s' := by
    intro E' s' hcs
    refine isCanonicalState_congr (fun a _ b _ => ?_) hcs
    rw [core_vis, core_vis, hvis]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v s E hv
    rw [hver] at hv
    exact h_same E s (h.canonical v s E hv)
  · intro a b c hab hbc
    rw [hvis] at hab hbc ⊢
    exact h.vis_trans hab hbc
  · intro a ha
    rw [hvis] at ha
    exact h.vis_irrefl a ha
  · intro v s E hv a ha
    rw [hver] at hv
    exact h_events a (h.ver_events_sub v s E hv a ha)
  · intro v s E hv a b hab hb
    rw [hver] at hv
    rw [hvis] at hab
    exact h.ver_causal v s E hv a b hab hb

/-- **Apply preserves the invariant**: the fresh version extends its parent's
canonical state (`isCanonicalState_extend`); every old version is untouched
because the fresh event lies outside its (universe-bounded) event set. -/
theorem goodConfig3_apply {C C' : Configuration D}
    {t : Timestamp} {r : Replica} {o : D.AppOp}
    {v : Version} {s : D.State} {ev : Set (Op D.AppOp)} {vnew : Version}
    (h_head : C.head r = some v)
    (h_ver : C.ver v = some (s, ev))
    (h_fresh_t : ∀ e', e' ∈ C.events → Op.time e' ≠ t)
    (h_vnew : C.ver vnew = none)
    (hL : C'.L = updateRep C.L r (ev ∪ {(t, r, o)}))
    (hvis : C'.vis = fun a b => C.vis a b ∨ (ev a ∧ b = (t, r, o)))
    (hver : C'.ver = fun w => if w = vnew
      then some (D.update s (t, r, o), ev ∪ {(t, r, o)}) else C.ver w)
    (h : GoodConfig3 C) : GoodConfig3 C' := by
  set e : Op D.AppOp := (t, r, o) with he_def
  have hco := C.head_coherent r v h_head
  have hLr : C.L r = some ev := by
    rw [← hco.2, h_ver]; rfl
  have he_not_events : e ∉ C.events := fun hmem => h_fresh_t _ hmem rfl
  have h_ev_events : ∀ x ∈ ev, x ∈ C.events := fun x hx => ⟨r, ev, hLr, hx⟩
  have he_not_ev : e ∉ ev := fun hmem => he_not_events (h_ev_events e hmem)
  have h_no_vis_out : ∀ x, ¬ C.vis e x := by
    intro x hx
    obtain ⟨r₀, s₀, hL₀, hs₀⟩ := C.vis_src hx
    exact he_not_events ⟨r₀, s₀, hL₀, hs₀⟩
  have hver_new : C'.ver vnew = some (D.update s e, ev ∪ {e}) := by
    rw [hver]; simp
  have hver_old : ∀ w, w ≠ vnew → C'.ver w = C.ver w := by
    intro w hw; rw [hver]; simp [hw]
  -- The event universe only grows (the touched replica's set grows).
  have h_events : ∀ x, x ∈ C.events → x ∈ C'.events := by
    rintro x ⟨r'', s'', hLr'', hx⟩
    by_cases hr'' : r'' = r
    · subst hr''
      rw [hLr, Option.some.injEq] at hLr''
      refine ⟨r'', ev ∪ {e}, ?_, Or.inl (hLr'' ▸ hx)⟩
      rw [hL]
      simp [updateRep]
    · refine ⟨r'', s'', ?_, hx⟩
      rw [hL]
      simp only [updateRep, if_neg hr'']
      exact hLr''
  have hL'r : C'.L r = some (ev ∪ {e}) := by
    rw [hL]
    simp [updateRep]
  -- Old event sets do not contain the fresh event.
  have h_old_no_e : ∀ (w : Version) (s' : D.State) (E' : Set (Op D.AppOp)),
      C.ver w = some (s', E') → e ∉ E' := by
    intro w s' E' hw hmem
    exact he_not_events (h.ver_events_sub w s' E' hw e hmem)
  -- vis is unchanged on pairs of old events.
  have h_vis_old : ∀ (E' : Set (Op D.AppOp)), (∀ x ∈ E', x ∈ C.events) →
      ∀ a, a ∈ E' → ∀ b, b ∈ E' → (C'.vis a b ↔ C.vis a b) := by
    intro E' hsub a _ b hb
    rw [hvis]
    constructor
    · rintro (hab | ⟨_, rfl⟩)
      · exact hab
      · exact absurd (hsub _ hb) he_not_events
    · exact Or.inl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- canonical
    intro w s' E' hw
    by_cases hwn : w = vnew
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.1, ← hw.2]
      -- extend the parent's canonical state by the fresh event
      have h_old : IsCanonicalState (Configuration.core C) ev s :=
        h.canonical v s ev h_ver
      have h_old' : IsCanonicalState (Configuration.core C') ev s := by
        refine isCanonicalState_congr (fun a ha b hb => ?_) h_old
        rw [core_vis, core_vis]
        exact h_vis_old ev h_ev_events a ha b hb
      have h_ext := isCanonicalState_extend (e := e) he_not_ev
        (fun x hx => by
          rw [core_vis, hvis]; exact Or.inr ⟨hx, rfl⟩)
        (fun x hx => by
          rw [core_vis, hvis]
          rintro (hex | ⟨he_ev, _⟩)
          · exact h_no_vis_out x hex
          · exact he_not_ev he_ev)
        h_old'
      rw [Set.union_singleton]
      exact h_ext
    · rw [hver_old w hwn] at hw
      have h_old : IsCanonicalState (Configuration.core C) E' s' :=
        h.canonical w s' E' hw
      refine isCanonicalState_congr (fun a ha b hb => ?_) h_old
      rw [core_vis, core_vis]
      exact h_vis_old E' (h.ver_events_sub w s' E' hw) a ha b hb
  · -- vis-transitivity
    intro a b c hab hbc
    rw [hvis] at hab hbc ⊢
    rcases hab with hab | ⟨ha_ev, rfl⟩
    · rcases hbc with hbc | ⟨hb_ev, rfl⟩
      · exact Or.inl (h.vis_trans hab hbc)
      · exact Or.inr ⟨h.ver_causal v s ev h_ver a b hab hb_ev, rfl⟩
    · rcases hbc with hbc | ⟨hb_ev, rfl⟩
      · exact absurd hbc (h_no_vis_out c)
      · exact absurd hb_ev he_not_ev
  · -- vis-irreflexivity
    intro a ha
    rw [hvis] at ha
    rcases ha with ha | ⟨ha_ev, rfl⟩
    · exact h.vis_irrefl a ha
    · exact he_not_ev ha_ev
  · -- ver_events_sub
    intro w s' E' hw a ha
    by_cases hwn : w = vnew
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at ha
      rcases ha with ha | ha
      · exact ⟨r, ev ∪ {e}, hL'r, Or.inl ha⟩
      · exact ⟨r, ev ∪ {e}, hL'r, Or.inr ha⟩
    · rw [hver_old w hwn] at hw
      exact h_events a (h.ver_events_sub w s' E' hw a ha)
  · -- ver_causal
    intro w s' E' hw a b hab hb
    rw [hvis] at hab
    by_cases hwn : w = vnew
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at hb ⊢
      rcases hb with hb | hb
      · -- b is an old event of the parent set
        rcases hab with hab | ⟨_, rfl⟩
        · exact Or.inl (h.ver_causal v s ev h_ver a b hab hb)
        · exact absurd hb he_not_ev
      · -- b is the fresh event
        have hb_e : b = e := hb
        subst hb_e
        rcases hab with hab | ⟨ha_ev, _⟩
        · exfalso
          obtain ⟨r₀, s₀, hL₀, hs₀⟩ := C.vis_tgt hab
          exact he_not_events ⟨r₀, s₀, hL₀, hs₀⟩
        · exact Or.inl ha_ev
    · rw [hver_old w hwn] at hw
      rcases hab with hab | ⟨_, rfl⟩
      · exact h.ver_causal w s' E' hw a b hab hb
      · exact absurd hb (h_old_no_e w s' E' hw)

/-- **Merge preserves the invariant** — `JoinLemma3` at work, with the LCA event
set delivered by the `lca_events` field (its maintainability is
`LCA_Lemma.lean`), and the LCA version's canonical state delivered by the
every-version coverage of `GoodConfig3`. -/
theorem goodConfig3_merge_at
    {C C' : Configuration D}
    (hJoin : JoinLemma3At D (Configuration.core C))
    {r₁ : Replica}
    {v₁ v₂ vT vm : Version} {s₁ s₂ sT : D.State}
    {ev₁ ev₂ evT : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (h_lca : IsLCA C.parents v₁ v₂ vT)
    (h_verT : C.ver vT = some (sT, evT))
    (hL : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some (D.mergeL sT s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (h : GoodConfig3 C) : GoodConfig3 C' := by
  have hco := C.head_coherent r₁ v₁ h_head₁
  have hLr₁ : C.L r₁ = some ev₁ := by
    rw [← hco.2, h_ver₁]; rfl
  have hevT_eq : evT = ev₁ ∩ ev₂ :=
    C.lca_events h_lca h_ver₁ h_ver₂ h_verT
  have hver_new : C'.ver vm = some (D.mergeL sT s₁ s₂, ev₁ ∪ ev₂) := by
    rw [hver]; simp
  have hver_old : ∀ w, w ≠ vm → C'.ver w = C.ver w := by
    intro w hw; rw [hver]; simp [hw]
  have h_same : ∀ (E' : Set (Op D.AppOp)) (s' : D.State),
      IsCanonicalState (Configuration.core C) E' s' →
      IsCanonicalState (Configuration.core C') E' s' := by
    intro E' s' hcs
    refine isCanonicalState_congr (fun a _ b _ => ?_) hcs
    rw [core_vis, core_vis, hvis]
  have hL'r₁ : C'.L r₁ = some (ev₁ ∪ ev₂) := by
    rw [hL]
    simp [updateRep]
  have h_events : ∀ x, x ∈ C.events → x ∈ C'.events := by
    rintro x ⟨r'', s'', hLr'', hx⟩
    by_cases hr'' : r'' = r₁
    · subst hr''
      rw [hLr₁, Option.some.injEq] at hLr''
      exact ⟨r'', ev₁ ∪ ev₂, hL'r₁, Or.inl (hLr'' ▸ hx)⟩
    · refine ⟨r'', s'', ?_, hx⟩
      rw [hL]
      simp only [updateRep, if_neg hr'']
      exact hLr''
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- canonical
    intro w s' E' hw
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.1, ← hw.2]
      -- the Join Lemma at the core configuration
      have hcT : IsCanonicalState (Configuration.core C) (ev₁ ∩ ev₂) sT := by
        rw [← hevT_eq]
        exact h.canonical vT sT evT h_verT
      have h_join := hJoin ev₁ ev₂ sT s₁ s₂
        (fun hab hbc => h.vis_trans hab hbc)
        (fun a ha => h.vis_irrefl a ha)
        (h.ver_events_sub v₁ s₁ ev₁ h_ver₁)
        (h.ver_events_sub v₂ s₂ ev₂ h_ver₂)
        (fun a b hab _ hb => h.ver_causal v₁ s₁ ev₁ h_ver₁ a b hab hb)
        (fun a b hab _ hb => h.ver_causal v₂ s₂ ev₂ h_ver₂ a b hab hb)
        hcT
        (h.canonical v₁ s₁ ev₁ h_ver₁)
        (h.canonical v₂ s₂ ev₂ h_ver₂)
      exact h_same _ _ h_join
    · rw [hver_old w hwn] at hw
      exact h_same E' s' (h.canonical w s' E' hw)
  · intro a b c hab hbc
    rw [hvis] at hab hbc ⊢
    exact h.vis_trans hab hbc
  · intro a ha
    rw [hvis] at ha
    exact h.vis_irrefl a ha
  · -- ver_events_sub
    intro w s' E' hw a ha
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at ha
      exact ⟨r₁, ev₁ ∪ ev₂, hL'r₁, ha⟩
    · rw [hver_old w hwn] at hw
      exact h_events a (h.ver_events_sub w s' E' hw a ha)
  · -- ver_causal
    intro w s' E' hw a b hab hb
    rw [hvis] at hab
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at hb ⊢
      rcases hb with hb | hb
      · exact Or.inl (h.ver_causal v₁ s₁ ev₁ h_ver₁ a b hab hb)
      · exact Or.inr (h.ver_causal v₂ s₂ ev₂ h_ver₂ a b hab hb)
    · rw [hver_old w hwn] at hw
      exact h.ver_causal w s' E' hw a b hab hb


/-! ### 1. Length bookkeeping (private copies of the binary helpers) -/

private theorem listPermOf_length_lt3 {α : Type} {l l' : List α}
    {ev ev' : Set α} {x : α}
    (h : listPermOf l ev) (h' : listPermOf l' ev')
    (hsub : ev ⊆ ev') (hx : x ∈ ev') (hxn : x ∉ ev) :
    l.length < l'.length := by
  have hnd : (x :: l).Nodup := by
    rw [List.nodup_cons]
    exact ⟨fun hmem => hxn ((h.2 x).mp hmem), h.1⟩
  have hsp : List.Subperm (x :: l) l' := by
    refine List.subperm_of_subset hnd ?_
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact (h'.2 a).mpr hx
    · exact (h'.2 a).mpr (hsub ((h.2 a).mp ha'))
  have hle := hsp.length_le
  simp only [List.length_cons] at hle
  omega

private theorem exists_listPermOf_subset3 {α : Type} {l : List α}
    {T S : Set α} (h : listPermOf l T) (hsub : S ⊆ T) :
    ∃ l', listPermOf l' S := by
  classical
  refine ⟨l.filter (fun a => decide (a ∈ S)), h.1.filter _, fun a => ?_⟩
  rw [List.mem_filter]
  constructor
  · rintro ⟨_, hd⟩
    exact of_decide_eq_true hd
  · intro ha
    exact ⟨(h.2 a).mpr (hsub ha), decide_eq_true ha⟩

/-! ### 2. The master induction -/

/-- The ternary Join Lemma at a fixed configuration, for instances whose
union has an enumeration of length `n`. -/
private def JoinAt3 (C : Sal.Emulation.Configuration D.toCRDTSig) (n : ℕ) :
    Prop :=
  ∀ (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State)
    (lU : List (Op D.AppOp)),
    listPermOf lU (ev₁ ∪ ev₂) → lU.length = n →
    (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
    IsCanonicalState C (ev₁ ∩ ev₂) s₀ →
    IsCanonicalState C ev₁ s₁ → IsCanonicalState C ev₂ s₂ →
    IsCanonicalState C (ev₁ ∪ ev₂) (D.mergeL s₀ s₁ s₂)

/-- **Side decomposition (ternary)**: a backward-closed `E ∋ e` inside `U`
satisfies `σ(E) = mergeL B σ(E∖e) (update B e)` — by the IH at `|E| < n` when
`E ⊊ U` (a Join-Lemma instance whose sides are `E∖e` and `↓e`, sitting at
their honest LCA set `(E∖e) ∩ ↓e = ↓e∖{e}` with state `B`), and by `CDVC3`
when `E = U`. As in the binary proof, no peel of `e` from `E`'s own
linearization is ever demanded — the buried-event difficulty (A3) dissolves. -/
private theorem side_decomposition3 (hVC : CoreVCs3 D) (hCD : CDVC3 D)
    {C : Sal.Emulation.Configuration D.toCRDTSig}
    (h_tr : ∀ {a b c : Op D.AppOp},
      C.vis a b → C.vis b c → C.vis a c)
    (h_ir : ∀ a : Op D.AppOp, ¬ C.vis a a)
    {n : ℕ} (IH : ∀ m, m < n → JoinAt3 C m)
    {U : Set (Op D.AppOp)} {lU : List (Op D.AppOp)}
    (hpU : listPermOf lU U) (hlen : lU.length = n)
    (h_inU : ∀ a ∈ U, a ∈ C.events)
    (h_clU : ∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b →
      b ∈ U → a ∈ U)
    {e : Op D.AppOp} (h_e : e ∈ U)
    (h_max : ∀ x ∈ U, x ≠ e → ¬ loOn C U e x)
    {A B : D.State}
    (hA : IsCanonicalState C (U \ {e}) A)
    (hB : IsCanonicalState C (downset C e \ {e}) B)
    {E : Set (Op D.AppOp)} {s t : D.State}
    (h_subE : E ⊆ U)
    (h_inE : ∀ a ∈ E, a ∈ C.events)
    (h_clE : ∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b →
      b ∈ E → a ∈ E)
    (h_eE : e ∈ E)
    (hs : IsCanonicalState C E s)
    (ht : IsCanonicalState C (E \ {e}) t) :
    s = D.mergeL B t (D.update B e) := by
  classical
  have hU := hVC.update_core
  -- update B e is canonical for the downset (free peel, no VC).
  have hT : IsCanonicalState C (downset C e) (D.update B e) :=
    isCanonicalState_snoc self_mem_downset (downset_max h_tr h_ir) hB
  by_cases hEU : E = U
  · -- E = U: exactly CDVC3.
    subst hEU
    have h_eq : D.mergeL B A (D.update B e) = D.update A e :=
      hCD C E A B e h_tr h_ir h_inE h_clE h_eE h_max hA hB
    have htA : t = A :=
      isCanonicalState_unique_u hU (fun a ha => h_inE a ha.1) ht hA
    have hsA : s = D.update A e :=
      isCanonicalState_unique_u hU h_inE hs
        (isCanonicalState_snoc h_eE h_max hA)
    rw [htA, h_eq]
    exact hsA
  · -- E ⊊ U: the IH at |E| < n, on the pair (E∖e, ↓e).
    obtain ⟨lE, hpE, -, -⟩ := id hs
    obtain ⟨x, hxU, hxE⟩ : ∃ x ∈ U, x ∉ E := by
      by_contra h
      push_neg at h
      exact hEU (Set.Subset.antisymm h_subE h)
    have hlt : lE.length < n := by
      rw [← hlen]
      exact listPermOf_length_lt3 hpE hpU h_subE hxU hxE
    have h_dsubE : downset C e ⊆ E := downset_subset h_clE h_eE
    -- the pair's honest LCA set
    have hsetI : (E \ {e}) ∩ downset C e = downset C e \ {e} := by
      ext y
      constructor
      · rintro ⟨⟨_, hyne⟩, hyd⟩
        exact ⟨hyd, hyne⟩
      · rintro ⟨hyd, hyne⟩
        exact ⟨⟨h_dsubE hyd, hyne⟩, hyd⟩
    have hsetE : (E \ {e}) ∪ downset C e = E := by
      ext y
      constructor
      · rintro (hy | hy)
        · exact hy.1
        · exact h_dsubE hy
      · intro hy
        by_cases hye : y = e
        · subst hye
          exact Or.inr self_mem_downset
        · exact Or.inl ⟨hy, hye⟩
    have hB' : IsCanonicalState C ((E \ {e}) ∩ downset C e) B := by
      rw [hsetI]
      exact hB
    have h_merge_can : IsCanonicalState C ((E \ {e}) ∪ downset C e)
        (D.mergeL B t (D.update B e)) := by
      refine IH lE.length hlt _ _ B t (D.update B e) lE ?_ rfl
        (fun a ha => h_inE a ha.1)
        (fun a ha => h_inE a (h_dsubE ha))
        (closure_diff_of_max h_subE h_clE h_max)
        downset_closed hB' ht hT
      rw [hsetE]
      exact hpE
    have h_merge_can' : IsCanonicalState C E
        (D.mergeL B t (D.update B e)) := by
      rw [← hsetE]
      exact h_merge_can
    exact isCanonicalState_unique_u hU h_inE hs h_merge_can'

/-- The original `JoinLemma3`-driven form, as a thin wrapper over
`goodConfig3_merge_at`. -/
theorem goodConfig3_merge (hJoin : JoinLemma3 D)
    {C C' : Configuration D} {r₁ : Replica}
    {v₁ v₂ vT vm : Version} {s₁ s₂ sT : D.State}
    {ev₁ ev₂ evT : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (h_lca : IsLCA C.parents v₁ v₂ vT)
    (h_verT : C.ver vT = some (sT, evT))
    (hL : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some (D.mergeL sT s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (h : GoodConfig3 C) : GoodConfig3 C' :=
  goodConfig3_merge_at (hJoin.at _) h_head₁ h_ver₁ h_ver₂ h_lca h_verT
    hL hvis hver h
/-- **The ternary Join Lemma from `CoreVCs3` + the delta contract + (CD3).**
Compare `join_lemma3_of_peel` (which consumes the two full peel equations with
their three-way LCA bookkeeping) and the binary `join_lemma_of_cd` (whose
lattice laws the delta contract replaces — no idempotence, no inflation, no
associativity, no order). -/
theorem join_lemma3_of_cd (hVC : CoreVCs3 D) (hΔ : DeltaVCs3 D)
    (hCD : CDVC3 D) : JoinLemma3 D := by
  intro C ev₁ ev₂ s₀ s₁ s₂ h_tr h_ir h_in₁ h_in₂ h_cl₁ h_cl₂ hc₀ hc₁ hc₂
  classical
  have hU := hVC.update_core
  obtain ⟨l₁, hp₁, -, -⟩ := id hc₁
  obtain ⟨l₂, hp₂, -, -⟩ := id hc₂
  have hpU₀ := listPermOf_union (D := D.toCRDTSig) hp₁ hp₂
  suffices gen : ∀ n, JoinAt3 (D := D) C n by
    exact gen _ ev₁ ev₂ s₀ s₁ s₂ _ hpU₀ rfl h_in₁ h_in₂ h_cl₁ h_cl₂
      hc₀ hc₁ hc₂
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro ev₁ ev₂ s₀ s₁ s₂ lU hpU hlen h_in₁ h_in₂ h_cl₁ h_cl₂ hc₀ hc₁ hc₂
    -- Empty sides collapse via mergeL_init.
    rcases Set.eq_empty_or_nonempty ev₁ with h_e₁ | h_ne₁
    · have hs₁ : s₁ = D.init := isCanonicalState_empty h_e₁ hc₁
      have h_int : ev₁ ∩ ev₂ = ∅ := by rw [h_e₁, Set.empty_inter]
      have hs₀ : s₀ = D.init := isCanonicalState_empty h_int hc₀
      subst h_e₁
      rw [hs₀, hs₁, hVC.mergeL_init, Set.empty_union]
      exact hc₂
    rcases Set.eq_empty_or_nonempty ev₂ with h_e₂ | h_ne₂
    · have hs₂ : s₂ = D.init := isCanonicalState_empty h_e₂ hc₂
      have h_int : ev₁ ∩ ev₂ = ∅ := by rw [h_e₂, Set.inter_empty]
      have hs₀ : s₀ = D.init := isCanonicalState_empty h_int hc₀
      subst h_e₂
      rw [hs₀, hs₂, hVC.mergeL_comm, hVC.mergeL_init, Set.union_empty]
      exact hc₁
    -- Select a loOn(∪)-maximal event; build A = σ(U∖e), B = σ(↓e∖e).
    have h_inU : ∀ a ∈ ev₁ ∪ ev₂, a ∈ C.events := by
      rintro a (h | h)
      · exact h_in₁ a h
      · exact h_in₂ a h
    have h_clU : ∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b →
        b ∈ ev₁ ∪ ev₂ → a ∈ ev₁ ∪ ev₂ := by
      rintro a b hv hnc (h | h)
      · exact Or.inl (h_cl₁ a b hv hnc h)
      · exact Or.inr (h_cl₂ a b hv hnc h)
    obtain ⟨x₁, hx₁⟩ := h_ne₁
    obtain ⟨e, he_U, h_max⟩ :=
      exists_loOn_maximal_u hU h_tr h_ir hpU h_inU ⟨x₁, Or.inl hx₁⟩
    have h_e_lU : e ∈ lU := (hpU.2 e).mpr he_U
    have hpU' : listPermOf (lU.filter (· ≠ e)) ((ev₁ ∪ ev₂) \ {e}) :=
      filter_ne_listPermOf hpU h_e_lU
    have hlen' : (lU.filter (· ≠ e)).length = n - 1 := by
      rw [listPermOf_diff_length hpU h_e_lU hpU', hlen]
    have h_pos : 0 < n := by
      rw [← hlen]
      exact List.length_pos_of_mem h_e_lU
    obtain ⟨A, hA⟩ : ∃ A, IsCanonicalState C ((ev₁ ∪ ev₂) \ {e}) A :=
      isCanonicalState_exists_u hU h_tr h_ir hpU'
        (fun a ha => h_inU a ha.1)
    have h_dsub : downset C e ⊆ ev₁ ∪ ev₂ := downset_subset h_clU he_U
    obtain ⟨lB, hpB⟩ :=
      exists_listPermOf_subset3 hpU
        (fun x (hx : x ∈ downset C e \ {e}) => h_dsub hx.1)
    obtain ⟨B, hB⟩ : ∃ B, IsCanonicalState C (downset C e \ {e}) B :=
      isCanonicalState_exists_u hU h_tr h_ir hpB
        (fun a ha => h_inU a (h_dsub ha.1))
    -- The CD equation and the target canonical state.
    have h_cd : D.mergeL B A (D.update B e) = D.update A e :=
      hCD C (ev₁ ∪ ev₂) A B e h_tr h_ir h_inU h_clU he_U h_max hA hB
    have h_target : IsCanonicalState C (ev₁ ∪ ev₂) (D.update A e) :=
      isCanonicalState_snoc he_U h_max hA
    by_cases he₁ : e ∈ ev₁
    · obtain ⟨t₁, ht₁⟩ : ∃ t, IsCanonicalState C (ev₁ \ {e}) t := by
        obtain ⟨l₁', hp₁', -, -⟩ := id hc₁
        have h_e_l₁ : e ∈ l₁' := (hp₁'.2 e).mpr he₁
        exact isCanonicalState_exists_u hU h_tr h_ir
          (filter_ne_listPermOf hp₁' h_e_l₁) (fun a ha => h_in₁ a ha.1)
      have hs₁d : s₁ = D.mergeL B t₁ (D.update B e) :=
        side_decomposition3 hVC hCD h_tr h_ir IH hpU hlen h_inU h_clU
          he_U h_max hA hB Set.subset_union_left h_in₁ h_cl₁ he₁ hc₁ ht₁
      by_cases he₂ : e ∈ ev₂
      · -- e shared: all three components decompose; `redistribute`
        -- extracts the delta once (the LCA slot cancels the duplicate —
        -- no idempotence).
        obtain ⟨t₂, ht₂⟩ : ∃ t, IsCanonicalState C (ev₂ \ {e}) t := by
          obtain ⟨l₂', hp₂', -, -⟩ := id hc₂
          have h_e_l₂ : e ∈ l₂' := (hp₂'.2 e).mpr he₂
          exact isCanonicalState_exists_u hU h_tr h_ir
            (filter_ne_listPermOf hp₂' h_e_l₂) (fun a ha => h_in₂ a ha.1)
        have hs₂d : s₂ = D.mergeL B t₂ (D.update B e) :=
          side_decomposition3 hVC hCD h_tr h_ir IH hpU hlen h_inU h_clU
            he_U h_max hA hB Set.subset_union_right h_in₂ h_cl₂ he₂
            hc₂ ht₂
        -- the LCA side also contains e and decomposes
        have he₀ : e ∈ ev₁ ∩ ev₂ := ⟨he₁, he₂⟩
        have h_in₀ : ∀ a ∈ ev₁ ∩ ev₂, a ∈ C.events :=
          fun a ha => h_in₁ a ha.1
        have h_cl₀ : ∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b →
            b ∈ ev₁ ∩ ev₂ → a ∈ ev₁ ∩ ev₂ :=
          fun a b hv hnc hb =>
            ⟨h_cl₁ a b hv hnc hb.1, h_cl₂ a b hv hnc hb.2⟩
        obtain ⟨l₀', hp₀'⟩ :=
          exists_listPermOf_subset3 hpU
            (show (ev₁ ∩ ev₂) \ {e} ⊆ ev₁ ∪ ev₂ from
              fun x hx => Or.inl hx.1.1)
        obtain ⟨t₀, ht₀⟩ :
            ∃ t, IsCanonicalState C ((ev₁ ∩ ev₂) \ {e}) t :=
          isCanonicalState_exists_u hU h_tr h_ir hp₀'
            (fun a ha => h_in₁ a ha.1.1)
        have hs₀d : s₀ = D.mergeL B t₀ (D.update B e) :=
          side_decomposition3 hVC hCD h_tr h_ir IH hpU hlen h_inU h_clU
            he_U h_max hA hB
            (show ev₁ ∩ ev₂ ⊆ ev₁ ∪ ev₂ from fun x hx => Or.inl hx.1)
            h_in₀ h_cl₀ he₀ hc₀ ht₀
        -- A = mergeL t₀ t₁ t₂ by the IH at n − 1.
        have hct₀' : IsCanonicalState C ((ev₁ \ {e}) ∩ (ev₂ \ {e})) t₀ := by
          rw [diff_inter_diff]
          exact ht₀
        have hsetm : (ev₁ \ {e}) ∪ (ev₂ \ {e}) = (ev₁ ∪ ev₂) \ {e} := by
          ext x
          simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
          tauto
        have h_mid_can : IsCanonicalState C ((ev₁ \ {e}) ∪ (ev₂ \ {e}))
            (D.mergeL t₀ t₁ t₂) := by
          refine IH (n - 1) (by omega) _ _ t₀ t₁ t₂
            (lU.filter (· ≠ e)) ?_ hlen'
            (fun a ha => h_in₁ a ha.1) (fun a ha => h_in₂ a ha.1)
            (closure_diff_of_max Set.subset_union_left h_cl₁ h_max)
            (closure_diff_of_max Set.subset_union_right h_cl₂ h_max)
            hct₀' ht₁ ht₂
          rw [hsetm]
          exact hpU'
        have h_mid_can' : IsCanonicalState C ((ev₁ ∪ ev₂) \ {e})
            (D.mergeL t₀ t₁ t₂) := by
          rw [← hsetm]
          exact h_mid_can
        have h_mid : D.mergeL t₀ t₁ t₂ = A :=
          isCanonicalState_unique_u hU (fun a ha => h_inU a ha.1)
            h_mid_can' hA
        rw [hs₀d, hs₁d, hs₂d, hΔ.redistribute, h_mid, h_cd]
        exact h_target
      · -- e local to side 1: the LCA component is untouched;
        -- `local_redistribute` moves the delta out.
        have hct₀' : IsCanonicalState C ((ev₁ \ {e}) ∩ ev₂) s₀ := by
          rw [inter_diff_left_of_not_mem he₂]
          exact hc₀
        have hset₁ : (ev₁ \ {e}) ∪ ev₂ = (ev₁ ∪ ev₂) \ {e} := by
          ext x
          simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
          constructor
          · rintro (⟨h, hne⟩ | h)
            · exact ⟨Or.inl h, hne⟩
            · exact ⟨Or.inr h, fun heq => he₂ (heq ▸ h)⟩
          · rintro ⟨h | h, hne⟩
            · exact Or.inl ⟨h, hne⟩
            · exact Or.inr h
        have h_mid_can : IsCanonicalState C ((ev₁ \ {e}) ∪ ev₂)
            (D.mergeL s₀ t₁ s₂) := by
          refine IH (n - 1) (by omega) _ _ s₀ t₁ s₂
            (lU.filter (· ≠ e)) ?_ hlen'
            (fun a ha => h_in₁ a ha.1) h_in₂
            (closure_diff_of_max Set.subset_union_left h_cl₁ h_max)
            h_cl₂ hct₀' ht₁ hc₂
          rw [hset₁]
          exact hpU'
        have h_mid_can' : IsCanonicalState C ((ev₁ ∪ ev₂) \ {e})
            (D.mergeL s₀ t₁ s₂) := by
          rw [← hset₁]
          exact h_mid_can
        have h_mid : D.mergeL s₀ t₁ s₂ = A :=
          isCanonicalState_unique_u hU (fun a ha => h_inU a ha.1)
            h_mid_can' hA
        rw [hs₁d, hΔ.local_redistribute, h_mid, h_cd]
        exact h_target
    · -- e local to side 2: mirror via mergeL_comm.
      have he₂ : e ∈ ev₂ := by
        rcases he_U with h | h
        · exact absurd h he₁
        · exact h
      obtain ⟨t₂, ht₂⟩ : ∃ t, IsCanonicalState C (ev₂ \ {e}) t := by
        obtain ⟨l₂', hp₂', -, -⟩ := id hc₂
        have h_e_l₂ : e ∈ l₂' := (hp₂'.2 e).mpr he₂
        exact isCanonicalState_exists_u hU h_tr h_ir
          (filter_ne_listPermOf hp₂' h_e_l₂) (fun a ha => h_in₂ a ha.1)
      have hs₂d : s₂ = D.mergeL B t₂ (D.update B e) :=
        side_decomposition3 hVC hCD h_tr h_ir IH hpU hlen h_inU h_clU
          he_U h_max hA hB Set.subset_union_right h_in₂ h_cl₂ he₂ hc₂ ht₂
      have hct₀' : IsCanonicalState C (ev₁ ∩ (ev₂ \ {e})) s₀ := by
        rw [inter_diff_right_of_not_mem he₁]
        exact hc₀
      have hset₂ : ev₁ ∪ (ev₂ \ {e}) = (ev₁ ∪ ev₂) \ {e} := by
        ext x
        simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
        constructor
        · rintro (h | ⟨h, hne⟩)
          · exact ⟨Or.inl h, fun heq => he₁ (heq ▸ h)⟩
          · exact ⟨Or.inr h, hne⟩
        · rintro ⟨h | h, hne⟩
          · exact Or.inl h
          · exact Or.inr ⟨h, hne⟩
      have h_mid_can : IsCanonicalState C (ev₁ ∪ (ev₂ \ {e}))
          (D.mergeL s₀ s₁ t₂) := by
        refine IH (n - 1) (by omega) _ _ s₀ s₁ t₂
          (lU.filter (· ≠ e)) ?_ hlen'
          h_in₁ (fun a ha => h_in₂ a ha.1) h_cl₁
          (closure_diff_of_max Set.subset_union_right h_cl₂ h_max)
          hct₀' hc₁ ht₂
        rw [hset₂]
        exact hpU'
      have h_mid_can' : IsCanonicalState C ((ev₁ ∪ ev₂) \ {e})
          (D.mergeL s₀ s₁ t₂) := by
        rw [← hset₂]
        exact h_mid_can
      have h_mid : D.mergeL s₀ s₁ t₂ = A :=
        isCanonicalState_unique_u hU (fun a ha => h_inU a ha.1)
          h_mid_can' hA
      rw [hs₂d, hVC.mergeL_comm s₀ s₁, hΔ.local_redistribute,
        hVC.mergeL_comm s₀ t₂ s₁, h_mid, h_cd]
      exact h_target

/-! ### 3. The commuting class discharges (CD3) for free

`↓e∖{e} = ∅`, so `B = init` and the bound is `merge_peel_comm3` at an empty
LCA fold plus `mergeL_init` — no idempotence needed (the binary
`cdVC_of_all_comm` consumed `merge_idem`; the ternary one does not). -/

theorem cdVC3_of_all_comm (hVC : CoreVCs3 D)
    (h_comm : ∀ a b : Op D.AppOp, D.toCRDTSig.commutes a b) : CDVC3 D := by
  intro C U A B e _ _ _ _ _ _ hA hB
  have h_down : downset C e \ {e} = ∅ := by
    ext x
    simp only [Set.mem_diff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false, not_and]
    rintro (hx | hx)
    · exact fun hne => hne hx
    · intro _
      exfalso
      cases hx with
      | single h' => exact h'.2 (h_comm _ _)
      | tail _ h' => exact h'.2 (h_comm _ _)
  have hBinit : B = D.init := isCanonicalState_empty h_down hB
  subst hBinit
  obtain ⟨ρ, hpA, -, hfA⟩ := id hA
  have h0 : applySeq D.toCRDTSig D.init ([] : List (Op D.AppOp)) = D.init :=
    rfl
  have hpc := hVC.merge_peel_comm3 D.init e [] ρ
    (fun x hx => absurd hx List.not_mem_nil)
    (fun x _ => h_comm e x)
  rw [h0] at hpc
  rw [hVC.mergeL_init] at hpc
  rw [← hfA, hVC.mergeL_comm, hpc]

/-! ### 4. End-to-end: the `GoodConfig3` induction against any `JoinLemma3` -/

open LabeledTS in
/-- The per-version RA-linearizability bridge from an abstract ternary Join
Lemma (the `GoodConfig3` induction of `RA_Lin_Of_Join3.lean`, replayed). -/
theorem ra_linearizable3_of_join (hJoin : JoinLemma3 D)
    {hInit : D.Inv D.init}
    (C : Configuration D)
    (hReach : (labeledTS3 D).ReachableFrom (initConfig D hInit) C) :
    IsRALinearizable3 C := by
  suffices h : GoodConfig3 C from isRALinearizable3_of_good h
  induction hReach with
  | refl => exact goodConfig3_init hInit
  | tail _ hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    cases hstep with
    | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
      exact goodConfig3_createReplica h_fresh hL hvis hver ih
    | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
        hN hL hvis hver hhead hparents =>
      exact goodConfig3_apply h_head h_ver h_fresh_t h_vnew hL hvis hver ih
    | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁
        h_rank₂ C' hN hL hvis hver hhead hparents =>
      exact goodConfig3_merge hJoin h_head₁ h_ver₁ h_ver₂ h_lca h_verT
        hL hvis hver ih
    | query h_s h_val => exact ih

/-- The unconditional contract implies the feasible one (context discarded);
`mergeL_init` supplies the unit law. T8's route is thereby a corollary of the
feasible route (`join_lemma3_of_cd'` below). -/
theorem feasibleDeltaVCs3_of_delta (hVC : CoreVCs3 D) (hΔ : DeltaVCs3 D) :
    FeasibleDeltaVCs3 D :=
  ⟨fun _ _ s _ _ => hVC.mergeL_init s,
   fun _ _ _ s₀ B t₁ s₂ e _ _ _ _ _ _ _ _ _ _ _ _ _ =>
     hΔ.local_redistribute s₀ B t₁ (D.update B e) s₂,
   fun _ _ _ t₀ t₁ t₂ B e _ _ _ _ _ _ _ _ _ _ _ _ _ =>
     hΔ.redistribute B t₀ t₁ t₂ (D.update B e)⟩

/-! ### 2. Private plumbing (copies; the originals are private upstream) -/

private theorem listPermOf_length_ltF {α : Type} {l l' : List α}
    {ev ev' : Set α} {x : α}
    (h : listPermOf l ev) (h' : listPermOf l' ev')
    (hsub : ev ⊆ ev') (hx : x ∈ ev') (hxn : x ∉ ev) :
    l.length < l'.length := by
  have hnd : (x :: l).Nodup := by
    rw [List.nodup_cons]
    exact ⟨fun hmem => hxn ((h.2 x).mp hmem), h.1⟩
  have hsp : List.Subperm (x :: l) l' := by
    refine List.subperm_of_subset hnd ?_
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact (h'.2 a).mpr hx
    · exact (h'.2 a).mpr (hsub ((h.2 a).mp ha'))
  have hle := hsp.length_le
  simp only [List.length_cons] at hle
  omega

private theorem exists_listPermOf_subsetF {α : Type} {l : List α}
    {T S : Set α} (h : listPermOf l T) (hsub : S ⊆ T) :
    ∃ l', listPermOf l' S := by
  classical
  refine ⟨l.filter (fun a => decide (a ∈ S)), h.1.filter _, fun a => ?_⟩
  rw [List.mem_filter]
  constructor
  · rintro ⟨_, hd⟩
    exact of_decide_eq_true hd
  · intro ha
    exact ⟨(h.2 a).mpr (hsub ha), decide_eq_true ha⟩

/-- The Join Lemma at a fixed configuration and union-enumeration length. -/
private def JoinAtF (C : Sal.Emulation.Configuration D.toCRDTSig) (n : ℕ) :
    Prop :=
  ∀ (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State)
    (lU : List (Op D.AppOp)),
    listPermOf lU (ev₁ ∪ ev₂) → lU.length = n →
    (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
    IsCanonicalState C (ev₁ ∩ ev₂) s₀ →
    IsCanonicalState C ev₁ s₁ → IsCanonicalState C ev₂ s₂ →
    IsCanonicalState C (ev₁ ∪ ev₂) (D.mergeL s₀ s₁ s₂)

/-- Side decomposition, slim-core version (verbatim from
`JoinLemma_Of_CD3.side_decomposition3` — only the bundle changes; it consumed
`update_core` alone). -/
private theorem side_decompositionF (hVC : CoreVCs3CD D) (hCD : CDVC3 D)
    {C : Sal.Emulation.Configuration D.toCRDTSig}
    (h_tr : ∀ {a b c : Op D.AppOp},
      C.vis a b → C.vis b c → C.vis a c)
    (h_ir : ∀ a : Op D.AppOp, ¬ C.vis a a)
    {n : ℕ} (IH : ∀ m, m < n → JoinAtF C m)
    {U : Set (Op D.AppOp)} {lU : List (Op D.AppOp)}
    (hpU : listPermOf lU U) (hlen : lU.length = n)
    (h_inU : ∀ a ∈ U, a ∈ C.events)
    (h_clU : ∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b →
      b ∈ U → a ∈ U)
    {e : Op D.AppOp} (h_e : e ∈ U)
    (h_max : ∀ x ∈ U, x ≠ e → ¬ loOn C U e x)
    {A B : D.State}
    (hA : IsCanonicalState C (U \ {e}) A)
    (hB : IsCanonicalState C (downset C e \ {e}) B)
    {E : Set (Op D.AppOp)} {s t : D.State}
    (h_subE : E ⊆ U)
    (h_inE : ∀ a ∈ E, a ∈ C.events)
    (h_clE : ∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b →
      b ∈ E → a ∈ E)
    (h_eE : e ∈ E)
    (hs : IsCanonicalState C E s)
    (ht : IsCanonicalState C (E \ {e}) t) :
    s = D.mergeL B t (D.update B e) := by
  classical
  have hU := hVC.update_core
  have hT : IsCanonicalState C (downset C e) (D.update B e) :=
    isCanonicalState_snoc self_mem_downset (downset_max h_tr h_ir) hB
  by_cases hEU : E = U
  · subst hEU
    have h_eq : D.mergeL B A (D.update B e) = D.update A e :=
      hCD C E A B e h_tr h_ir h_inE h_clE h_eE h_max hA hB
    have htA : t = A :=
      isCanonicalState_unique_u hU (fun a ha => h_inE a ha.1) ht hA
    have hsA : s = D.update A e :=
      isCanonicalState_unique_u hU h_inE hs
        (isCanonicalState_snoc h_eE h_max hA)
    rw [htA, h_eq]
    exact hsA
  · obtain ⟨lE, hpE, -, -⟩ := id hs
    obtain ⟨x, hxU, hxE⟩ : ∃ x ∈ U, x ∉ E := by
      by_contra h
      push_neg at h
      exact hEU (Set.Subset.antisymm h_subE h)
    have hlt : lE.length < n := by
      rw [← hlen]
      exact listPermOf_length_ltF hpE hpU h_subE hxU hxE
    have h_dsubE : downset C e ⊆ E := downset_subset h_clE h_eE
    have hsetI : (E \ {e}) ∩ downset C e = downset C e \ {e} := by
      ext y
      constructor
      · rintro ⟨⟨_, hyne⟩, hyd⟩
        exact ⟨hyd, hyne⟩
      · rintro ⟨hyd, hyne⟩
        exact ⟨⟨h_dsubE hyd, hyne⟩, hyd⟩
    have hsetE : (E \ {e}) ∪ downset C e = E := by
      ext y
      constructor
      · rintro (hy | hy)
        · exact hy.1
        · exact h_dsubE hy
      · intro hy
        by_cases hye : y = e
        · subst hye
          exact Or.inr self_mem_downset
        · exact Or.inl ⟨hy, hye⟩
    have hB' : IsCanonicalState C ((E \ {e}) ∩ downset C e) B := by
      rw [hsetI]
      exact hB
    have h_merge_can : IsCanonicalState C ((E \ {e}) ∪ downset C e)
        (D.mergeL B t (D.update B e)) := by
      refine IH lE.length hlt _ _ B t (D.update B e) lE ?_ rfl
        (fun a ha => h_inE a ha.1)
        (fun a ha => h_inE a (h_dsubE ha))
        (closure_diff_of_max h_subE h_clE h_max)
        downset_closed hB' ht hT
      rw [hsetE]
      exact hpE
    have h_merge_can' : IsCanonicalState C E
        (D.mergeL B t (D.update B e)) := by
      rw [← hsetE]
      exact h_merge_can
    exact isCanonicalState_unique_u hU h_inE hs h_merge_can'

/-! ### 3. The feasible master induction -/

/-- **The ternary Join Lemma from the slim core + the feasible delta contract
+ (CD3).** The `join_lemma3_of_cd` induction, with the two redistribution
rewrites and the empty-side unit law replaced by their feasible-tuple forms;
the hypotheses each feasible law demands are exactly those in scope at its
call site (the honest-LCA discipline of T8.4, now definitional). -/
theorem join_lemma3_of_cd_feasible (hVC : CoreVCs3CD D)
    (hFΔ : FeasibleDeltaVCs3 D) (hCD : CDVC3 D) : JoinLemma3 D := by
  intro C ev₁ ev₂ s₀ s₁ s₂ h_tr h_ir h_in₁ h_in₂ h_cl₁ h_cl₂ hc₀ hc₁ hc₂
  classical
  have hU := hVC.update_core
  obtain ⟨l₁, hp₁, -, -⟩ := id hc₁
  obtain ⟨l₂, hp₂, -, -⟩ := id hc₂
  have hpU₀ := listPermOf_union (D := D.toCRDTSig) hp₁ hp₂
  suffices gen : ∀ n, JoinAtF (D := D) C n by
    exact gen _ ev₁ ev₂ s₀ s₁ s₂ _ hpU₀ rfl h_in₁ h_in₂ h_cl₁ h_cl₂
      hc₀ hc₁ hc₂
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro ev₁ ev₂ s₀ s₁ s₂ lU hpU hlen h_in₁ h_in₂ h_cl₁ h_cl₂ hc₀ hc₁ hc₂
    -- Empty sides collapse via the feasible unit law.
    rcases Set.eq_empty_or_nonempty ev₁ with h_e₁ | h_ne₁
    · have hs₁ : s₁ = D.init := isCanonicalState_empty h_e₁ hc₁
      have h_int : ev₁ ∩ ev₂ = ∅ := by rw [h_e₁, Set.empty_inter]
      have hs₀ : s₀ = D.init := isCanonicalState_empty h_int hc₀
      have hinit := hFΔ.feasible_init C ev₂ s₂ h_in₂ hc₂
      subst h_e₁
      rw [hs₀, hs₁, hinit, Set.empty_union]
      exact hc₂
    rcases Set.eq_empty_or_nonempty ev₂ with h_e₂ | h_ne₂
    · have hs₂ : s₂ = D.init := isCanonicalState_empty h_e₂ hc₂
      have h_int : ev₁ ∩ ev₂ = ∅ := by rw [h_e₂, Set.inter_empty]
      have hs₀ : s₀ = D.init := isCanonicalState_empty h_int hc₀
      have hinit := hFΔ.feasible_init C ev₁ s₁ h_in₁ hc₁
      subst h_e₂
      rw [hs₀, hs₂, hVC.mergeL_comm, hinit, Set.union_empty]
      exact hc₁
    -- Select a loOn(∪)-maximal event; build A = σ(U∖e), B = σ(↓e∖e).
    have h_inU : ∀ a ∈ ev₁ ∪ ev₂, a ∈ C.events := by
      rintro a (h | h)
      · exact h_in₁ a h
      · exact h_in₂ a h
    have h_clU : ∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b →
        b ∈ ev₁ ∪ ev₂ → a ∈ ev₁ ∪ ev₂ := by
      rintro a b hv hnc (h | h)
      · exact Or.inl (h_cl₁ a b hv hnc h)
      · exact Or.inr (h_cl₂ a b hv hnc h)
    obtain ⟨x₁, hx₁⟩ := h_ne₁
    obtain ⟨e, he_U, h_max⟩ :=
      exists_loOn_maximal_u hU h_tr h_ir hpU h_inU ⟨x₁, Or.inl hx₁⟩
    have h_e_lU : e ∈ lU := (hpU.2 e).mpr he_U
    have hpU' : listPermOf (lU.filter (· ≠ e)) ((ev₁ ∪ ev₂) \ {e}) :=
      filter_ne_listPermOf hpU h_e_lU
    have hlen' : (lU.filter (· ≠ e)).length = n - 1 := by
      rw [listPermOf_diff_length hpU h_e_lU hpU', hlen]
    have h_pos : 0 < n := by
      rw [← hlen]
      exact List.length_pos_of_mem h_e_lU
    obtain ⟨A, hA⟩ : ∃ A, IsCanonicalState C ((ev₁ ∪ ev₂) \ {e}) A :=
      isCanonicalState_exists_u hU h_tr h_ir hpU'
        (fun a ha => h_inU a ha.1)
    have h_dsub : downset C e ⊆ ev₁ ∪ ev₂ := downset_subset h_clU he_U
    obtain ⟨lB, hpB⟩ :=
      exists_listPermOf_subsetF hpU
        (fun x (hx : x ∈ downset C e \ {e}) => h_dsub hx.1)
    obtain ⟨B, hB⟩ : ∃ B, IsCanonicalState C (downset C e \ {e}) B :=
      isCanonicalState_exists_u hU h_tr h_ir hpB
        (fun a ha => h_inU a (h_dsub ha.1))
    have h_cd : D.mergeL B A (D.update B e) = D.update A e :=
      hCD C (ev₁ ∪ ev₂) A B e h_tr h_ir h_inU h_clU he_U h_max hA hB
    have h_target : IsCanonicalState C (ev₁ ∪ ev₂) (D.update A e) :=
      isCanonicalState_snoc he_U h_max hA
    by_cases he₁ : e ∈ ev₁
    · obtain ⟨t₁, ht₁⟩ : ∃ t, IsCanonicalState C (ev₁ \ {e}) t := by
        obtain ⟨l₁', hp₁', -, -⟩ := id hc₁
        have h_e_l₁ : e ∈ l₁' := (hp₁'.2 e).mpr he₁
        exact isCanonicalState_exists_u hU h_tr h_ir
          (filter_ne_listPermOf hp₁' h_e_l₁) (fun a ha => h_in₁ a ha.1)
      have hs₁d : s₁ = D.mergeL B t₁ (D.update B e) :=
        side_decompositionF hVC hCD h_tr h_ir IH hpU hlen h_inU h_clU
          he_U h_max hA hB Set.subset_union_left h_in₁ h_cl₁ he₁ hc₁ ht₁
      by_cases he₂ : e ∈ ev₂
      · -- e shared: feasible redistribution.
        obtain ⟨t₂, ht₂⟩ : ∃ t, IsCanonicalState C (ev₂ \ {e}) t := by
          obtain ⟨l₂', hp₂', -, -⟩ := id hc₂
          have h_e_l₂ : e ∈ l₂' := (hp₂'.2 e).mpr he₂
          exact isCanonicalState_exists_u hU h_tr h_ir
            (filter_ne_listPermOf hp₂' h_e_l₂) (fun a ha => h_in₂ a ha.1)
        have hs₂d : s₂ = D.mergeL B t₂ (D.update B e) :=
          side_decompositionF hVC hCD h_tr h_ir IH hpU hlen h_inU h_clU
            he_U h_max hA hB Set.subset_union_right h_in₂ h_cl₂ he₂
            hc₂ ht₂
        have he₀ : e ∈ ev₁ ∩ ev₂ := ⟨he₁, he₂⟩
        have h_in₀ : ∀ a ∈ ev₁ ∩ ev₂, a ∈ C.events :=
          fun a ha => h_in₁ a ha.1
        have h_cl₀ : ∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b →
            b ∈ ev₁ ∩ ev₂ → a ∈ ev₁ ∩ ev₂ :=
          fun a b hv hnc hb =>
            ⟨h_cl₁ a b hv hnc hb.1, h_cl₂ a b hv hnc hb.2⟩
        obtain ⟨l₀', hp₀'⟩ :=
          exists_listPermOf_subsetF hpU
            (show (ev₁ ∩ ev₂) \ {e} ⊆ ev₁ ∪ ev₂ from
              fun x hx => Or.inl hx.1.1)
        obtain ⟨t₀, ht₀⟩ :
            ∃ t, IsCanonicalState C ((ev₁ ∩ ev₂) \ {e}) t :=
          isCanonicalState_exists_u hU h_tr h_ir hp₀'
            (fun a ha => h_in₁ a ha.1.1)
        have hs₀d : s₀ = D.mergeL B t₀ (D.update B e) :=
          side_decompositionF hVC hCD h_tr h_ir IH hpU hlen h_inU h_clU
            he_U h_max hA hB
            (show ev₁ ∩ ev₂ ⊆ ev₁ ∪ ev₂ from fun x hx => Or.inl hx.1)
            h_in₀ h_cl₀ he₀ hc₀ ht₀
        have hct₀' : IsCanonicalState C ((ev₁ \ {e}) ∩ (ev₂ \ {e})) t₀ := by
          rw [diff_inter_diff]
          exact ht₀
        have hsetm : (ev₁ \ {e}) ∪ (ev₂ \ {e}) = (ev₁ ∪ ev₂) \ {e} := by
          ext x
          simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
          tauto
        have h_mid_can : IsCanonicalState C ((ev₁ \ {e}) ∪ (ev₂ \ {e}))
            (D.mergeL t₀ t₁ t₂) := by
          refine IH (n - 1) (by omega) _ _ t₀ t₁ t₂
            (lU.filter (· ≠ e)) ?_ hlen'
            (fun a ha => h_in₁ a ha.1) (fun a ha => h_in₂ a ha.1)
            (closure_diff_of_max Set.subset_union_left h_cl₁ h_max)
            (closure_diff_of_max Set.subset_union_right h_cl₂ h_max)
            hct₀' ht₁ ht₂
          rw [hsetm]
          exact hpU'
        have h_mid_can' : IsCanonicalState C ((ev₁ ∪ ev₂) \ {e})
            (D.mergeL t₀ t₁ t₂) := by
          rw [← hsetm]
          exact h_mid_can
        have h_mid : D.mergeL t₀ t₁ t₂ = A :=
          isCanonicalState_unique_u hU (fun a ha => h_inU a ha.1)
            h_mid_can' hA
        have h_redis := hFΔ.feasible_redistribute C ev₁ ev₂ t₀ t₁ t₂ B e
          h_tr h_ir h_in₁ h_in₂ h_cl₁ h_cl₂ he₁ he₂ h_max
          ht₀ hB ht₁ ht₂
        rw [hs₀d, hs₁d, hs₂d, h_redis, h_mid, h_cd]
        exact h_target
      · -- e local to side 1: feasible local redistribution.
        have hct₀' : IsCanonicalState C ((ev₁ \ {e}) ∩ ev₂) s₀ := by
          rw [inter_diff_left_of_not_mem he₂]
          exact hc₀
        have hset₁ : (ev₁ \ {e}) ∪ ev₂ = (ev₁ ∪ ev₂) \ {e} := by
          ext x
          simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
          constructor
          · rintro (⟨h, hne⟩ | h)
            · exact ⟨Or.inl h, hne⟩
            · exact ⟨Or.inr h, fun heq => he₂ (heq ▸ h)⟩
          · rintro ⟨h | h, hne⟩
            · exact Or.inl ⟨h, hne⟩
            · exact Or.inr h
        have h_mid_can : IsCanonicalState C ((ev₁ \ {e}) ∪ ev₂)
            (D.mergeL s₀ t₁ s₂) := by
          refine IH (n - 1) (by omega) _ _ s₀ t₁ s₂
            (lU.filter (· ≠ e)) ?_ hlen'
            (fun a ha => h_in₁ a ha.1) h_in₂
            (closure_diff_of_max Set.subset_union_left h_cl₁ h_max)
            h_cl₂ hct₀' ht₁ hc₂
          rw [hset₁]
          exact hpU'
        have h_mid_can' : IsCanonicalState C ((ev₁ ∪ ev₂) \ {e})
            (D.mergeL s₀ t₁ s₂) := by
          rw [← hset₁]
          exact h_mid_can
        have h_mid : D.mergeL s₀ t₁ s₂ = A :=
          isCanonicalState_unique_u hU (fun a ha => h_inU a ha.1)
            h_mid_can' hA
        have h_lr := hFΔ.feasible_local_redistribute C ev₁ ev₂ s₀ B t₁ s₂ e
          h_tr h_ir h_in₁ h_in₂ h_cl₁ h_cl₂ he₁ he₂ h_max
          hc₀ hB ht₁ hc₂
        rw [hs₁d, h_lr, h_mid, h_cd]
        exact h_target
    · -- e local to side 2: mirror via mergeL_comm.
      have he₂ : e ∈ ev₂ := by
        rcases he_U with h | h
        · exact absurd h he₁
        · exact h
      obtain ⟨t₂, ht₂⟩ : ∃ t, IsCanonicalState C (ev₂ \ {e}) t := by
        obtain ⟨l₂', hp₂', -, -⟩ := id hc₂
        have h_e_l₂ : e ∈ l₂' := (hp₂'.2 e).mpr he₂
        exact isCanonicalState_exists_u hU h_tr h_ir
          (filter_ne_listPermOf hp₂' h_e_l₂) (fun a ha => h_in₂ a ha.1)
      have hs₂d : s₂ = D.mergeL B t₂ (D.update B e) :=
        side_decompositionF hVC hCD h_tr h_ir IH hpU hlen h_inU h_clU
          he_U h_max hA hB Set.subset_union_right h_in₂ h_cl₂ he₂ hc₂ ht₂
      have hct₀' : IsCanonicalState C (ev₁ ∩ (ev₂ \ {e})) s₀ := by
        rw [inter_diff_right_of_not_mem he₁]
        exact hc₀
      have hset₂ : ev₁ ∪ (ev₂ \ {e}) = (ev₁ ∪ ev₂) \ {e} := by
        ext x
        simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
        constructor
        · rintro (h | ⟨h, hne⟩)
          · exact ⟨Or.inl h, fun heq => he₁ (heq ▸ h)⟩
          · exact ⟨Or.inr h, hne⟩
        · rintro ⟨h | h, hne⟩
          · exact Or.inl h
          · exact Or.inr ⟨h, hne⟩
      have h_mid_can : IsCanonicalState C (ev₁ ∪ (ev₂ \ {e}))
          (D.mergeL s₀ s₁ t₂) := by
        refine IH (n - 1) (by omega) _ _ s₀ s₁ t₂
          (lU.filter (· ≠ e)) ?_ hlen'
          h_in₁ (fun a ha => h_in₂ a ha.1) h_cl₁
          (closure_diff_of_max Set.subset_union_right h_cl₂ h_max)
          hct₀' hc₁ ht₂
        rw [hset₂]
        exact hpU'
      have h_mid_can' : IsCanonicalState C ((ev₁ ∪ ev₂) \ {e})
          (D.mergeL s₀ s₁ t₂) := by
        rw [← hset₂]
        exact h_mid_can
      have h_mid : D.mergeL s₀ s₁ t₂ = A :=
        isCanonicalState_unique_u hU (fun a ha => h_inU a ha.1)
          h_mid_can' hA
      -- The mirrored feasible law instance (sides swapped).
      have h_max' : ∀ x ∈ ev₂ ∪ ev₁, x ≠ e →
          ¬ loOn C (ev₂ ∪ ev₁) e x := by
        rw [Set.union_comm]
        exact h_max
      have hc₀_swap : IsCanonicalState C (ev₂ ∩ ev₁) s₀ := by
        rw [Set.inter_comm]
        exact hc₀
      have h_lr := hFΔ.feasible_local_redistribute C ev₂ ev₁ s₀ B t₂ s₁ e
        h_tr h_ir h_in₂ h_in₁ h_cl₂ h_cl₁ he₂ he₁ h_max'
        hc₀_swap hB ht₂ hc₁
      rw [hs₂d, hVC.mergeL_comm s₀ s₁, h_lr,
        hVC.mergeL_comm s₀ t₂ s₁, h_mid, h_cd]
      exact h_target

/-- **T8 as a corollary**: the unconditional route factors through the
feasible one. -/
theorem join_lemma3_of_cd' (hVC : CoreVCs3 D) (hΔ : DeltaVCs3 D)
    (hCD : CDVC3 D) : JoinLemma3 D :=
  join_lemma3_of_cd_feasible hVC.toCD (feasibleDeltaVCs3_of_delta hVC hΔ) hCD

end

section Bridge
variable {D : ConditionedMRDTSig}

/-- Merge preservation from a full-closure join lemma (the `GoodConfig3`
merge case verbatim, passing `ver_causal` un-weakened). -/
theorem goodConfig3_mergeF (hJoin : JoinLemma3F D)
    {C C' : Configuration D} {r₁ : Replica}
    {v₁ v₂ vT vm : Version} {s₁ s₂ sT : D.State}
    {ev₁ ev₂ evT : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (h_lca : IsLCA C.parents v₁ v₂ vT)
    (h_verT : C.ver vT = some (sT, evT))
    (hL : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some (D.mergeL sT s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (h : GoodConfig3 C) : GoodConfig3 C' := by
  have hco := C.head_coherent r₁ v₁ h_head₁
  have hLr₁ : C.L r₁ = some ev₁ := by
    rw [← hco.2, h_ver₁]; rfl
  have hevT_eq : evT = ev₁ ∩ ev₂ :=
    C.lca_events h_lca h_ver₁ h_ver₂ h_verT
  have hver_new : C'.ver vm = some (D.mergeL sT s₁ s₂, ev₁ ∪ ev₂) := by
    rw [hver]; simp
  have hver_old : ∀ w, w ≠ vm → C'.ver w = C.ver w := by
    intro w hw; rw [hver]; simp [hw]
  have h_same : ∀ (E' : Set (Op D.AppOp)) (s' : D.State),
      IsCanonicalState (Configuration.core C) E' s' →
      IsCanonicalState (Configuration.core C') E' s' := by
    intro E' s' hcs
    refine isCanonicalState_congr (fun a _ b _ => ?_) hcs
    rw [core_vis, core_vis, hvis]
  have hL'r₁ : C'.L r₁ = some (ev₁ ∪ ev₂) := by
    rw [hL]
    simp [updateRep]
  have h_events : ∀ x, x ∈ C.events → x ∈ C'.events := by
    rintro x ⟨r'', s'', hLr'', hx⟩
    by_cases hr'' : r'' = r₁
    · subst hr''
      rw [hLr₁, Option.some.injEq] at hLr''
      exact ⟨r'', ev₁ ∪ ev₂, hL'r₁, Or.inl (hLr'' ▸ hx)⟩
    · refine ⟨r'', s'', ?_, hx⟩
      rw [hL]
      simp only [updateRep, if_neg hr'']
      exact hLr''
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w s' E' hw
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.1, ← hw.2]
      have hcT : IsCanonicalState (Configuration.core C) (ev₁ ∩ ev₂) sT := by
        rw [← hevT_eq]
        exact h.canonical vT sT evT h_verT
      have h_join := hJoin (Configuration.core C) ev₁ ev₂ sT s₁ s₂
        (fun hab hbc => h.vis_trans hab hbc)
        (fun a ha => h.vis_irrefl a ha)
        (h.ver_events_sub v₁ s₁ ev₁ h_ver₁)
        (h.ver_events_sub v₂ s₂ ev₂ h_ver₂)
        (fun a b hab hb => h.ver_causal v₁ s₁ ev₁ h_ver₁ a b hab hb)
        (fun a b hab hb => h.ver_causal v₂ s₂ ev₂ h_ver₂ a b hab hb)
        hcT
        (h.canonical v₁ s₁ ev₁ h_ver₁)
        (h.canonical v₂ s₂ ev₂ h_ver₂)
      exact h_same _ _ h_join
    · rw [hver_old w hwn] at hw
      exact h_same E' s' (h.canonical w s' E' hw)
  · intro a b c hab hbc
    rw [hvis] at hab hbc ⊢
    exact h.vis_trans hab hbc
  · intro a ha
    rw [hvis] at ha
    exact h.vis_irrefl a ha
  · intro w s' E' hw a ha
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at ha
      exact ⟨r₁, ev₁ ∪ ev₂, hL'r₁, ha⟩
    · rw [hver_old w hwn] at hw
      exact h_events a (h.ver_events_sub w s' E' hw a ha)
  · intro w s' E' hw a b hab hb
    rw [hvis] at hab
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at hb ⊢
      rcases hb with hb | hb
      · exact Or.inl (h.ver_causal v₁ s₁ ev₁ h_ver₁ a b hab hb)
      · exact Or.inr (h.ver_causal v₂ s₂ ev₂ h_ver₂ a b hab hb)
    · rw [hver_old w hwn] at hw
      exact h.ver_causal w s' E' hw a b hab hb

open LabeledTS in
/-- The end-to-end bridge from a full-closure join lemma. -/
theorem ra_linearizable3_of_joinF (hJoin : JoinLemma3F D)
    {hInit : D.Inv D.init}
    (C : Configuration D)
    (hReach : (labeledTS3 D).ReachableFrom (initConfig D hInit) C) :
    IsRALinearizable3 C := by
  suffices h : GoodConfig3 C from isRALinearizable3_of_good h
  induction hReach with
  | refl => exact goodConfig3_init hInit
  | tail _ hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    cases hstep with
    | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
      exact goodConfig3_createReplica h_fresh hL hvis hver ih
    | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
        hN hL hvis hver hhead hparents =>
      exact goodConfig3_apply h_head h_ver h_fresh_t h_vnew hL hvis hver ih
    | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁
        h_rank₂ C' hN hL hvis hver hhead hparents =>
      exact goodConfig3_mergeF hJoin h_head₁ h_ver₁ h_ver₂ h_lca h_verT
        hL hvis hver ih
    | query h_s h_val => exact ih

end Bridge

/-! ## Virtual LCAs (task #90): fold canonicity and the widened adequacy

The virtual construction re-supplies, from the ternary join lemma alone, the two facts
the adequacy induction consumed about the LCA slot: its event set is the intersection
(`mca_events_cover`, `LCA_Lemma.lean`) and its state is canonical for that set
(`virtualLCAState_canonical`, the fold induction below — note §5, "Claim (virtual
join)"). `goodConfig3_mergeVirtual_at` then mirrors `goodConfig3_merge_at`, and the
reachability bridges re-thread over the widened LTS `labeledTS3V`. The per-datatype VC
surface for `JoinLemma3` datatypes does not move — that is the headline. -/

section VirtualLCA
variable {D : ConditionedMRDTSig}

/-- The union of the registered event sets over a finite support. -/
def unionEvents (C : Configuration D) (S : Finset Version) : Set (Op D.AppOp) :=
  {e | ∃ u ∈ S, ∃ su Eu, C.ver u = some (su, Eu) ∧ e ∈ Eu}

theorem unionEvents_empty (C : Configuration D) :
    unionEvents C ∅ = (∅ : Set (Op D.AppOp)) := by
  ext e
  constructor
  · rintro ⟨u, hu, -⟩
    exact absurd hu (Finset.notMem_empty u)
  · intro h
    exact absurd h (Set.notMem_empty e)

theorem unionEvents_singleton {C : Configuration D} {v : Version} {s : D.State}
    {E : Set (Op D.AppOp)} (hv : C.ver v = some (s, E)) :
    unionEvents C {v} = E := by
  ext e
  constructor
  · rintro ⟨u, hu, su, Eu, hu', he⟩
    rw [Finset.mem_singleton] at hu
    subst hu
    rw [hv, Option.some.injEq, Prod.mk.injEq] at hu'
    rw [hu'.2]
    exact he
  · intro he
    exact ⟨v, Finset.mem_singleton_self v, s, E, hv, he⟩

theorem unionEvents_union (C : Configuration D) (X Y : Finset Version) :
    unionEvents C (X ∪ Y) = unionEvents C X ∪ unionEvents C Y := by
  ext e
  constructor
  · rintro ⟨u, hu, su, Eu, hu', he⟩
    rcases Finset.mem_union.mp hu with hu | hu
    · exact Or.inl ⟨u, hu, su, Eu, hu', he⟩
    · exact Or.inr ⟨u, hu, su, Eu, hu', he⟩
  · rintro (⟨u, hu, su, Eu, hu', he⟩ | ⟨u, hu, su, Eu, hu', he⟩)
    · exact ⟨u, Finset.mem_union_left _ hu, su, Eu, hu', he⟩
    · exact ⟨u, Finset.mem_union_right _ hu, su, Eu, hu', he⟩

/-- **Proposition 1 at the `Finset` level**: the MCA antichain's event-set union is
exactly the support-union ∩ `E(w)` (from `mca_events_cover` + the `mcaFinset`
characterization). -/
theorem mcaFinset_unionEvents {C : Configuration D}
    (hSI : StoreInv C.ver C.parents) {S : Finset Version} {w : Version}
    (hS : ∀ u ∈ S, (C.ver u).isSome)
    {sw : D.State} {Ew : Set (Op D.AppOp)} (hw : C.ver w = some (sw, Ew)) :
    unionEvents C (mcaFinset C.parents S w) = unionEvents C S ∩ Ew := by
  ext e
  have hcov := mca_events_cover hSI C.parents_lt (S := (↑S : Set Version))
    (fun u hu => hS u (Finset.mem_coe.mp hu)) hw e
  constructor
  · rintro ⟨m, hm, sm, Em, hm', he⟩
    obtain ⟨⟨u, huS, su, Eu, hu, heEu⟩, heEw⟩ :=
      hcov.mp ⟨m, mcaFinset_isMCA C.parents hm, sm, Em, hm', he⟩
    exact ⟨⟨u, Finset.mem_coe.mp huS, su, Eu, hu, heEu⟩, heEw⟩
  · rintro ⟨⟨u, huS, su, Eu, hu, heEu⟩, heEw⟩
    obtain ⟨m, hmMCA, sm, Em, hm', he⟩ :=
      hcov.mpr ⟨⟨u, Finset.mem_coe.mpr huS, su, Eu, hu, heEu⟩, heEw⟩
    exact ⟨m, (mem_mcaFinset C.parents C.parents_lt).mpr hmMCA, sm, Em, hm', he⟩

/-- The abstract per-configuration join hook the fold consumes: **full-closure**
premises (what `GoodConfig3.ver_causal` supplies at every intermediate antichain
union), canonical triple in, canonical union out. Both `JoinLemma3At` (weak closure —
implied by full) and `JoinLemma3F` instantiate it, so one fold induction serves both
routes. -/
private def VJoinHook (C : Configuration D) : Prop :=
  ∀ (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ s₁ s₂ : D.State),
    (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
    (∀ a b, C.vis a b → b ∈ ev₁ → a ∈ ev₁) →
    (∀ a b, C.vis a b → b ∈ ev₂ → a ∈ ev₂) →
    IsCanonicalState (Configuration.core C) (ev₁ ∩ ev₂) s₀ →
    IsCanonicalState (Configuration.core C) ev₁ s₁ →
    IsCanonicalState (Configuration.core C) ev₂ s₂ →
    IsCanonicalState (Configuration.core C) (ev₁ ∪ ev₂) (D.mergeL s₀ s₁ s₂)

private theorem vJoinHook_of_joinAt {C : Configuration D} (hG : GoodConfig3 C)
    (hJ : JoinLemma3At D (Configuration.core C)) : VJoinHook C :=
  fun ev₁ ev₂ s₀ s₁ s₂ h1 h2 hcl1 hcl2 h₀ hs₁ hs₂ =>
    hJ ev₁ ev₂ s₀ s₁ s₂ (fun hab hbc => hG.vis_trans hab hbc)
      (fun a ha => hG.vis_irrefl a ha) h1 h2
      (fun a b hab _ hb => hcl1 a b hab hb)
      (fun a b hab _ hb => hcl2 a b hab hb) h₀ hs₁ hs₂

private theorem vJoinHook_of_joinF {C : Configuration D} (hG : GoodConfig3 C)
    (hJ : JoinLemma3F D) : VJoinHook C :=
  fun ev₁ ev₂ s₀ s₁ s₂ h1 h2 hcl1 hcl2 h₀ hs₁ hs₂ =>
    hJ (Configuration.core C) ev₁ ev₂ s₀ s₁ s₂
      (fun hab hbc => hG.vis_trans hab hbc)
      (fun a ha => hG.vis_irrefl a ha) h1 h2 hcl1 hcl2 h₀ hs₁ hs₂

/-- The canonicity claim at a fixed joint-support measure (the strong-induction
package, mirroring `JoinAt3`). -/
private def VCanonAt (C : Configuration D) (n : ℕ) : Prop :=
  ∀ (S : Finset Version) (w : Version) (sw : D.State) (Ew : Set (Op D.AppOp)),
    (supportOf C.parents (S ∪ {w})).card = n →
    (∀ u ∈ S, (C.ver u).isSome) →
    C.ver w = some (sw, Ew) →
    IsCanonicalState (Configuration.core C)
      (unionEvents C S ∩ Ew) (vlcaAux C.ver C.parents C.parents_lt S w)

/-- **The fold induction, inner layer** (note §5): along the ascending-rank fold every
scratch node's state is canonical for its union event set. The inner LCA slot of each
sub-pair is canonical by the outer induction (`IH`) plus covering; the hook joins. -/
private theorem vfold_canonical {C : Configuration D}
    (hSI : StoreInv C.ver C.parents) (hG : GoodConfig3 C) (hHook : VJoinHook C)
    {n : ℕ} (IH : ∀ k, k < n → VCanonAt C k)
    {S₀ : Finset Version} {w₀ : Version} (hw₀ : (C.ver w₀).isSome)
    (hstrict : (supportOf C.parents (mcaFinset C.parents S₀ w₀)).card < n)
    (pending : List Version) :
    ∀ (accS : Finset Version) (acc : D.State),
      (∀ x ∈ accS, x ∈ mcaFinset C.parents S₀ w₀) →
      (∀ x ∈ pending, x ∈ mcaFinset C.parents S₀ w₀) →
      IsCanonicalState (Configuration.core C) (unionEvents C accS) acc →
      IsCanonicalState (Configuration.core C)
        (unionEvents C (accS ∪ pending.toFinset))
        (vfoldAux C.ver C.parents C.parents_lt accS acc pending) := by
  -- every antichain member is allocated (it reaches the allocated `w₀`)
  have halloc : ∀ x ∈ mcaFinset C.parents S₀ w₀, (C.ver x).isSome := fun x hx =>
    reaches_alloc hSI (mcaFinset_isMCA C.parents hx).1.2 hw₀
  induction pending with
  | nil =>
    intro accS acc _ _ hacc
    rw [vfoldAux_nil]
    simpa using hacc
  | cons m ms ih =>
    intro accS acc haccS hpend hacc
    rw [vfoldAux_cons]
    have hmM : m ∈ mcaFinset C.parents S₀ w₀ := hpend m List.mem_cons_self
    obtain ⟨⟨sm, Em⟩, hm⟩ := Option.isSome_iff_exists.mp (halloc m hmM)
    have hsd : stateD C.ver m = sm := by
      simp [stateD, hm]
    -- the sub-pair's virtual LCA is canonical for the honest intersection (outer IH)
    have hsub : accS ∪ {m} ⊆ mcaFinset C.parents S₀ w₀ := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact haccS x hx
      · rw [Finset.mem_singleton] at hx
        subst hx
        exact hmM
    have hcard : (supportOf C.parents (accS ∪ {m})).card < n :=
      Nat.lt_of_le_of_lt
        (Finset.card_le_card (supportOf_mono C.parents C.parents_lt hsub)) hstrict
    have hinner := IH _ hcard accS m sm Em rfl
      (fun u hu => halloc u (haccS u hu)) hm
    -- hook side conditions at (unionEvents accS, Em)
    have h1 : ∀ a ∈ unionEvents C accS, a ∈ C.events := by
      rintro a ⟨u, hu, su, Eu, hu', ha⟩
      exact hG.ver_events_sub u su Eu hu' a ha
    have hcl1 : ∀ a b, C.vis a b → b ∈ unionEvents C accS →
        a ∈ unionEvents C accS := by
      rintro a b hab ⟨u, hu, su, Eu, hu', hb⟩
      exact ⟨u, hu, su, Eu, hu', hG.ver_causal u su Eu hu' a b hab hb⟩
    have hjoin := hHook (unionEvents C accS) Em
      (vlcaAux C.ver C.parents C.parents_lt accS m) acc sm
      h1 (hG.ver_events_sub m sm Em hm) hcl1
      (fun a b hab hb => hG.ver_causal m sm Em hm a b hab hb)
      hinner hacc (hG.canonical m sm Em hm)
    -- fold the union back into the grown support and recurse
    have hset : unionEvents C accS ∪ Em = unionEvents C (accS ∪ {m}) := by
      rw [unionEvents_union, unionEvents_singleton hm]
    rw [hset] at hjoin
    have hstep := ih (accS ∪ {m})
      (D.mergeL (vlcaAux C.ver C.parents C.parents_lt accS m) acc sm)
      (fun x hx => hsub hx) (fun x hx => hpend x (List.mem_cons_of_mem m hx)) hjoin
    have hsets : ((accS ∪ {m}) ∪ ms.toFinset : Finset Version)
        = accS ∪ (m :: ms).toFinset := by
      rw [List.toFinset_cons, Finset.insert_eq, ← Finset.union_assoc]
    rw [hsets] at hstep
    rw [hsd]
    exact hstep

/-- The canonicity claim at every measure, by strong induction. -/
private theorem vlcaAux_canonical_at {C : Configuration D}
    (hSI : StoreInv C.ver C.parents) (hG : GoodConfig3 C) (hHook : VJoinHook C) :
    ∀ n, VCanonAt C n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro S w sw Ew hmeas hS hw
    rcases hsort : (mcaFinset C.parents S w).sort (· ≤ ·) with _ | ⟨m₁, ms₁⟩
    · -- empty antichain: covering forces an empty intersection; `σ₀` is canonical
      rw [vlcaAux_of_sort_nil C.ver C.parents C.parents_lt hsort]
      have hM : mcaFinset C.parents S w = ∅ := by
        rw [← Finset.sort_toFinset (mcaFinset C.parents S w) (· ≤ ·), hsort]
        rfl
      have hcov := mcaFinset_unionEvents hSI hS hw
      rw [hM, unionEvents_empty] at hcov
      rw [← hcov]
      exact ⟨[], ⟨List.nodup_nil, fun a => by simp⟩, List.Pairwise.nil, rfl⟩
    · have hm₁M : m₁ ∈ mcaFinset C.parents S w := by
        rw [← Finset.mem_sort (· ≤ ·), hsort]
        exact List.mem_cons_self
      have hm₁alloc : (C.ver m₁).isSome :=
        reaches_alloc hSI (mcaFinset_isMCA C.parents hm₁M).1.2 (by rw [hw]; rfl)
      obtain ⟨⟨sm₁, Em₁⟩, hm₁⟩ := Option.isSome_iff_exists.mp hm₁alloc
      have hsd₁ : stateD C.ver m₁ = sm₁ := by simp [stateD, hm₁]
      have hcov := mcaFinset_unionEvents hSI hS hw
      rw [vlcaAux_of_sort_cons C.ver C.parents C.parents_lt hsort]
      rcases ms₁ with _ | ⟨m₂, ms₂⟩
      · -- singleton antichain: the existing LCA rule
        rw [vfoldAux_nil, hsd₁]
        have hM : mcaFinset C.parents S w = {m₁} := by
          rw [← Finset.sort_toFinset (mcaFinset C.parents S w) (· ≤ ·), hsort]
          rfl
        rw [hM, unionEvents_singleton hm₁] at hcov
        rw [← hcov]
        exact hG.canonical m₁ sm₁ Em₁ hm₁
      · -- proper antichain: strict support drop, then the fold
        have hm₂M : m₂ ∈ mcaFinset C.parents S w := by
          rw [← Finset.mem_sort (· ≤ ·), hsort]
          exact List.mem_cons_of_mem _ List.mem_cons_self
        have hne : m₁ ≠ m₂ := by
          have hnd := Finset.sort_nodup (mcaFinset C.parents S w) (· ≤ ·)
          rw [hsort, List.nodup_cons] at hnd
          intro h
          exact hnd.1 (h ▸ List.mem_cons_self)
        have hstrict : (supportOf C.parents (mcaFinset C.parents S w)).card < n :=
          hmeas ▸ Finset.card_lt_card
            (supportOf_mca_ssubset C.parents C.parents_lt hm₁M hm₂M hne)
        have hfold := vfold_canonical hSI hG hHook IH (by rw [hw]; rfl) hstrict
          (m₂ :: ms₂) {m₁} (stateD C.ver m₁)
          (fun x hx => by rw [Finset.mem_singleton] at hx; subst hx; exact hm₁M)
          (fun x hx => by
            rw [← Finset.mem_sort (· ≤ ·), hsort]
            exact List.mem_cons_of_mem _ hx)
          (by rw [unionEvents_singleton hm₁, hsd₁]; exact hG.canonical m₁ sm₁ Em₁ hm₁)
        have hMset : ({m₁} ∪ (m₂ :: ms₂).toFinset : Finset Version)
            = mcaFinset C.parents S w := by
          rw [← Finset.sort_toFinset (mcaFinset C.parents S w) (· ≤ ·), hsort]
          ext x
          simp only [Finset.mem_union, Finset.mem_singleton, List.mem_toFinset,
            List.mem_cons]
        rw [hMset, hcov] at hfold
        exact hfold

/-- **Task #90, the fold canonicity (note §5, "Claim (virtual join)")**: at any
configuration satisfying the reachability invariant and the ternary join lemma, the
recursive antichain merge of a head pair is **canonical for the pair's event-set
intersection** — exactly what the adequacy induction demanded of a registered LCA. -/
theorem virtualLCAState_canonical {C : Configuration D}
    (hSI : StoreInv C.ver C.parents) (hG : GoodConfig3 C)
    (hJoin : JoinLemma3At D (Configuration.core C))
    {v₁ v₂ : Version} {s₁ s₂ : D.State} {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂)) :
    IsCanonicalState (Configuration.core C) (ev₁ ∩ ev₂)
      (virtualLCAState C v₁ v₂) := by
  have h := vlcaAux_canonical_at hSI hG (vJoinHook_of_joinAt hG hJoin) _
    {v₁} v₂ s₂ ev₂ rfl
    (fun u hu => by rw [Finset.mem_singleton] at hu; subst hu; rw [h_ver₁]; rfl)
    h_ver₂
  rw [unionEvents_singleton h_ver₁] at h
  exact h

/-- **Virtual merge preserves the invariant** — `goodConfig3_merge_at` with the
registered LCA slot replaced by the recursive antichain merge: `lca_events` is
re-supplied by `mca_events_cover` and the slot's canonicity by
`virtualLCAState_canonical`; the rest is verbatim. The extra `StoreInv` hypothesis is
what plain/honest reachability already carries (`storeInv_reachableV`). -/
theorem goodConfig3_mergeVirtual_at
    {C C' : Configuration D}
    (hJoin : JoinLemma3At D (Configuration.core C))
    (hSI : StoreInv C.ver C.parents)
    {r₁ : Replica} {v₁ v₂ vm : Version} {s₁ s₂ : D.State}
    {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (hL : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some (D.mergeL (virtualLCAState C v₁ v₂) s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (h : GoodConfig3 C) : GoodConfig3 C' := by
  have hco := C.head_coherent r₁ v₁ h_head₁
  have hLr₁ : C.L r₁ = some ev₁ := by
    rw [← hco.2, h_ver₁]; rfl
  have hver_new : C'.ver vm
      = some (D.mergeL (virtualLCAState C v₁ v₂) s₁ s₂, ev₁ ∪ ev₂) := by
    rw [hver]; simp
  have hver_old : ∀ w, w ≠ vm → C'.ver w = C.ver w := by
    intro w hw; rw [hver]; simp [hw]
  have h_same : ∀ (E' : Set (Op D.AppOp)) (s' : D.State),
      IsCanonicalState (Configuration.core C) E' s' →
      IsCanonicalState (Configuration.core C') E' s' := by
    intro E' s' hcs
    refine isCanonicalState_congr (fun a _ b _ => ?_) hcs
    rw [core_vis, core_vis, hvis]
  have hL'r₁ : C'.L r₁ = some (ev₁ ∪ ev₂) := by
    rw [hL]
    simp [updateRep]
  have h_events : ∀ x, x ∈ C.events → x ∈ C'.events := by
    rintro x ⟨r'', s'', hLr'', hx⟩
    by_cases hr'' : r'' = r₁
    · subst hr''
      rw [hLr₁, Option.some.injEq] at hLr''
      exact ⟨r'', ev₁ ∪ ev₂, hL'r₁, Or.inl (hLr'' ▸ hx)⟩
    · refine ⟨r'', s'', ?_, hx⟩
      rw [hL]
      simp only [updateRep, if_neg hr'']
      exact hLr''
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- canonical: the virtual LCA slot is canonical for the intersection
    intro w s' E' hw
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.1, ← hw.2]
      have hcT : IsCanonicalState (Configuration.core C) (ev₁ ∩ ev₂)
          (virtualLCAState C v₁ v₂) :=
        virtualLCAState_canonical hSI h hJoin h_ver₁ h_ver₂
      have h_join := hJoin ev₁ ev₂ (virtualLCAState C v₁ v₂) s₁ s₂
        (fun hab hbc => h.vis_trans hab hbc)
        (fun a ha => h.vis_irrefl a ha)
        (h.ver_events_sub v₁ s₁ ev₁ h_ver₁)
        (h.ver_events_sub v₂ s₂ ev₂ h_ver₂)
        (fun a b hab _ hb => h.ver_causal v₁ s₁ ev₁ h_ver₁ a b hab hb)
        (fun a b hab _ hb => h.ver_causal v₂ s₂ ev₂ h_ver₂ a b hab hb)
        hcT
        (h.canonical v₁ s₁ ev₁ h_ver₁)
        (h.canonical v₂ s₂ ev₂ h_ver₂)
      exact h_same _ _ h_join
    · rw [hver_old w hwn] at hw
      exact h_same E' s' (h.canonical w s' E' hw)
  · intro a b c hab hbc
    rw [hvis] at hab hbc ⊢
    exact h.vis_trans hab hbc
  · intro a ha
    rw [hvis] at ha
    exact h.vis_irrefl a ha
  · -- ver_events_sub
    intro w s' E' hw a ha
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at ha
      exact ⟨r₁, ev₁ ∪ ev₂, hL'r₁, ha⟩
    · rw [hver_old w hwn] at hw
      exact h_events a (h.ver_events_sub w s' E' hw a ha)
  · -- ver_causal
    intro w s' E' hw a b hab hb
    rw [hvis] at hab
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at hb ⊢
      rcases hb with hb | hb
      · exact Or.inl (h.ver_causal v₁ s₁ ev₁ h_ver₁ a b hab hb)
      · exact Or.inr (h.ver_causal v₂ s₂ ev₂ h_ver₂ a b hab hb)
    · rw [hver_old w hwn] at hw
      exact h.ver_causal w s' E' hw a b hab hb

/-- The `JoinLemma3`-driven wrapper (mirror of `goodConfig3_merge`). -/
theorem goodConfig3_mergeVirtual (hJoin : JoinLemma3 D)
    {C C' : Configuration D}
    (hSI : StoreInv C.ver C.parents)
    {r₁ : Replica} {v₁ v₂ vm : Version} {s₁ s₂ : D.State}
    {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (hL : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some (D.mergeL (virtualLCAState C v₁ v₂) s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (h : GoodConfig3 C) : GoodConfig3 C' :=
  goodConfig3_mergeVirtual_at (hJoin.at _) hSI h_head₁ h_ver₁ h_ver₂ hL hvis hver h

/-- The full-closure variant (the `JoinLemma3F` route owes nothing new either:
intermediate antichain unions and their meets are fully causally closed). -/
theorem virtualLCAState_canonicalF {C : Configuration D}
    (hSI : StoreInv C.ver C.parents) (hG : GoodConfig3 C)
    (hJoin : JoinLemma3F D)
    {v₁ v₂ : Version} {s₁ s₂ : D.State} {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂)) :
    IsCanonicalState (Configuration.core C) (ev₁ ∩ ev₂)
      (virtualLCAState C v₁ v₂) := by
  have h := vlcaAux_canonical_at hSI hG (vJoinHook_of_joinF hG hJoin) _
    {v₁} v₂ s₂ ev₂ rfl
    (fun u hu => by rw [Finset.mem_singleton] at hu; subst hu; rw [h_ver₁]; rfl)
    h_ver₂
  rw [unionEvents_singleton h_ver₁] at h
  exact h

/-- Virtual-merge preservation from the full-closure join (mirror of
`goodConfig3_mergeF`; consumed by the Enable-wins route). -/
theorem goodConfig3_mergeVirtualF (hJoin : JoinLemma3F D)
    {C C' : Configuration D}
    (hSI : StoreInv C.ver C.parents)
    {r₁ : Replica} {v₁ v₂ vm : Version} {s₁ s₂ : D.State}
    {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (hL : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hver : C'.ver = fun w => if w = vm
      then some (D.mergeL (virtualLCAState C v₁ v₂) s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
    (h : GoodConfig3 C) : GoodConfig3 C' := by
  have hco := C.head_coherent r₁ v₁ h_head₁
  have hLr₁ : C.L r₁ = some ev₁ := by
    rw [← hco.2, h_ver₁]; rfl
  have hver_new : C'.ver vm
      = some (D.mergeL (virtualLCAState C v₁ v₂) s₁ s₂, ev₁ ∪ ev₂) := by
    rw [hver]; simp
  have hver_old : ∀ w, w ≠ vm → C'.ver w = C.ver w := by
    intro w hw; rw [hver]; simp [hw]
  have h_same : ∀ (E' : Set (Op D.AppOp)) (s' : D.State),
      IsCanonicalState (Configuration.core C) E' s' →
      IsCanonicalState (Configuration.core C') E' s' := by
    intro E' s' hcs
    refine isCanonicalState_congr (fun a _ b _ => ?_) hcs
    rw [core_vis, core_vis, hvis]
  have hL'r₁ : C'.L r₁ = some (ev₁ ∪ ev₂) := by
    rw [hL]
    simp [updateRep]
  have h_events : ∀ x, x ∈ C.events → x ∈ C'.events := by
    rintro x ⟨r'', s'', hLr'', hx⟩
    by_cases hr'' : r'' = r₁
    · subst hr''
      rw [hLr₁, Option.some.injEq] at hLr''
      exact ⟨r'', ev₁ ∪ ev₂, hL'r₁, Or.inl (hLr'' ▸ hx)⟩
    · refine ⟨r'', s'', ?_, hx⟩
      rw [hL]
      simp only [updateRep, if_neg hr'']
      exact hLr''
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w s' E' hw
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.1, ← hw.2]
      have hcT : IsCanonicalState (Configuration.core C) (ev₁ ∩ ev₂)
          (virtualLCAState C v₁ v₂) :=
        virtualLCAState_canonicalF hSI h hJoin h_ver₁ h_ver₂
      have h_join := hJoin (Configuration.core C) ev₁ ev₂
        (virtualLCAState C v₁ v₂) s₁ s₂
        (fun hab hbc => h.vis_trans hab hbc)
        (fun a ha => h.vis_irrefl a ha)
        (h.ver_events_sub v₁ s₁ ev₁ h_ver₁)
        (h.ver_events_sub v₂ s₂ ev₂ h_ver₂)
        (fun a b hab hb => h.ver_causal v₁ s₁ ev₁ h_ver₁ a b hab hb)
        (fun a b hab hb => h.ver_causal v₂ s₂ ev₂ h_ver₂ a b hab hb)
        hcT
        (h.canonical v₁ s₁ ev₁ h_ver₁)
        (h.canonical v₂ s₂ ev₂ h_ver₂)
      exact h_same _ _ h_join
    · rw [hver_old w hwn] at hw
      exact h_same E' s' (h.canonical w s' E' hw)
  · intro a b c hab hbc
    rw [hvis] at hab hbc ⊢
    exact h.vis_trans hab hbc
  · intro a ha
    rw [hvis] at ha
    exact h.vis_irrefl a ha
  · intro w s' E' hw a ha
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at ha
      exact ⟨r₁, ev₁ ∪ ev₂, hL'r₁, ha⟩
    · rw [hver_old w hwn] at hw
      exact h_events a (h.ver_events_sub w s' E' hw a ha)
  · intro w s' E' hw a b hab hb
    rw [hvis] at hab
    by_cases hwn : w = vm
    · rw [hwn, hver_new, Option.some.injEq, Prod.mk.injEq] at hw
      rw [← hw.2] at hb ⊢
      rcases hb with hb | hb
      · exact Or.inl (h.ver_causal v₁ s₁ ev₁ h_ver₁ a b hab hb)
      · exact Or.inr (h.ver_causal v₂ s₂ ev₂ h_ver₂ a b hab hb)
    · rw [hver_old w hwn] at hw
      exact h.ver_causal w s' E' hw a b hab hb

open LabeledTS in
/-- **The widened `GoodConfig3` induction**: `StoreInv` is carried alongside (the
virtual case reads it); every gated case is the existing per-step lemma. -/
theorem goodConfig3_reachableV (hJoin : JoinLemma3 D)
    {hInit : D.Inv D.init} {C : Configuration D}
    (hReach : (labeledTS3V D).ReachableFrom (initConfig D hInit) C) :
    GoodConfig3 C := by
  have h : StoreInv C.ver C.parents ∧ GoodConfig3 C := by
    induction hReach with
    | refl => exact ⟨storeInv_init hInit, goodConfig3_init hInit⟩
    | tail _ hs ih =>
      obtain ⟨ℓ, hstep⟩ := hs
      refine ⟨storeInv_stepV hstep ih.1, ?_⟩
      cases hstep with
      | base hstep' =>
        cases hstep' with
        | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
          exact goodConfig3_createReplica h_fresh hL hvis hver ih.2
        | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
            hN hL hvis hver hhead hparents =>
          exact goodConfig3_apply h_head h_ver h_fresh_t h_vnew hL hvis hver ih.2
        | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁
            h_rank₂ C' hN hL hvis hver hhead hparents =>
          exact goodConfig3_merge hJoin h_head₁ h_ver₁ h_ver₂ h_lca h_verT
            hL hvis hver ih.2
        | query h_s h_val => exact ih.2
      | mergeVirtual h_head₁ h_head₂ h_ver₁ h_ver₂ h_vm h_rank₁ h_rank₂ C'
          hN hL hvis hver hhead hparents =>
        exact goodConfig3_mergeVirtual hJoin ih.1 h_head₁ h_ver₁ h_ver₂
          hL hvis hver ih.2
  exact h.2

open LabeledTS in
/-- **The widened bridge** (re-thread of `ra_linearizable3_of_join`): per-version
RA-linearizability at every configuration reachable in the LTS **with the
criss-cross gate lifted**, from the same `JoinLemma3` — no new per-datatype VC. -/
theorem ra_linearizable3V_of_join (hJoin : JoinLemma3 D)
    {hInit : D.Inv D.init}
    (C : Configuration D)
    (hReach : (labeledTS3V D).ReachableFrom (initConfig D hInit) C) :
    IsRALinearizable3 C :=
  isRALinearizable3_of_good (goodConfig3_reachableV hJoin hReach)

open LabeledTS in
/-- The widened route-B bridge (mirror of `ra_linearizable_of_core_delta_cd3`). -/
theorem ra_linearizable_of_core_delta_cd3V
    (hVC : CoreVCs3 D) (hΔ : DeltaVCs3 D) (hCD : CDVC3 D)
    {hInit : D.Inv D.init}
    (C : Configuration D)
    (hReach : (labeledTS3V D).ReachableFrom (initConfig D hInit) C) :
    IsRALinearizable3 C :=
  ra_linearizable3V_of_join (join_lemma3_of_cd hVC hΔ hCD) C hReach

open LabeledTS in
/-- The widened full-closure bridge (re-thread of `ra_linearizable3_of_joinF`). -/
theorem ra_linearizable3V_of_joinF (hJoin : JoinLemma3F D)
    {hInit : D.Inv D.init}
    (C : Configuration D)
    (hReach : (labeledTS3V D).ReachableFrom (initConfig D hInit) C) :
    IsRALinearizable3 C := by
  suffices h : StoreInv C.ver C.parents ∧ GoodConfig3 C from
    isRALinearizable3_of_good h.2
  induction hReach with
  | refl => exact ⟨storeInv_init hInit, goodConfig3_init hInit⟩
  | tail _ hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    refine ⟨storeInv_stepV hstep ih.1, ?_⟩
    cases hstep with
    | base hstep' =>
      cases hstep' with
      | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
        exact goodConfig3_createReplica h_fresh hL hvis hver ih.2
      | apply h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank C'
          hN hL hvis hver hhead hparents =>
        exact goodConfig3_apply h_head h_ver h_fresh_t h_vnew hL hvis hver ih.2
      | merge h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT h_vm h_rank₁
          h_rank₂ C' hN hL hvis hver hhead hparents =>
        exact goodConfig3_mergeF hJoin h_head₁ h_ver₁ h_ver₂ h_lca h_verT
          hL hvis hver ih.2
      | query h_s h_val => exact ih.2
    | mergeVirtual h_head₁ h_head₂ h_ver₁ h_ver₂ h_vm h_rank₁ h_rank₂ C'
        hN hL hvis hver hhead hparents =>
      exact goodConfig3_mergeVirtualF hJoin ih.1 h_head₁ h_ver₁ h_ver₂
        hL hvis hver ih.2

/-! ### Axiom audit (task #90 adequacy layer) -/

#print axioms virtualLCAState_canonical
#print axioms virtualLCAState_canonicalF
#print axioms goodConfig3_mergeVirtual_at
#print axioms ra_linearizable3V_of_join
#print axioms ra_linearizable3V_of_joinF

end VirtualLCA

end Sal.ConditionedMRDTs
