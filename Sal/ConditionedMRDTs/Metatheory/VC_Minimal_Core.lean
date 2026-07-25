import Sal.ConditionedMRDTs.Metatheory.Adequacy

/-!
# The minimal VC core (task #114, phase 2)

Mechanization of the VC-minimality sweep (`whiteboard/vc-minimality-note.md`).
The flat bundle `CoreVCs3CD + FeasibleDeltaVCs3 + CDVC3` (eight verification
conditions) is adequate for RA-linearizability
(`ra_linearizable_of_core_feasible_cd3`); this file mechanizes the *shrink*
direction: the shell conditions VC1..VC4 are consumed only in weakened forms,
and VC5 (`feasible_init`) splits into an independent nullary unit plus a
derivable nonempty half.

## The consumption-site inventory (audited against `Adequacy.lean` and
`Sigma_LoOn3.lean`)

The adequacy chain is
`ra_linearizable_of_core_feasible_cd3 = ra_linearizable3_of_join ∘
join_lemma3_of_cd_feasible`. The reachability induction
(`ra_linearizable3_of_join`, the `GoodConfig3` fold) consumes ONLY the Join
Lemma; every VC consumption happens inside `join_lemma3_of_cd_feasible` and
the σ-machinery it invokes. Per shell VC:

* **VC1** (`rc_non_comm_directional`, a biconditional): consumed at exactly
  ONE site, `Sigma_LoOn3.lean:474` inside `convergence_on_u`'s absorber
  construction, and only in the FORWARD direction (`.mp`: non-commuting
  concurrent pair must carry an rc edge), on events of the configuration and
  states folded from `σ₀`. The reverse direction (`.mpr`) is consumed only by
  `loOn_empty_of_all_comm_u` / `cdVC3_of_all_comm`, which are OFF the adequacy
  chain. Weakened form: `WeakUpdateVCs.rc_of_non_comm`.
* **VC2** (`no_rc_chain`): consumed only through `loOn_rc_no_succ_u`
  (`Sigma_LoOn3.lean:85`), whose sole client chain is
  `transGen_loOnNe_structure_u → loOnNe_acyclic_u → exists_loOn_maximal_u`;
  the adequacy content is exactly acyclicity of `loOnNe` on event sets of a
  configuration. Weakened form: `WeakUpdateVCs.loOn_acyclic`.
* **VC3** (`cond_comm_lift`): consumed at exactly ONE site,
  `Sigma_LoOn3.lean:81` (`applySeq_swap_via_cond_comm_lift_u`), reached only
  from `convergence_on_u` (via `applySeq_swap_loOn_incomparable_u` and
  `applySeq_bubble_to_front_loOn_u`); every invocation is at a state of the
  form `applySeq σ₀ pfx` with `pfx` and all three ops drawn from `C.events`:
  the state argument is always reachable. Weakened form:
  `WeakUpdateVCs.cond_comm_lift_reach` (`ReachState`-guarded).
* **VC4** (`mergeL_comm`): consumed at exactly THREE sites in
  `join_lemma3_of_cd_feasible` (`Adequacy.lean:1009,1203,1204`), each on a
  canonical tuple at its honest LCA:
  `(σ(ev₁∩∅), σ(ev₁), σ(∅))`, `(σ(ev₁∩ev₂), σ(ev₁), σ(ev₂))`, and
  `(σ((ev₂∖e)∩ev₁), σ(ev₂∖e), σ(ev₁))`. Weakened form:
  `WeakShellVCs.mergeL_comm_canonical`.
* **VC5** (`feasible_init`): consumed at exactly TWO sites
  (`Adequacy.lean:999,1007`), both with `vis`-transitivity, irreflexivity and
  weak closure of the event set in scope (the raw field demands none of
  them). Split: `FeasibleInitAtEmpty` (VC5°, the nullary unit, independent:
  see `Refutations/FeasibleInit_Not_Derivable_At_Empty.lean`) plus the
  derivable nonempty half (`feasible_init_nonempty_w` below, the note's VC5⁺
  induction).

## The theorems (delivered) and the re-close residue

Delivered (all kernel-clean):

* `WeakUpdateVCs`, `WeakShellVCs`: the weakened shell; `CoreVCs3CD.toWeakShell`
  shows it is genuinely a weakening (and is axiom-free).
* `feasibleDeltaVCs3_iff_split`, `FeasibleInitVC.atEmpty`, `FeasibleInitConsumed`:
  the VC5 split apparatus (VC5° = the empty-set instance).
* `feasible_init_nonempty_w` (**T3**): VC5 away from the empty set is derivable
  from `CoreVCs3CD` (VC1–VC4) + VC6 + VC8 on weakly closed event sets. Both
  `mergeL_comm` uses are on canonical tuples, so the *weakened* VC4 already
  suffices; the update layer is used at full strength through the σ-machinery.
* `feasibleInitConsumed_of_split` (**T4, the split at the sites**): the
  consumed form of `feasible_init` (matching `Adequacy.lean:999,1007`, where
  closure + `vis`-structure are in scope) is exactly `VC5°` plus the VC5⁺
  derivation. This is the mechanized content of the VC5 shrink.

**The re-close residue** (honest partial; not mechanized here). Gluing the
weakened bundle into `JoinLemma3` by *composition* with the existing
`join_lemma3_of_cd_feasible` is BLOCKED: that theorem consumes the raw
`FeasibleDeltaVCs3.feasible_init` field, which is stated WITHOUT the closure /
`vis` hypotheses that the VC5⁺ derivation requires, so it is strictly stronger
than `FeasibleInitConsumed` and is NOT reconstructible from the split. A
genuine re-close therefore needs (a) re-threading the `join_lemma3_of_cd_feasible`
induction to consume `FeasibleInitConsumed` at sites 999/1007 and
`mergeL_comm_canonical` at 1009/1203/1204 (all in-scope there); and (b)
re-hosting the σ-machinery (`convergence_on_u`, `loOnNe_acyclic_u`,
`isCanonicalState_unique_u`/`_exists_u`) on `WeakUpdateVCs` + `ReachState` in
place of the bundled `UpdateVCs`. Both are mechanical (~500 lines) with NO
mathematical obstruction — the consumption-site audit above shows every
consumption is at a reachable state / config-event set — but they are a
re-derivation, not a composition. Named as the phase-2 tail per the note's
"a full re-derivation of the metatheory ... is the phase-2 Lean obligation".
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## §1. The feasible delta laws, split into standalone conditions -/

section Split
variable (D : ConditionedMRDTSig)

/-- **VC5 as a standalone condition**: the `feasible_init` field of
`FeasibleDeltaVCs3`, verbatim. -/
def FeasibleInitVC : Prop :=
  ∀ (C : Sal.Emulation.Configuration D.toCRDTSig)
    (ev : Set (Op D.AppOp)) (s : D.State),
    (∀ a ∈ ev, a ∈ C.events) →
    IsCanonicalState C ev s →
    D.mergeL D.init D.init s = s

/-- **VC6 as a standalone condition**: the `feasible_local_redistribute`
field of `FeasibleDeltaVCs3`, verbatim. -/
def FeasibleLocalRedistributeVC : Prop :=
  ∀ (C : Sal.Emulation.Configuration D.toCRDTSig)
    (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ B t₁ s₂ : D.State) (e : Op D.AppOp),
    (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
    (∀ a : Op D.AppOp, ¬ C.vis a a) →
    (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
    e ∈ ev₁ → e ∉ ev₂ →
    (∀ x ∈ ev₁ ∪ ev₂, x ≠ e → ¬ loOn C (ev₁ ∪ ev₂) e x) →
    IsCanonicalState C (ev₁ ∩ ev₂) s₀ →
    IsCanonicalState C (downset C e \ {e}) B →
    IsCanonicalState C (ev₁ \ {e}) t₁ →
    IsCanonicalState C ev₂ s₂ →
    D.mergeL s₀ (D.mergeL B t₁ (D.update B e)) s₂
      = D.mergeL B (D.mergeL s₀ t₁ s₂) (D.update B e)

/-- **VC7 as a standalone condition**: the `feasible_redistribute` field of
`FeasibleDeltaVCs3`, verbatim. -/
def FeasibleRedistributeVC : Prop :=
  ∀ (C : Sal.Emulation.Configuration D.toCRDTSig)
    (ev₁ ev₂ : Set (Op D.AppOp)) (t₀ t₁ t₂ B : D.State) (e : Op D.AppOp),
    (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
    (∀ a : Op D.AppOp, ¬ C.vis a a) →
    (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₁ → a ∈ ev₁) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev₂ → a ∈ ev₂) →
    e ∈ ev₁ → e ∈ ev₂ →
    (∀ x ∈ ev₁ ∪ ev₂, x ≠ e → ¬ loOn C (ev₁ ∪ ev₂) e x) →
    IsCanonicalState C ((ev₁ ∩ ev₂) \ {e}) t₀ →
    IsCanonicalState C (downset C e \ {e}) B →
    IsCanonicalState C (ev₁ \ {e}) t₁ →
    IsCanonicalState C (ev₂ \ {e}) t₂ →
    D.mergeL (D.mergeL B t₀ (D.update B e)) (D.mergeL B t₁ (D.update B e))
        (D.mergeL B t₂ (D.update B e))
      = D.mergeL B (D.mergeL t₀ t₁ t₂) (D.update B e)

/-- **VC5°, the nullary unit**: `feasible_init` at the empty event set,
`mergeL σ₀ σ₀ σ₀ = σ₀`. The empty set sits below the floor of the VC5⁺
induction (`feasible_init_nonempty_w`), and this corner is INDEPENDENT of the
other seven conditions (the poisoned-empty-merge G-set,
`Refutations/FeasibleInit_Not_Derivable_At_Empty.lean`). -/
def FeasibleInitAtEmpty : Prop :=
  D.mergeL D.init D.init D.init = D.init

/-- **VC5 in the form the adequacy induction consumes it**
(`Adequacy.lean:999,1007`): at both sites `vis`-transitivity, irreflexivity
and weak closure of the event set are in scope. The raw `feasible_init` field
is stated without them: that surplus is never consumed. -/
def FeasibleInitConsumed : Prop :=
  ∀ (C : Sal.Emulation.Configuration D.toCRDTSig)
    (ev : Set (Op D.AppOp)) (s : D.State),
    (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
    (∀ a : Op D.AppOp, ¬ C.vis a a) →
    (∀ a ∈ ev, a ∈ C.events) →
    (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev → a ∈ ev) →
    IsCanonicalState C ev s →
    D.mergeL D.init D.init s = s

end Split

section SplitLemmas
variable {D : ConditionedMRDTSig}

/-- The bundle splits into the three standalone conditions. -/
theorem feasibleDeltaVCs3_iff_split :
    FeasibleDeltaVCs3 D ↔
      FeasibleInitVC D ∧ FeasibleLocalRedistributeVC D ∧
        FeasibleRedistributeVC D :=
  ⟨fun h => ⟨h.feasible_init, h.feasible_local_redistribute,
     h.feasible_redistribute⟩,
   fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩⟩

/-- The raw field implies the consumed form (extra hypotheses discarded). -/
theorem FeasibleInitVC.toConsumed (h : FeasibleInitVC D) :
    FeasibleInitConsumed D :=
  fun C ev s _ _ h_in _ hcs => h C ev s h_in hcs

/-- `σ₀` is canonical for the empty event set in every configuration. -/
theorem isCanonicalState_empty_init {D' : CRDTSig}
    (C : Sal.Emulation.Configuration D') :
    IsCanonicalState C (∅ : Set (Op D'.AppOp)) D'.init :=
  ⟨[], ⟨List.nodup_nil, fun a => by simp⟩, List.Pairwise.nil, rfl⟩

/-- VC5 implies the nullary unit VC5° (instantiate at the empty
configuration and event set). The converse fails: the poisoned-empty G-set
separates them from the other direction, and VC5⁺
(`feasible_init_nonempty_w`) recovers exactly the nonempty remainder. -/
theorem FeasibleInitVC.atEmpty (h : FeasibleInitVC D) :
    FeasibleInitAtEmpty D :=
  h (Sal.Emulation.initConfig D.toCRDTSig) ∅ D.init
    (fun a ha => absurd ha (Set.notMem_empty a))
    (isCanonicalState_empty_init _)

end SplitLemmas

/-! ## §2. Reachable states and the weakened shell -/

/-- A state of `D'` reachable in configuration `C`: some fold of events of
`C` from `σ₀` produces it. This is the "reachable" of the VC3 sentinel
witness (a state no event fold attains is invisible to adequacy). -/
def ReachState (D' : CRDTSig) (C : Sal.Emulation.Configuration D')
    (s : D'.State) : Prop :=
  ∃ pfx : List (Op D'.AppOp),
    (∀ x ∈ pfx, x ∈ C.events) ∧ applySeq D' D'.init pfx = s

section Reach
variable {D : CRDTSig} {C : Sal.Emulation.Configuration D}

theorem reachState_init : ReachState D C D.init :=
  ⟨[], fun _ hx => absurd hx List.not_mem_nil, rfl⟩

theorem applySeq_append_chunks (s : D.State) (l₁ l₂ : List (Op D.AppOp)) :
    applySeq D s (l₁ ++ l₂) = applySeq D (applySeq D s l₁) l₂ := by
  simp [applySeq, List.foldl_append]

theorem ReachState.update {s : D.State} (hs : ReachState D C s)
    {e : Op D.AppOp} (he : e ∈ C.events) :
    ReachState D C (D.update s e) := by
  obtain ⟨pfx, hm, hf⟩ := hs
  refine ⟨pfx ++ [e], ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hm x h
    · rw [List.mem_singleton] at h
      subst h
      exact he
  · rw [applySeq_append_single, hf]

theorem ReachState.fold {s : D.State} (hs : ReachState D C s)
    {π : List (Op D.AppOp)} (hπ : ∀ x ∈ π, x ∈ C.events) :
    ReachState D C (applySeq D s π) := by
  obtain ⟨pfx, hm, hf⟩ := hs
  refine ⟨pfx ++ π, ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hm x h
    · exact hπ x h
  · rw [applySeq_append_chunks, hf]

end Reach

/-- **The weakened update layer**: exactly the content of VC1..VC3 the
adequacy proof consumes (see the file header inventory).

* `rc_of_non_comm`: VC1's forward direction only. The reverse direction (an
  rc edge implies non-commutation) is dropped: it is consumed nowhere on the
  adequacy chain, and the G-set with a spurious rc edge on a commuting pair
  violates it while remaining RA-linearizable.
* `loOn_acyclic`: VC2 replaced by its consumed consequence, acyclicity of
  `loOnNe` on event sets of a configuration. `no_rc_chain` is sufficient but
  not necessary (the LWW register's timestamp-total rc chains are acyclic).
* `cond_comm_lift_reach`: VC3 restricted to reachable states (`ReachState`)
  and configuration events. The unconditional VC3 quantifies over the whole
  state universe; the sentinel witness breaks it only at an unreachable
  state and stays RA-linearizable. -/
structure WeakUpdateVCs (D : CRDTSig) : Prop where
  rc_of_non_comm :
    ∀ o₁ o₂ : Op D.AppOp,
      distinctOps o₁ o₂ → differentReplicas o₁ o₂ →
      ¬ D.commutes o₁ o₂ →
      (D.rc o₁ o₂ = RcRes.Fst_then_snd ∨ D.rc o₂ o₁ = RcRes.Fst_then_snd)
  loOn_acyclic :
    ∀ (C : Sal.Emulation.Configuration D) (T : Set (Op D.AppOp)),
      (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
      (∀ a : Op D.AppOp, ¬ C.vis a a) →
      (∀ a ∈ T, a ∈ C.events) →
      ∀ a : Op D.AppOp, ¬ Relation.TransGen (loOnNe C T) a a
  cond_comm_lift_reach :
    ∀ (C : Sal.Emulation.Configuration D) (s : D.State),
      ReachState D C s →
      ∀ (e e' e'' : Op D.AppOp) (π : List (Op D.AppOp)),
        e ∈ C.events → e' ∈ C.events → e'' ∈ C.events →
        (∀ x ∈ π, x ∈ C.events) →
        distinctOps e e' → distinctOps e e'' → distinctOps e' e'' →
        D.rc e e' = RcRes.Fst_then_snd →
        ¬ D.commutes e' e'' →
        D.update (applySeq D (D.update (D.update s e') e) π) e''
          = D.update (applySeq D (D.update (D.update s e) e') π) e''

/-- The full update layer implies the weakened one (VC1 forward via `.mp`,
acyclicity via `loOnNe_acyclic_u`, the lift by discarding the reachability
guards). The converse fails at each field. -/
theorem UpdateVCs.toWeak {D : CRDTSig} (hU : UpdateVCs D) :
    WeakUpdateVCs D where
  rc_of_non_comm := fun o₁ o₂ hd hr hnc =>
    (hU.rc_non_comm_directional o₁ o₂ hd hr).mp hnc
  loOn_acyclic := fun _C _T h_tr h_ir h_in a =>
    loOnNe_acyclic_u hU h_tr h_ir h_in a
  cond_comm_lift_reach := fun _C s _hs e e' e'' π _ _ _ _ hd₁ hd₂ hd₃ hrc hnc =>
    hU.cond_comm_lift s e e' e'' π hd₁ hd₂ hd₃ hrc hnc

/-- **The weakened shell**: the weakened update layer plus merge symmetry
restricted to canonical tuples at honest LCAs (the three consumption sites of
VC4, see the file header). -/
structure WeakShellVCs (D : ConditionedMRDTSig) : Prop where
  update_weak : WeakUpdateVCs D.toCRDTSig
  mergeL_comm_canonical :
    ∀ (C : Sal.Emulation.Configuration D.toCRDTSig)
      (ev₁ ev₂ : Set (Op D.AppOp)) (l a b : D.State),
      (∀ {x y z : Op D.AppOp}, C.vis x y → C.vis y z → C.vis x z) →
      (∀ x : Op D.AppOp, ¬ C.vis x x) →
      (∀ x ∈ ev₁, x ∈ C.events) → (∀ x ∈ ev₂, x ∈ C.events) →
      (∀ x y, C.vis x y → ¬ D.toCRDTSig.commutes x y → y ∈ ev₁ → x ∈ ev₁) →
      (∀ x y, C.vis x y → ¬ D.toCRDTSig.commutes x y → y ∈ ev₂ → x ∈ ev₂) →
      IsCanonicalState C (ev₁ ∩ ev₂) l →
      IsCanonicalState C ev₁ a → IsCanonicalState C ev₂ b →
      D.mergeL l a b = D.mergeL l b a

/-- The flat slim core implies the weakened shell. -/
theorem CoreVCs3CD.toWeakShell {D : ConditionedMRDTSig}
    (hVC : CoreVCs3CD D) : WeakShellVCs D where
  update_weak := hVC.update_core.toWeak
  mergeL_comm_canonical :=
    fun _C _ev₁ _ev₂ l a b _ _ _ _ _ _ _ _ _ => hVC.mergeL_comm l a b

/-! ## §3. T3 — VC5⁺ is derivable off the empty set

`feasible_init` at a **nonempty** canonical state follows from
`CoreVCs3CD` (VC1–VC4) + `feasible_local_redistribute` (VC6) + `CDVC3` (VC8),
on weakly-closed event sets. This is the note's strong-induction derivation.
Both `mergeL_comm` uses land on canonical tuples (`(σ∅, σ(E∖e), σ∅)` and
`(σ∅, σE, σ∅)`), so the *weakened* VC4 already suffices; the update layer is
used at full strength through the σ-machinery. -/

/-- A subset of an enumerable set is enumerable (public copy of the `private`
`exists_listPermOf_subsetF`). -/
theorem exists_listPermOf_sub {α : Type} {l : List α}
    {T S : Set α} (h : listPermOf l T) (hsub : S ⊆ T) :
    ∃ l', listPermOf l' S := by
  classical
  refine ⟨l.filter (fun a => decide (a ∈ S)), h.1.filter _, fun a => ?_⟩
  rw [List.mem_filter]
  constructor
  · rintro ⟨_, hd⟩; exact of_decide_eq_true hd
  · intro ha; exact ⟨(h.2 a).mpr (hsub ha), decide_eq_true ha⟩

/-- **T3: VC5⁺.** On weakly-closed nonempty event sets, `feasible_init` is a
theorem of `CoreVCs3CD + VC6 + VC8` (strong induction on `|ev|`; base = `CDVC3`
at `U = {e}`, step = `VC6` at `(ev, ∅)`). -/
theorem feasible_init_nonempty_w {D : ConditionedMRDTSig}
    (hVC : CoreVCs3CD D) (hVC6 : FeasibleLocalRedistributeVC D) (hCD : CDVC3 D)
    {C : Sal.Emulation.Configuration D.toCRDTSig}
    (h_tr : ∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c)
    (h_ir : ∀ a : Op D.AppOp, ¬ C.vis a a) :
    ∀ (ev : Set (Op D.AppOp)) (s : D.State),
      (∀ a ∈ ev, a ∈ C.events) →
      (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev → a ∈ ev) →
      ev.Nonempty → IsCanonicalState C ev s →
      D.mergeL D.init D.init s = s := by
  have hU := hVC.update_core
  suffices gen : ∀ n (ev : Set (Op D.AppOp)) (s : D.State) (l : List (Op D.AppOp)),
      listPermOf l ev → l.length = n →
      (∀ a ∈ ev, a ∈ C.events) →
      (∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → b ∈ ev → a ∈ ev) →
      ev.Nonempty → IsCanonicalState C ev s →
      D.mergeL D.init D.init s = s by
    intro ev s h_in h_cl h_ne hcs
    obtain ⟨l, hp, -, -⟩ := id hcs
    exact gen l.length ev s l hp rfl h_in h_cl h_ne hcs
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro ev s l hp hlen h_in h_cl h_ne hcs
    obtain ⟨e, he_ev, h_max⟩ := exists_loOn_maximal_u hU h_tr h_ir hp h_in h_ne
    have h_e_l : e ∈ l := (hp.2 e).mpr he_ev
    have hp' : listPermOf (l.filter (· ≠ e)) (ev \ {e}) := filter_ne_listPermOf hp h_e_l
    obtain ⟨t₁, ht₁⟩ : ∃ t, IsCanonicalState C (ev \ {e}) t :=
      isCanonicalState_exists_u hU h_tr h_ir hp' (fun a ha => h_in a ha.1)
    have h_dsub : downset C e ⊆ ev := downset_subset h_cl he_ev
    obtain ⟨lB, hpB⟩ :=
      exists_listPermOf_sub (S := downset C e \ {e}) hp (fun x hx => h_dsub hx.1)
    obtain ⟨B, hB⟩ : ∃ B, IsCanonicalState C (downset C e \ {e}) B :=
      isCanonicalState_exists_u hU h_tr h_ir hpB (fun a ha => h_in a (h_dsub ha.1))
    have hs_eq : s = D.update t₁ e :=
      isCanonicalState_unique_u hU h_in hcs (isCanonicalState_snoc he_ev h_max ht₁)
    have h_cd : D.mergeL B t₁ (D.update B e) = D.update t₁ e :=
      hCD C ev t₁ B e h_tr h_ir h_in h_cl he_ev h_max ht₁ hB
    rcases Set.eq_empty_or_nonempty (ev \ {e}) with h_empty | h_ne'
    · -- Base: ev = {e}, so t₁ = B = σ₀; the unit law is `CDVC3` at `U = {e}`.
      have ht1_init : t₁ = D.init := isCanonicalState_empty h_empty ht₁
      have hB_empty : downset C e \ {e} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]; intro x hx
        have hx' : x ∈ ev \ {e} := ⟨h_dsub hx.1, hx.2⟩
        rw [h_empty] at hx'; exact hx'
      have hB_init : B = D.init := isCanonicalState_empty hB_empty hB
      rw [hs_eq, ht1_init]
      rw [ht1_init, hB_init] at h_cd
      exact h_cd
    · -- Step: `VC6` at `(ev, ∅)` with the induction hypothesis at `t₁`.
      have h_pos : 0 < n := by rw [← hlen]; exact List.length_pos_of_mem h_e_l
      have hlen' : (l.filter (· ≠ e)).length < n := by
        rw [listPermOf_diff_length hp h_e_l hp', hlen]; omega
      have IHt1 : D.mergeL D.init D.init t₁ = t₁ :=
        IH _ hlen' (ev \ {e}) t₁ (l.filter (· ≠ e)) hp' rfl
          (fun a ha => h_in a ha.1) (closure_diff_of_max Set.Subset.rfl h_cl h_max)
          h_ne' ht₁
      have hsym1 : D.mergeL D.init t₁ D.init = t₁ := by
        rw [hVC.mergeL_comm]; exact IHt1
      have hVC6i := hVC6 C ev ∅ D.init B t₁ D.init e h_tr h_ir h_in
        (fun a ha => absurd ha (Set.notMem_empty a)) h_cl
        (fun a b _ _ hb => absurd hb (Set.notMem_empty b))
        he_ev (Set.notMem_empty e)
        (by rw [Set.union_empty]; exact h_max)
        (by rw [Set.inter_empty]; exact isCanonicalState_empty_init C)
        hB ht₁ (isCanonicalState_empty_init C)
      rw [h_cd, hsym1, h_cd] at hVC6i
      rw [hs_eq, hVC.mergeL_comm]
      exact hVC6i

/-! ## §4. T4 — the split at the consumption sites

`feasible_init` as the adequacy induction consumes it (`FeasibleInitConsumed`,
matching sites `Adequacy.lean:999,1007` where closure + `vis`-structure are in
scope) is exactly `VC5°` (empty side) plus `VC5⁺` (nonempty side). This is the
mechanized shrink of VC5: the raw `feasible_init` field's surplus over
`FeasibleInitConsumed` (it omits closure/`vis`) is never consumed, and its
consumed content splits into the independent nullary unit `VC5°` and the
`CoreVCs3CD + VC6 + VC8`-derivable nonempty half. -/

/-- **VC5 splits at the consumption sites**: `FeasibleInitConsumed` is exactly
`VC5°` (`FeasibleInitAtEmpty`) plus the `CoreVCs3CD + VC6 + VC8` core. -/
theorem feasibleInitConsumed_of_split {D : ConditionedMRDTSig}
    (hVC : CoreVCs3CD D) (hVC6 : FeasibleLocalRedistributeVC D) (hCD : CDVC3 D)
    (h0 : FeasibleInitAtEmpty D) : FeasibleInitConsumed D := by
  intro C ev s h_tr h_ir h_in h_cl hcs
  rcases Set.eq_empty_or_nonempty ev with rfl | h_ne
  · have hs : s = D.init := isCanonicalState_empty rfl hcs
    rw [hs]; exact h0
  · exact feasible_init_nonempty_w hVC hVC6 hCD h_tr h_ir ev s h_in h_cl h_ne hcs

end Sal.ConditionedMRDTs
