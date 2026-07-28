import Sal.ConditionedMRDTs.Metatheory.GenHonest

/-!
# Generic safety for conditioned MRDTs (causal witnesses)

The per-version invariant theorem for conditioned MRDTs, by induction along a
**causal canonical witness** (an enumeration that linearizes `vis` in addition
to `loOn`). Over arbitrary canonical witnesses the per-version invariant is
false (the bounded counter's `[dec, inc]` witness has an `Inv`-violating
intermediate state); restricting to causal witnesses makes every prefix a
vis-backward-closed, future-free superset of each event's causal past, which
is exactly what the per-datatype `SafetyStep` obligation can be sound over.

Contents:

* `CausalFold`: a state is the fold of some vis-linearizing enumeration of a
  set; `HonestApp`: every event was `applicable` at some causal
  fold of its causal past (the client-checkable, ∃-form honesty);
* `CausalCanonical`: every version state is the fold of a vis-linearizing
  and `loOn`-respecting enumeration (strictly refines `GoodConfig3.canonical`);
* `SafetyStep`: the fused stability + `Inv`-preservation obligation;
* `version_inv_of_causal_canonical`: the metatheorem: `Inv init` +
  `SafetyStep` + `GoodConfig3` + `CausalCanonical` + `HonestApp` give `Inv`
  at every version. Configuration-level: no `Step3` induction;
* `causalCanonical_of_all_comm_rc_either`: the pointwise discharge species
  (all-comm + `rc ≡ Either`): any canonical witness reorders into a causal
  one with the same fold;
* `ObservedRegistered` / `observedRegistered_of_honest_reach`: every
  replica-observed set is registered at some version (the one reachability
  fact the honesty bridges need to *enumerate* causal pasts);
* `honestAppOn_of_genHonest`: the ∀-enumeration honesty shape (`GenHonest`)
  discharges the ∃-form: the registering version's causal witness restricts
  by `filter` to a causal enumeration of each causal past;
* `countP_prefix_eq_causal_past`: the reusable issuer-local discharge core;
  counts of own-replica events agree between any admissible causal prefix and
  the causal past.

The predicates come in an `…On` form over an explicit conditioning pair
`(I, A)` with the `D.Inv`/`D.applicable` form as an abbreviation. The
explicit pair is what instances whose contract lives *beside* the signature
consume (the bounded counter: the configuration is over the flat `BC`, the
contract is `BCInv`/`bcApplicable`, and transporting a `Configuration BC` to
`Configuration BCCond` is impossible without already knowing the theorem's
conclusion, since the `ver_inv` structure field demands `Inv` of every
registered state).
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! ## §1  Causal folds, honesty, causal canonicity, and the step obligation -/

/-- **Causal fold**: `σ` is the fold of some enumeration of `E`
that linearizes `vis` (no later element is `vis`-before an earlier one).
Prefixes of such an enumeration are exactly the vis-backward-closed subsets
of `E`. -/
def CausalFold {D' : CRDTSig} (C : Sal.Emulation.Configuration D')
    (E : Set (Op D'.AppOp)) (σ : D'.State) : Prop :=
  ∃ ρ : List (Op D'.AppOp),
    listPermOf ρ E ∧ respects ρ C.vis ∧ applySeq D' D'.init ρ = σ

section
variable {D : ConditionedMRDTSig}

/-- The ∃-form honesty over an explicit guard `A`: every event satisfies `A`
at some causal fold of its causal past. Existential because the issuer holds
only the one fold its replica materialized (order-sensitive datatypes:
different causal enumerations of the same past can fold differently). Being
an ∃-statement, it carries its own enumeration witness, with no separate
enumerability side condition. -/
def HonestAppOn (D : ConditionedMRDTSig)
    (A : Op D.AppOp → D.State → Prop) (C : Configuration D) : Prop :=
  ∀ e ∈ C.events, ∃ σ : D.State,
    CausalFold (Configuration.core C) {e' ∈ C.events | C.vis e' e} σ ∧ A e σ

/-- **`HonestApp`**: the ∃-form honesty at the datatype's own
generation-time guard. -/
abbrev HonestApp (D : ConditionedMRDTSig) (C : Configuration D) : Prop :=
  HonestAppOn D D.applicable C

/-- **Causal canonical witness**: every version state is the
fold of an enumeration of its event set that linearizes `vis` and respects
`loOn`, strictly refining `GoodConfig3.canonical`. -/
def CausalCanonical (C : Configuration D) : Prop :=
  ∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
    C.ver v = some (s, E) →
    ∃ ρ : List (Op D.AppOp),
      listPermOf ρ E ∧ respects ρ C.vis ∧
      respects ρ (loOn (Configuration.core C) E) ∧
      applySeq D.toCRDTSig D.init ρ = s

/-- **The per-datatype safety obligation**, over an explicit
conditioning pair `(I, A)`: over vis-closed, future-free causal prefixes `S`
with `past(e) ⊆ S ⊆ E` and causal folds `σS` of `S`, `σP` of `past(e)`,
`I σS → A e σP → I (update σS e)`. Fused with `I`-preservation so that
unconditionally-safe ops need no guard at all. -/
def SafetyStepOn (D : ConditionedMRDTSig) (I : D.State → Prop)
    (A : Op D.AppOp → D.State → Prop) : Prop :=
  ∀ (C : Configuration D) (E S : Set (Op D.AppOp)) (e : Op D.AppOp)
    (σS σP : D.State),
    (∀ a ∈ E, a ∈ C.events) →
    (∀ a b, C.vis a b → b ∈ E → a ∈ E) →
    e ∈ E → S ⊆ E → e ∉ S →
    (∀ a b, C.vis a b → b ∈ S → a ∈ S) →
    (∀ x ∈ S, ¬ C.vis e x) →
    (∀ x, C.vis x e → x ∈ S) →
    CausalFold (Configuration.core C) S σS →
    CausalFold (Configuration.core C) {e' ∈ C.events | C.vis e' e} σP →
    I σS → A e σP → I (D.update σS e)

/-- **`SafetyStep`**: the obligation at the datatype's own
conditioning split. -/
abbrev SafetyStep (D : ConditionedMRDTSig) : Prop :=
  SafetyStepOn D D.Inv D.applicable

/-! ## §2  The metatheorem: induction along the causal witness

Snoc-forward along the causal witness ρ of a version `(s, E)`, maintaining
`I` at every prefix fold. The bookkeeping: a
prefix set of a `respects · vis` enumeration of the (fully causally closed,
`GoodConfig3.ver_causal`) set `E` is vis-backward-closed, future-free, and
contains the whole causal past of the next element, all read off the
`Pairwise` structure of `π ++ e :: τ`. -/

/-- **Generic safety, causal-witness form, explicit conditioning pair.** -/
theorem version_inv_on_of_causal_canonical
    {I : D.State → Prop} {A : Op D.AppOp → D.State → Prop}
    (hInit : I D.init) (hStep : SafetyStepOn D I A)
    {C : Configuration D}
    (hG : GoodConfig3 C) (hCC : CausalCanonical C)
    (hHon : HonestAppOn D A C) :
    ∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
      C.ver v = some (s, E) → I s := by
  intro v s E hv
  obtain ⟨ρ, hperm, hvisR, _hloR, hfold⟩ := hCC v s E hv
  have hE_ev : ∀ a ∈ E, a ∈ C.events := hG.ver_events_sub v s E hv
  have hE_cl : ∀ a b, C.vis a b → b ∈ E → a ∈ E := hG.ver_causal v s E hv
  suffices h : ∀ (τ π : List (Op D.AppOp)), ρ = π ++ τ →
      I (applySeq D.toCRDTSig D.init π) →
      I (applySeq D.toCRDTSig D.init ρ) by
    rw [← hfold]
    exact h ρ [] rfl hInit
  intro τ
  induction τ with
  | nil =>
    intro π hsplit hI
    rw [List.append_nil] at hsplit
    rw [hsplit]
    exact hI
  | cons e τ' ih =>
    intro π hsplit hI
    -- prefix bookkeeping at the step `e`
    have hnd : (π ++ e :: τ').Nodup := by rw [← hsplit]; exact hperm.1
    have hpw : (π ++ e :: τ').Pairwise (fun a b => ¬ C.vis b a) := by
      rw [← hsplit]; exact hvisR
    obtain ⟨hpwπ, hpwE, hcross⟩ := List.pairwise_append.mp hpw
    have hτ'_no_e : ∀ x ∈ τ', ¬ C.vis x e := (List.pairwise_cons.mp hpwE).1
    have hmemρ : ∀ x, x ∈ π ++ e :: τ' ↔ x ∈ E := by
      intro x; rw [← hsplit]; exact hperm.2 x
    have he_E : e ∈ E :=
      (hmemρ e).mp (List.mem_append_right _ List.mem_cons_self)
    have hS_sub : {x : Op D.AppOp | x ∈ π} ⊆ E := fun x hx =>
      (hmemρ x).mp (List.mem_append_left _ hx)
    have he_not_π : e ∉ ({x : Op D.AppOp | x ∈ π} : Set (Op D.AppOp)) := by
      intro hmem
      exact (List.nodup_append.mp hnd).2.2 e hmem e List.mem_cons_self rfl
    have hfut : ∀ x ∈ ({x : Op D.AppOp | x ∈ π} : Set (Op D.AppOp)),
        ¬ C.vis e x :=
      fun x hx => hcross x hx e List.mem_cons_self
    have hpast : ∀ x, C.vis x e →
        x ∈ ({x : Op D.AppOp | x ∈ π} : Set (Op D.AppOp)) := by
      intro x hvis
      have hxE : x ∈ E := hE_cl x e hvis he_E
      rcases List.mem_append.mp ((hmemρ x).mpr hxE) with hx | hx
      · exact hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd hvis (hG.vis_irrefl x)
        · exact absurd hvis (hτ'_no_e x hx)
    have hS_cl : ∀ a b, C.vis a b →
        b ∈ ({x : Op D.AppOp | x ∈ π} : Set (Op D.AppOp)) →
        a ∈ ({x : Op D.AppOp | x ∈ π} : Set (Op D.AppOp)) := by
      intro a b hvis hb
      have haE : a ∈ E := hE_cl a b hvis (hS_sub hb)
      rcases List.mem_append.mp ((hmemρ a).mpr haE) with ha | ha
      · exact ha
      · exfalso
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hfut b hb hvis
        · exact hcross b hb a (List.mem_cons_of_mem _ ha) hvis
    -- the prefix fold IS a causal fold of its own set
    have hσS : CausalFold (Configuration.core C) {x : Op D.AppOp | x ∈ π}
        (applySeq D.toCRDTSig D.init π) :=
      ⟨π, ⟨(List.nodup_append.mp hnd).1, fun _ => Iff.rfl⟩, hpwπ, rfl⟩
    -- honesty supplies the causal-past fold
    obtain ⟨σP, hσP, happ⟩ := hHon e (hE_ev e he_E)
    -- the step, then recurse on the extended prefix
    have hstep := hStep C E {x : Op D.AppOp | x ∈ π} e
      (applySeq D.toCRDTSig D.init π) σP
      hE_ev hE_cl he_E hS_sub he_not_π hS_cl hfut hpast hσS hσP hI happ
    refine ih (π ++ [e]) (by rw [hsplit, List.append_cons]) ?_
    rw [applySeq_append_single]
    exact hstep

/-- **Generic safety, causal-witness form**: if
`D.Inv D.init`, `SafetyStep D`, and `C` satisfies `GoodConfig3`,
`CausalCanonical`, `HonestApp`, then every version state satisfies `D.Inv`.
Configuration-level: reachability rides the `HonestReach`
machinery. -/
theorem version_inv_of_causal_canonical
    (hInit : D.Inv D.init) (hStep : SafetyStep D)
    {C : Configuration D}
    (hG : GoodConfig3 C) (hCC : CausalCanonical C) (hHon : HonestApp D C) :
    ∀ (v : Version) (s : D.State) (E : Set (Op D.AppOp)),
      C.ver v = some (s, E) → D.Inv s :=
  version_inv_on_of_causal_canonical hInit hStep hG hCC hHon

/-! ## §3  The pointwise `CausalCanonical` discharge (all-comm + rc-Either)

Any finite enumeration reorders into a vis-linearizing one (peel a
vis-minimal element — exists since `vis` is transitive and irreflexive on a
finite list), and all-comm makes folds permutation-invariant; `rc ≡ Either`
kills the `loOn` rc-arm, so the `loOn`-respect conjunct is free. -/

/-- A nonempty list ordered by a transitive irreflexive relation has an
`R`-minimal element (no element of the list is `R`-below it). -/
private theorem exists_rel_min {α : Type} {R : α → α → Prop}
    (htrans : ∀ {a b c}, R a b → R b c → R a c)
    (hirrefl : ∀ a, ¬ R a a) :
    ∀ (l : List α), l ≠ [] → ∃ m ∈ l, ∀ x ∈ l, ¬ R x m := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons a l ih =>
    intro _
    by_cases hl : l = []
    · subst hl
      refine ⟨a, List.mem_cons_self, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hirrefl _
      · exact absurd hx List.not_mem_nil
    · obtain ⟨m, hm, hmin⟩ := ih hl
      by_cases ham : R a m
      · refine ⟨a, List.mem_cons_self, ?_⟩
        intro x hx hxa
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hirrefl _ hxa
        · exact hmin x hx (htrans hxa ham)
      · refine ⟨m, List.mem_cons_of_mem _ hm, ?_⟩
        intro x hx hxm
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ham hxm
        · exact hmin x hx hxm

/-- Any finite list reorders into an `R`-respecting one (`R` transitive,
irreflexive): peel a minimal element, recurse on the rest. -/
private theorem exists_respecting_perm_aux {α : Type} {R : α → α → Prop}
    (htrans : ∀ {a b c}, R a b → R b c → R a c)
    (hirrefl : ∀ a, ¬ R a a) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n →
      ∃ l', l.Perm l' ∧ respects l' R := by
  classical
  intro n
  induction n with
  | zero =>
    intro l hl
    have hnil : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    subst hnil
    exact ⟨[], List.Perm.refl _, List.Pairwise.nil⟩
  | succ n ihn =>
    intro l hl
    by_cases hnil : l = []
    · subst hnil
      exact ⟨[], List.Perm.refl _, List.Pairwise.nil⟩
    · obtain ⟨m, hm_mem, hm_min⟩ :=
        exists_rel_min (R := R) (fun hab hbc => htrans hab hbc) hirrefl l hnil
      have hperm : l.Perm (m :: l.erase m) := List.perm_cons_erase hm_mem
      have hlen : (l.erase m).length ≤ n := by
        have herase := List.length_erase_of_mem hm_mem
        have hpos : l.length ≠ 0 :=
          fun h => hnil (List.eq_nil_of_length_eq_zero h)
        omega
      obtain ⟨l'', hp'', hr''⟩ := ihn (l.erase m) hlen
      refine ⟨m :: l'', hperm.trans (hp''.cons m), ?_⟩
      unfold respects
      rw [List.pairwise_cons]
      refine ⟨?_, hr''⟩
      intro y hy
      exact hm_min y (List.mem_of_mem_erase (hp''.mem_iff.mpr hy))

/-- Reordering wrapper: every finite list has an `R`-respecting
permutation. -/
theorem exists_respecting_perm {α : Type} {R : α → α → Prop}
    (htrans : ∀ {a b c}, R a b → R b c → R a c)
    (hirrefl : ∀ a, ¬ R a a) (l : List α) :
    ∃ l', l.Perm l' ∧ respects l' R :=
  exists_respecting_perm_aux (R := R) (fun hab hbc => htrans hab hbc) hirrefl
    l.length l (Nat.le_refl _)

/-- Folds are permutation-invariant when every pair of ops commutes
(adjacent-swap induction over the `Perm` derivation; `commutes` is exactly
the needed swap equation). -/
theorem applySeq_perm_of_all_comm {D' : CRDTSig}
    (hcomm : ∀ a b : Op D'.AppOp, D'.commutes a b)
    {l₁ l₂ : List (Op D'.AppOp)} (h : l₁.Perm l₂) :
    ∀ s : D'.State, applySeq D' s l₁ = applySeq D' s l₂ := by
  induction h with
  | nil => intro _; rfl
  | cons x _ ih => intro s; exact ih (D'.update s x)
  | swap x y l =>
    intro s
    show applySeq D' (D'.update (D'.update s y) x) l
      = applySeq D' (D'.update (D'.update s x) y) l
    rw [hcomm y x s]
  | trans _ _ ih₁ ih₂ => intro s; exact (ih₁ s).trans (ih₂ s)

/-- **The pointwise `CausalCanonical` discharge** (first species): all-comm +
`rc ≡ Either` upgrade `GoodConfig3.canonical` to a causal witness. Reorder the
canonical enumeration into a vis-linearization (same fold by all-comm); the
`loOn`-respect conjunct is vacuous (`loOn = ∅`: vis-arm dead by all-comm, rc-arm
dead by `Either`). No reachability induction. -/
theorem causalCanonical_of_all_comm_rc_either
    (hcomm : ∀ a b : Op D.AppOp, D.toCRDTSig.commutes a b)
    (hrc : ∀ a b : Op D.AppOp, D.toCRDTSig.rc a b = RcRes.Either)
    {C : Configuration D} (hG : GoodConfig3 C) :
    CausalCanonical C := by
  intro v s E hv
  obtain ⟨ρ, hperm, _hresp, hfold⟩ := hG.canonical v s E hv
  obtain ⟨ρ', hp, hr⟩ := exists_respecting_perm (R := C.vis)
    (fun hab hbc => hG.vis_trans hab hbc) hG.vis_irrefl ρ
  refine ⟨ρ', ⟨hp.nodup hperm.1,
    fun a => (hp.mem_iff (a := a)).symm.trans (hperm.2 a)⟩, hr, ?_, ?_⟩
  · -- `loOn` has no edges at all under all-comm + rc-Either
    exact hr.imp (fun _ hlo => by
      rcases hlo with ⟨_, hnc⟩ | ⟨_, _, hfs, _⟩
      · exact hnc (hcomm _ _)
      · rw [hrc] at hfs
        exact RcRes.noConfusion hfs)
  · exact (applySeq_perm_of_all_comm hcomm hp D.init).symm.trans hfold

/-! ## §4  Sub-enumerations, the registered-store fact, and the honesty
bridge -/

/-- Any subset of an enumerable set is enumerable via `filter` (classical
membership test); the workhorse for restricting a version witness to a
causal past. -/
theorem listPermOf_filter_subset {α : Type} {ρ : List α} {T S : Set α}
    (hperm : listPermOf ρ T) (hsub : S ⊆ T) :
    listPermOf (ρ.filter fun a => decide (a ∈ S)) S := by
  refine ⟨hperm.1.filter _, fun a => ?_⟩
  rw [List.mem_filter]
  constructor
  · rintro ⟨_, hd⟩
    exact of_decide_eq_true hd
  · intro ha
    exact ⟨(hperm.2 a).mpr (hsub ha), decide_eq_true ha⟩

/-- Every replica-observed event set is registered at some version of the
store. A reachability fact (`observedRegistered_of_honest_reach`); it is what
lets the honesty bridges *produce* enumerations of causal pasts: there is no
generic finiteness result for reachable event universes, but the store's
canonical witnesses enumerate every registered set. -/
def ObservedRegistered (C : Configuration D) : Prop :=
  ∀ (r : Replica) (ev : Set (Op D.AppOp)), C.L r = some ev →
    ∃ (v : Version) (s : D.State), C.ver v = some (s, ev)

/-- `ObservedRegistered` is preserved by every `Step3` transition: the store
registers every head. CreateReplica points at version `0` (`ver_init`),
Apply and Merge allocate the version carrying exactly the new observed
set. -/
private theorem observedRegistered_step {C C' : Configuration D}
    {ℓ : Label3 D} (hstep : Step3 D C ℓ C') (ih : ObservedRegistered C) :
    ObservedRegistered C' := by
  cases hstep with
  | @createReplica r h_fresh C'' hN hL hvis hver hhead hparents =>
    intro r' ev' hL'
    rw [hL] at hL'
    simp only [updateRep] at hL'
    split at hL'
    · rw [Option.some.injEq] at hL'
      subst hL'
      exact ⟨0, D.init, C'.ver_init⟩
    · obtain ⟨v', s', hv'⟩ := ih r' ev' hL'
      exact ⟨v', s', by rw [hver]; exact hv'⟩
  | @apply t r o v s ev vnew h_head h_ver h_fresh_t h_fresh_store h_vnew
      h_rank C'' hN hL hvis hver hhead hparents =>
    have hver_old : ∀ w, w ≠ vnew → C'.ver w = C.ver w := by
      intro w hw; rw [hver]; simp [hw]
    intro r' ev' hL'
    rw [hL] at hL'
    simp only [updateRep] at hL'
    split at hL'
    · rw [Option.some.injEq] at hL'
      subst hL'
      exact ⟨vnew, D.update s (t, r, o), by rw [hver]; simp⟩
    · obtain ⟨v', s', hv'⟩ := ih r' ev' hL'
      have hne : v' ≠ vnew := by
        intro h
        rw [h, h_vnew] at hv'
        simp at hv'
      exact ⟨v', s', by rw [hver_old v' hne]; exact hv'⟩
  | @merge r₁ r₂ v₁ v₂ vT vm s₁ s₂ sT ev₁ ev₂ evT h_head₁ h_head₂ h_ver₁
      h_ver₂ h_lca h_verT h_vm h_rank₁ h_rank₂ C'' hN hL hvis hver hhead
      hparents =>
    have hver_old : ∀ w, w ≠ vm → C'.ver w = C.ver w := by
      intro w hw; rw [hver]; simp [hw]
    intro r' ev' hL'
    rw [hL] at hL'
    simp only [updateRep] at hL'
    split at hL'
    · rw [Option.some.injEq] at hL'
      subst hL'
      exact ⟨vm, D.mergeL sT s₁ s₂, by rw [hver]; simp⟩
    · obtain ⟨v', s', hv'⟩ := ih r' ev' hL'
      have hne : v' ≠ vm := by
        intro h
        rw [h, h_vm] at hv'
        simp at hv'
      exact ⟨v', s', by rw [hver_old v' hne]; exact hv'⟩
  | query h_s h_val => exact ih

/-- `ObservedRegistered` holds at every honestly reachable configuration
(hence, via `honestReach_of_reachable`, at every reachable one). -/
theorem observedRegistered_of_honest_reach {H : Configuration D → Prop}
    {hInit : D.Inv D.init} {C : Configuration D}
    (hReach : HonestReach D H hInit C) : ObservedRegistered C := by
  induction hReach with
  | init =>
    intro r ev hL
    have hL0 : (if r = 0 then some (∅ : Set (Op D.AppOp)) else none)
        = some ev := hL
    by_cases hr : r = 0
    · rw [if_pos hr, Option.some.injEq] at hL0
      subst hL0
      exact ⟨0, D.init, (initConfig D hInit).ver_init⟩
    · rw [if_neg hr] at hL0
      simp at hL0
  | step _ _ hstep ih => exact observedRegistered_step hstep ih

/-- `ObservedRegistered` is preserved by every widened step: the
`mergeVirtual` case registers the merged head at the fresh `vm` exactly as the gated
merge does; the LCA slot's contents are irrelevant to registration. -/
private theorem observedRegistered_stepV {C C' : Configuration D}
    {ℓ : Label3 D} (hstep : Step3V D C ℓ C') (ih : ObservedRegistered C) :
    ObservedRegistered C' := by
  cases hstep with
  | base hstep' => exact observedRegistered_step hstep' ih
  | @mergeVirtual r₁ r₂ v₁ v₂ vm s₁ s₂ ev₁ ev₂ h_head₁ h_head₂ h_ver₁
      h_ver₂ h_vm h_rank₁ h_rank₂ C'' hN hL hvis hver hhead hparents =>
    have hver_old : ∀ w, w ≠ vm → C'.ver w = C.ver w := by
      intro w hw; rw [hver]; simp [hw]
    intro r' ev' hL'
    rw [hL] at hL'
    simp only [updateRep] at hL'
    split at hL'
    · rw [Option.some.injEq] at hL'
      subst hL'
      exact ⟨vm, D.mergeL (virtualLCAState C v₁ v₂) s₁ s₂, by rw [hver]; simp⟩
    · obtain ⟨v', s', hv'⟩ := ih r' ev' hL'
      have hne : v' ≠ vm := by
        intro h
        rw [h, h_vm] at hv'
        simp at hv'
      exact ⟨v', s', by rw [hver_old v' hne]; exact hv'⟩

/-- `ObservedRegistered` at every widened honestly reachable configuration. -/
theorem observedRegistered_of_honest_reachV {H : Configuration D → Prop}
    {hInit : D.Inv D.init} {C : Configuration D}
    (hReach : HonestReachV D H hInit C) : ObservedRegistered C := by
  induction hReach with
  | init =>
    intro r ev hL
    have hL0 : (if r = 0 then some (∅ : Set (Op D.AppOp)) else none)
        = some ev := hL
    by_cases hr : r = 0
    · rw [if_pos hr, Option.some.injEq] at hL0
      subst hL0
      exact ⟨0, D.init, (initConfig D hInit).ver_init⟩
    · rw [if_neg hr] at hL0
      simp at hL0
  | step _ _ hstep ih => exact observedRegistered_stepV hstep ih

/-- **The generic honesty bridge**: the ∀-enumeration shape (`GenHonest`,
which `BCHonest` instantiates) discharges the ∃-form `HonestAppOn` wherever
every observed set is registered and versions carry causal witnesses. The
causal enumeration of `past(e)` is the registering version's causal witness
filtered to the past (`listPermOf` transfers by `filter`, `respects` by
sublist; `past(e) ⊆ ev` is `vis_causal`). -/
theorem honestAppOn_of_genHonest {A : Op D.AppOp → D.State → Prop}
    {C : Configuration D}
    (hObs : ObservedRegistered C) (hCC : CausalCanonical C)
    (hGen : GenHonest D A C) : HonestAppOn D A C := by
  intro e he
  obtain ⟨r, ev, hL, he_ev⟩ := he
  obtain ⟨v, s, hv⟩ := hObs r ev hL
  obtain ⟨ρ, hperm, hresp, _hlo, _hfold⟩ := hCC v s ev hv
  have hPsub : {e' ∈ C.events | C.vis e' e} ⊆ ev := by
    rintro x ⟨_, hvis⟩
    exact C.vis_causal hvis hL he_ev
  obtain ⟨ρP, hpermP, hrespP⟩ :
      ∃ ρP, listPermOf ρP {e' ∈ C.events | C.vis e' e} ∧
        respects ρP C.vis :=
    ⟨_, listPermOf_filter_subset hperm hPsub,
      List.Pairwise.sublist List.filter_sublist hresp⟩
  exact ⟨applySeq D.toCRDTSig D.init ρP, ⟨ρP, hpermP, hrespP, rfl⟩,
    hGen e ⟨r, ev, hL, he_ev⟩ ρP hpermP⟩

/-! ## §5  The reusable issuer-local discharge core

The bounded-counter discharge used only: (i) the guard reads
state components only same-replica events modify, (ii) those components are
order-free counts. Step (i)+(ii)'s joint content is this lemma: the count of
any own-replica predicate agrees between any admissible causal prefix and
the causal past, since the extras `S \ past(e)` are all cross-replica
(`vis_total_same_replica`: a same-replica extra would be vis-comparable with
`e`, and both directions are excluded). Escrow-style instances discharge
`SafetyStepOn` from this plus their per-slot fold formulas. -/

/-- Issuer-local counts are prefix-stable: under `SafetyStepOn`'s prefix
hypotheses, `countP p` agrees between enumerations of `S` and of `past(e)`
for any `p` firing only on events of `e`'s replica. -/
theorem countP_prefix_eq_causal_past {C : Configuration D}
    {E S : Set (Op D.AppOp)} {e : Op D.AppOp}
    (hEev : ∀ a ∈ E, a ∈ C.events)
    (hSsub : S ⊆ E) (heE : e ∈ E) (heS : e ∉ S)
    (hfut : ∀ x ∈ S, ¬ C.vis e x)
    (hpast : ∀ x, C.vis x e → x ∈ S)
    {ρS ρP : List (Op D.AppOp)}
    (hpS : listPermOf ρS S)
    (hpP : listPermOf ρP {e' ∈ C.events | C.vis e' e})
    (p : Op D.AppOp → Bool)
    (hp : ∀ x, p x = true → x.2.1 = e.2.1) :
    ρS.countP p = ρP.countP p := by
  have hperm : (ρS.filter p).Perm (ρP.filter p) := by
    rw [List.perm_ext_iff_of_nodup (hpS.1.filter _) (hpP.1.filter _)]
    intro x
    rw [List.mem_filter, List.mem_filter]
    constructor
    · rintro ⟨hxS, hpx⟩
      refine ⟨?_, hpx⟩
      have hxSset : x ∈ S := (hpS.2 x).mp hxS
      have hx_ev : x ∈ C.events := hEev x (hSsub hxSset)
      have he_ev : e ∈ C.events := hEev e heE
      have hne : x ≠ e := fun h => heS (h ▸ hxSset)
      obtain ⟨r₁, s₁, hL₁, hs₁⟩ := hx_ev
      obtain ⟨r₂, s₂, hL₂, hs₂⟩ := he_ev
      rcases C.vis_total_same_replica hL₁ hs₁ hL₂ hs₂ hne (hp x hpx) with
        hxe | hex
      · exact (hpP.2 x).mpr ⟨⟨r₁, s₁, hL₁, hs₁⟩, hxe⟩
      · exact absurd hex (hfut x hxSset)
    · rintro ⟨hxP, hpx⟩
      obtain ⟨_, hvis⟩ := (hpP.2 x).mp hxP
      exact ⟨(hpS.2 x).mpr (hpast x hvis), hpx⟩
  rw [List.countP_eq_length_filter, List.countP_eq_length_filter,
    hperm.length_eq]

end

/-! ## Axiom audit -/

#print axioms version_inv_of_causal_canonical
#print axioms causalCanonical_of_all_comm_rc_either
#print axioms honestAppOn_of_genHonest
#print axioms observedRegistered_of_honest_reach
#print axioms observedRegistered_of_honest_reachV

end Sal.ConditionedMRDTs
