import Sal.ConditionedMRDTs.Metatheory.GC_Safety

/-!
# Bounded-state commit GC: the clock representation swap

`GC_Safety.lean`'s `gc_safety` prunes the **payload** (the `ver` states and event sets)
while keeping the DAG **skeleton** (`parents`) verbatim. The skeleton is a total function
`Version → List Version` over allocated ids, so the pruned store still costs
`O(number of commits ever)`: `gc_safety` reclaims the payload but not the history.

The skeleton was kept for one reason (`GC_Safety` §2): the store field `lca_events`
quantifies over *all* structural LCA triples, and restricting `parents` can mint new LCA
triples (removing common ancestors weakens the domination clause) whose event sets
falsify that invariant, even though no reachable `Step3` ever queries such a pair. Two
kept interior nodes above different frontier MCAs can have all their common ancestors
dropped.

**This file removes the skeleton** by a representation swap: the
commit graph is a delta-compression of event sets, so a version's ancestry role is
carried by its event set used as a **clock**. Ancestry becomes `⊆` (pointwise `≤` on the
per-event clock), and the LCA of a head pair is the kept version at the **clock meet**
`E(v₁) ∩ E(v₂)` (this is exactly `lca_events`). The bounded store keeps only the kept
payloads and drops `parents` to the constant empty function: `lca_events` is then
discharged trivially (`Reaches (fun _ => []) = (·=·)`, so the only structural LCA is the
reflexive one), and there is no history to store.

**The lineage-collision constraint.**
Identifying the LCA by clock *alone* is sound before datatype-level compaction (the
payload is then a function of the event set) and UNSOUND after: a same-clock version from
an unrelated lineage, used as the merge's `L`, resurrects a dropped instance. The
framework's structural `IsLCA` sidesteps this because it resolves within shared ancestry.
A clock swap cannot, so it must **restrict LCA lookup to `R_S`-compatible payloads**. The
guard `ClockCoherent` ("two kept versions with the same
event-set clock carry the same state", i.e. the payload is a function of the clock on the
keep set) is precisely `R_S`-compatibility, and it is exactly what compaction threatens.
`clockLCA_sound` needs it; `spot_lineage_resurrection` witnesses the resurrection when it
is dropped.

**What is proved here.**
* `clockPrune` (§1): the bounded store, a genuine `Configuration` with `parents ≡ []` and
  `ver` supported on the keep set. `clockPrune_support` bounds the state at `O(keep-set)`.
* `ClockLCAState` (§3): the clock LCA lookup, over event sets only.
  `clockLCA_complete` shows every head pair with a structural LCA has its LCA recovered by
  the clock lookup in the bounded store (the meet is `lca_events`, and the LCA is kept by
  `lca_not_dropped`), so the swap never disables a merge the skeleton enabled.
* `clockLCA_sound` (§4): under `ClockCoherent`, every clock LCA carries the structural
  LCA's state, so the clock merge computes the same result as the structural merge.
* `Step3C` / `gc_safety_bounded` (§5): the bounded LTS runs on the clock store, every head
  run and head read is preserved, and state is bounded (no skeleton).
* §6: the machine-checked SPOT (PASS: a bounded prune whose future head-pair merge still
  finds its LCA at the clock meet and reads correctly; FAIL: the lineage resurrection).

Interaction with virtual LCAs (`gc_safetyV`, `mcasClosure`): the clock swap resolves the
**gated** merge (a single LCA = the clock meet). A **virtual** merge over a criss-cross
antichain of MCAs is a genuine DAG-order notion (the meet is not a single clock), so its
bounded-state form needs the retained lineage among the MCA closure and is left owed; see
the closing note.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

section BoundedGC

variable {D : ConditionedMRDTSig}

open Classical

/-! ## §0  Reachability over the empty skeleton -/

/-- With no edges, reachability collapses to equality: this is what makes the trivial
`lca_events` of the skeleton-free store hold (the only structural LCA is the reflexive
one). -/
theorem reaches_empty_eq {a b : Version}
    (h : Reaches (fun _ => ([] : List Version)) a b) : a = b := by
  induction h with
  | refl => rfl
  | tail _ hstep _ => exact absurd hstep List.not_mem_nil

/-! ## §1  The bounded store `clockPrune`

The clock store is `dropVer`'s payload prune (states/event sets outside `Keep'` removed)
with the DAG skeleton flattened to `parents ≡ []`. It is a genuine `Configuration`: the
only fields sensitive to `parents` are `parents_lt` (vacuous) and `lca_events`
(`reaches_empty_eq` collapses `IsLCA` to the reflexive triple, where the intersection is
`Set.inter_self`). Replica reads (`N`, `L`, `vis`) and the kept payloads are carried
verbatim from `C`. -/
open Classical in
/-- The bounded (skeleton-free) prune: `dropVer`'s payload prune with the DAG skeleton
flattened to the constant empty function. Parametrized by the drop set `S` (exactly like
`dropVer`) so the run-level simulation can prune every config along a run against the same
prune-time drop set. -/
noncomputable def flatDropVer (C : Configuration D) (S : Set Version)
    (h0 : 0 ∉ S)
    (hheads : ∀ r v, C.head r = some v → (C.ver v).isSome → v ∉ S) :
    Configuration D :=
  { dropVer C S h0 hheads with
    parents := fun _ => []
    parents_lt := by intro v p hp; exact absurd hp List.not_mem_nil
    lca_events := by
      intro v₁ v₂ vT s₁ e₁ s₂ e₂ sT eT hlca h1 h2 hT
      have hv1 : vT = v₁ := reaches_empty_eq hlca.1
      have hv2 : vT = v₂ := reaches_empty_eq hlca.2.1
      subst hv1; subst hv2
      rw [h1, Option.some.injEq, Prod.mk.injEq] at h2 hT
      obtain ⟨_, rfl⟩ := h2
      obtain ⟨_, rfl⟩ := hT
      exact (Set.inter_self e₁).symm }

@[simp] theorem flatDropVer_ver (C : Configuration D) (S : Set Version) (h0 hheads)
    (v : Version) :
    (flatDropVer C S h0 hheads).ver v = if v ∈ S then none else C.ver v := rfl

@[simp] theorem flatDropVer_parents (C : Configuration D) (S : Set Version) (h0 hheads)
    (v : Version) : (flatDropVer C S h0 hheads).parents v = [] := rfl

@[simp] theorem flatDropVer_head (C : Configuration D) (S : Set Version) (h0 hheads) :
    (flatDropVer C S h0 hheads).head = C.head := rfl

@[simp] theorem flatDropVer_N (C : Configuration D) (S : Set Version) (h0 hheads) :
    (flatDropVer C S h0 hheads).N = C.N := rfl

/-- The bounded (skeleton-free) prune of `C` at its own prune point, over `Keep'`. -/
noncomputable def clockPrune (C : Configuration D)
    (hStore : StoreInv C.ver C.parents) : Configuration D :=
  flatDropVer C (droppedSet C) (zero_not_dropped C) (heads_kept (gcInv_init C hStore))

@[simp] theorem clockPrune_ver (C : Configuration D)
    (hStore : StoreInv C.ver C.parents) (v : Version) :
    (clockPrune C hStore).ver v
      = if v ∈ droppedSet C then none else C.ver v := rfl

@[simp] theorem clockPrune_parents (C : Configuration D)
    (hStore : StoreInv C.ver C.parents) (v : Version) :
    (clockPrune C hStore).parents v = [] := rfl

@[simp] theorem clockPrune_head (C : Configuration D)
    (hStore : StoreInv C.ver C.parents) :
    (clockPrune C hStore).head = C.head := rfl

@[simp] theorem clockPrune_N (C : Configuration D)
    (hStore : StoreInv C.ver C.parents) :
    (clockPrune C hStore).N = C.N := rfl

/-! ### The state bound: `O(keep-set)` -/

/-- **The state bound.** The bounded store carries a payload only at kept versions: its
`ver` support is contained in `Keep'`. Combined with `clockPrune_parents` (the skeleton is
the constant empty function, `O(1)`), the entire store costs `O(|Keep'|)`, not
`O(number of commits ever)`. -/
theorem clockPrune_support (C : Configuration D)
    (hStore : StoreInv C.ver C.parents) {v : Version}
    (hv : (clockPrune C hStore).ver v ≠ none) : v ∈ keepSet' C := by
  rw [clockPrune_ver] at hv
  by_cases hd : v ∈ droppedSet C
  · rw [if_pos hd] at hv; exact absurd rfl hv
  · rw [if_neg hd] at hv
    by_contra hk
    exact hd ⟨Option.isSome_iff_ne_none.mpr hv, hk⟩

/-- The skeleton is gone: the bounded store's parent function is constantly empty, so no
per-commit history is retained. -/
theorem clockPrune_no_skeleton (C : Configuration D)
    (hStore : StoreInv C.ver C.parents) :
    (clockPrune C hStore).parents = fun _ => [] := rfl

/-! ## §3  The clock LCA lookup, and completeness

The merge's LCA state, read structurally as `ver vT` off the DAG (`IsLCA parents`), is
recovered from event sets alone: the LCA's clock is the pointwise **meet**
`E(v₁) ∩ E(v₂)` (this is `lca_events`). The lookup below reads only event sets, never
`parents`. -/

/-- `u` is a **clock LCA** of the head pair `(v₁, v₂)` carrying state `su`: its event-set
clock is the pointwise meet `E(v₁) ∩ E(v₂)` of the heads' clocks. Reads event sets only,
never `parents`. -/
def ClockLCA (cc : Configuration D) (v₁ v₂ u : Version) (su : D.State) : Prop :=
  ∃ s₁ e₁ s₂ e₂, cc.ver v₁ = some (s₁, e₁) ∧ cc.ver v₂ = some (s₂, e₂) ∧
    cc.ver u = some (su, e₁ ∩ e₂)

/-- **Completeness of the swap.** Every head pair with a *structural* LCA `vT` (the
premise `Step3.merge` supplies) has, in the bounded store, `vT` as a *clock* LCA carrying
the structural LCA's state `sT`. So dropping the skeleton never disables a merge the DAG
enabled: `lca_events` gives the meet, `lca_not_dropped` keeps `vT`, `heads_kept` keeps the
heads. -/
theorem clockLCA_complete (C : Configuration D) (hStore : StoreInv C.ver C.parents)
    {r₁ r₂ : Replica} {v₁ v₂ vT : Version} {s₁ s₂ sT : D.State}
    {ev₁ ev₂ evT : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁) (h_head₂ : C.head r₂ = some v₂)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (h_lca : IsLCA C.parents v₁ v₂ vT) (h_verT : C.ver vT = some (sT, evT)) :
    ClockLCA (clockPrune C hStore) v₁ v₂ vT sT := by
  have hInv := gcInv_init C hStore
  have hv1 : v₁ ∉ droppedSet C := heads_kept hInv r₁ v₁ h_head₁ (by rw [h_ver₁]; rfl)
  have hv2 : v₂ ∉ droppedSet C := heads_kept hInv r₂ v₂ h_head₂ (by rw [h_ver₂]; rfl)
  have hvT : vT ∉ droppedSet C :=
    lca_not_dropped hInv h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT
  have hmeet : evT = ev₁ ∩ ev₂ := C.lca_events h_lca h_ver₁ h_ver₂ h_verT
  refine ⟨s₁, ev₁, s₂, ev₂, ?_, ?_, ?_⟩
  · rw [clockPrune_ver, if_neg hv1]; exact h_ver₁
  · rw [clockPrune_ver, if_neg hv2]; exact h_ver₂
  · rw [clockPrune_ver, if_neg hvT, h_verT, hmeet]

/-! ## §4  The lineage guard: `R_S`-compatible payloads

Clock identification alone is unsound once datatype-level compaction exists: a same-clock
version from an unrelated lineage, used as `L`,
resurrects a dropped instance. The framework's structural `IsLCA` sidesteps this by
resolving within shared ancestry; the clock swap cannot, so it **restricts LCA lookup to
`R_S`-compatible payloads**, formalized as `ClockCoherent`. -/

/-- **The lineage guard** (`R_S`-compatibility): two kept versions with the same event-set
clock carry the same state, i.e. the payload is a function of the clock on the store.
Automatic before compaction (states are determined by their event sets); compaction is
precisely what breaks it (`spot_lineage_resurrection`). -/
def ClockCoherent (cc : Configuration D) : Prop :=
  ∀ u u' su su' e, cc.ver u = some (su, e) → cc.ver u' = some (su', e) → su = su'

/-- **Clock LCA is well-defined under the guard.** Any two clock-LCA candidates of a head
pair carry the same state: the heads pin the meet clock `E(v₁) ∩ E(v₂)`, so both share
that clock and `ClockCoherent` forces the states equal. The lookup therefore returns a
unique state regardless of which same-clock version it lands on. -/
theorem clockLCA_sound {cc : Configuration D} (hCoh : ClockCoherent cc)
    {v₁ v₂ u u' : Version} {su su' : D.State}
    (hu : ClockLCA cc v₁ v₂ u su) (hu' : ClockLCA cc v₁ v₂ u' su') : su = su' := by
  obtain ⟨s₁, e₁, s₂, e₂, hv1, hv2, hru⟩ := hu
  obtain ⟨s₁', e₁', s₂', e₂', hv1', hv2', hru'⟩ := hu'
  rw [hv1, Option.some.injEq, Prod.mk.injEq] at hv1'
  rw [hv2, Option.some.injEq, Prod.mk.injEq] at hv2'
  obtain ⟨_, rfl⟩ := hv1'
  obtain ⟨_, rfl⟩ := hv2'
  exact hCoh u u' su su' (e₁ ∩ e₂) hru hru'

/-- **The swap recovers the structural LCA state.** Under the guard, any clock LCA of a
head pair in the bounded store carries exactly the structural LCA's state: the clock meet,
resolved on `R_S`-compatible payloads, reconstructs what the dropped skeleton's `IsLCA`
would have read. This is the merge-agreement content of `gc_safety_bounded`. -/
theorem clockLCA_recovers (C : Configuration D) (hStore : StoreInv C.ver C.parents)
    (hCoh : ClockCoherent (clockPrune C hStore))
    {r₁ r₂ : Replica} {v₁ v₂ vT u : Version} {s₁ s₂ sT su : D.State}
    {ev₁ ev₂ evT : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁) (h_head₂ : C.head r₂ = some v₂)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (h_lca : IsLCA C.parents v₁ v₂ vT) (h_verT : C.ver vT = some (sT, evT))
    (hu : ClockLCA (clockPrune C hStore) v₁ v₂ u su) : su = sT :=
  clockLCA_sound hCoh hu
    (clockLCA_complete C hStore h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT)

/-! ## §5  The bounded LTS `Step3C` and the run simulation

`Step3C` is `Step3` on the bounded store: every rule **freezes `parents`** (the skeleton
never grows, so the bounded store stays skeleton-free along a run), and Merge reads its LCA
state by the **clock lookup** (`ClockLCA`) rather than the structural `IsLCA` and stored
`ver vT`. Every other premise is verbatim `Step3`. -/

/-- The ternary step relation on the bounded store: `parents` frozen, Merge clock-gated. -/
inductive Step3C (D : ConditionedMRDTSig) :
    Configuration D → Label3 D → Configuration D → Prop where
  | createReplica {C : Configuration D} {r : Replica}
      (h_fresh : C.N r = none)
      (C' : Configuration D)
      (hN : C'.N = updateRep C.N r D.init)
      (hL : C'.L = updateRep C.L r ∅)
      (hvis : C'.vis = C.vis)
      (hver : C'.ver = C.ver)
      (hhead : C'.head = fun r' => if r' = r then some 0 else C.head r')
      (hparents : C'.parents = C.parents) :
      Step3C D C (.createReplica r) C'
  | apply {C : Configuration D} {t : Timestamp} {r : Replica} {o : D.AppOp}
      {v : Version} {s : D.State} {ev : Set (Op D.AppOp)} {vnew : Version}
      (h_head : C.head r = some v)
      (h_ver : C.ver v = some (s, ev))
      (h_fresh_t : ∀ e', e' ∈ C.events → Op.time e' ≠ t)
      (h_fresh_store : ∀ w sw Ew, C.ver w = some (sw, Ew) →
        ∀ e' ∈ Ew, Op.time e' ≠ t)
      (h_vnew : C.ver vnew = none)
      (h_rank : v < vnew)
      (C' : Configuration D)
      (hN : C'.N = updateRep C.N r (D.update s (t, r, o)))
      (hL : C'.L = updateRep C.L r (ev ∪ {(t, r, o)}))
      (hvis : C'.vis = fun a b => C.vis a b ∨ (ev a ∧ b = (t, r, o)))
      (hver : C'.ver = fun w => if w = vnew
        then some (D.update s (t, r, o), ev ∪ {(t, r, o)}) else C.ver w)
      (hhead : C'.head = fun r' => if r' = r then some vnew else C.head r')
      (hparents : C'.parents = C.parents) :
      Step3C D C (.apply t r o) C'
  /-- **Merge, clock-gated**: the LCA state `sT` is read by the clock lookup `ClockLCA`
  (event-set meet), not from the (dropped) skeleton. -/
  | merge {C : Configuration D} {r₁ r₂ : Replica}
      {v₁ v₂ vT vm : Version} {s₁ s₂ sT : D.State}
      {ev₁ ev₂ : Set (Op D.AppOp)}
      (h_head₁ : C.head r₁ = some v₁) (h_head₂ : C.head r₂ = some v₂)
      (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
      (h_clca : ClockLCA C v₁ v₂ vT sT)
      (h_vm : C.ver vm = none)
      (h_rank₁ : v₁ < vm) (h_rank₂ : v₂ < vm)
      (C' : Configuration D)
      (hN : C'.N = updateRep C.N r₁ (D.mergeL sT s₁ s₂))
      (hL : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
      (hvis : C'.vis = C.vis)
      (hver : C'.ver = fun w => if w = vm
        then some (D.mergeL sT s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
      (hhead : C'.head = fun r' => if r' = r₁ then some vm else C.head r')
      (hparents : C'.parents = C.parents) :
      Step3C D C (.merge r₁ r₂) C'
  | query {C : Configuration D} {r : Replica} {q : D.Query}
      {v : D.Value} {s : D.State}
      (h_s : C.N r = some s)
      (h_val : v = D.query s q) :
      Step3C D C (.query r q v) C

/-- The bounded ternary LTS. -/
def labeledTS3C (D : ConditionedMRDTSig) : LabeledTS where
  State := Configuration D
  Label := Label3 D
  step := Step3C D
  silent := fun _ => False

/-- **Single-step simulation.** Every `Step3` step on the skeleton is matched, same label,
by a `Step3C` step on the bounded (`flatDropVer`) images. Non-merge cases are `step_dropVer`
verbatim over the flattened store; Merge's structural `IsLCA`/`ver vT` read is replaced by
the clock lookup (`clockLCA_complete`'s construction at the fixed prune point), and every
rule's frozen `parents` is `rfl` (both sides are the empty skeleton). -/
theorem step_clockFlat {C₀ C C' : Configuration D} {ℓ : Label3 D}
    (hInv : GCInv C₀ C) (hstep : Step3 D C ℓ C')
    (hh' : ∀ r v, C'.head r = some v → (C'.ver v).isSome → v ∉ droppedSet C₀) :
    Step3C D (flatDropVer C (droppedSet C₀) (zero_not_dropped C₀) (heads_kept hInv)) ℓ
      (flatDropVer C' (droppedSet C₀) (zero_not_dropped C₀) hh') := by
  cases hstep with
  | @createReplica r h_fresh C' hN hL hvis hver hhead hparents =>
    refine Step3C.createReplica ?_ _ ?_ ?_ ?_ ?_ ?_ ?_
    · exact h_fresh
    · exact hN
    · exact hL
    · exact hvis
    · funext w; simp only [flatDropVer_ver, hver]
    · exact hhead
    · rfl
  | @apply t r o v s ev vnew h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank
      C' hN hL hvis hver hhead hparents =>
    have hvKeep : v ∉ droppedSet C₀ :=
      heads_kept hInv r v h_head (by rw [h_ver]; rfl)
    have hvnewKeep : vnew ∉ droppedSet C₀ := fun hm =>
      not_alloc₀_of_fresh hInv h_vnew hm.1
    refine Step3C.apply (v := v) (s := s) (ev := ev) (vnew := vnew)
      ?_ ?_ ?_ ?_ ?_ h_rank _ ?_ ?_ ?_ ?_ ?_ ?_
    · exact h_head
    · show (if v ∈ droppedSet C₀ then none else C.ver v) = some (s, ev)
      rw [if_neg hvKeep]; exact h_ver
    · exact h_fresh_t
    · intro w sw Ew hw
      by_cases hwS : w ∈ droppedSet C₀
      · rw [flatDropVer_ver, if_pos hwS] at hw; cases hw
      · rw [flatDropVer_ver, if_neg hwS] at hw
        exact h_fresh_store w sw Ew hw
    · show (if vnew ∈ droppedSet C₀ then none else C.ver vnew) = none
      rw [if_neg hvnewKeep]; exact h_vnew
    · exact hN
    · exact hL
    · exact hvis
    · funext w
      simp only [flatDropVer_ver, hver]
      by_cases hw : w = vnew
      · subst hw; simp [hvnewKeep]
      · simp [hw]
    · exact hhead
    · rfl
  | @merge r₁ r₂ v₁ v₂ vT vm s₁ s₂ sT ev₁ ev₂ evT h_head₁ h_head₂ h_ver₁ h_ver₂
      h_lca h_verT h_vm h_rank₁ h_rank₂ C' hN hL hvis hver hhead hparents =>
    have hv₁Keep : v₁ ∉ droppedSet C₀ :=
      heads_kept hInv r₁ v₁ h_head₁ (by rw [h_ver₁]; rfl)
    have hv₂Keep : v₂ ∉ droppedSet C₀ :=
      heads_kept hInv r₂ v₂ h_head₂ (by rw [h_ver₂]; rfl)
    have hvTKeep : vT ∉ droppedSet C₀ :=
      lca_not_dropped hInv h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca h_verT
    have hvmKeep : vm ∉ droppedSet C₀ := fun hm =>
      not_alloc₀_of_fresh hInv h_vm hm.1
    have hmeet : evT = ev₁ ∩ ev₂ := C.lca_events h_lca h_ver₁ h_ver₂ h_verT
    refine Step3C.merge (v₁ := v₁) (v₂ := v₂) (vT := vT) (vm := vm)
      (s₁ := s₁) (s₂ := s₂) (sT := sT) (ev₁ := ev₁) (ev₂ := ev₂)
      ?_ ?_ ?_ ?_ ?_ ?_ h_rank₁ h_rank₂ _ ?_ ?_ ?_ ?_ ?_ ?_
    · exact h_head₁
    · exact h_head₂
    · show (if v₁ ∈ droppedSet C₀ then none else C.ver v₁) = some (s₁, ev₁)
      rw [if_neg hv₁Keep]; exact h_ver₁
    · show (if v₂ ∈ droppedSet C₀ then none else C.ver v₂) = some (s₂, ev₂)
      rw [if_neg hv₂Keep]; exact h_ver₂
    · refine ⟨s₁, ev₁, s₂, ev₂, ?_, ?_, ?_⟩
      · show (if v₁ ∈ droppedSet C₀ then none else C.ver v₁) = some (s₁, ev₁)
        rw [if_neg hv₁Keep]; exact h_ver₁
      · show (if v₂ ∈ droppedSet C₀ then none else C.ver v₂) = some (s₂, ev₂)
        rw [if_neg hv₂Keep]; exact h_ver₂
      · show (if vT ∈ droppedSet C₀ then none else C.ver vT) = some (sT, ev₁ ∩ ev₂)
        rw [if_neg hvTKeep, h_verT, hmeet]
    · show (if vm ∈ droppedSet C₀ then none else C.ver vm) = none
      rw [if_neg hvmKeep]; exact h_vm
    · exact hN
    · exact hL
    · exact hvis
    · funext w
      simp only [flatDropVer_ver, hver]
      by_cases hw : w = vm
      · subst hw; simp [hvmKeep]
      · simp [hw]
    · exact hhead
    · rfl
  | @query r q v s h_s h_val =>
    refine Step3C.query (s := s) ?_ ?_
    · exact h_s
    · exact h_val

/-- A labelled `Step3C` run (finite trace on the bounded LTS). -/
inductive StepsC (D : ConditionedMRDTSig) :
    Configuration D → List (Label3 D) → Configuration D → Prop where
  | nil (C : Configuration D) : StepsC D C [] C
  | cons {C C' C'' : Configuration D} {ℓ : Label3 D} {ℓs : List (Label3 D)} :
      Step3C D C ℓ C' → StepsC D C' ℓs C'' → StepsC D C (ℓ :: ℓs) C''

/-- **Run-level simulation.** The whole `Step3` trace transports, label for label, to a
`Step3C` trace on the bounded images. -/
theorem steps_clockFlat {C₀ : Configuration D} {C ℓs C'}
    (hrun : Steps D C ℓs C') (hInv : GCInv C₀ C)
    (hh : ∀ r v, C.head r = some v → (C.ver v).isSome → v ∉ droppedSet C₀)
    (hh' : ∀ r v, C'.head r = some v → (C'.ver v).isSome → v ∉ droppedSet C₀) :
    StepsC D (flatDropVer C (droppedSet C₀) (zero_not_dropped C₀) hh) ℓs
      (flatDropVer C' (droppedSet C₀) (zero_not_dropped C₀) hh') := by
  induction hrun with
  | nil => exact StepsC.nil _
  | @cons Ca Cb Cc ℓ ℓs hstep hrest ih =>
    exact StepsC.cons
      (step_clockFlat hInv hstep (heads_kept (gcInv_step hInv hstep)))
      (ih (gcInv_step hInv hstep) (heads_kept (gcInv_step hInv hstep)) hh')

/-! ## §5.1  The main theorem `gc_safety_bounded` -/

/-- **Bounded-state commit GC.** Pruning to the clock store
`clockPrune C₀` (the keep-set payloads, DAG skeleton dropped) over the keep set `Keep'`:

1. **preserves every head run** — the entire `Step3` trace replays, label for label, on the
   bounded LTS `Step3C` (Merge resolves its LCA state by the clock meet, `clockLCA_complete`,
   not by the dropped skeleton);
2. **preserves every head read** — the transported run's `N` agrees with `C`'s at every
   replica, at every point (definitional, `flatDropVer_N`);
3. **bounds state at `O(|Keep'|)`** — the clock store's `ver` support is contained in
   `Keep'` (`clockPrune_support`) and its skeleton is the constant empty function
   (`clockPrune_parents`), so it costs `O(number of live commits)`, not
   `O(number of commits ever)`.

The single hypothesis is `StoreInv C₀` (supplied by plain reachability,
`storeInv_reachable`). The merge results replayed here are the *structural* LCA states
(`step_clockFlat` witnesses each clock LCA by the true `vT`); that the bounded LTS is
moreover deterministic on the merge state — no unrelated-lineage clock collision resurrects
a dropped instance — is `clockLCA_recovers` under the `ClockCoherent` (`R_S`-compatible)
guard, with `spot_lineage_resurrection` the countermodel when the guard is dropped. -/
theorem gc_safety_bounded (C₀ : Configuration D) (hStore : StoreInv C₀.ver C₀.parents)
    {ℓs : List (Label3 D)} {C : Configuration D} (hRun : Steps D C₀ ℓs C) :
    StepsC D (clockPrune C₀ hStore) ℓs
      (flatDropVer C (droppedSet C₀) (zero_not_dropped C₀)
        (heads_kept (gcInv_steps hRun (gcInv_init C₀ hStore))))
    ∧ (∀ r, (flatDropVer C (droppedSet C₀) (zero_not_dropped C₀)
        (heads_kept (gcInv_steps hRun (gcInv_init C₀ hStore)))).N r = C.N r)
    ∧ (∀ v, (clockPrune C₀ hStore).ver v ≠ none → v ∈ keepSet' C₀)
    ∧ (∀ v, (clockPrune C₀ hStore).parents v = []) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact steps_clockFlat hRun (gcInv_init C₀ hStore)
      (heads_kept (gcInv_init C₀ hStore)) _
  · intro _; rfl
  · intro v hv; exact clockPrune_support C₀ hStore hv
  · intro v; rfl

#print axioms gc_safety_bounded

end BoundedGC

/-! ## §6  SPOT: the clock swap and the lineage-collision countermodel

Two concrete verdicts over `GSetCond`, both hand-derived (never `#eval`'d).

**PASS** reuses `GCSpot.Cex` (the §7 store of `GC_Safety`, pre-compaction, so the payload
is a function of the event set): the future head-pair merge of heads `4, 5` finds its LCA
at the clock meet `E(4) ∩ E(5) = {e1,e2} = E(2)`, and the bounded store still carries
`(S2, {e1,e2})` at version `2`, so the merge reads the correct LCA state with no skeleton.

**FAIL** (the lineage resurrection): a *compacted* store
`Ccoll` where two versions share the event-set clock `{a1,…}` but carry different states
(`{10}` on the kept lineage, `∅` on the compacted lineage). The clock lookup for the head
pair `(3,4)` — whose meet clock is exactly that shared clock — returns *both* states, so
clock identification alone resurrects the dropped `10` (or drops it) depending on the
lineage it lands on. This is why the swap must restrict to `R_S`-compatible payloads:
`ClockCoherent Ccoll` is provably false. -/

namespace BoundedSpot

open GCSpot

/-! ### PASS: the clock meet recovers the structural LCA on the coherent store -/

/-- Hand-derived: `E(4) ∩ E(5) = F2` (both `⊆` directions). Pins the meet away from the
degenerate `∅` (`spot_meet_nonempty`). -/
theorem spot_meet_eq : F4 ∩ F5 = F2 := by
  apply Set.Subset.antisymm F45_sub_F2
  intro x hx
  simp only [F2, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact ⟨Or.inl rfl, Or.inl rfl⟩
  · exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inl rfl)⟩

/-- **SPOT PASS**: in the bounded (skeleton-free) prune of `Cex`, the head pair `(4,5)`
has version `2` as its *clock* LCA at the meet `F4 ∩ F5`, carrying the hand-derived state
`S2`. The structural skeleton has been dropped; the LCA is found by event sets alone. -/
theorem spot_clock_lca_pass :
    ClockLCA (clockPrune Cex storeInvEx) 4 5 2 S2 :=
  clockLCA_complete Cex storeInvEx (r₁ := 0) (r₂ := 1)
    rfl rfl verEx4 verEx5 spot_isLCA verEx2

open Classical in
/-- **SPOT PASS, read pinned**: the bounded store still registers the LCA `(S2, F2)` at
version `2` (the merge reads it correctly), while the dropped version `1` is genuinely
absent (`spot_bounded_dropped`). -/
theorem spot_clock_lca_present :
    (clockPrune Cex storeInvEx).ver 2 = some (S2, F2) := by
  show (if (2 : Version) ∈ droppedSet Cex then none else Cex.ver 2) = some (S2, F2)
  rw [if_neg two_not_dropped]; rfl

open Classical in
/-- **SPOT FAIL-companion (bound is strict)**: the skeleton is gone (parents empty) and the
strictly-dropped version `1` carries no payload in the bounded store. -/
theorem spot_bounded_dropped :
    (clockPrune Cex storeInvEx).ver 1 = none ∧
    (clockPrune Cex storeInvEx).parents 3 = [] := by
  refine ⟨?_, rfl⟩
  show (if (1 : Version) ∈ droppedSet Cex then none else Cex.ver 1) = none
  rw [if_pos one_dropped]

/-- **SPOT FAIL-companion (non-degeneracy)**: the meet is not the degenerate empty clock,
and the recovered LCA state `S2` is neither head's state (not a projection of an input). -/
theorem spot_meet_nonempty : F4 ∩ F5 ≠ (∅ : Set O) ∧ S2 ≠ S4 ∧ S2 ≠ S5 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have : e1 ∈ F4 ∩ F5 := ⟨Or.inl rfl, Or.inl rfl⟩
    rw [h] at this; exact this
  · intro h
    have h30 : (30 : Nat) ∈ S4 := Or.inr (Or.inr rfl)
    rw [← h] at h30
    simp only [S2, Set.mem_insert_iff, Set.mem_singleton_iff] at h30
    rcases h30 with h | h <;> exact absurd h (by decide)
  · intro h
    have h40 : (40 : Nat) ∈ S5 := Or.inr (Or.inr rfl)
    rw [← h] at h40
    simp only [S2, Set.mem_insert_iff, Set.mem_singleton_iff] at h40
    rcases h40 with h | h <;> exact absurd h (by decide)

/-! ### FAIL: the lineage-collision resurrection on a compacted store -/

/-- Ops for the collision store (distinct timestamps). -/
abbrev O' := Op GSetCond.AppOp
def a1 : O' := (1, 0, (10 : Nat))
def a2 : O' := (2, 0, (20 : Nat))
def a3 : O' := (3, 0, (30 : Nat))

def St10 : Set Nat := {10}
def Ehead3 : Set O' := {a1, a2}
def Ehead4 : Set O' := {a1, a3}

/-- The compacted store. Version `1` (kept lineage) and version `2` (compacted lineage)
share the clock `Ehead3 ∩ Ehead4` but carry different states (`{10}` vs `∅`); versions
`3, 4` are the heads whose meet is exactly that shared clock. -/
noncomputable def verColl : Version → Option (GSetCond.State × Set O') := fun v =>
  if v = 0 then some ((∅ : Set Nat), (∅ : Set O'))
  else if v = 1 then some (St10, Ehead3 ∩ Ehead4)
  else if v = 2 then some ((∅ : Set Nat), Ehead3 ∩ Ehead4)
  else if v = 3 then some ((∅ : Set Nat), Ehead3)
  else if v = 4 then some ((∅ : Set Nat), Ehead4)
  else none

/-- The compacted configuration: an inert core (no replicas, no visibility) with the
collision store and the empty skeleton. Not reachable; it models a store *after*
datatype-level compaction, exactly where clock identification loses lineage. -/
noncomputable def Ccoll : Configuration GSetCond where
  N := fun _ => none
  L := fun _ => none
  vis := fun _ _ => False
  dom_eq := by intro r; exact iff_of_true rfl rfl
  vis_src := fun h => absurd h id
  vis_tgt := fun h => absurd h id
  vis_causal := fun h _ _ => absurd h id
  timestamps_distinct := by
    intro a b r s r' s' hL _ _ _ _
    have hL' : (none : Option (Set (Op GSetCond.AppOp))) = some s := hL
    simp at hL'
  causal_mono := fun h => absurd h id
  vis_total_same_replica := by
    intro a b r s r' s' hL _ _ _ _ _
    have hL' : (none : Option (Set (Op GSetCond.AppOp))) = some s := hL
    simp at hL'
  ver := verColl
  head := fun _ => none
  parents := fun _ => []
  parents_lt := by intro v p hp; exact absurd hp List.not_mem_nil
  ver_init := rfl
  head_coherent := by
    intro r v hr
    have hr' : (none : Option Version) = some v := hr
    simp at hr'
  ver_inv := fun _ _ _ _ => trivial
  lca_events := by
    intro v₁ v₂ vT s₁ e₁ s₂ e₂ sT eT hlca h1 h2 hT
    have hv1 : vT = v₁ := reaches_empty_eq hlca.1
    have hv2 : vT = v₂ := reaches_empty_eq hlca.2.1
    subst hv1; subst hv2
    rw [h1, Option.some.injEq, Prod.mk.injEq] at h2 hT
    obtain ⟨_, rfl⟩ := h2
    obtain ⟨_, rfl⟩ := hT
    exact (Set.inter_self e₁).symm

theorem verColl3 : Ccoll.ver 3 = some ((∅ : Set Nat), Ehead3) := rfl
theorem verColl4 : Ccoll.ver 4 = some ((∅ : Set Nat), Ehead4) := rfl
theorem verColl1 : Ccoll.ver 1 = some (St10, Ehead3 ∩ Ehead4) := rfl
theorem verColl2 : Ccoll.ver 2 = some ((∅ : Set Nat), Ehead3 ∩ Ehead4) := rfl

/-- The kept lineage's state carries `10`; the compacted one does not. -/
theorem St10_ne_empty : St10 ≠ (∅ : Set Nat) := by
  intro h
  have : (10 : Nat) ∈ St10 := rfl
  rw [h] at this; exact this

/-- **SPOT FAIL: the lineage resurrection.** For the same head pair `(3,4)` in the
compacted store, the clock lookup returns version `1` with state `{10}` AND version `2`
with state `∅`: identical clock (the meet `Ehead3 ∩ Ehead4`), divergent state. Clock
identification alone resurrects the dropped `10` (picking `1`) or loses it (picking `2`),
and the guard `ClockCoherent` is provably false. -/
theorem spot_lineage_resurrection :
    ClockLCA Ccoll 3 4 1 St10 ∧ ClockLCA Ccoll 3 4 2 (∅ : Set Nat) ∧
    St10 ≠ (∅ : Set Nat) ∧ ¬ ClockCoherent Ccoll := by
  refine ⟨⟨_, Ehead3, _, Ehead4, verColl3, verColl4, verColl1⟩,
          ⟨_, Ehead3, _, Ehead4, verColl3, verColl4, verColl2⟩,
          St10_ne_empty, ?_⟩
  intro hCoh
  exact St10_ne_empty (hCoh 1 2 St10 (∅ : Set Nat) (Ehead3 ∩ Ehead4) verColl1 verColl2)

/-- Conversely, had the guard held (`R_S`-compatible payloads), `clockLCA_sound` would have
forced the two lookups equal: the resurrection is exactly the guard's failure. -/
theorem spot_guard_would_fix
    (hCoh : ClockCoherent Ccoll) : St10 = (∅ : Set Nat) :=
  clockLCA_sound hCoh
    (⟨_, Ehead3, _, Ehead4, verColl3, verColl4, verColl1⟩ : ClockLCA Ccoll 3 4 1 St10)
    (⟨_, Ehead3, _, Ehead4, verColl3, verColl4, verColl2⟩ :
      ClockLCA Ccoll 3 4 2 (∅ : Set Nat))

/-! ### Axiom audit -/

#print axioms spot_clock_lca_pass
#print axioms spot_lineage_resurrection
#print axioms spot_guard_would_fix

end BoundedSpot

end Sal.ConditionedMRDTs
