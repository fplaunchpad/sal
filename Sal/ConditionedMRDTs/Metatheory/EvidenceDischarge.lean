import Sal.ConditionedMRDTs.Metatheory.Stability_VC
import Sal.ConditionedMRDTs.Metatheory.GC_Safety
import Sal.ConditionedMRDTs.Metatheory.HonestReach

/-!
# Discharging `SettledAt` from honest reachability and the all-heads frontier

The stability GC (`Stability_VC.lean`) leaves `SettledAt` a *hypothesis*: the
callback bundle `StabilityVC` carries a `gate` obligated only to imply `SettledAt`
(`gate_settled`), and every instance (e.g. the OR-set, `ORSet_Stability.lean`)
supplies it as a raw conjunct of its gate. This file discharges that hypothesis at
every honestly reachable configuration from the runtime's *observable* knowledge,
the all-heads causal frontier, so the stability capstones hold
unconditionally at every reachable all-heard configuration.

**The design** (causal stability, Baquero-Almeida-Shoker, on the commit DAG). For a
configuration `C`, a version `v`, and a cut `S`, `AllHeardSince C v S` says: for every
replica `j` *registered* in `C`, `v`'s ancestry contains an **evidence commit** `c_j`
(a version reaching `v`) whose event set contains `S` and which certifies that every
later `j`-event has all of `S` in its causal past (`EvidenceCommit`,
commit-shaped: a no-new-events pull still carries `c_j`, so this is stated over
*ancestry*, not event-subsumption of the pull).

**The claim** (`settledAt_of_allHeard`): on an honestly reachable `C`,
`AllHeardSince C v S` implies `SettledAt C v S`. Proof: an event `e` concurrent with
some `s ∈ S`, existing in `C`, is minted by some replica `j`, which is registered
(`authorsRegistered`); `j`'s evidence commit `c_j` has `S ⊆ E(c_j) ⊆ E(v)`; either
`e ∈ E(c_j) ⊆ E(v)` (done), or `c_j`'s certification puts all of `S` before `e`,
contradicting `e ‖ s`. The concurrency step is exactly `settledAtOn_of_evidence`
(proved in `Stability_VC.lean`, consuming `StoreInv.events_mono`); this file
supplies the configuration-level quantifier and the two reachability facts it needs
(every event author is a registered replica; the root replica is registered).

**Layering.** Metatheory only (imports `Stability_VC`, `GC_Safety`); the all-heads
frontier here is the same frontier `gc_safety` prunes to. No `MRDT_Instances` import,
so the OR-set payoff (§5) is stated generically over `StabilityVC`/`StabReach`, not
against the concrete `orStabilityVC` bundle.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

section Discharge

variable {D : ConditionedMRDTSig}

/-! ## §0 `updateRep` and event-membership plumbing -/

/-- `updateRep` applied at a point (definitional). -/
@[simp] theorem updateRep_apply {α} (f : Replica → Option α) (r j : Replica) (x : α) :
    updateRep f r x j = if j = r then some x else f j := rfl

/-- Allocation of a replica head is monotone under a point update. -/
theorem updateRep_isSome {α} {f : Replica → Option α} {r j : Replica} {x : α}
    (hj : (f j).isSome) : (updateRep f r x j).isSome := by
  rw [updateRep_apply]
  by_cases h : j = r
  · rw [if_pos h]; rfl
  · rw [if_neg h]; exact hj

/-- The freshly-updated slot is allocated. -/
theorem updateRep_isSome_self {α} (f : Replica → Option α) (r : Replica) (x : α) :
    (updateRep f r x r).isSome := by
  rw [updateRep_apply, if_pos rfl]; rfl

/-- An event of a replica's head version is witnessed in the configuration. -/
theorem mem_events_of_head {C : Configuration D} {r : Replica} {v : Version}
    {s : D.State} {e : Set (Op D.AppOp)} {x : Op D.AppOp}
    (h_head : C.head r = some v) (h_ver : C.ver v = some (s, e)) (hx : x ∈ e) :
    x ∈ C.events := by
  have hL : C.L r = some e := by
    have h2 := (C.head_coherent r v h_head).2
    rw [h_ver] at h2
    exact h2.symm
  exact ⟨r, e, hL, hx⟩

/-! ## §1 Registered replicas; the author-registration reachability invariant

`settledAtOn_of_evidence` needs a covered replica set `J` with `∀ e ∈ events, rep e ∈ J`.
The canonical choice is the *registered* replicas, `Registered C j := (C.N j).isSome`.
That every event author is registered, and that the root replica `0` stays registered
(so the cut sits below at least one commit), are reachability invariants, packaged in
`ReachInvE` and proved by a single `Step3` induction reusing `storeInv_step`. -/

/-- Replica `j` is registered in `C` (has a head state). -/
def Registered (C : Configuration D) (j : Replica) : Prop := (C.N j).isSome

/-- Every event witnessed in `C` was authored by a registered replica. -/
def AuthorsRegistered (C : Configuration D) : Prop :=
  ∀ e ∈ C.events, Registered C (Op.rep e)

/-- Registration is monotone along a `Step3` step (`N` only grows). -/
theorem nSome_step {C C' : Configuration D} {ℓ : Label3 D} {j : Replica}
    (hstep : Step3 D C ℓ C') (hj : (C.N j).isSome) : (C'.N j).isSome := by
  cases hstep with
  | createReplica h_fresh C' hN hL hvis hver hhead hparents =>
    rw [hN]; exact updateRep_isSome hj
  | @apply t r o v s ev vnew h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank
      C' hN hL hvis hver hhead hparents =>
    rw [hN]; exact updateRep_isSome hj
  | @merge r₁ r₂ v₁ v₂ vT vm s₁ s₂ sT ev₁ ev₂ evT h_head₁ h_head₂ h_ver₁ h_ver₂
      h_lca h_verT h_vm h_rank₁ h_rank₂ C' hN hL hvis hver hhead hparents =>
    rw [hN]; exact updateRep_isSome hj
  | query h_s h_val => exact hj

/-- `AuthorsRegistered` is a `Step3` invariant: a fresh mint's author is the (already
registered) minting replica; every other event is inherited and `N` only grows. -/
theorem authorsReg_step {C C' : Configuration D} {ℓ : Label3 D}
    (hstep : Step3 D C ℓ C') (h : AuthorsRegistered C) : AuthorsRegistered C' := by
  cases hstep with
  | @createReplica r h_fresh C' hN hL hvis hver hhead hparents =>
    intro x hx
    obtain ⟨r', s', hL', hs'⟩ := hx
    rw [hL, updateRep_apply] at hL'
    show (C'.N (Op.rep x)).isSome
    rw [hN]
    by_cases hr : r' = r
    · rw [if_pos hr] at hL'
      injection hL' with hL'
      subst hL'
      exact absurd hs' (Set.notMem_empty x)
    · rw [if_neg hr] at hL'
      exact updateRep_isSome (h x ⟨r', s', hL', hs'⟩)
  | @apply t r o v s ev vnew h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank
      C' hN hL hvis hver hhead hparents =>
    intro x hx
    obtain ⟨r', s', hL', hs'⟩ := hx
    rw [hL, updateRep_apply] at hL'
    show (C'.N (Op.rep x)).isSome
    rw [hN]
    by_cases hr : r' = r
    · rw [if_pos hr] at hL'
      injection hL' with hL'
      subst hL'
      rcases hs' with hxev | hxnew
      · exact updateRep_isSome (h x (mem_events_of_head h_head h_ver hxev))
      · rw [Set.mem_singleton_iff] at hxnew
        subst hxnew
        show (updateRep C.N r (D.update s (t, r, o)) (Op.rep ((t, r, o) : Op D.AppOp))).isSome
        have hrep : Op.rep ((t, r, o) : Op D.AppOp) = r := rfl
        rw [hrep]
        exact updateRep_isSome_self _ _ _
    · rw [if_neg hr] at hL'
      exact updateRep_isSome (h x ⟨r', s', hL', hs'⟩)
  | @merge r₁ r₂ v₁ v₂ vT vm s₁ s₂ sT ev₁ ev₂ evT h_head₁ h_head₂ h_ver₁ h_ver₂
      h_lca h_verT h_vm h_rank₁ h_rank₂ C' hN hL hvis hver hhead hparents =>
    intro x hx
    obtain ⟨r', s', hL', hs'⟩ := hx
    rw [hL, updateRep_apply] at hL'
    show (C'.N (Op.rep x)).isSome
    rw [hN]
    by_cases hr : r' = r₁
    · rw [if_pos hr] at hL'
      injection hL' with hL'
      subst hL'
      rcases hs' with hx1 | hx2
      · exact updateRep_isSome (h x (mem_events_of_head h_head₁ h_ver₁ hx1))
      · exact updateRep_isSome (h x (mem_events_of_head h_head₂ h_ver₂ hx2))
    · rw [if_neg hr] at hL'
      exact updateRep_isSome (h x ⟨r', s', hL', hs'⟩)
  | query h_s h_val => exact h

/-- **The evidence-discharge reachability bundle**: `StoreInv` (for `events_mono`),
author-registration (for the covered-replica quantifier), and root-registration (so the
cut sits below at least one commit, giving `S ⊆ E(v)`). -/
structure ReachInvE (C : Configuration D) : Prop where
  store : StoreInv C.ver C.parents
  authors : AuthorsRegistered C
  root : Registered C 0

theorem reachInvE_init (hInit : D.Inv D.init) : ReachInvE (initConfig D hInit) where
  store := storeInv_init hInit
  authors := by
    intro x hx
    obtain ⟨r, s, hL, hs⟩ := hx
    have hL0 : (initConfig D hInit).L r
        = if r = 0 then some (∅ : Set (Op D.AppOp)) else none := rfl
    rw [hL0] at hL
    by_cases hr : r = 0
    · rw [if_pos hr] at hL
      injection hL with hL; subst hL
      exact absurd hs (Set.notMem_empty x)
    · rw [if_neg hr] at hL; cases hL
  root := by
    show ((initConfig D hInit).N 0).isSome
    have h0 : (initConfig D hInit).N 0 = some D.init := rfl
    rw [h0]; rfl

theorem reachInvE_step {C C' : Configuration D} {ℓ : Label3 D}
    (h : ReachInvE C) (hstep : Step3 D C ℓ C') : ReachInvE C' where
  store := storeInv_step hstep h.store
  authors := authorsReg_step hstep h.authors
  root := nSome_step hstep h.root

open LabeledTS in
/-- `ReachInvE` at every LTS-reachable configuration. -/
theorem reachInvE_reachable {hInit : D.Inv D.init} {C : Configuration D}
    (hReach : (labeledTS3 D).ReachableFrom (initConfig D hInit) C) : ReachInvE C := by
  induction hReach with
  | refl => exact reachInvE_init hInit
  | tail _ hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    exact reachInvE_step ih hstep

/-- `ReachInvE` at every honestly reachable configuration (honest reach ⊆ reach). -/
theorem reachInvE_honestReach {H : Configuration D → Prop} {hInit : D.Inv D.init}
    {C : Configuration D} (hReach : HonestReach D H hInit C) : ReachInvE C := by
  induction hReach with
  | init => exact reachInvE_init hInit
  | step _ _ hstep ih => exact reachInvE_step ih hstep

/-! ## §2 `AllHeardSince` and the discharge of `SettledAt`

`AllHeardSince C v S`: the runtime has learned that **every registered replica** has
an evidence commit for the cut `S` inside `v`'s ancestry (commit-shaped).
This is exactly the covered-replica hypothesis of `settledAtOn_of_evidence`, quantified
over the registered set; `ReachInvE` supplies the two reachability facts that convert it
into the semantic `SettledAt`. -/

/-- **The configuration-level all-heard-since predicate.** For every registered replica
`j`, version `v`'s ancestry contains a commit certifying `j` heard all of `S`. -/
def AllHeardSince (C : Configuration D) (v : Version) (S : Set (Op D.AppOp)) : Prop :=
  ∀ j, Registered C j → EvidenceCommit C v S j

/-- **The claim** (`SettledAtOn` form): on a config satisfying `ReachInvE`,
`AllHeardSince C v S` implies the semantic concurrency-containment condition. `S ⊆ E(v)`
is read off the root replica's evidence commit (below `v`), and the concurrency step is
`settledAtOn_of_evidence` with the covered set taken to be the registered replicas
(covered by `ReachInvE.authors`). -/
theorem settledAtOn_of_allHeard {C : Configuration D} (hInvE : ReachInvE C)
    {v : Version} {s : D.State} {E S : Set (Op D.AppOp)}
    (hv : C.ver v = some (s, E))
    (hdown : ∀ a b, C.vis a b → b ∈ S → a ∈ S)
    (hAll : AllHeardSince C v S) :
    SettledAtOn C E S := by
  obtain ⟨c, sc, Ec, hreach, hc, hSc, _hcert⟩ := hAll 0 hInvE.root
  have hEcE : Ec ⊆ E := storeInv_events_mono_reaches hInvE.store hreach hc hv
  have hsub : S ⊆ E := hSc.trans hEcE
  exact settledAtOn_of_evidence hInvE.store hv hsub hdown
    (J := {j | Registered C j}) hInvE.authors hAll

/-- **The payoff, version-level** (`settledAt_of_allHeard`): the `SettledAt C v S` that
`StabilityVC.gate_settled` demands, derived from the frontier knowledge alone. -/
theorem settledAt_of_allHeard {C : Configuration D} (hInvE : ReachInvE C)
    {v : Version} {s : D.State} {E S : Set (Op D.AppOp)}
    (hv : C.ver v = some (s, E))
    (hdown : ∀ a b, C.vis a b → b ∈ S → a ∈ S)
    (hAll : AllHeardSince C v S) :
    SettledAt C v S :=
  ⟨s, E, hv, settledAtOn_of_allHeard hInvE hv hdown hAll⟩

open LabeledTS in
/-- `SettledAt` discharged at every plain-reachable all-heard configuration. -/
theorem settledAt_of_allHeard_reachable {hInit : D.Inv D.init} {C : Configuration D}
    (hReach : (labeledTS3 D).ReachableFrom (initConfig D hInit) C)
    {v : Version} {s : D.State} {E S : Set (Op D.AppOp)}
    (hv : C.ver v = some (s, E))
    (hdown : ∀ a b, C.vis a b → b ∈ S → a ∈ S)
    (hAll : AllHeardSince C v S) :
    SettledAt C v S :=
  settledAt_of_allHeard (reachInvE_reachable hReach) hv hdown hAll

/-- `SettledAt` discharged at every **honestly** reachable all-heard configuration,
for any client/delivery contract `H`. -/
theorem settledAt_of_allHeard_honest {H : Configuration D → Prop} {hInit : D.Inv D.init}
    {C : Configuration D} (hReach : HonestReach D H hInit C)
    {v : Version} {s : D.State} {E S : Set (Op D.AppOp)}
    (hv : C.ver v = some (s, E))
    (hdown : ∀ a b, C.vis a b → b ∈ S → a ∈ S)
    (hAll : AllHeardSince C v S) :
    SettledAt C v S :=
  settledAt_of_allHeard (reachInvE_honestReach hReach) hv hdown hAll

/-! ## §3 Preservation: the all-heads frontier and the cut-monotonicity

The runtime maintains the all-heads causal frontier `AllHeard C S` (every current head
has heard the cut). Apply and Merge preserve it (the fresh version's event set contains
a current head's, which already contains `S`); `createReplica` is the one operation that
breaks it (a replica minted at the root observes `∅ ⊉ S`), which is exactly the
`canCreate` gate / open-membership deferral (`Stability_VC.lean` scope note 2).

`AllHeardSince` itself is the per-version certificate the frontier *implies* at a version
that absorbs the frontier. Its exact monotonicity is: (i) **antitone in the cut**: heard
since the later, larger cut ⟹ heard since the earlier, smaller one (the
`CompatChain` step, §5); (ii) preserved across the no-new-event steps (Merge/Query) for a
fixed existing version, and across an Apply *whose minter has heard `S`*, i.e. under the
`AllHeard C S` side-condition (the fresh mint then carries `S` in its past, minting no new
`S`-concurrency). The Apply case's dependence on `AllHeard C S` is precisely why the
frontier invariant is the load-bearing runtime obligation. -/

/-- **Frontier preservation across Apply**: the fresh version's event set extends the
minter's head, which already contains `S`; every other head is untouched. -/
theorem allHeard_apply {C C' : Configuration D} {S : Set (Op D.AppOp)}
    {t : Timestamp} {r : Replica} {o : D.AppOp} {v vnew : Version}
    {s : D.State} {ev : Set (Op D.AppOp)}
    (hAH : AllHeard C S)
    (h_head : C.head r = some v) (h_ver : C.ver v = some (s, ev))
    (h_vnew : C.ver vnew = none)
    (hHA : ∀ r' w, C.head r' = some w → (C.ver w).isSome)
    (hver : C'.ver = fun w => if w = vnew
      then some (D.update s (t, r, o), ev ∪ {(t, r, o)}) else C.ver w)
    (hhead : C'.head = fun r' => if r' = r then some vnew else C.head r') :
    AllHeard C' S := by
  intro r' w s' E' hh hv
  simp only [hhead] at hh
  rw [hver] at hv
  dsimp only at hv
  by_cases hr : r' = r
  · rw [if_pos hr] at hh
    injection hh with hh; subst hh
    rw [if_pos rfl] at hv
    injection hv with hv
    have hE' : E' = ev ∪ {(t, r, o)} := (congrArg Prod.snd hv).symm
    rw [hE']
    exact fun a ha => Set.mem_union_left _ (hAH r v s ev h_head h_ver ha)
  · rw [if_neg hr] at hh
    have hwne : w ≠ vnew := by
      intro h; have := hHA r' w hh; rw [h, h_vnew] at this; cases this
    rw [if_neg hwne] at hv
    exact hAH r' w s' E' hh hv

/-- **Frontier preservation across Merge** (and the compaction self-merge): the merged
version's event set is a union containing a current head's, which contains `S`. -/
theorem allHeard_merge {C C' : Configuration D} {S : Set (Op D.AppOp)}
    {r₁ : Replica} {v₁ vm : Version} {s₁ : D.State} {ev₁ ev₂ : Set (Op D.AppOp)}
    {sm : D.State}
    (hAH : AllHeard C S)
    (h_head₁ : C.head r₁ = some v₁) (h_ver₁ : C.ver v₁ = some (s₁, ev₁))
    (h_vm : C.ver vm = none)
    (hHA : ∀ r' w, C.head r' = some w → (C.ver w).isSome)
    (hver : C'.ver = fun w => if w = vm then some (sm, ev₁ ∪ ev₂) else C.ver w)
    (hhead : C'.head = fun r' => if r' = r₁ then some vm else C.head r') :
    AllHeard C' S := by
  intro r' w s' E' hh hv
  simp only [hhead] at hh
  rw [hver] at hv
  dsimp only at hv
  by_cases hr : r' = r₁
  · rw [if_pos hr] at hh
    injection hh with hh; subst hh
    rw [if_pos rfl] at hv
    injection hv with hv
    have hE' : E' = ev₁ ∪ ev₂ := (congrArg Prod.snd hv).symm
    rw [hE']
    exact fun a ha => Set.mem_union_left _ (hAH r₁ v₁ s₁ ev₁ h_head₁ h_ver₁ ha)
  · rw [if_neg hr] at hh
    have hwne : w ≠ vm := by
      intro h; have := hHA r' w hh; rw [h, h_vm] at this; cases this
    rw [if_neg hwne] at hv
    exact hAH r' w s' E' hh hv

/-- **Cut-antitonicity of `AllHeardSince`**, the `CompatChain` monotonicity (§5): having
heard everyone since the larger cut `S'` implies having heard everyone since any smaller
`S ⊆ S'`. Each replica's evidence commit for `S'` serves verbatim for `S` (`S ⊆ S' ⊆ E(c)`,
and the certification quantifies over the smaller `S`). -/
theorem allHeardSince_antitone {C : Configuration D} {v : Version}
    {S S' : Set (Op D.AppOp)} (hSS : S ⊆ S') (hAll : AllHeardSince C v S') :
    AllHeardSince C v S := by
  intro j hj
  obtain ⟨c, sc, Ec, hreach, hc, hSc, hcert⟩ := hAll j hj
  exact ⟨c, sc, Ec, hreach, hc, hSS.trans hSc,
    fun e he hej hne a ha => hcert e he hej hne a (hSS ha)⟩

/-! ## §4 The payoff: `SettledAt` discharged along the stability simulation

`stability_simulation` (`Stability_VC.lean`) exposes, at every paired run, that the full
side `C` is an ordinary `Step3`-reachable configuration (`.2.2`). That is precisely the
`ReachInvE` premise `settledAt_of_allHeard` needs, so the `SettledAt` conjunct that every
`StabilityVC.gate` must feed to `gate_settled` is *derivable from the frontier knowledge*
at every stability-run configuration, with no standalone `SettledAt` hypothesis. Feeding this
into `orStabilityVC`'s gate (`gate := SettledAt ∧ AllHeard`, `ORSet_Stability.lean`)
discharges its `SettledAt` half, leaving only the observable `AllHeardSince`/`AllHeard`
frontier, which the runtime maintains (§3). The OR-set reads-preservation
(`stability_reads_equal`) then holds without `SettledAt` assumed. -/

open LabeledTS in
/-- At every configuration of a stability paired run, `SettledAt` for the
bundle's cut is a *theorem*, discharged from `AllHeardSince` (the runtime's frontier
knowledge) rather than assumed, exactly what `StabilityVC.gate_settled` requires. -/
theorem settledAt_of_allHeard_stabReach {V : StabilityVC D} {hInit : D.Inv D.init}
    {C Ĉ : Configuration D} (h : StabReach V hInit C Ĉ)
    {v : Version} {s : D.State} {E : Set (Op D.AppOp)}
    (hv : C.ver v = some (s, E))
    (hdown : ∀ a b, C.vis a b → b ∈ V.S → a ∈ V.S)
    (hAll : AllHeardSince C v V.S) :
    SettledAt C v V.S :=
  settledAt_of_allHeard_reachable (stability_simulation h).2.2 hv hdown hAll

/-! ## §5 Connection to the epoch boundary (`CompatChain`)

A multi-epoch compaction (`EmbedRGA_MultiEpoch.lean`) compacts first at cut `S`
(epoch 1), later at cut `S' ⊇ S` (epoch 2). Between-epoch compatibility (`Compat`, whose
list-fold is `CompatChain`) demands that the later, coarser compaction refine the earlier
one *on the shared stable prefix*. The metatheory core is `allHeardSince_antitone`: the
frontier knowledge at the later cut `S'` subsumes the earlier cut `S` (`S ⊆ S'`), so a
single "heard from everyone since `S'`" certificate discharges settledness at *both*
epochs' cuts simultaneously. Concretely, `allHeardSince_antitone (hSS : S ⊆ S')` turns the
epoch-2 `AllHeardSince C v S'` into the epoch-1 `AllHeardSince C v S`, and
`settledAt_of_allHeard` then yields `SettledAt C v S` and `SettledAt C v S'` from the one
frontier. The full `CompatChain` discharge (the code-level `StablePrefixMap` refinement)
is instance-specific to the embed RGA and lives in `EmbedRGA_MultiEpoch.lean`; it is a
follow-on that consumes this antitonicity as its causal-stability input. -/

/-- The `CompatChain` precondition, metatheory form: one frontier certificate at the later
cut `S'` discharges settledness at the earlier cut `S ⊆ S'` (the nested-epoch step). -/
theorem settledAt_compatStep {C : Configuration D} (hInvE : ReachInvE C)
    {v : Version} {s : D.State} {E S S' : Set (Op D.AppOp)}
    (hv : C.ver v = some (s, E)) (hSS : S ⊆ S')
    (hdown : ∀ a b, C.vis a b → b ∈ S → a ∈ S)
    (hAll : AllHeardSince C v S') :
    SettledAt C v S :=
  settledAt_of_allHeard hInvE hv hdown (allHeardSince_antitone hSS hAll)

end Discharge

/-! ## §6 SPOTs (PASS + FAIL), on the concrete `Cex` DAG of `GC_Safety.lean` §7

Reuses the hand-built 6-version `GSetCond` configuration `Cex` (replica A = 0 authors
`e1 e2 e3`, replica B = 1 authors `e4`; `e1 → e2 → e3`, `e1,e2 → e4`, and crucially
`e3 ∥ e4`). Both concurrent frontiers sit *above* the common prefix `F2 = {e1,e2}`.

* **PASS** (`spot_pass_settled`): at B's head `v = 5`, `AllHeardSince Cex 5 F2` holds
  (A's evidence commit is version 2, B's is version 5), so `settledAt_of_allHeard` derives
  `SettledAt Cex 5 F2`. Companion `spot_pass_cut_strict` pins that the cut is a *proper*
  causal prefix (`e4 ∉ F2` though `e4 ∈ E(5)`), so this is not the degenerate
  "settle the whole event set" reading.
* **FAIL** (`spot_fail_settledOn` + `spot_fail_evidence`): at A's head `v = 4` with cut
  `F4 = {e1,e2,e3}`, replica B has **no** evidence commit reaching `4` (its event `e4` is
  concurrent with `e3 ∈ F4`, so no version reaching `4` places `S` before `e4`), and
  `SettledAtOn Cex F4 F4` is correspondingly **false**: B's not-yet-heard `e4 ∥ e3`
  sits outside `E(4) = F4`. All expected values hand-derived, never `#eval`'d.
-/

namespace EvidenceSpot

open GCSpot

/-- `Cex` satisfies the evidence-discharge reachability bundle (built directly: it is a
hand-crafted witness config, and `ReachInvE` is exactly `StoreInv` + author/root
registration, all discharged pointwise, no run required). -/
theorem reachInvE_Cex : ReachInvE Cex where
  store := storeInvEx
  authors := by
    intro e he
    obtain ⟨r, s, hL, hs⟩ := he
    rcases mem_of_Lex hL hs with rfl | rfl | rfl | rfl <;> rfl
  root := rfl

/-- The registered replicas of `Cex` are exactly A = 0 and B = 1. -/
theorem registered_Cex {j : Replica} (hj : Registered Cex j) : j = 0 ∨ j = 1 := by
  by_cases h0 : j = 0
  · exact Or.inl h0
  by_cases h1 : j = 1
  · exact Or.inr h1
  exfalso
  have hnone : Cex.N j = none := by
    show Nex j = none
    unfold Nex; rw [if_neg h0, if_neg h1]
  rw [Registered, hnone] at hj
  exact absurd hj (by decide)

theorem e3_nmem_F2 : e3 ∉ F2 := by
  intro h
  simp only [F2, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h <;> exact absurd (congrArg Prod.fst h) (by decide)

theorem e4_nmem_F2 : e4 ∉ F2 := by
  intro h
  simp only [F2, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h <;> exact absurd (congrArg Prod.fst h) (by decide)

theorem e4_mem_events : e4 ∈ Cex.events :=
  ⟨1, F5, rfl, Or.inr (Or.inr rfl)⟩

theorem e3_mem_F4 : e3 ∈ F4 := Or.inr (Or.inr rfl)

theorem not_visEx_e4_e3 : ¬ Cex.vis e4 e3 := by
  rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) <;> exact absurd h (by decide)

theorem not_visEx_e3_e4 : ¬ Cex.vis e3 e4 := by
  rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) <;> exact absurd h (by decide)

/-- `e4` and `e3` are concurrent in `Cex`: the discriminating anomaly. -/
theorem concOp_e4_e3 : ConcOp Cex e4 e3 :=
  ⟨by decide, not_visEx_e4_e3, not_visEx_e3_e4⟩

/-- The cut `F2` is downward closed under `Cex.vis`. -/
theorem hdown_F2 : ∀ a b, Cex.vis a b → b ∈ F2 → a ∈ F2 := by
  intro a b hab hb
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · exact absurd hb e3_nmem_F2
  · exact absurd hb e3_nmem_F2
  · exact absurd hb e4_nmem_F2
  · exact absurd hb e4_nmem_F2

/-- A's (replica 0) certification for cut `F2` at commit version 2: the only
`0`-event outside `F2` is `e3`, and `e1, e2 → e3`. -/
theorem cert0_F2 : ∀ e ∈ Cex.events, Op.rep e = 0 → e ∉ F2 →
    ∀ a ∈ F2, Cex.vis a e := by
  intro e he hrep hnF2 a ha
  obtain ⟨r, s, hL, hs⟩ := he
  rcases mem_of_Lex hL hs with rfl | rfl | rfl | rfl
  · exact absurd (Or.inl rfl) hnF2
  · exact absurd (Or.inr rfl) hnF2
  · rcases ha with rfl | rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact absurd hrep (by decide)

/-- B's (replica 1) certification for cut `F2` at commit version 5: its only event
`e4` is already inside `E(5) = F5`, so the clause is vacuous. -/
theorem cert1_F2 : ∀ e ∈ Cex.events, Op.rep e = 1 → e ∉ F5 →
    ∀ a ∈ F2, Cex.vis a e := by
  intro e he hrep hnF5 a ha
  obtain ⟨r, s, hL, hs⟩ := he
  rcases mem_of_Lex hL hs with rfl | rfl | rfl | rfl
  · exact absurd hrep (by decide)
  · exact absurd hrep (by decide)
  · exact absurd hrep (by decide)
  · exact absurd (Or.inr (Or.inr rfl)) hnF5

/-- **AllHeardSince holds** at B's head `5` for the common prefix `F2`: A's evidence
commit is version 2, B's is version 5. -/
theorem allHeardSince_Cex5 : AllHeardSince Cex 5 F2 := by
  intro j hj
  rcases registered_Cex hj with rfl | rfl
  · exact ⟨2, S2, F2, re_25, verEx2, subset_rfl, cert0_F2⟩
  · exact ⟨5, S5, F5, Relation.ReflTransGen.refl, verEx5, F2_sub_F5, cert1_F2⟩

/-- **SPOT PASS**: `SettledAt` derived from the frontier knowledge alone. -/
theorem spot_pass_settled : SettledAt Cex 5 F2 :=
  settledAt_of_allHeard reachInvE_Cex verEx5 hdown_F2 allHeardSince_Cex5

/-- PASS companion (pins the non-degeneracy): `F2` is a *proper* causal cut: it omits
`e4`, which nonetheless lies in the settling version's event set `E(5) = F5`. So this is
not the vacuous "settle the entire event set" reading. -/
theorem spot_pass_cut_strict : e4 ∉ F2 ∧ e4 ∈ F5 :=
  ⟨e4_nmem_F2, Or.inr (Or.inr rfl)⟩

/-- **SPOT FAIL (semantic)**: at A's head `4` the cut `F4` is **not** settled: B's
concurrent event `e4 ∥ e3 ∈ F4` sits outside `E(4) = F4`. -/
theorem spot_fail_settledOn : ¬ SettledAtOn Cex F4 F4 := by
  intro hset
  exact e4_nmem_F4 (hset.conc e4 e4_mem_events ⟨e3, e3_mem_F4, concOp_e4_e3⟩)

/-- **SPOT FAIL (the missing evidence)**: replica B (= 1) has no evidence commit for
`F4` reaching version `4`: every version reaching `4` has events `⊆ F4`, so cannot place
`F4` before the concurrent `e4 ∉ F4`. This is exactly the replica whose absence from the
frontier falsifies `AllHeardSince Cex 4 F4`, matching `spot_fail_settledOn`. -/
theorem spot_fail_evidence : ¬ EvidenceCommit Cex 4 F4 1 := by
  rintro ⟨c, sc, Ec, hreach, hc, hSc, hcert⟩
  have hEcF4 : Ec ⊆ F4 := storeInv_events_mono_reaches storeInvEx hreach hc verEx4
  have he4nEc : e4 ∉ Ec := fun h => e4_nmem_F4 (hEcF4 h)
  exact not_visEx_e3_e4 (hcert e4 e4_mem_events rfl he4nEc e3 e3_mem_F4)

end EvidenceSpot

/-! ## Axiom audit -/

#print axioms settledAtOn_of_allHeard
#print axioms settledAt_of_allHeard
#print axioms settledAt_of_allHeard_honest
#print axioms settledAt_of_allHeard_stabReach
#print axioms settledAt_compatStep
#print axioms allHeardSince_antitone
#print axioms allHeard_apply
#print axioms allHeard_merge
#print axioms EvidenceSpot.spot_pass_settled
#print axioms EvidenceSpot.spot_fail_settledOn
#print axioms EvidenceSpot.spot_fail_evidence

end Sal.ConditionedMRDTs
