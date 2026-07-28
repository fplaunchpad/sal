import Sal.ConditionedMRDTs.Metatheory.LCA_Lemma
-- `Set.mem_insert_iff` / `Set.mem_singleton_iff` for the §7 concrete SPOT sets; a
-- foundational Mathlib file, not in `LCA_Lemma`'s cone (which stops at `Set.Basic`).
import Mathlib.Data.Set.Insert

/-!
# Commit GC-safety for the ranked version store

Which store entries may a runtime reclaim without changing any future behavior? Merges
arbitrarily far in the future reach back into the store for their LCA state
(`Step3.merge`'s `h_verT`), so the answer is not "everything below the heads".

**The keep set** (§1). At a prune-point configuration `C₀` with heads `H₁ … Hₙ`:

    Keep  = { v allocated : ∃ i j (i = j allowed), E(Hᵢ) ∩ E(Hⱼ) ⊆ E(v) }
    Keep' = Keep ∪ {0}

Every allocated head is in `Keep` (self-pair). The root `0` is pinned separately:
`ver_init` fixes it structurally and `Step3.createReplica` rebases fresh replicas there.

**Pruning** (§2, `dropVer`) removes the `ver` payload of allocated versions outside
`Keep'` and touches nothing else. Keeping the DAG *skeleton* (`parents`) is forced, not a
convenience: restricting `parents` changes `IsLCA` (removing common ancestors weakens the
domination clause), which can mint new LCA triples whose event sets falsify the
configuration's own `lca_events` invariant. The reclaimable payload is the states and
event sets; the skeleton is ids only.

**The three lemmas** (§3–§5): (1) *monotonicity*: along any `Step3` run every current
head either event-set-dominates a prune-time head (`HeadDom`) or is a virgin lineage
whose only prune-time ancestor is the root (`Virgin`; the disjunct is forced by
`createReplica`); (2) *intersection containment* (`lca_not_dropped`): any allocated LCA
of two future heads lies in `Keep'` (both-`HeadDom`: `E(vT) = E(v₁) ∩ E(v₂) ⊇
E(Hᵢ) ∩ E(Hⱼ)` via the `lca_events` field; a `Virgin` side: the LCA is the pinned root);
(3) *prune commutation* (`step_dropVer`): every step of the unpruned run is matched,
same label, by the dropped images; replica reads are *definitionally* unchanged
(`dropVer` does not touch `N`).

**Headline** (§6): `gc_safety`: pruning to `Keep'` preserves every `Step3` run (same
label trace) and every head read, from the single hypothesis `StoreInv C₀` (supplied by
plain reachability via `storeInv_reachable`).

**Necessity of head-sync** (§7): the framework's Merge is head-sync *by construction*
(`v₁, v₂` are read off the head map). The concrete countermodel `gc_needs_head_sync`
shows this is load-bearing: an interior version (`1` in the SPOT DAG) satisfies
`IsLCA parents 1 5 1`, so a widened merge accepting an interior argument (rewind,
checkpoint restore, a replica missing from the head map) demands exactly the version
pruning removed. Head-sync is a hypothesis, not pessimism.

**Criss-cross boundary** (honest scope): the Merge rule fires only when a version
satisfying `IsLCA` EXISTS and is allocated. In criss-cross configurations no such
version exists, no merge fires there, and this theorem is vacuously unaffected. The
virtual-LCA extension (§6V) widens the step relation to synthesize a merge
input from *potential* LCAs, whose event sets sit strictly BELOW the pairwise head
intersection, while this `Keep` retains versions ABOVE some pairwise intersection. Under
that widening this `Keep` prunes exactly what the virtual merge needs; the keep set must
then be revisited (retain the below-approximations of each pairwise meet as well).

**Converse scope**: the pruned configuration can take steps the unpruned one cannot
(re-allocating a freed version slot; `h_fresh_store` quantifies over fewer entries, so a
timestamp recorded only in a dropped entry becomes reusable). In reachable configurations
every allocated version sits below some head, making the asymmetry unobservable, but that
is a reachability invariant, not a structural one; the converse simulation is
deliberately out of scope. GC-safety (nothing is *lost*) is the mechanized direction.

Layering: Metatheory imports Framework only; the §7 SPOT uses the Framework-resident
`GSetCond`, no `MRDT_Instances` import.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

section GC

variable {D : ConditionedMRDTSig}

/-! ## §1 The keep set -/

/-- `v` is a current head version of `C`. -/
def IsHead (C : Configuration D) (v : Version) : Prop := ∃ r, C.head r = some v

/-- **The keep set**: allocated versions whose event set contains the pairwise
intersection of two (allocated) head event sets; `h₁ = h₂` is allowed, so everything
event-set-above any single head is kept, in particular the heads themselves
(`head_mem_keepSet`). -/
def keepSet (C : Configuration D) : Set Version :=
  {v | ∃ h₁ h₂ s₁ e₁ s₂ e₂ s e,
        IsHead C h₁ ∧ IsHead C h₂ ∧
        C.ver h₁ = some (s₁, e₁) ∧ C.ver h₂ = some (s₂, e₂) ∧
        C.ver v = some (s, e) ∧ e₁ ∩ e₂ ⊆ e}

/-- The keep set plus the pinned root: `ver_init` fixes version `0` structurally and
`createReplica` rebases fresh replicas there, so `0` is not reclaimable in this model. -/
def keepSet' (C : Configuration D) : Set Version := keepSet C ∪ {0}

/-- What pruning removes: allocated versions outside `Keep'`. -/
def droppedSet (C : Configuration D) : Set Version :=
  {v | (C.ver v).isSome ∧ v ∉ keepSet' C}

theorem zero_not_dropped (C : Configuration D) : (0 : Version) ∉ droppedSet C :=
  fun h => h.2 (Or.inr rfl)

/-- Allocated heads are kept (the `i = j` self-pair). -/
theorem head_mem_keepSet {C : Configuration D} {v : Version} {s : D.State}
    {e : Set (Op D.AppOp)} (hh : IsHead C v) (hv : C.ver v = some (s, e)) :
    v ∈ keepSet C :=
  ⟨v, v, s, e, s, e, s, e, hh, hh, hv, hv, hv, fun _ hx => hx.1⟩

/-! ## §2 The pruned configuration

`dropVer C S` removes the `ver` entries of `S` and touches nothing else: `N`, `L`,
`vis`, `head`, `parents` are carried verbatim, so replica reads are *definitionally*
preserved. The two hypotheses are exactly what the structure invariants need: the root
is kept (`ver_init`) and allocated heads are kept (`head_coherent`). -/

open Classical in
/-- Prune the store payload of `S` out of `C`. -/
noncomputable def dropVer (C : Configuration D) (S : Set Version)
    (h0 : 0 ∉ S)
    (hheads : ∀ r v, C.head r = some v → (C.ver v).isSome → v ∉ S) :
    Configuration D where
  N := C.N
  L := C.L
  vis := C.vis
  dom_eq := C.dom_eq
  vis_src := C.vis_src
  vis_tgt := C.vis_tgt
  vis_causal := C.vis_causal
  timestamps_distinct := C.timestamps_distinct
  causal_mono := C.causal_mono
  vis_total_same_replica := C.vis_total_same_replica
  ver := fun v => if v ∈ S then none else C.ver v
  head := C.head
  parents := C.parents
  parents_lt := C.parents_lt
  ver_init := by rw [if_neg h0]; exact C.ver_init
  head_coherent := by
    intro r v hv
    by_cases hvS : v ∈ S
    · have hnone : C.ver v = none := by
        cases hcv : C.ver v with
        | none => rfl
        | some x => exact absurd hvS (hheads r v hv (by rw [hcv]; rfl))
      have hc := C.head_coherent r v hv
      rw [hnone] at hc
      simpa [if_pos hvS] using hc
    · simpa [if_neg hvS] using C.head_coherent r v hv
  ver_inv := by
    intro v s e hv
    by_cases hvS : v ∈ S
    · rw [if_pos hvS] at hv; cases hv
    · rw [if_neg hvS] at hv; exact C.ver_inv v s e hv
  lca_events := by
    intro v₁ v₂ vT s₁ e₁ s₂ e₂ sT eT hlca h1 h2 hT
    by_cases h1S : v₁ ∈ S
    · rw [if_pos h1S] at h1; cases h1
    · by_cases h2S : v₂ ∈ S
      · rw [if_pos h2S] at h2; cases h2
      · by_cases hTS : vT ∈ S
        · rw [if_pos hTS] at hT; cases hT
        · rw [if_neg h1S] at h1; rw [if_neg h2S] at h2; rw [if_neg hTS] at hT
          exact C.lca_events hlca h1 h2 hT

open Classical in
@[simp] theorem dropVer_ver (C : Configuration D) (S : Set Version) (h0 hheads)
    (v : Version) :
    (dropVer C S h0 hheads).ver v
      = if v ∈ S then none else C.ver v := rfl

@[simp] theorem dropVer_N (C : Configuration D) (S : Set Version) (h0 hheads) :
    (dropVer C S h0 hheads).N = C.N := rfl

@[simp] theorem dropVer_head (C : Configuration D) (S : Set Version) (h0 hheads) :
    (dropVer C S h0 hheads).head = C.head := rfl

@[simp] theorem dropVer_parents (C : Configuration D) (S : Set Version) (h0 hheads) :
    (dropVer C S h0 hheads).parents = C.parents := rfl

/-! ## §3 Monotonicity: lemma (1), disjunctive form

A future head's event set need not contain any current head's: `createReplica` rebases
fresh replicas at the root, whose lineages start from the empty event set. The invariant
is therefore the disjunction below: a future head
either event-set-dominates a prune-time head (`HeadDom`) or is a *virgin lineage* whose
only prune-time-allocated ancestor is the root (`Virgin`). A virgin lineage becomes
`HeadDom` the moment it merges with a `HeadDom` one. -/

/-- Some allocated prune-time head's event set is below `e`. -/
def HeadDom (C₀ : Configuration D) (e : Set (Op D.AppOp)) : Prop :=
  ∃ h s₀ e₀, IsHead C₀ h ∧ C₀.ver h = some (s₀, e₀) ∧ e₀ ⊆ e

/-- Virgin lineage: the only ancestor of `v` allocated at prune time is the root. -/
def Virgin (C₀ : Configuration D) (parents : Version → List Version) (v : Version) :
    Prop :=
  ∀ w, Reaches parents w v → (C₀.ver w).isSome → w = 0

/-- **The GC run invariant.** `verExt`: allocation is permanent and entries are
immutable, so prune-time entries persist verbatim. `mono`: lemma (1). `store`: the
framework's `StoreInv` (preserved by `storeInv_step`), consumed for the DAG-extension
reachability lemmas. -/
structure GCInv (C₀ C : Configuration D) : Prop where
  verExt : ∀ v, (C₀.ver v).isSome → C.ver v = C₀.ver v
  mono : ∀ r v s e, C.head r = some v → C.ver v = some (s, e) →
    HeadDom C₀ e ∨ Virgin C₀ C.parents v
  store : StoreInv C.ver C.parents

theorem gcInv_init (C₀ : Configuration D) (hStore : StoreInv C₀.ver C₀.parents) :
    GCInv C₀ C₀ where
  verExt := fun _ _ => rfl
  mono := fun r v s e hh hv => Or.inl ⟨v, s, e, ⟨r, hh⟩, hv, fun _ hx => hx⟩
  store := hStore

/-- A version fresh in `C` (unallocated) was unallocated at prune time too. -/
theorem not_alloc₀_of_fresh {C₀ C : Configuration D} (hInv : GCInv C₀ C)
    {v : Version} (hfresh : C.ver v = none) : ¬ (C₀.ver v).isSome := by
  intro h
  have h' := hInv.verExt v h
  rw [hfresh] at h'
  rw [← h'] at h
  simp at h

/-- **Lemma (1) preservation**: `GCInv` is a `Step3` invariant. -/
theorem gcInv_step {C₀ C C' : Configuration D} {ℓ : Label3 D}
    (hInv : GCInv C₀ C) (hstep : Step3 D C ℓ C') : GCInv C₀ C' := by
  have hstore' : StoreInv C'.ver C'.parents := storeInv_step hstep hInv.store
  cases hstep with
  | @createReplica r h_fresh C' hN hL hvis hver hhead hparents =>
    refine ⟨?_, ?_, hstore'⟩
    · intro v hv; rw [hver]; exact hInv.verExt v hv
    · intro r' v s e hh hv
      simp only [hhead] at hh
      simp only [hver] at hv
      simp only [hparents]
      by_cases hr : r' = r
      · rw [if_pos hr] at hh
        injection hh with hh
        subst hh
        exact Or.inr fun w hw _ =>
          Nat.le_antisymm (reaches_le C.parents_lt hw) (Nat.zero_le w)
      · rw [if_neg hr] at hh
        exact hInv.mono r' v s e hh hv
  | @apply t r o v s ev vnew h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank
      C' hN hL hvis hver hhead hparents =>
    refine ⟨?_, ?_, hstore'⟩
    · intro w hw
      have hwne : w ≠ vnew := by
        rintro rfl; exact not_alloc₀_of_fresh hInv h_vnew hw
      simp only [hver, if_neg hwne]
      exact hInv.verExt w hw
    · intro r' w sw ew hh hv
      simp only [hhead] at hh
      simp only [hver] at hv
      simp only [hparents]
      by_cases hw : w = vnew
      · -- the freshly allocated version, whichever head points at it
        subst hw
        rw [if_pos rfl] at hv
        injection hv with hv
        have hew : ew = ev ∪ {(t, r, o)} := (congrArg Prod.snd hv).symm
        rcases hInv.mono r v s ev h_head h_ver with hd | hvir
        · obtain ⟨h₀, s₀, e₀, hh₀, hv₀, hsub⟩ := hd
          exact Or.inl ⟨h₀, s₀, e₀, hh₀, hv₀,
            hsub.trans (by rw [hew]; exact Set.subset_union_left)⟩
        · refine Or.inr fun u hu hu₀ => ?_
          rcases reaches_new_target hInv.store.parents_alloc h_vnew
              (if_pos rfl) (fun x hx => if_neg hx)
              (by intro p hp; rw [List.mem_singleton] at hp; subst hp
                  rw [h_ver]; rfl) hu with h | ⟨p, hp, hre⟩
          · exact absurd hu₀ (h ▸ not_alloc₀_of_fresh hInv h_vnew)
          · rw [List.mem_singleton] at hp; subst hp
            exact hvir u hre hu₀
      · -- an untouched head: transport `mono` along the conservative DAG extension
        rw [if_neg hw] at hv
        have hh' : C.head r' = some w := by
          by_cases hr : r' = r
          · rw [if_pos hr] at hh; injection hh with hh; exact absurd hh.symm hw
          · rw [if_neg hr] at hh; exact hh
        rcases hInv.mono r' w sw ew hh' hv with hd | hvir
        · exact Or.inl hd
        · refine Or.inr fun u hu hu₀ => ?_
          have hwsome : (C.ver w).isSome := by rw [hv]; rfl
          exact hvir u (reaches_old_of_new hInv.store.parents_alloc h_vnew
            (fun x hx => if_neg hx) hu hwsome) hu₀
  | @merge r₁ r₂ v₁ v₂ vT vm s₁ s₂ sT ev₁ ev₂ evT h_head₁ h_head₂ h_ver₁ h_ver₂
      h_lca h_verT h_vm h_rank₁ h_rank₂ C' hN hL hvis hver hhead hparents =>
    refine ⟨?_, ?_, hstore'⟩
    · intro w hw
      have hwne : w ≠ vm := by
        rintro rfl; exact not_alloc₀_of_fresh hInv h_vm hw
      simp only [hver, if_neg hwne]
      exact hInv.verExt w hw
    · intro r' w sw ew hh hv
      simp only [hhead] at hh
      simp only [hver] at hv
      simp only [hparents]
      by_cases hw : w = vm
      · subst hw
        rw [if_pos rfl] at hv
        injection hv with hv
        have hew : ew = ev₁ ∪ ev₂ := (congrArg Prod.snd hv).symm
        rcases hInv.mono r₁ v₁ s₁ ev₁ h_head₁ h_ver₁ with hd₁ | hvir₁
        · obtain ⟨h₀, s₀, e₀, hh₀, hv₀, hsub⟩ := hd₁
          exact Or.inl ⟨h₀, s₀, e₀, hh₀, hv₀,
            hsub.trans (by rw [hew]; exact Set.subset_union_left)⟩
        · rcases hInv.mono r₂ v₂ s₂ ev₂ h_head₂ h_ver₂ with hd₂ | hvir₂
          · obtain ⟨h₀, s₀, e₀, hh₀, hv₀, hsub⟩ := hd₂
            exact Or.inl ⟨h₀, s₀, e₀, hh₀, hv₀,
              hsub.trans (by rw [hew]; exact Set.subset_union_right)⟩
          · refine Or.inr fun u hu hu₀ => ?_
            rcases reaches_new_target hInv.store.parents_alloc h_vm
                (if_pos rfl) (fun x hx => if_neg hx)
                (by intro p hp
                    rcases List.mem_cons.mp hp with rfl | hp'
                    · rw [h_ver₁]; rfl
                    · rw [List.mem_singleton] at hp'; subst hp'
                      rw [h_ver₂]; rfl) hu with h | ⟨p, hp, hre⟩
            · exact absurd hu₀ (h ▸ not_alloc₀_of_fresh hInv h_vm)
            · rcases List.mem_cons.mp hp with rfl | hp'
              · exact hvir₁ u hre hu₀
              · rw [List.mem_singleton] at hp'; subst hp'
                exact hvir₂ u hre hu₀
      · rw [if_neg hw] at hv
        have hh' : C.head r' = some w := by
          by_cases hr : r' = r₁
          · rw [if_pos hr] at hh; injection hh with hh; exact absurd hh.symm hw
          · rw [if_neg hr] at hh; exact hh
        rcases hInv.mono r' w sw ew hh' hv with hd | hvir
        · exact Or.inl hd
        · refine Or.inr fun u hu hu₀ => ?_
          have hwsome : (C.ver w).isSome := by rw [hv]; rfl
          exact hvir u (reaches_old_of_new hInv.store.parents_alloc h_vm
            (fun x hx => if_neg hx) hu hwsome) hu₀
  | query h_s h_val => exact ⟨hInv.verExt, hInv.mono, hInv.store⟩

/-! ## §4 Intersection containment: lemma (2) -/

/-- **Lemma (2)**: any allocated LCA of two current heads (of any configuration
`GCInv`-reachable from the prune point) survives pruning. If it postdates the prune it
was never dropped; otherwise `lca_events` pins `E(vT) = E(v₁) ∩ E(v₂)`, and either both
heads are `HeadDom` (so `E(vT) ⊇ E(h₁) ∩ E(h₂)` puts `vT` in the keep set) or a head is
`Virgin` (so `vT`, its prune-time-allocated ancestor, is the pinned root). -/
theorem lca_not_dropped {C₀ C : Configuration D} (hInv : GCInv C₀ C)
    {r₁ r₂ : Replica} {v₁ v₂ vT : Version} {s₁ s₂ sT : D.State}
    {ev₁ ev₂ evT : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁) (h_head₂ : C.head r₂ = some v₂)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (h_lca : IsLCA C.parents v₁ v₂ vT) (h_verT : C.ver vT = some (sT, evT)) :
    vT ∉ droppedSet C₀ := by
  rintro ⟨hAlloc, hNK⟩
  have hT₀ : C₀.ver vT = some (sT, evT) := by rw [← hInv.verExt vT hAlloc, h_verT]
  have hT0 : vT ≠ 0 := fun h => hNK (Or.inr h)
  have hevT : evT = ev₁ ∩ ev₂ := C.lca_events h_lca h_ver₁ h_ver₂ h_verT
  rcases hInv.mono r₁ v₁ s₁ ev₁ h_head₁ h_ver₁ with hd₁ | hvir₁
  · rcases hInv.mono r₂ v₂ s₂ ev₂ h_head₂ h_ver₂ with hd₂ | hvir₂
    · obtain ⟨h₁, s₁', e₁', hh₁, hv₁', hsub₁⟩ := hd₁
      obtain ⟨h₂, s₂', e₂', hh₂, hv₂', hsub₂⟩ := hd₂
      exact hNK (Or.inl ⟨h₁, h₂, s₁', e₁', s₂', e₂', sT, evT, hh₁, hh₂, hv₁', hv₂', hT₀,
        by rw [hevT]; exact Set.inter_subset_inter hsub₁ hsub₂⟩)
    · exact hT0 (hvir₂ vT h_lca.2.1 (by rw [hT₀]; rfl))
  · exact hT0 (hvir₁ vT h_lca.1 (by rw [hT₀]; rfl))

/-- Allocated heads survive pruning, at every `GCInv`-reachable configuration
(`HeadDom` collapses to the self-pair; `Virgin` collapses to the root). This is what
lets `dropVer` be re-formed at every point of the run. -/
theorem heads_kept {C₀ C : Configuration D} (hInv : GCInv C₀ C) :
    ∀ r v, C.head r = some v → (C.ver v).isSome → v ∉ droppedSet C₀ := by
  intro r v hh hsome hmem
  obtain ⟨hAlloc, hNK⟩ := hmem
  obtain ⟨⟨s, e⟩, hv⟩ := Option.isSome_iff_exists.mp hsome
  have hv₀ : C₀.ver v = some (s, e) := by rw [← hInv.verExt v hAlloc, hv]
  rcases hInv.mono r v s e hh hv with hd | hvir
  · obtain ⟨h₀, s₀, e₀, hh₀, hv₀', hsub⟩ := hd
    exact hNK (Or.inl ⟨h₀, h₀, s₀, e₀, s₀, e₀, s, e, hh₀, hh₀, hv₀', hv₀', hv₀,
      fun x hx => hsub hx.1⟩)
  · exact hNK (Or.inr (hvir v Relation.ReflTransGen.refl (by rw [hv₀]; rfl)))

/-! ## §5 Prune commutation: lemma (3), the forward simulation

The only `Step3` premise that consults a non-head version is Merge's `h_verT`; lemma (2)
keeps it. Freshness premises transfer because the pruned store is pointwise below the
unpruned one, and fresh slots were never dropped (dropped slots are prune-time
allocated, allocation is permanent). -/

open Classical in
/-- **Lemma (3)**: every step of the unpruned run is matched, same label, by the
`dropVer` images. -/
theorem step_dropVer {C₀ C C' : Configuration D} {ℓ : Label3 D}
    (hInv : GCInv C₀ C) (hstep : Step3 D C ℓ C')
    (hh' : ∀ r v, C'.head r = some v → (C'.ver v).isSome → v ∉ droppedSet C₀) :
    Step3 D (dropVer C (droppedSet C₀) (zero_not_dropped C₀) (heads_kept hInv)) ℓ
      (dropVer C' (droppedSet C₀) (zero_not_dropped C₀) hh') := by
  cases hstep with
  | @createReplica r h_fresh C' hN hL hvis hver hhead hparents =>
    refine Step3.createReplica ?_ _ ?_ ?_ ?_ ?_ ?_ ?_
    · exact h_fresh
    · exact hN
    · exact hL
    · exact hvis
    · funext w
      simp only [dropVer_ver, hver]
    · exact hhead
    · exact hparents
  | @apply t r o v s ev vnew h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank
      C' hN hL hvis hver hhead hparents =>
    have hvKeep : v ∉ droppedSet C₀ :=
      heads_kept hInv r v h_head (by rw [h_ver]; rfl)
    have hvnewKeep : vnew ∉ droppedSet C₀ := fun hm =>
      not_alloc₀_of_fresh hInv h_vnew hm.1
    refine Step3.apply (v := v) (s := s) (ev := ev) (vnew := vnew)
      ?_ ?_ ?_ ?_ ?_ h_rank _ ?_ ?_ ?_ ?_ ?_ ?_
    · exact h_head
    · show (if v ∈ droppedSet C₀ then none else C.ver v) = some (s, ev)
      rw [if_neg hvKeep]; exact h_ver
    · exact h_fresh_t
    · intro w sw Ew hw
      by_cases hwS : w ∈ droppedSet C₀
      · rw [dropVer_ver, if_pos hwS] at hw; cases hw
      · rw [dropVer_ver, if_neg hwS] at hw
        exact h_fresh_store w sw Ew hw
    · show (if vnew ∈ droppedSet C₀ then none else C.ver vnew) = none
      rw [if_neg hvnewKeep]; exact h_vnew
    · exact hN
    · exact hL
    · exact hvis
    · funext w
      simp only [dropVer_ver, hver]
      by_cases hw : w = vnew
      · subst hw; simp [hvnewKeep]
      · simp [hw]
    · exact hhead
    · exact hparents
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
    refine Step3.merge (v₁ := v₁) (v₂ := v₂) (vT := vT) (vm := vm)
      (s₁ := s₁) (s₂ := s₂) (sT := sT) (ev₁ := ev₁) (ev₂ := ev₂) (evT := evT)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ h_rank₁ h_rank₂ _ ?_ ?_ ?_ ?_ ?_ ?_
    · exact h_head₁
    · exact h_head₂
    · show (if v₁ ∈ droppedSet C₀ then none else C.ver v₁) = some (s₁, ev₁)
      rw [if_neg hv₁Keep]; exact h_ver₁
    · show (if v₂ ∈ droppedSet C₀ then none else C.ver v₂) = some (s₂, ev₂)
      rw [if_neg hv₂Keep]; exact h_ver₂
    · exact h_lca
    · show (if vT ∈ droppedSet C₀ then none else C.ver vT) = some (sT, evT)
      rw [if_neg hvTKeep]; exact h_verT
    · show (if vm ∈ droppedSet C₀ then none else C.ver vm) = none
      rw [if_neg hvmKeep]; exact h_vm
    · exact hN
    · exact hL
    · exact hvis
    · funext w
      simp only [dropVer_ver, hver]
      by_cases hw : w = vm
      · subst hw; simp [hvmKeep]
      · simp [hw]
    · exact hhead
    · exact hparents
  | @query r q v s h_s h_val =>
    refine Step3.query (s := s) ?_ ?_
    · exact h_s
    · exact h_val

/-! ## §6 The headline: `gc_safety` -/

/-- A labelled `Step3` run (finite trace). -/
inductive Steps (D : ConditionedMRDTSig) :
    Configuration D → List (Label3 D) → Configuration D → Prop where
  | nil (C : Configuration D) : Steps D C [] C
  | cons {C C' C'' : Configuration D} {ℓ : Label3 D} {ℓs : List (Label3 D)} :
      Step3 D C ℓ C' → Steps D C' ℓs C'' → Steps D C (ℓ :: ℓs) C''

/-- `GCInv` along a run. -/
theorem gcInv_steps {C₀ : Configuration D} {C ℓs C'}
    (hrun : Steps D C ℓs C') : GCInv C₀ C → GCInv C₀ C' := by
  induction hrun with
  | nil => exact id
  | cons hstep _ ih => exact fun hInv => ih (gcInv_step hInv hstep)

/-- Run-level prune commutation: the whole trace transports, label for label. -/
theorem steps_dropVer {C₀ : Configuration D} {C ℓs C'}
    (hrun : Steps D C ℓs C') (hInv : GCInv C₀ C)
    (hh : ∀ r v, C.head r = some v → (C.ver v).isSome → v ∉ droppedSet C₀)
    (hh' : ∀ r v, C'.head r = some v → (C'.ver v).isSome → v ∉ droppedSet C₀) :
    Steps D (dropVer C (droppedSet C₀) (zero_not_dropped C₀) hh) ℓs
      (dropVer C' (droppedSet C₀) (zero_not_dropped C₀) hh') := by
  induction hrun with
  | nil => exact Steps.nil _
  | @cons Ca Cb Cc ℓ ℓs hstep hrest ih =>
    exact Steps.cons
      (step_dropVer hInv hstep (heads_kept (gcInv_step hInv hstep)))
      (ih (gcInv_step hInv hstep) (heads_kept (gcInv_step hInv hstep)) hh')

/-- The prune-point configuration: `C₀` with the store payload outside `Keep'`
reclaimed. The single hypothesis is the store invariant, which plain reachability
supplies (`storeInv_reachable`). -/
noncomputable def pruneKeep (C₀ : Configuration D)
    (hStore : StoreInv C₀.ver C₀.parents) : Configuration D :=
  dropVer C₀ (droppedSet C₀) (zero_not_dropped C₀)
    (heads_kept (gcInv_init C₀ hStore))

/-- **Commit GC safety.** Pruning the version store to the keep set
`Keep' = {v : ∃ heads hᵢ hⱼ, E(hᵢ) ∩ E(hⱼ) ⊆ E(v)} ∪ {0}` preserves every `Step3` run
(same label trace, so in particular every query, whose value rides on the label) and
every head read (`N` agrees definitionally at every point of the transported run).

The step relation is head-sync by construction (Merge's arguments are read off the head
map); §7's `gc_needs_head_sync` shows a widened, non-head-sync merge genuinely escapes
`Keep'`. Under the virtual-LCA extension (§6V) the step relation widens and this
keep set must be revisited; see the file header. -/
theorem gc_safety (C₀ : Configuration D) (hStore : StoreInv C₀.ver C₀.parents)
    {ℓs : List (Label3 D)} {C : Configuration D} (hRun : Steps D C₀ ℓs C) :
    Steps D (pruneKeep C₀ hStore) ℓs
      (dropVer C (droppedSet C₀) (zero_not_dropped C₀)
        (heads_kept (gcInv_steps hRun (gcInv_init C₀ hStore))))
    ∧ ∀ r, (dropVer C (droppedSet C₀) (zero_not_dropped C₀)
        (heads_kept (gcInv_steps hRun (gcInv_init C₀ hStore)))).N r = C.N r :=
  ⟨steps_dropVer hRun (gcInv_init C₀ hStore) _ _, fun _ => rfl⟩

#print axioms gc_safety

/-! ## §6V  GC under virtual LCAs: the MCA-closure keep set

Under the widened step relation (`Step3V`, `LCA_Lemma.lean` §9) a merge may read the
states of **maximal common ancestors**, versions strictly below the pairwise head
meets, and of the MCAs of MCAs, recursively. The keep set is reseeded by the
**pairwise-MCA closure** of the prune-time heads (`mcasClosure`); the
argument needs two invariant strengthenings of `GCInv` (packaged in `GCInvV`):

* `headGate`: a current head that was allocated at prune time is a prune-time head
  (or the pinned root): heads only ever move to freshly allocated versions or to `0`;
* `gateway`, **the gateway invariant**: every ancestry
  path from a prune-time-allocated version to a post-prune version passes through a
  prune-time head (or collapses to the root).

`mcaClosure_not_dropped` then transfers closure membership at ANY future configuration
down to the prune-time closure (maximality transfers along the gateway), and the prune
commutation (`step_dropVerV`) matches virtual merges verbatim because pruning keeps the
DAG skeleton, so the recursion reads only closure members, all kept. -/

/-- The pairwise-MCA closure of the current (allocated) heads: the least version-set
containing the heads and closed under taking MCAs of member pairs. -/
inductive InMcasClosure (C : Configuration D) : Version → Prop where
  | head {v : Version} (h : IsHead C v) (halloc : (C.ver v).isSome) :
      InMcasClosure C v
  | mca {a b m : Version} (ha : InMcasClosure C a) (hb : InMcasClosure C b)
      (hm : IsMCA C.parents {a} b m) : InMcasClosure C m

/-- The closure as a set (`mcasClosure(heads C)`). -/
def mcasClosure (C : Configuration D) : Set Version := {v | InMcasClosure C v}

/-- Closure members are allocated (an MCA reaches a member, and heads are). -/
theorem inMcasClosure_alloc {C : Configuration D}
    (hStore : StoreInv C.ver C.parents) {v : Version}
    (h : InMcasClosure C v) : (C.ver v).isSome := by
  induction h with
  | head _ halloc => exact halloc
  | mca _ _ hm _ ihb => exact reaches_alloc hStore hm.1.2 ihb

/-- Sub-pair MCAs decompose into pairwise MCAs: a maximal element of the union of
common-ancestor sets is maximal in any member set containing it, so every
`mcaFinset` read over a closure-supported pair stays in the closure. -/
theorem inMcasClosure_of_mcaFinset {C : Configuration D}
    {S : Finset Version} {w m : Version}
    (hS : ∀ x ∈ S, InMcasClosure C x) (hw : InMcasClosure C w)
    (hm : m ∈ mcaFinset C.parents S w) : InMcasClosure C m := by
  obtain ⟨⟨⟨u, huS, hmu⟩, hmw⟩, hmax⟩ := mcaFinset_isMCA C.parents hm
  refine InMcasClosure.mca (hS u huS) hw ⟨⟨⟨u, rfl, hmu⟩, hmw⟩, ?_⟩
  rintro x ⟨⟨u', hu', hxu⟩, hxw⟩ hmx
  rcases hu' with rfl
  exact hmax x ⟨⟨u', huS, hxu⟩, hxw⟩ hmx

/-- **The MCA-closure keep set**: allocated versions event-set-above some
prune-time closure member, plus the pinned root. Every recursion read of every future
virtual resolution lies here (`mcaClosure_not_dropped` + `inMcasClosure_of_mcaFinset`). -/
def keepSetV (C : Configuration D) : Set Version :=
  {v | ∃ s e w sw ew, InMcasClosure C w ∧ C.ver w = some (sw, ew) ∧
        C.ver v = some (s, e) ∧ ew ⊆ e} ∪ {0}

/-- What the `keepSetV` pruning removes. -/
def droppedSetV (C : Configuration D) : Set Version :=
  {v | (C.ver v).isSome ∧ v ∉ keepSetV C}

theorem zero_not_droppedV (C : Configuration D) : (0 : Version) ∉ droppedSetV C :=
  fun h => h.2 (Or.inr rfl)

/-- Closure members keep themselves (the reflexive witness). -/
theorem inMcasClosure_mem_keepSetV {C : Configuration D} {v : Version}
    (h : InMcasClosure C v) {s : D.State} {e : Set (Op D.AppOp)}
    (hv : C.ver v = some (s, e)) : v ∈ keepSetV C :=
  Or.inl ⟨s, e, v, s, e, h, hv, hv, fun _ hx => hx⟩

/-- **The GC run invariant, virtual-LCA form**: `GCInv` plus the head gate and the
gateway invariant (file-header of this section). -/
structure GCInvV (C₀ C : Configuration D) : Prop extends GCInv C₀ C where
  /-- The prune-time store invariant, carried for the closure-transfer argument
  (`mcaClosure_not_dropped` moves reachability between the two graphs). -/
  store₀ : StoreInv C₀.ver C₀.parents
  /-- Parent lists of prune-time versions are immutable: the DAG only grows at
  freshly allocated versions. -/
  parentsExt : ∀ v, (C₀.ver v).isSome → C.parents v = C₀.parents v
  /-- A current head allocated at prune time is a prune-time head or the root
  (heads only move to freshly allocated versions, or to `0` at `createReplica`). -/
  headGate : ∀ r v, C.head r = some v → (C₀.ver v).isSome → IsHead C₀ v ∨ v = 0
  /-- **The gateway invariant**: an ancestry path from a prune-time-allocated `w` to a
  post-prune-allocated `v` passes through a prune-time head, or `w` is the root. -/
  gateway : ∀ v, (C.ver v).isSome → ¬ (C₀.ver v).isSome →
    ∀ w, (C₀.ver w).isSome → Reaches C.parents w v →
      w = 0 ∨ ∃ h, IsHead C₀ h ∧ (C₀.ver h).isSome ∧
        Reaches C.parents w h ∧ Reaches C.parents h v

theorem gcInvV_init (C₀ : Configuration D)
    (hStore : StoreInv C₀.ver C₀.parents) : GCInvV C₀ C₀ where
  toGCInv := gcInv_init C₀ hStore
  store₀ := hStore
  parentsExt := fun _ _ => rfl
  headGate := fun r v hh _ => Or.inl ⟨r, hh⟩
  gateway := fun _ hv hv₀ => absurd hv hv₀

/-- A current-graph path to a prune-time version restricts to the prune-time graph
(prune-time parent lists are immutable, and their sources are prune-time-allocated). -/
theorem GCInvV.reaches_restrict {C₀ C : Configuration D} (hInv : GCInvV C₀ C)
    {a b : Version} (hr : Reaches C.parents a b) :
    (C₀.ver b).isSome → Reaches C₀.parents a b := by
  induction hr with
  | refl => intro _; exact Relation.ReflTransGen.refl
  | tail _hpre hstep ih =>
    rename_i mid c
    intro hc
    have hedge : mid ∈ C₀.parents c := by
      rw [← hInv.parentsExt c hc]; exact hstep
    have hmid : (C₀.ver mid).isSome := hInv.store₀.parents_alloc c mid hedge
    exact (ih hmid).tail hedge

/-- A prune-time-graph path embeds into the current graph (same immutability). -/
theorem GCInvV.reaches_extend {C₀ C : Configuration D} (hInv : GCInvV C₀ C)
    {a b : Version} (hr : Reaches C₀.parents a b) :
    (C₀.ver b).isSome → Reaches C.parents a b := by
  induction hr with
  | refl => intro _; exact Relation.ReflTransGen.refl
  | tail _hpre hstep ih =>
    rename_i mid c
    intro hc
    have hmid : (C₀.ver mid).isSome := hInv.store₀.parents_alloc c mid hstep
    have hedge : mid ∈ C.parents c := by
      rw [hInv.parentsExt c hc]; exact hstep
    exact (ih hmid).tail hedge

/-- `GCInv` is preserved by every widened step: the `mergeVirtual` case is the merge
case verbatim (it never consulted the LCA slot). -/
theorem gcInv_stepV {C₀ C C' : Configuration D} {ℓ : Label3 D}
    (hInv : GCInv C₀ C) (hstep : Step3V D C ℓ C') : GCInv C₀ C' := by
  cases hstep with
  | base hstep' => exact gcInv_step hInv hstep'
  | @mergeVirtual r₁ r₂ v₁ v₂ vm s₁ s₂ ev₁ ev₂ h_head₁ h_head₂ h_ver₁ h_ver₂
      h_vm h_rank₁ h_rank₂ C'' hN hL hvis hver hhead hparents =>
    have hstore' : StoreInv C'.ver C'.parents :=
      storeInv_merge_extend (sm := D.mergeL (virtualLCAState C v₁ v₂) s₁ s₂)
        hInv.store h_vm h_ver₁ h_ver₂
        (by rw [hver]; simp)
        (fun w hw => by rw [hver]; simp [hw])
        (by rw [hparents]; simp)
        (fun w hw => by rw [hparents]; simp [hw])
    refine ⟨?_, ?_, hstore'⟩
    · intro w hw
      have hwne : w ≠ vm := by
        rintro rfl; exact not_alloc₀_of_fresh hInv h_vm hw
      simp only [hver, if_neg hwne]
      exact hInv.verExt w hw
    · intro r' w sw ew hh hv
      simp only [hhead] at hh
      simp only [hver] at hv
      simp only [hparents]
      by_cases hw : w = vm
      · subst hw
        rw [if_pos rfl] at hv
        injection hv with hv
        have hew : ew = ev₁ ∪ ev₂ := (congrArg Prod.snd hv).symm
        rcases hInv.mono r₁ v₁ s₁ ev₁ h_head₁ h_ver₁ with hd₁ | hvir₁
        · obtain ⟨h₀, s₀, e₀, hh₀, hv₀, hsub⟩ := hd₁
          exact Or.inl ⟨h₀, s₀, e₀, hh₀, hv₀,
            hsub.trans (by rw [hew]; exact Set.subset_union_left)⟩
        · rcases hInv.mono r₂ v₂ s₂ ev₂ h_head₂ h_ver₂ with hd₂ | hvir₂
          · obtain ⟨h₀, s₀, e₀, hh₀, hv₀, hsub⟩ := hd₂
            exact Or.inl ⟨h₀, s₀, e₀, hh₀, hv₀,
              hsub.trans (by rw [hew]; exact Set.subset_union_right)⟩
          · refine Or.inr fun u hu hu₀ => ?_
            rcases reaches_new_target hInv.store.parents_alloc h_vm
                (if_pos rfl) (fun x hx => if_neg hx)
                (by intro p hp
                    rcases List.mem_cons.mp hp with rfl | hp'
                    · rw [h_ver₁]; rfl
                    · rw [List.mem_singleton] at hp'; subst hp'
                      rw [h_ver₂]; rfl) hu with h | ⟨p, hp, hre⟩
            · exact absurd hu₀ (h ▸ not_alloc₀_of_fresh hInv h_vm)
            · rcases List.mem_cons.mp hp with rfl | hp'
              · exact hvir₁ u hre hu₀
              · rw [List.mem_singleton] at hp'; subst hp'
                exact hvir₂ u hre hu₀
      · rw [if_neg hw] at hv
        have hh' : C.head r' = some w := by
          by_cases hr : r' = r₁
          · rw [if_pos hr] at hh; injection hh with hh; exact absurd hh.symm hw
          · rw [if_neg hr] at hh; exact hh
        rcases hInv.mono r' w sw ew hh' hv with hd | hvir
        · exact Or.inl hd
        · refine Or.inr fun u hu hu₀ => ?_
          have hwsome : (C.ver w).isSome := by rw [hv]; rfl
          exact hvir u (reaches_old_of_new hInv.store.parents_alloc h_vm
            (fun x hx => if_neg hx) hu hwsome) hu₀

/-- The per-head-side gateway factoring, old graph: a prune-time-allocated `w`
reaching a *current head* reaches it through a prune-time head, or is the root
(`headGate` when the head predates the prune, `gateway` when it postdates it). -/
private theorem gateway_side {C₀ C : Configuration D} (hInv : GCInvV C₀ C)
    {r : Replica} {vp : Version} (hhead : C.head r = some vp)
    (hvp : (C.ver vp).isSome)
    {w : Version} (hw₀ : (C₀.ver w).isSome) (hwvp : Reaches C.parents w vp) :
    w = 0 ∨ ∃ h, IsHead C₀ h ∧ (C₀.ver h).isSome ∧
      Reaches C.parents w h ∧ Reaches C.parents h vp := by
  by_cases hvp₀ : (C₀.ver vp).isSome
  · rcases hInv.headGate r vp hhead hvp₀ with hh | h0
    · exact Or.inr ⟨vp, hh, hvp₀, hwvp, Relation.ReflTransGen.refl⟩
    · subst h0
      exact Or.inl (Nat.le_antisymm (reaches_le C.parents_lt hwvp) (Nat.zero_le w))
  · exact hInv.gateway vp hvp hvp₀ w hw₀ hwvp

/-- Gateway at the freshly allocated node: a path into it factors through a declared
parent, a current head, where `gateway_side` routes it; both legs transport along
the conservative DAG extension. -/
private theorem gateway_new_node {C₀ C C' : Configuration D} (hInv : GCInvV C₀ C)
    {vm : Version} (h_vm : C.ver vm = none) {ps : List Version}
    (hpar_old : ∀ x, x ≠ vm → C'.parents x = C.parents x)
    (hpar_new : C'.parents vm = ps)
    (hps_heads : ∀ p ∈ ps, ∃ r, C.head r = some p)
    (hps_alloc : ∀ p ∈ ps, (C.ver p).isSome)
    {w : Version} (hw₀ : (C₀.ver w).isSome) (hr : Reaches C'.parents w vm) :
    w = 0 ∨ ∃ h, IsHead C₀ h ∧ (C₀.ver h).isSome ∧
      Reaches C'.parents w h ∧ Reaches C'.parents h vm := by
  rcases reaches_new_target hInv.store.parents_alloc h_vm hpar_new hpar_old
      hps_alloc hr with h | ⟨p, hp, hre⟩
  · exact absurd hw₀ (h ▸ not_alloc₀_of_fresh hInv.toGCInv h_vm)
  · obtain ⟨r, hhead⟩ := hps_heads p hp
    rcases gateway_side hInv hhead (hps_alloc p hp) hw₀ hre
      with h0 | ⟨h, hh, hh₀, hwh, hhp⟩
    · exact Or.inl h0
    · have hhC : (C.ver h).isSome := by rw [hInv.verExt h hh₀]; exact hh₀
      refine Or.inr ⟨h, hh, hh₀,
        reaches_new_of_old hInv.store.parents_alloc h_vm hpar_old hwh hhC, ?_⟩
      refine Relation.ReflTransGen.tail
        (reaches_new_of_old hInv.store.parents_alloc h_vm hpar_old hhp
          (hps_alloc p hp)) ?_
      show p ∈ C'.parents vm
      rw [hpar_new]
      exact hp

/-- Gateway at an untouched post-prune node: collapse to the old graph, use the old
gateway, transport back. -/
private theorem gateway_old_node {C₀ C C' : Configuration D} (hInv : GCInvV C₀ C)
    {vm : Version} (h_vm : C.ver vm = none)
    (hpar_old : ∀ x, x ≠ vm → C'.parents x = C.parents x)
    {v' : Version} (hv'C : (C.ver v').isSome) (hv₀' : ¬ (C₀.ver v').isSome)
    {w : Version} (hw₀ : (C₀.ver w).isSome) (hr : Reaches C'.parents w v') :
    w = 0 ∨ ∃ h, IsHead C₀ h ∧ (C₀.ver h).isSome ∧
      Reaches C'.parents w h ∧ Reaches C'.parents h v' := by
  have hrold := reaches_old_of_new hInv.store.parents_alloc h_vm hpar_old hr hv'C
  rcases hInv.gateway v' hv'C hv₀' w hw₀ hrold with h0 | ⟨h, hh, hh₀, hwh, hhv⟩
  · exact Or.inl h0
  · have hhC : (C.ver h).isSome := by rw [hInv.verExt h hh₀]; exact hh₀
    exact Or.inr ⟨h, hh, hh₀,
      reaches_new_of_old hInv.store.parents_alloc h_vm hpar_old hwh hhC,
      reaches_new_of_old hInv.store.parents_alloc h_vm hpar_old hhv hv'C⟩

/-- **`GCInvV` is a `Step3V` invariant**: the gateway invariant's preservation. After the
prune point, versions extend only current
heads, and `headGate`/`gateway` route every prune-time ancestor through a prune-time
head (or the root). -/
theorem gcInvV_step {C₀ C C' : Configuration D} {ℓ : Label3 D}
    (hInv : GCInvV C₀ C) (hstep : Step3V D C ℓ C') : GCInvV C₀ C' := by
  have hbase : GCInv C₀ C' := gcInv_stepV hInv.toGCInv hstep
  cases hstep with
  | base hstep' =>
    cases hstep' with
    | @createReplica r h_fresh C'' hN hL hvis hver hhead hparents =>
      refine ⟨hbase, hInv.store₀, ?_, ?_, ?_⟩
      · intro v hv
        rw [hparents]
        exact hInv.parentsExt v hv
      · intro r' v hh hv₀
        simp only [hhead] at hh
        by_cases hr : r' = r
        · rw [if_pos hr, Option.some.injEq] at hh
          exact Or.inr hh.symm
        · rw [if_neg hr] at hh
          exact hInv.headGate r' v hh hv₀
      · intro v hv hv₀ w hw₀ hr
        rw [hver] at hv
        rw [hparents] at hr
        rcases hInv.gateway v hv hv₀ w hw₀ hr with h0 | ⟨h, hh, hh₀, hwh, hhv⟩
        · exact Or.inl h0
        · exact Or.inr ⟨h, hh, hh₀, by rw [hparents]; exact hwh,
            by rw [hparents]; exact hhv⟩
    | @apply t r o v s ev vnew h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank
        C'' hN hL hvis hver hhead hparents =>
      have hpar_old : ∀ x, x ≠ vnew → C'.parents x = C.parents x := fun x hx => by
        rw [hparents]; simp [hx]
      have hpar_new : C'.parents vnew = [v] := by rw [hparents]; simp
      have hver_old : ∀ x, x ≠ vnew → C'.ver x = C.ver x := fun x hx => by
        rw [hver]; simp [hx]
      refine ⟨hbase, hInv.store₀, ?_, ?_, ?_⟩
      · intro v' hv'
        rw [hpar_old v'
          (fun h => not_alloc₀_of_fresh hInv.toGCInv h_vnew (h ▸ hv'))]
        exact hInv.parentsExt v' hv'
      · intro r' v' hh hv₀
        simp only [hhead] at hh
        by_cases hr : r' = r
        · rw [if_pos hr, Option.some.injEq] at hh
          subst hh
          exact absurd hv₀ (not_alloc₀_of_fresh hInv.toGCInv h_vnew)
        · rw [if_neg hr] at hh
          exact hInv.headGate r' v' hh hv₀
      · intro v' hv' hv₀' w hw₀ hr
        by_cases hvn : v' = vnew
        · subst hvn
          exact gateway_new_node hInv h_vnew hpar_old hpar_new
            (by intro p hp; rw [List.mem_singleton] at hp; subst hp
                exact ⟨r, h_head⟩)
            (by intro p hp; rw [List.mem_singleton] at hp; subst hp
                rw [h_ver]; rfl)
            hw₀ hr
        · have hv'C : (C.ver v').isSome := by rw [← hver_old v' hvn]; exact hv'
          exact gateway_old_node hInv h_vnew hpar_old hv'C hv₀' hw₀ hr
    | @merge r₁ r₂ v₁ v₂ vT vm s₁ s₂ sT ev₁ ev₂ evT h_head₁ h_head₂ h_ver₁ h_ver₂
        h_lca h_verT h_vm h_rank₁ h_rank₂ C'' hN hL hvis hver hhead hparents =>
      have hpar_old : ∀ x, x ≠ vm → C'.parents x = C.parents x := fun x hx => by
        rw [hparents]; simp [hx]
      have hpar_new : C'.parents vm = [v₁, v₂] := by rw [hparents]; simp
      have hver_old : ∀ x, x ≠ vm → C'.ver x = C.ver x := fun x hx => by
        rw [hver]; simp [hx]
      refine ⟨hbase, hInv.store₀, ?_, ?_, ?_⟩
      · intro v' hv'
        rw [hpar_old v'
          (fun h => not_alloc₀_of_fresh hInv.toGCInv h_vm (h ▸ hv'))]
        exact hInv.parentsExt v' hv'
      · intro r' v' hh hv₀
        simp only [hhead] at hh
        by_cases hr : r' = r₁
        · rw [if_pos hr, Option.some.injEq] at hh
          subst hh
          exact absurd hv₀ (not_alloc₀_of_fresh hInv.toGCInv h_vm)
        · rw [if_neg hr] at hh
          exact hInv.headGate r' v' hh hv₀
      · intro v' hv' hv₀' w hw₀ hr
        by_cases hvn : v' = vm
        · subst hvn
          exact gateway_new_node hInv h_vm hpar_old hpar_new
            (by intro p hp
                rcases List.mem_cons.mp hp with rfl | hp'
                · exact ⟨r₁, h_head₁⟩
                · rw [List.mem_singleton] at hp'; subst hp'
                  exact ⟨r₂, h_head₂⟩)
            (by intro p hp
                rcases List.mem_cons.mp hp with rfl | hp'
                · rw [h_ver₁]; rfl
                · rw [List.mem_singleton] at hp'; subst hp'
                  rw [h_ver₂]; rfl)
            hw₀ hr
        · have hv'C : (C.ver v').isSome := by rw [← hver_old v' hvn]; exact hv'
          exact gateway_old_node hInv h_vm hpar_old hv'C hv₀' hw₀ hr
    | @query r q vq s h_s h_val =>
      exact ⟨hbase, hInv.store₀, hInv.parentsExt, hInv.headGate, hInv.gateway⟩
  | @mergeVirtual r₁ r₂ v₁ v₂ vm s₁ s₂ ev₁ ev₂ h_head₁ h_head₂ h_ver₁ h_ver₂
      h_vm h_rank₁ h_rank₂ C'' hN hL hvis hver hhead hparents =>
    have hpar_old : ∀ x, x ≠ vm → C'.parents x = C.parents x := fun x hx => by
      rw [hparents]; simp [hx]
    have hpar_new : C'.parents vm = [v₁, v₂] := by rw [hparents]; simp
    have hver_old : ∀ x, x ≠ vm → C'.ver x = C.ver x := fun x hx => by
      rw [hver]; simp [hx]
    refine ⟨hbase, hInv.store₀, ?_, ?_, ?_⟩
    · intro v' hv'
      rw [hpar_old v'
        (fun h => not_alloc₀_of_fresh hInv.toGCInv h_vm (h ▸ hv'))]
      exact hInv.parentsExt v' hv'
    · intro r' v' hh hv₀
      simp only [hhead] at hh
      by_cases hr : r' = r₁
      · rw [if_pos hr, Option.some.injEq] at hh
        subst hh
        exact absurd hv₀ (not_alloc₀_of_fresh hInv.toGCInv h_vm)
      · rw [if_neg hr] at hh
        exact hInv.headGate r' v' hh hv₀
    · intro v' hv' hv₀' w hw₀ hr
      by_cases hvn : v' = vm
      · subst hvn
        exact gateway_new_node hInv h_vm hpar_old hpar_new
          (by intro p hp
              rcases List.mem_cons.mp hp with rfl | hp'
              · exact ⟨r₁, h_head₁⟩
              · rw [List.mem_singleton] at hp'; subst hp'
                exact ⟨r₂, h_head₂⟩)
          (by intro p hp
              rcases List.mem_cons.mp hp with rfl | hp'
              · rw [h_ver₁]; rfl
              · rw [List.mem_singleton] at hp'; subst hp'
                rw [h_ver₂]; rfl)
          hw₀ hr
      · have hv'C : (C.ver v').isSome := by rw [← hver_old v' hvn]; exact hv'
        exact gateway_old_node hInv h_vm hpar_old hv'C hv₀' hw₀ hr

/-- **Closure transfer (`mcaClosure_not_dropped`, the `lca_not_dropped` analog)**: a
prune-time-allocated member of the *current* heads' MCA closure lies in the
*prune-time* closure, or is the root. Induction over the closure derivation: heads
transfer by `headGate`; an MCA of closure members routes each side through a
prune-time closure member (`gateway` / the side's own transfer), and **maximality
transfers downward**, a dominating common ancestor of the gateway pair would
dominate the original pair too. -/
theorem mcaClosure_not_dropped {C₀ C : Configuration D} (hInv : GCInvV C₀ C)
    {x : Version} (hx : InMcasClosure C x) (hx₀ : (C₀.ver x).isSome) :
    x = 0 ∨ InMcasClosure C₀ x := by
  induction hx with
  | @head v hh halloc =>
    obtain ⟨r, hr⟩ := hh
    rcases hInv.headGate r v hr hx₀ with hh₀ | h0
    · exact Or.inr (InMcasClosure.head hh₀ hx₀)
    · exact Or.inl h0
  | @mca a b m ha hb hm iha ihb =>
    have hside : ∀ t, InMcasClosure C t →
        ((C₀.ver t).isSome → (t = 0 ∨ InMcasClosure C₀ t)) →
        Reaches C.parents m t →
        m = 0 ∨ ∃ g, InMcasClosure C₀ g ∧
          Reaches C.parents m g ∧ Reaches C.parents g t := by
      intro t ht iht hmt
      by_cases ht₀ : (C₀.ver t).isSome
      · rcases iht ht₀ with rfl | hcl₀
        · exact Or.inl
            (Nat.le_antisymm (reaches_le C.parents_lt hmt) (Nat.zero_le m))
        · exact Or.inr ⟨t, hcl₀, hmt, Relation.ReflTransGen.refl⟩
      · have htC : (C.ver t).isSome := inMcasClosure_alloc hInv.store ht
        rcases hInv.gateway t htC ht₀ m hx₀ hmt with h0 | ⟨h, hh, hh₀, hmh, hht⟩
        · exact Or.inl h0
        · exact Or.inr ⟨h, InMcasClosure.head hh hh₀, hmh, hht⟩
    obtain ⟨⟨u, hu, hmu⟩, hmb⟩ := hm.1
    rcases hu with rfl
    rcases hside u ha iha hmu with h0 | ⟨ga, hga₀, hmga, hgaa⟩
    · exact Or.inl h0
    rcases hside b hb ihb hmb with h0 | ⟨gb, hgb₀, hmgb, hgbb⟩
    · exact Or.inl h0
    have hgaA : (C₀.ver ga).isSome := inMcasClosure_alloc hInv.store₀ hga₀
    have hgbA : (C₀.ver gb).isSome := inMcasClosure_alloc hInv.store₀ hgb₀
    refine Or.inr (InMcasClosure.mca hga₀ hgb₀
      ⟨⟨⟨ga, rfl, hInv.reaches_restrict hmga hgaA⟩,
        hInv.reaches_restrict hmgb hgbA⟩, ?_⟩)
    rintro y ⟨⟨u', hu', hyga⟩, hygb⟩ hmy
    rcases hu' with rfl
    have hyA : (C₀.ver y).isSome := reaches_alloc hInv.store₀ hyga hgaA
    exact hm.2 y
      ⟨⟨u, rfl, (hInv.reaches_extend hyga hgaA).trans hgaa⟩,
        (hInv.reaches_extend hygb hgbA).trans hgbb⟩
      (hInv.reaches_extend hmy hyA)

/-- Every member of the current closure survives pruning to `keepSetV`: prune-time
members transfer into the prune-time closure (kept by `keepSetV`), post-prune members
were never dropped. -/
theorem inMcasClosure_not_dropped {C₀ C : Configuration D} (hInv : GCInvV C₀ C)
    {x : Version} (hx : InMcasClosure C x) : x ∉ droppedSetV C₀ := by
  rintro ⟨hAlloc, hNK⟩
  rcases mcaClosure_not_dropped hInv hx hAlloc with rfl | hcl₀
  · exact hNK (Or.inr rfl)
  · obtain ⟨⟨sx, ex⟩, hvx⟩ := Option.isSome_iff_exists.mp hAlloc
    exact hNK (inMcasClosure_mem_keepSetV hcl₀ hvx)

/-- Allocated heads survive pruning to `keepSetV` (closure base + transfer). -/
theorem heads_keptV {C₀ C : Configuration D} (hInv : GCInvV C₀ C) :
    ∀ r v, C.head r = some v → (C.ver v).isSome → v ∉ droppedSetV C₀ :=
  fun r v hh hsome =>
    inMcasClosure_not_dropped hInv (InMcasClosure.head ⟨r, hh⟩ hsome)

/-- Allocated LCAs of current heads survive pruning to `keepSetV`: an LCA is the
singleton MCA of the head pair, closure layer one. (The `lca_not_dropped` argument,
re-derived through the closure.) -/
theorem lca_not_droppedV {C₀ C : Configuration D} (hInv : GCInvV C₀ C)
    {r₁ r₂ : Replica} {v₁ v₂ vT : Version} {s₁ s₂ : D.State}
    {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_head₁ : C.head r₁ = some v₁) (h_head₂ : C.head r₂ = some v₂)
    (h_ver₁ : C.ver v₁ = some (s₁, ev₁)) (h_ver₂ : C.ver v₂ = some (s₂, ev₂))
    (h_lca : IsLCA C.parents v₁ v₂ vT) :
    vT ∉ droppedSetV C₀ :=
  inMcasClosure_not_dropped hInv
    (InMcasClosure.mca
      (.head ⟨r₁, h_head₁⟩ (by rw [h_ver₁]; rfl))
      (.head ⟨r₂, h_head₂⟩ (by rw [h_ver₂]; rfl))
      (isMCA_singleton_of_isLCA C.parents_lt h_lca))

/-! ### §6V.2  The recursion reads only closure members: pruning commutes with the
virtual state (pure congruence, `parents`, hence every MCA query and the measure,
is shared by the pruned store). -/

private theorem vfoldAux_agree {C : Configuration D}
    (ver' : Version → Option (D.State × Set (Op D.AppOp)))
    (hagree : ∀ v, InMcasClosure C v → ver' v = C.ver v)
    {n : ℕ}
    (IH : ∀ k, k < n → ∀ (S : Finset Version) (w : Version),
      (supportOf C.parents (S ∪ {w})).card = k →
      (∀ x ∈ S, InMcasClosure C x) → InMcasClosure C w →
      vlcaAux ver' C.parents C.parents_lt S w
        = vlcaAux C.ver C.parents C.parents_lt S w)
    {S₀ : Finset Version} {w₀ : Version}
    (hcl : ∀ x ∈ mcaFinset C.parents S₀ w₀, InMcasClosure C x)
    (hstrict : (supportOf C.parents (mcaFinset C.parents S₀ w₀)).card < n)
    (pending : List Version) :
    ∀ (accS : Finset Version) (acc : D.State),
      (∀ x ∈ accS, x ∈ mcaFinset C.parents S₀ w₀) →
      (∀ x ∈ pending, x ∈ mcaFinset C.parents S₀ w₀) →
      vfoldAux ver' C.parents C.parents_lt accS acc pending
        = vfoldAux C.ver C.parents C.parents_lt accS acc pending := by
  induction pending with
  | nil =>
    intro accS acc _ _
    rw [vfoldAux_nil, vfoldAux_nil]
  | cons m ms ih =>
    intro accS acc haccS hpend
    rw [vfoldAux_cons, vfoldAux_cons]
    have hmM := hpend m List.mem_cons_self
    have hstateD : stateD ver' m = stateD C.ver m := by
      unfold stateD
      rw [hagree m (hcl m hmM)]
    have hsub : accS ∪ {m} ⊆ mcaFinset C.parents S₀ w₀ := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact haccS x hx
      · rw [Finset.mem_singleton] at hx; subst hx; exact hmM
    have hcard : (supportOf C.parents (accS ∪ {m})).card < n :=
      Nat.lt_of_le_of_lt
        (Finset.card_le_card (supportOf_mono C.parents C.parents_lt hsub)) hstrict
    have hinner : vlcaAux ver' C.parents C.parents_lt accS m
        = vlcaAux C.ver C.parents C.parents_lt accS m :=
      IH _ hcard accS m rfl (fun x hx => hcl x (haccS x hx)) (hcl m hmM)
    rw [hstateD, hinner]
    exact ih (accS ∪ {m}) _ (fun x hx => hsub hx)
      (fun x hx => hpend x (List.mem_cons_of_mem m hx))

/-- **The virtual state reads only the closure**: any store agreeing with `C`'s on
the current MCA closure computes the same `vlcaAux` at closure-supported pairs. -/
theorem vlcaAux_agree {C : Configuration D}
    (ver' : Version → Option (D.State × Set (Op D.AppOp)))
    (hagree : ∀ v, InMcasClosure C v → ver' v = C.ver v) :
    ∀ (n : ℕ) (S : Finset Version) (w : Version),
      (supportOf C.parents (S ∪ {w})).card = n →
      (∀ x ∈ S, InMcasClosure C x) → InMcasClosure C w →
      vlcaAux ver' C.parents C.parents_lt S w
        = vlcaAux C.ver C.parents C.parents_lt S w := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro S w hmeas hS hw
    have hcl : ∀ x ∈ mcaFinset C.parents S w, InMcasClosure C x := fun x hx =>
      inMcasClosure_of_mcaFinset hS hw hx
    rcases hsort : (mcaFinset C.parents S w).sort (· ≤ ·) with _ | ⟨m₁, ms₁⟩
    · rw [vlcaAux_of_sort_nil ver' C.parents C.parents_lt hsort,
        vlcaAux_of_sort_nil C.ver C.parents C.parents_lt hsort]
    · have hm₁M : m₁ ∈ mcaFinset C.parents S w := by
        rw [← Finset.mem_sort (· ≤ ·), hsort]
        exact List.mem_cons_self
      have hstateD : stateD ver' m₁ = stateD C.ver m₁ := by
        unfold stateD
        rw [hagree m₁ (hcl m₁ hm₁M)]
      rw [vlcaAux_of_sort_cons ver' C.parents C.parents_lt hsort,
        vlcaAux_of_sort_cons C.ver C.parents C.parents_lt hsort, hstateD]
      rcases ms₁ with _ | ⟨m₂, ms₂⟩
      · rw [vfoldAux_nil, vfoldAux_nil]
      · have hm₂M : m₂ ∈ mcaFinset C.parents S w := by
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
        exact vfoldAux_agree ver' hagree IH hcl hstrict (m₂ :: ms₂) {m₁} _
          (fun x hx => by rw [Finset.mem_singleton] at hx; subst hx; exact hm₁M)
          (fun x hx => by
            rw [← Finset.mem_sort (· ≤ ·), hsort]
            exact List.mem_cons_of_mem _ hx)

open Classical in
/-- Pruning to `keepSetV` preserves the virtual LCA state of a head pair. -/
theorem virtualLCAState_dropVerV {C₀ C : Configuration D} (hInv : GCInvV C₀ C)
    {r₁ r₂ : Replica} {v₁ v₂ : Version}
    (h_head₁ : C.head r₁ = some v₁) (h_head₂ : C.head r₂ = some v₂)
    (h_alloc₁ : (C.ver v₁).isSome) (h_alloc₂ : (C.ver v₂).isSome) :
    virtualLCAState
        (dropVer C (droppedSetV C₀) (zero_not_droppedV C₀) (heads_keptV hInv)) v₁ v₂
      = virtualLCAState C v₁ v₂ := by
  have hagree : ∀ v, InMcasClosure C v →
      (dropVer C (droppedSetV C₀) (zero_not_droppedV C₀) (heads_keptV hInv)).ver v
        = C.ver v := by
    intro v hv
    rw [dropVer_ver, if_neg (inMcasClosure_not_dropped hInv hv)]
  exact vlcaAux_agree (C := C) _ hagree _ {v₁} v₂ rfl
    (fun x hx => by
      rw [Finset.mem_singleton] at hx
      subst hx
      exact .head ⟨r₁, h_head₁⟩ h_alloc₁)
    (.head ⟨r₂, h_head₂⟩ h_alloc₂)

/-! ### §6V.3  Prune commutation and the headline, widened LTS -/

open Classical in
/-- **Prune commutation, virtual form** (`step_dropVer` on the widened LTS with the
`keepSetV` pruning): every `Step3V` step is matched, same label, by the pruned
images. The gated merge's LCA read survives via `lca_not_droppedV`; the virtual
merge's recursion reads survive via `inMcasClosure_not_dropped`, and the virtual
state is computed identically (`virtualLCAState_dropVerV`). -/
theorem step_dropVerV {C₀ C C' : Configuration D} {ℓ : Label3 D}
    (hInv : GCInvV C₀ C) (hstep : Step3V D C ℓ C')
    (hh' : ∀ r v, C'.head r = some v → (C'.ver v).isSome → v ∉ droppedSetV C₀) :
    Step3V D
      (dropVer C (droppedSetV C₀) (zero_not_droppedV C₀) (heads_keptV hInv)) ℓ
      (dropVer C' (droppedSetV C₀) (zero_not_droppedV C₀) hh') := by
  cases hstep with
  | base hstep' =>
    refine Step3V.base ?_
    cases hstep' with
    | @createReplica r h_fresh C'' hN hL hvis hver hhead hparents =>
      refine Step3.createReplica ?_ _ ?_ ?_ ?_ ?_ ?_ ?_
      · exact h_fresh
      · exact hN
      · exact hL
      · exact hvis
      · funext w
        simp only [dropVer_ver, hver]
      · exact hhead
      · exact hparents
    | @apply t r o v s ev vnew h_head h_ver h_fresh_t h_fresh_store h_vnew h_rank
        C'' hN hL hvis hver hhead hparents =>
      have hvKeep : v ∉ droppedSetV C₀ :=
        heads_keptV hInv r v h_head (by rw [h_ver]; rfl)
      have hvnewKeep : vnew ∉ droppedSetV C₀ := fun hm =>
        not_alloc₀_of_fresh hInv.toGCInv h_vnew hm.1
      refine Step3.apply (v := v) (s := s) (ev := ev) (vnew := vnew)
        ?_ ?_ ?_ ?_ ?_ h_rank _ ?_ ?_ ?_ ?_ ?_ ?_
      · exact h_head
      · show (if v ∈ droppedSetV C₀ then none else C.ver v) = some (s, ev)
        rw [if_neg hvKeep]; exact h_ver
      · exact h_fresh_t
      · intro w sw Ew hw
        by_cases hwS : w ∈ droppedSetV C₀
        · rw [dropVer_ver, if_pos hwS] at hw; cases hw
        · rw [dropVer_ver, if_neg hwS] at hw
          exact h_fresh_store w sw Ew hw
      · show (if vnew ∈ droppedSetV C₀ then none else C.ver vnew) = none
        rw [if_neg hvnewKeep]; exact h_vnew
      · exact hN
      · exact hL
      · exact hvis
      · funext w
        simp only [dropVer_ver, hver]
        by_cases hw : w = vnew
        · subst hw; simp [hvnewKeep]
        · simp [hw]
      · exact hhead
      · exact hparents
    | @merge r₁ r₂ v₁ v₂ vT vm s₁ s₂ sT ev₁ ev₂ evT h_head₁ h_head₂ h_ver₁ h_ver₂
        h_lca h_verT h_vm h_rank₁ h_rank₂ C'' hN hL hvis hver hhead hparents =>
      have hv₁Keep : v₁ ∉ droppedSetV C₀ :=
        heads_keptV hInv r₁ v₁ h_head₁ (by rw [h_ver₁]; rfl)
      have hv₂Keep : v₂ ∉ droppedSetV C₀ :=
        heads_keptV hInv r₂ v₂ h_head₂ (by rw [h_ver₂]; rfl)
      have hvTKeep : vT ∉ droppedSetV C₀ :=
        lca_not_droppedV hInv h_head₁ h_head₂ h_ver₁ h_ver₂ h_lca
      have hvmKeep : vm ∉ droppedSetV C₀ := fun hm =>
        not_alloc₀_of_fresh hInv.toGCInv h_vm hm.1
      refine Step3.merge (v₁ := v₁) (v₂ := v₂) (vT := vT) (vm := vm)
        (s₁ := s₁) (s₂ := s₂) (sT := sT) (ev₁ := ev₁) (ev₂ := ev₂) (evT := evT)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ h_rank₁ h_rank₂ _ ?_ ?_ ?_ ?_ ?_ ?_
      · exact h_head₁
      · exact h_head₂
      · show (if v₁ ∈ droppedSetV C₀ then none else C.ver v₁) = some (s₁, ev₁)
        rw [if_neg hv₁Keep]; exact h_ver₁
      · show (if v₂ ∈ droppedSetV C₀ then none else C.ver v₂) = some (s₂, ev₂)
        rw [if_neg hv₂Keep]; exact h_ver₂
      · exact h_lca
      · show (if vT ∈ droppedSetV C₀ then none else C.ver vT) = some (sT, evT)
        rw [if_neg hvTKeep]; exact h_verT
      · show (if vm ∈ droppedSetV C₀ then none else C.ver vm) = none
        rw [if_neg hvmKeep]; exact h_vm
      · exact hN
      · exact hL
      · exact hvis
      · funext w
        simp only [dropVer_ver, hver]
        by_cases hw : w = vm
        · subst hw; simp [hvmKeep]
        · simp [hw]
      · exact hhead
      · exact hparents
    | @query r q vq s h_s h_val =>
      exact Step3.query (s := s) h_s h_val
  | @mergeVirtual r₁ r₂ v₁ v₂ vm s₁ s₂ ev₁ ev₂ h_head₁ h_head₂ h_ver₁ h_ver₂
      h_vm h_rank₁ h_rank₂ C'' hN hL hvis hver hhead hparents =>
    have hv₁Keep : v₁ ∉ droppedSetV C₀ :=
      heads_keptV hInv r₁ v₁ h_head₁ (by rw [h_ver₁]; rfl)
    have hv₂Keep : v₂ ∉ droppedSetV C₀ :=
      heads_keptV hInv r₂ v₂ h_head₂ (by rw [h_ver₂]; rfl)
    have hvmKeep : vm ∉ droppedSetV C₀ := fun hm =>
      not_alloc₀_of_fresh hInv.toGCInv h_vm hm.1
    have hvirt := virtualLCAState_dropVerV hInv h_head₁ h_head₂
      (by rw [h_ver₁]; rfl) (by rw [h_ver₂]; rfl)
    refine Step3V.mergeVirtual (v₁ := v₁) (v₂ := v₂) (vm := vm)
      (s₁ := s₁) (s₂ := s₂) (ev₁ := ev₁) (ev₂ := ev₂)
      ?_ ?_ ?_ ?_ ?_ h_rank₁ h_rank₂ _ ?_ ?_ ?_ ?_ ?_ ?_
    · exact h_head₁
    · exact h_head₂
    · show (if v₁ ∈ droppedSetV C₀ then none else C.ver v₁) = some (s₁, ev₁)
      rw [if_neg hv₁Keep]; exact h_ver₁
    · show (if v₂ ∈ droppedSetV C₀ then none else C.ver v₂) = some (s₂, ev₂)
      rw [if_neg hv₂Keep]; exact h_ver₂
    · show (if vm ∈ droppedSetV C₀ then none else C.ver vm) = none
      rw [if_neg hvmKeep]; exact h_vm
    · rw [hvirt]
      exact hN
    · exact hL
    · exact hvis
    · funext w
      rw [hvirt]
      simp only [dropVer_ver, hver]
      by_cases hw : w = vm
      · subst hw; simp [hvmKeep]
      · simp [hw]
    · exact hhead
    · exact hparents

/-- A labelled `Step3V` run (finite trace on the widened LTS). -/
inductive StepsV (D : ConditionedMRDTSig) :
    Configuration D → List (Label3 D) → Configuration D → Prop where
  | nil (C : Configuration D) : StepsV D C [] C
  | cons {C C' C'' : Configuration D} {ℓ : Label3 D} {ℓs : List (Label3 D)} :
      Step3V D C ℓ C' → StepsV D C' ℓs C'' → StepsV D C (ℓ :: ℓs) C''

/-- Every gated run is a widened run. -/
theorem stepsV_of_steps {C : Configuration D} {ℓs : List (Label3 D)}
    {C' : Configuration D} (hrun : Steps D C ℓs C') : StepsV D C ℓs C' := by
  induction hrun with
  | nil C => exact StepsV.nil C
  | cons hstep _ ih => exact StepsV.cons (Step3V.base hstep) ih

/-- `GCInvV` along a widened run. -/
theorem gcInvV_steps {C₀ : Configuration D} {C ℓs C'}
    (hrun : StepsV D C ℓs C') : GCInvV C₀ C → GCInvV C₀ C' := by
  induction hrun with
  | nil => exact id
  | cons hstep _ ih => exact fun hInv => ih (gcInvV_step hInv hstep)

/-- Run-level prune commutation on the widened LTS. -/
theorem steps_dropVerV {C₀ : Configuration D} {C ℓs C'}
    (hrun : StepsV D C ℓs C') (hInv : GCInvV C₀ C)
    (hh : ∀ r v, C.head r = some v → (C.ver v).isSome → v ∉ droppedSetV C₀)
    (hh' : ∀ r v, C'.head r = some v → (C'.ver v).isSome → v ∉ droppedSetV C₀) :
    StepsV D (dropVer C (droppedSetV C₀) (zero_not_droppedV C₀) hh) ℓs
      (dropVer C' (droppedSetV C₀) (zero_not_droppedV C₀) hh') := by
  induction hrun with
  | nil => exact StepsV.nil _
  | @cons Ca Cb Cc ℓ ℓs hstep hrest ih =>
    exact StepsV.cons
      (step_dropVerV hInv hstep (heads_keptV (gcInvV_step hInv hstep)))
      (ih (gcInvV_step hInv hstep) (heads_keptV (gcInvV_step hInv hstep)) hh')

/-- The prune-point configuration under the MCA-closure keep set. -/
noncomputable def pruneKeepV (C₀ : Configuration D)
    (hStore : StoreInv C₀.ver C₀.parents) : Configuration D :=
  dropVer C₀ (droppedSetV C₀) (zero_not_droppedV C₀)
    (heads_keptV (gcInvV_init C₀ hStore))

/-- **Commit GC safety on the widened LTS**: pruning the store to the
MCA-closure keep set
`keepSetV = {v : ∃ w ∈ mcasClosure(heads), E(w) ⊆ E(v)} ∪ {0}` preserves every
`Step3V` run, gated merges AND virtual (recursive) merges, same label trace, and
every head read, from the single hypothesis `StoreInv C₀`. -/
theorem gc_safetyV (C₀ : Configuration D) (hStore : StoreInv C₀.ver C₀.parents)
    {ℓs : List (Label3 D)} {C : Configuration D} (hRun : StepsV D C₀ ℓs C) :
    StepsV D (pruneKeepV C₀ hStore) ℓs
      (dropVer C (droppedSetV C₀) (zero_not_droppedV C₀)
        (heads_keptV (gcInvV_steps hRun (gcInvV_init C₀ hStore))))
    ∧ ∀ r, (dropVer C (droppedSetV C₀) (zero_not_droppedV C₀)
        (heads_keptV (gcInvV_steps hRun (gcInvV_init C₀ hStore)))).N r = C.N r :=
  ⟨steps_dropVerV hRun (gcInvV_init C₀ hStore) _ _, fun _ => rfl⟩

/-! ### Axiom audit -/

#print axioms gcInvV_step
#print axioms mcaClosure_not_dropped
#print axioms lca_not_droppedV
#print axioms virtualLCAState_dropVerV
#print axioms step_dropVerV
#print axioms gc_safetyV

end GC

/-! ## §7 SPOT + the head-sync necessity countermodel

A concrete 6-version DAG over the Framework-resident `GSetCond` (no `MRDT_Instances`
import). Replica A = 0, B = 1; events `e1 e2 e3 e4` with distinct timestamps. History:
A applies `e1` (version 1) then `e2` (version 2); B merges A through LCA 0 (version 3);
A applies `e3` (version 4); B applies `e4` (version 5). Heads: A at 4, B at 5.

Hand-derived (never `#eval`'d): `E(4) ∩ E(5) = {e1,e2}`, so `Keep = {2,3,4,5}`,
`Keep' = {0,2,3,4,5}`, and **version 1 is dropped** (its `{e1}` contains no pairwise
head intersection). Pruning is strict. The head merge's LCA is 2 (kept, still
registered after pruning); the interior pair `(1,5)` has LCA 1, dropped, which is the
necessity countermodel for head-sync. -/

namespace GCSpot

/-- Op alias for the toy: `(timestamp, replica, payload)`. -/
abbrev O := Op GSetCond.AppOp

def e1 : O := (1, 0, (10 : Nat))
def e2 : O := (2, 0, (20 : Nat))
def e3 : O := (3, 0, (30 : Nat))
def e4 : O := (4, 1, (40 : Nat))

def F1 : Set O := {e1}
def F2 : Set O := {e1, e2}
def F4 : Set O := {e1, e2, e3}
def F5 : Set O := {e1, e2, e4}

def S1 : Set Nat := {10}
def S2 : Set Nat := {10, 20}
def S4 : Set Nat := {10, 20, 30}
def S5 : Set Nat := {10, 20, 40}

/-- The ranked store: version ↦ `(state, event set)`. -/
noncomputable def verEx : Version → Option (GSetCond.State × Set O) := fun v =>
  if v = 0 then some ((∅ : Set Nat), (∅ : Set O))
  else if v = 1 then some (S1, F1)
  else if v = 2 then some (S2, F2)
  else if v = 3 then some (S2, F2)
  else if v = 4 then some (S4, F4)
  else if v = 5 then some (S5, F5)
  else none

/-- The version DAG. -/
def parEx : Version → List Version := fun v =>
  if v = 1 then [0]
  else if v = 2 then [1]
  else if v = 3 then [0, 2]
  else if v = 4 then [2]
  else if v = 5 then [3]
  else []

/-! ### Reachability in the toy DAG: chains and inversions -/

theorem re_01 : Reaches parEx 0 1 := Relation.ReflTransGen.single (by decide)
theorem re_12 : Reaches parEx 1 2 := Relation.ReflTransGen.single (by decide)
theorem re_23 : Reaches parEx 2 3 := Relation.ReflTransGen.single (by decide)
theorem re_03 : Reaches parEx 0 3 := Relation.ReflTransGen.single (by decide)
theorem re_24 : Reaches parEx 2 4 := Relation.ReflTransGen.single (by decide)
theorem re_35 : Reaches parEx 3 5 := Relation.ReflTransGen.single (by decide)
theorem re_02 : Reaches parEx 0 2 := re_01.trans re_12
theorem re_13 : Reaches parEx 1 3 := re_12.trans re_23
theorem re_14 : Reaches parEx 1 4 := re_12.trans re_24
theorem re_25 : Reaches parEx 2 5 := re_23.trans re_35
theorem re_15 : Reaches parEx 1 5 := re_13.trans re_35

theorem reachEx0 {w : Version} (h : Reaches parEx w 0) : w = 0 := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, _, hstep⟩
  · exact h.symm
  · exact absurd hstep (by simp [parEx])

theorem reachEx1 {w : Version} (h : Reaches parEx w 1) : w = 1 ∨ w = 0 := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hpre, hstep⟩
  · exact Or.inl h.symm
  · have hc : c = 0 := by simpa [parEx] using hstep
    subst hc
    exact Or.inr (reachEx0 hpre)

theorem reachEx2 {w : Version} (h : Reaches parEx w 2) : w = 2 ∨ w = 1 ∨ w = 0 := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hpre, hstep⟩
  · exact Or.inl h.symm
  · have hc : c = 1 := by simpa [parEx] using hstep
    subst hc
    exact Or.inr (reachEx1 hpre)

theorem reachEx3 {w : Version} (h : Reaches parEx w 3) :
    w = 3 ∨ w = 2 ∨ w = 1 ∨ w = 0 := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hpre, hstep⟩
  · exact Or.inl h.symm
  · have hc : c = 0 ∨ c = 2 := by simpa [parEx] using hstep
    rcases hc with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (reachEx0 hpre)))
    · exact Or.inr (reachEx2 hpre)

theorem reachEx4 {w : Version} (h : Reaches parEx w 4) :
    w = 4 ∨ w = 2 ∨ w = 1 ∨ w = 0 := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hpre, hstep⟩
  · exact Or.inl h.symm
  · have hc : c = 2 := by simpa [parEx] using hstep
    subst hc
    exact Or.inr (reachEx2 hpre)

theorem reachEx5 {w : Version} (h : Reaches parEx w 5) :
    w = 5 ∨ w = 3 ∨ w = 2 ∨ w = 1 ∨ w = 0 := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hpre, hstep⟩
  · exact Or.inl h.symm
  · have hc : c = 3 := by simpa [parEx] using hstep
    subst hc
    exact Or.inr (reachEx3 hpre)

/-! ### The store invariant for the toy store -/

theorem verEx0 : verEx 0 = some ((∅ : Set Nat), (∅ : Set O)) := rfl
theorem verEx1 : verEx 1 = some (S1, F1) := rfl
theorem verEx2 : verEx 2 = some (S2, F2) := rfl
theorem verEx3 : verEx 3 = some (S2, F2) := rfl
theorem verEx4 : verEx 4 = some (S4, F4) := rfl
theorem verEx5 : verEx 5 = some (S5, F5) := rfl

theorem F1_sub_F2 : F1 ⊆ F2 := fun _ hx => Or.inl hx
theorem F2_sub_F4 : F2 ⊆ F4 := fun _ hx => hx.imp id Or.inl
theorem F2_sub_F5 : F2 ⊆ F5 := fun _ hx => hx.imp id Or.inl

/-- Inversion for the toy store: an allocated version is one of the six. -/
theorem verEx_cases {w : Version} {x : GSetCond.State × Set O}
    (hw : verEx w = some x) :
    w = 0 ∧ x = ((∅ : Set Nat), (∅ : Set O)) ∨ w = 1 ∧ x = (S1, F1) ∨
    w = 2 ∧ x = (S2, F2) ∨ w = 3 ∧ x = (S2, F2) ∨ w = 4 ∧ x = (S4, F4) ∨
    w = 5 ∧ x = (S5, F5) := by
  unfold verEx at hw
  by_cases h0 : w = 0
  · rw [if_pos h0] at hw
    exact Or.inl ⟨h0, ((Option.some.injEq _ _).mp hw).symm⟩
  rw [if_neg h0] at hw
  by_cases h1 : w = 1
  · rw [if_pos h1] at hw
    exact Or.inr (Or.inl ⟨h1, ((Option.some.injEq _ _).mp hw).symm⟩)
  rw [if_neg h1] at hw
  by_cases h2 : w = 2
  · rw [if_pos h2] at hw
    exact Or.inr (Or.inr (Or.inl ⟨h2, ((Option.some.injEq _ _).mp hw).symm⟩))
  rw [if_neg h2] at hw
  by_cases h3 : w = 3
  · rw [if_pos h3] at hw
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, ((Option.some.injEq _ _).mp hw).symm⟩)))
  rw [if_neg h3] at hw
  by_cases h4 : w = 4
  · rw [if_pos h4] at hw
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨h4, ((Option.some.injEq _ _).mp hw).symm⟩))))
  rw [if_neg h4] at hw
  by_cases h5 : w = 5
  · rw [if_pos h5] at hw
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨h5, ((Option.some.injEq _ _).mp hw).symm⟩))))
  rw [if_neg h5] at hw
  cases hw

/-- Inversion for the toy DAG's edges. -/
theorem parEx_cases {v p : Version} (hp : p ∈ parEx v) :
    v = 1 ∧ p = 0 ∨ v = 2 ∧ p = 1 ∨ v = 3 ∧ (p = 0 ∨ p = 2) ∨
    v = 4 ∧ p = 2 ∨ v = 5 ∧ p = 3 := by
  unfold parEx at hp
  by_cases h1 : v = 1
  · rw [if_pos h1] at hp
    exact Or.inl ⟨h1, by simpa using hp⟩
  rw [if_neg h1] at hp
  by_cases h2 : v = 2
  · rw [if_pos h2] at hp
    exact Or.inr (Or.inl ⟨h2, by simpa using hp⟩)
  rw [if_neg h2] at hp
  by_cases h3 : v = 3
  · rw [if_pos h3] at hp
    exact Or.inr (Or.inr (Or.inl ⟨h3, by simpa using hp⟩))
  rw [if_neg h3] at hp
  by_cases h4 : v = 4
  · rw [if_pos h4] at hp
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h4, by simpa using hp⟩)))
  rw [if_neg h4] at hp
  by_cases h5 : v = 5
  · rw [if_pos h5] at hp
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h5, by simpa using hp⟩)))
  rw [if_neg h5] at hp
  exact absurd hp List.not_mem_nil

/-- Every version containing `e1` is reachable from its generator, version 1. -/
theorem cont_e1 : ∀ {w : Version} {sw : GSetCond.State} {Ew : Set O},
    verEx w = some (sw, Ew) → e1 ∈ Ew → Reaches parEx 1 w := by
  intro w sw Ew hw he
  rcases verEx_cases hw with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
    ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;>
    (rw [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx)
  · exact absurd he (Set.notMem_empty _)
  · exact Relation.ReflTransGen.refl
  · exact re_12
  · exact re_13
  · exact re_14
  · exact re_15

/-- Every version containing `e2` is reachable from its generator, version 2. -/
theorem cont_e2 : ∀ {w : Version} {sw : GSetCond.State} {Ew : Set O},
    verEx w = some (sw, Ew) → e2 ∈ Ew → Reaches parEx 2 w := by
  intro w sw Ew hw he
  rcases verEx_cases hw with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
    ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;>
    (rw [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx)
  · exact absurd he (Set.notMem_empty _)
  · simp [F1, e1, e2, Set.mem_singleton_iff, Prod.mk.injEq] at he
  · exact Relation.ReflTransGen.refl
  · exact re_23
  · exact re_24
  · exact re_25

/-- Only version 4 contains `e3`; it is its own generator. -/
theorem cont_e3 : ∀ {w : Version} {sw : GSetCond.State} {Ew : Set O},
    verEx w = some (sw, Ew) → e3 ∈ Ew → Reaches parEx 4 w := by
  intro w sw Ew hw he
  rcases verEx_cases hw with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
    ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;>
    (rw [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx)
  · exact absurd he (Set.notMem_empty _)
  · simp [F1, e1, e3, Set.mem_singleton_iff, Prod.mk.injEq] at he
  · simp [F2, e1, e2, e3, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq] at he
  · simp [F2, e1, e2, e3, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq] at he
  · exact Relation.ReflTransGen.refl
  · simp [F5, e1, e2, e3, e4, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq] at he

/-- Only version 5 contains `e4`; it is its own generator. -/
theorem cont_e4 : ∀ {w : Version} {sw : GSetCond.State} {Ew : Set O},
    verEx w = some (sw, Ew) → e4 ∈ Ew → Reaches parEx 5 w := by
  intro w sw Ew hw he
  rcases verEx_cases hw with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
    ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;>
    (rw [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx)
  · exact absurd he (Set.notMem_empty _)
  · simp [F1, e1, e4, Set.mem_singleton_iff, Prod.mk.injEq] at he
  · simp [F2, e1, e2, e4, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq] at he
  · simp [F2, e1, e2, e4, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq] at he
  · simp [F4, e1, e2, e3, e4, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq] at he
  · exact Relation.ReflTransGen.refl

/-- The toy store satisfies the framework's `StoreInv`, so the LCA lemma
(`lca_events_of_storeInv`) discharges `Cex`'s `lca_events` field generically: no
per-triple LCA analysis needed. -/
theorem storeInvEx : StoreInv (D := GSetCond) verEx parEx := by
  refine ⟨?_, ?_, ?_⟩
  · -- parents_alloc
    intro v p hp
    rcases parEx_cases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hp'⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · rfl
    · rcases hp' with rfl | rfl <;> rfl
    · rfl
    · rfl
  · -- events_mono
    intro v p hp sp Ep sv Ev hvp hvv
    rcases parEx_cases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hp'⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [verEx0, Option.some.injEq, Prod.mk.injEq] at hvp
      obtain ⟨rfl, rfl⟩ := hvp
      exact Set.empty_subset _
    · rw [verEx1, Option.some.injEq, Prod.mk.injEq] at hvp
      rw [verEx2, Option.some.injEq, Prod.mk.injEq] at hvv
      obtain ⟨rfl, rfl⟩ := hvp
      obtain ⟨rfl, rfl⟩ := hvv
      exact F1_sub_F2
    · rw [verEx3, Option.some.injEq, Prod.mk.injEq] at hvv
      obtain ⟨rfl, rfl⟩ := hvv
      rcases hp' with rfl | rfl
      · rw [verEx0, Option.some.injEq, Prod.mk.injEq] at hvp
        obtain ⟨rfl, rfl⟩ := hvp
        exact Set.empty_subset _
      · rw [verEx2, Option.some.injEq, Prod.mk.injEq] at hvp
        obtain ⟨rfl, rfl⟩ := hvp
        exact fun _ hx => hx
    · rw [verEx2, Option.some.injEq, Prod.mk.injEq] at hvp
      rw [verEx4, Option.some.injEq, Prod.mk.injEq] at hvv
      obtain ⟨rfl, rfl⟩ := hvp
      obtain ⟨rfl, rfl⟩ := hvv
      exact F2_sub_F4
    · rw [verEx3, Option.some.injEq, Prod.mk.injEq] at hvp
      rw [verEx5, Option.some.injEq, Prod.mk.injEq] at hvv
      obtain ⟨rfl, rfl⟩ := hvp
      obtain ⟨rfl, rfl⟩ := hvv
      exact F2_sub_F5
  · -- origin
    intro v s E hv e he
    rcases verEx_cases hv with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩ |
      ⟨rfl, hx⟩ | ⟨rfl, hx⟩ <;>
      (rw [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx)
    · exact absurd he (Set.notMem_empty _)
    · simp only [F1, Set.mem_singleton_iff] at he
      subst he
      exact ⟨1, S1, F1, verEx1, rfl, cont_e1⟩
    · simp only [F2, Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl
      · exact ⟨1, S1, F1, verEx1, rfl, cont_e1⟩
      · exact ⟨2, S2, F2, verEx2, Or.inr rfl, cont_e2⟩
    · simp only [F2, Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl
      · exact ⟨1, S1, F1, verEx1, rfl, cont_e1⟩
      · exact ⟨2, S2, F2, verEx2, Or.inr rfl, cont_e2⟩
    · simp only [F4, Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl | rfl
      · exact ⟨1, S1, F1, verEx1, rfl, cont_e1⟩
      · exact ⟨2, S2, F2, verEx2, Or.inr rfl, cont_e2⟩
      · exact ⟨4, S4, F4, verEx4, Or.inr (Or.inr rfl), cont_e3⟩
    · simp only [F5, Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl | rfl
      · exact ⟨1, S1, F1, verEx1, rfl, cont_e1⟩
      · exact ⟨2, S2, F2, verEx2, Or.inr rfl, cont_e2⟩
      · exact ⟨5, S5, F5, verEx5, Or.inr (Or.inr rfl), cont_e4⟩

/-! ### The concrete configuration -/

noncomputable def Nex : Replica → Option GSetCond.State := fun r =>
  if r = 0 then some S4 else if r = 1 then some S5 else none

noncomputable def Lex : Replica → Option (Set O) := fun r =>
  if r = 0 then some F4 else if r = 1 then some F5 else none

def headEx : Replica → Option Version := fun r =>
  if r = 0 then some 4 else if r = 1 then some 5 else none

/-- The causal order: `e1 → e2 → e3` (A's chain); `e1, e2 → e4` (B applied `e4` after
absorbing A's `{e1, e2}` prefix); `e3 ∥ e4`. -/
abbrev visEx (a b : O) : Prop :=
  (a = e1 ∧ b = e2) ∨ (a = e1 ∧ b = e3) ∨ (a = e2 ∧ b = e3) ∨
  (a = e1 ∧ b = e4) ∨ (a = e2 ∧ b = e4)

theorem e4_nmem_F4 : e4 ∉ F4 := by
  intro h
  simp only [F4, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h <;> exact absurd (congrArg Prod.fst h) (by decide)

theorem e3_nmem_F5 : e3 ∉ F5 := by
  intro h
  simp only [F5, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h <;> exact absurd (congrArg Prod.fst h) (by decide)

theorem e2_nmem_F1 : e2 ∉ F1 := by
  intro h
  simp only [F1, Set.mem_singleton_iff] at h
  exact absurd (congrArg Prod.fst h) (by decide)

/-- Every observed event is one of the four. -/
theorem mem_of_Lex {r : Replica} {s : Set O} {a : O} (hL : Lex r = some s)
    (ha : a ∈ s) : a = e1 ∨ a = e2 ∨ a = e3 ∨ a = e4 := by
  unfold Lex at hL
  by_cases h0 : r = 0
  · rw [if_pos h0] at hL
    injection hL with hL
    subst hL
    simp only [F4, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    exact ha.imp id (Or.imp id Or.inl)
  rw [if_neg h0] at hL
  by_cases h1 : r = 1
  · rw [if_pos h1] at hL
    injection hL with hL
    subst hL
    simp only [F5, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    exact ha.imp id (Or.imp id Or.inr)
  rw [if_neg h1] at hL
  cases hL

/-- The prune-point configuration (see the §7 header for the history). -/
noncomputable def Cex : Configuration GSetCond where
  N := Nex
  L := Lex
  vis := visEx
  dom_eq := by
    intro r
    unfold Nex Lex
    by_cases h0 : r = 0
    · rw [if_pos h0, if_pos h0]; simp
    rw [if_neg h0, if_neg h0]
    by_cases h1 : r = 1
    · rw [if_pos h1, if_pos h1]; simp
    rw [if_neg h1, if_neg h1]
    exact iff_of_true rfl rfl
  vis_src := by
    intro a b hv
    rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨0, F4, rfl, Or.inl rfl⟩
    · exact ⟨0, F4, rfl, Or.inl rfl⟩
    · exact ⟨0, F4, rfl, Or.inr (Or.inl rfl)⟩
    · exact ⟨0, F4, rfl, Or.inl rfl⟩
    · exact ⟨0, F4, rfl, Or.inr (Or.inl rfl)⟩
  vis_tgt := by
    intro a b hv
    rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨0, F4, rfl, Or.inr (Or.inl rfl)⟩
    · exact ⟨0, F4, rfl, Or.inr (Or.inr rfl)⟩
    · exact ⟨0, F4, rfl, Or.inr (Or.inr rfl)⟩
    · exact ⟨1, F5, rfl, Or.inr (Or.inr rfl)⟩
    · exact ⟨1, F5, rfl, Or.inr (Or.inr rfl)⟩
  vis_causal := by
    intro a b r s hv hL hb
    have hL' : Lex r = some s := hL
    unfold Lex at hL'
    by_cases h0 : r = 0
    · rw [if_pos h0] at hL'
      injection hL' with hL'
      subst hL'
      rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact absurd hb e4_nmem_F4
      · exact absurd hb e4_nmem_F4
    rw [if_neg h0] at hL'
    by_cases h1 : r = 1
    · rw [if_pos h1] at hL'
      injection hL' with hL'
      subst hL'
      rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl rfl
      · exact absurd hb e3_nmem_F5
      · exact absurd hb e3_nmem_F5
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    rw [if_neg h1] at hL'
    cases hL'
  timestamps_distinct := by
    intro a b r s r' s' hL hsa hL' hsb hab
    rcases mem_of_Lex hL hsa with rfl | rfl | rfl | rfl <;>
      rcases mem_of_Lex hL' hsb with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hab
        | decide
  causal_mono := by
    intro a b hv
    rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      decide
  vis_total_same_replica := by
    intro a b r s r' s' hL hsa hL' hsb hab hrep
    rcases mem_of_Lex hL hsa with rfl | rfl | rfl | rfl <;>
      rcases mem_of_Lex hL' hsb with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hab
        | exact absurd hrep (by decide)
        | exact Or.inl (Or.inl ⟨rfl, rfl⟩)
        | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        | exact Or.inl (Or.inr (Or.inl ⟨rfl, rfl⟩))
        | exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
        | exact Or.inl (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
        | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  ver := verEx
  head := headEx
  parents := parEx
  parents_lt := by
    intro v p hp
    rcases parEx_cases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hp'⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · decide
    · decide
    · rcases hp' with rfl | rfl <;> decide
    · decide
    · decide
  ver_init := rfl
  head_coherent := by
    intro r v hr
    have hr' : headEx r = some v := hr
    unfold headEx at hr'
    by_cases h0 : r = 0
    · rw [if_pos h0] at hr'
      injection hr' with hr'
      subst hr'
      subst h0
      exact ⟨rfl, rfl⟩
    rw [if_neg h0] at hr'
    by_cases h1 : r = 1
    · rw [if_pos h1] at hr'
      injection hr' with hr'
      subst hr'
      subst h1
      exact ⟨rfl, rfl⟩
    rw [if_neg h1] at hr'
    cases hr'
  ver_inv := fun _ _ _ _ => trivial
  lca_events := fun hlca h1 h2 hT => lca_events_of_storeInv storeInvEx hlca h1 h2 hT

/-! ### Keep, dropped, and the SPOT verdicts (all expected values hand-derived) -/

theorem head4 : IsHead Cex 4 := ⟨0, rfl⟩
theorem head5 : IsHead Cex 5 := ⟨1, rfl⟩

/-- The heads are exactly 4 and 5. -/
theorem head_cases {h : Version} (hh : IsHead Cex h) : h = 4 ∨ h = 5 := by
  obtain ⟨r, hr⟩ := hh
  have hr' : headEx r = some h := hr
  unfold headEx at hr'
  by_cases h0 : r = 0
  · rw [if_pos h0] at hr'
    injection hr' with hr'
    exact Or.inl hr'.symm
  rw [if_neg h0] at hr'
  by_cases h1 : r = 1
  · rw [if_pos h1] at hr'
    injection hr' with hr'
    exact Or.inr hr'.symm
  rw [if_neg h1] at hr'
  cases hr'

/-- Every allocated head's event set contains `e2` (so does every pairwise
intersection of head event sets). -/
theorem head_events_e2 {h : Version} (hh : IsHead Cex h) {s : GSetCond.State}
    {f : Set O} (hv : Cex.ver h = some (s, f)) : e2 ∈ f := by
  rcases head_cases hh with rfl | rfl
  · have hv' : verEx 4 = some (s, f) := hv
    rw [verEx4, Option.some.injEq, Prod.mk.injEq] at hv'
    rw [← hv'.2]
    exact Or.inr (Or.inl rfl)
  · have hv' : verEx 5 = some (s, f) := hv
    rw [verEx5, Option.some.injEq, Prod.mk.injEq] at hv'
    rw [← hv'.2]
    exact Or.inr (Or.inl rfl)

/-- **Version 1 is dropped**: `E(1) = {e1}` contains no pairwise head intersection
(each contains `e2`), and `1` is not the pinned root. Pruning is strict. -/
theorem one_dropped : (1 : Version) ∈ droppedSet Cex := by
  refine ⟨rfl, ?_⟩
  rintro (⟨h₁, h₂, s₁, f₁, s₂, f₂, s, f, hh₁, hh₂, hv₁, hv₂, hv, hsub⟩ | h0)
  · have hv' : verEx 1 = some (s, f) := hv
    rw [verEx1, Option.some.injEq, Prod.mk.injEq] at hv'
    have he2 : e2 ∈ f := hsub ⟨head_events_e2 hh₁ hv₁, head_events_e2 hh₂ hv₂⟩
    rw [← hv'.2] at he2
    exact e2_nmem_F1 he2
  · exact absurd h0 (by decide)

/-- Hand-derived: `E(4) ∩ E(5) = {e1, e2} ⊆ E(2)`. -/
theorem F45_sub_F2 : F4 ∩ F5 ⊆ F2 := by
  rintro x ⟨hx4, hx5⟩
  simp only [F4, F5, Set.mem_insert_iff, Set.mem_singleton_iff] at hx4 hx5
  rcases hx4 with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · rcases hx5 with h | h | h <;> exact absurd (congrArg Prod.fst h) (by decide)

/-- Version 2, the future merge's LCA, is kept. -/
theorem two_kept : (2 : Version) ∈ keepSet Cex :=
  ⟨4, 5, S4, F4, S5, F5, S2, F2, head4, head5, verEx4, verEx5, verEx2, F45_sub_F2⟩

theorem two_not_dropped : (2 : Version) ∉ droppedSet Cex :=
  fun hm => hm.2 (Or.inl two_kept)

/-- The pruned prune-point configuration. -/
noncomputable def CexPruned : Configuration GSetCond := pruneKeep Cex storeInvEx

open Classical in
/-- **SPOT FAIL-companion**: pruning is not a no-op: the dropped entry is genuinely
absent (while `Cex.ver 1 = some (S1, F1)`, see `spot_prune_strict`). -/
theorem spot_pruned_absent : CexPruned.ver 1 = none := by
  show (if (1 : Version) ∈ droppedSet Cex then none else Cex.ver 1) = none
  rw [if_pos one_dropped]

/-- The dropped version was allocated before the prune (hand-derived literal). -/
theorem spot_prune_strict : Cex.ver 1 = some (S1, F1) := rfl

open Classical in
/-- **SPOT PASS**: the future head merge's LCA (version 2) is still registered after
pruning, with the hand-derived `(state, events)` payload. -/
theorem spot_lca_present : CexPruned.ver 2 = some (S2, F2) := by
  show (if (2 : Version) ∈ droppedSet Cex then none else Cex.ver 2) = some (S2, F2)
  rw [if_neg two_not_dropped]
  rfl

/-- `IsLCA` of the head pair `(4, 5)` is version 2 (common ancestors `{0,1,2}`, all
reaching 2). -/
theorem spot_isLCA : IsLCA Cex.parents 4 5 2 := by
  refine ⟨re_24, re_25, ?_⟩
  intro w h4 h5
  rcases reachEx4 h4 with rfl | rfl | rfl | rfl
  · rcases reachEx5 h5 with h | h | h | h | h <;> exact absurd h (by decide)
  · exact Relation.ReflTransGen.refl
  · exact re_12
  · exact re_02

open Classical in
/-- **SPOT PASS, full merge enabledness in the pruned configuration**: every premise of
`Step3.merge` for the head pair holds after pruning (heads, head payloads, the `IsLCA`
witness, the registered LCA payload, a fresh slot `6`, the rank bounds). Together with
the generic `step_dropVer`/`merged_store_lca_events` machinery, the head merge fires in
the pruned world exactly as in the unpruned one. -/
theorem spot_merge_enabled :
    CexPruned.head 0 = some 4 ∧ CexPruned.head 1 = some 5 ∧
    CexPruned.ver 4 = some (S4, F4) ∧ CexPruned.ver 5 = some (S5, F5) ∧
    IsLCA CexPruned.parents 4 5 2 ∧ CexPruned.ver 2 = some (S2, F2) ∧
    CexPruned.ver 6 = none ∧ (4 : Version) < 6 ∧ (5 : Version) < 6 := by
  refine ⟨rfl, rfl, ?_, ?_, spot_isLCA, spot_lca_present, ?_, by decide, by decide⟩
  · show (if (4 : Version) ∈ droppedSet Cex then none else Cex.ver 4) = some (S4, F4)
    rw [if_neg (fun hm => hm.2 (Or.inl (head_mem_keepSet head4 verEx4)))]
    rfl
  · show (if (5 : Version) ∈ droppedSet Cex then none else Cex.ver 5) = some (S5, F5)
    rw [if_neg (fun hm => hm.2 (Or.inl (head_mem_keepSet head5 verEx5)))]
    rfl
  · show (if (6 : Version) ∈ droppedSet Cex then none else Cex.ver 6) = none
    by_cases h : (6 : Version) ∈ droppedSet Cex
    · rw [if_pos h]
    · rw [if_neg h]; rfl

/-- **SPOT PASS, reads pinned equal** (hand-derived literals): pruning changes no
replica read; both heads still answer their pre-prune states. -/
theorem spot_reads :
    CexPruned.N = Cex.N ∧ Cex.N 0 = some S4 ∧ Cex.N 1 = some S5 :=
  ⟨rfl, rfl, rfl⟩

/-! ### The necessity countermodel: non-head-sync merges escape the keep set -/

/-- The interior version 1 is the LCA of the (non-head) pair `(1, 5)`. -/
theorem cm_interior_isLCA : IsLCA Cex.parents 1 5 1 :=
  ⟨Relation.ReflTransGen.refl, re_15, fun _ h _ => h⟩

theorem cm_one_not_head : ¬ IsHead Cex 1 := fun hh => by
  rcases head_cases hh with h | h <;> exact absurd h (by decide)

/-- **NECESSITY of head-sync.** In `Cex`, version 1 is (i) the `IsLCA` of the pair
`(1, 5)` whose first component is an *interior* (non-head) version, and (ii) dropped by
the keep set, so (iii) the pruned store no longer registers it. A widened Merge rule
that accepted an interior argument, a rewound replica, a checkpoint restore, a replica
missing from the head map, would demand exactly the version pruning removed
(`h_verT` fails). The head-sync discipline (the framework's Merge reads its arguments
off the head map) is therefore a load-bearing hypothesis of `gc_safety`, not
pessimism. -/
theorem gc_needs_head_sync :
    IsLCA Cex.parents 1 5 1 ∧ ¬ IsHead Cex 1 ∧
    (1 : Version) ∈ droppedSet Cex ∧ CexPruned.ver 1 = none :=
  ⟨cm_interior_isLCA, cm_one_not_head, one_dropped, spot_pruned_absent⟩

/-- A live observable step in the pruned configuration: querying head A returns the
hand-derived pre-prune state `S4` (the value rides on the label, so the pruned and
unpruned observations coincide literally). -/
theorem spot_query_step :
    Step3 GSetCond CexPruned (.query 0 () S4) CexPruned :=
  Step3.query rfl rfl

/-! ### Axiom audit -/

#print axioms gcInv_step
#print axioms lca_not_dropped
#print axioms step_dropVer
#print axioms spot_query_step
#print axioms gc_needs_head_sync
#print axioms spot_merge_enabled
#print axioms spot_reads
#print axioms spot_lca_present
#print axioms spot_pruned_absent
#print axioms storeInvEx

end GCSpot

end Sal.ConditionedMRDTs
