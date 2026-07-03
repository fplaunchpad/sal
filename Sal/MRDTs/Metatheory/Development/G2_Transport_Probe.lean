import Sal.MRDTs.Metatheory.Sigma_LoOn3
import Sal.MRDTs.RGA_Tombstone_Free.RGA_Reachability_Invariant

/-!
# Gate G2 (OQ4): permutation-transport of the RGA invariant — the probe

Task #3 of `CONDITIONED_METATHEORY_PLAN.md`. The feasible update layer wants the
convergence induction (`convergence_on_u`, `Sigma_LoOn3.lean:372`) to run with
`CRDTSig.commutes` replaced by `ConditionedMRDTSig.commutesOn` (`MRDTSig.lean:73`)
at every ⚑ site. This file maps the ⚑ sites, discharges obligation (A)
(Inv-transport) generically, and **refutes** obligation (B)
(applicability-transport) with a kernel-checked 2-event counterexample.

## The ⚑-site map

The induction `convergence_on_u` peels the head `e` of π₁ and bubbles `e` to the
front of π₂ = σ ++ e :: τ (`applySeq_bubble_to_front_loOn_u`,
`Sigma_LoOn3.lean:320`). Commutation is invoked at exactly two families of sites,
both inside `applySeq_swap_loOn_incomparable_u` (`Sigma_LoOn3.lean:279`):

* **⚑1 (`Sigma_LoOn3.lean:296`)** — the `D.commutes a b` branch
  (`applySeq_swap_commute`, `Merge_Linearization.lean:394`): the adjacent pair
  `(y, e)` is swapped at the state `applySeq D D.init (peeled π₁-prefix ++
  bubbled σ-prefix)`.  These are **hybrid** states: prefix-folds of mid-bubble
  permutations that are themselves NOT `loOn`-respecting enumerations.
* **⚑2 (`Sigma_LoOn3.lean:60,313-317`)** — the `cond_comm_lift` VC, invoked at
  the same hybrid states with an arbitrary interleaved residual `π`.

So the conditioned induction needs, at every hybrid prefix-fold state `σ*`:
**(A)** `Inv σ*`, and **(B)** `applicable e σ*` for both swapped events —
because `commutesOn` (`MRDTSig.lean:73`) only yields the swap under
`Inv σ* → applicable e₁ σ* → applicable e₂ σ*`.

## Verdicts (mechanized below, 0 sorries)

* **(A) = PROVABLE, unconditionally, and decoupled from (B).**
  `Inv_doIns`/`Inv_doDel` (`RGA_Reachability_Invariant.lean`) take the
  state-dependent hypotheses `accurate`/`fresh_ts`, which would entangle (A)
  with (B).  But the *load-bearing* content is order-stable and op-only:
  `Ins` needs only `t ≠ 0`, `Del` needs only `x ∉ pre` (packaged as `opOK`;
  derivable at generation time — `opOK_of_generation`).  With `opOK`, `RgaInv`
  transports along **every** permutation and every mid-bubble hybrid
  (`Inv_transport_generic`/`obligation_A_RGA`), covering all ⚑ states.
* **(B) = FALSE — trichotomy branch (ii).**  Counterexample `insOpE`/`delOpE`
  below: a genuine single-replica execution (insert node 1, then delete node 1)
  whose conditioned `lo` has NO edge between the two events — `fresh_ts insOpE`
  demands node 1 absent, `accurate delOpE` demands node 1 present, so the two
  events are never jointly applicable and `commutesOn` holds **vacuously** in
  both directions, while `rc = Either` kills the rc-flavored edge.  Hence both
  `[ins, del]` and `[del, ins]` respect the conditioned `loOn`, but they fold to
  different states.  The conditioned convergence statement is refuted outright
  (`G2_conditioned_convergence_refuted`), not merely unprovable.
* **Route (iii) (strengthened `Inv`) is DEAD**: the failing enumeration's every
  state satisfies `RgaInv` (`bad_enumeration_stays_in_Inv`), and conditioning is
  *antitone* — strengthening `Inv`/`applicable` shrinks `commutesOn`'s domain,
  makes `commutesOn` easier, hence **removes** `lo`-edges and admits MORE
  enumerations.  No state-shape envelope can restore the lost edge.
* **Contrast**: the unconditioned binary `loOn` keeps the edge
  (`binary_loOn_keeps_edge`) and correctly excludes the bad order
  (`binary_respects_excludes_bad_order`) — the failure is introduced exactly by
  the `commutes ↦ commutesOn` substitution.

Consequence for the feasible update layer: the conditioned `lo` must be
**applicability-aware** — a vis-edge `e₁ → e₂` must survive not only when
`¬ commutesOn e₁ e₂` but also when `e₂`'s applicability *depends on* `e₁`
(generation dependency; for the RGA this is op-syntactic: `e₂` references
`e₁`'s timestamp as Del-target / Ins-anchor / path member).  See
`G2_FINDINGS.md` for the proposed interface.
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.G2Probe

open Sal.Emulation

/-! ## §1 Obligation (A), generic part: an invariant preserved by every
`update` step transports to every prefix-fold of every enumeration — including
the mid-bubble hybrids, because the statement quantifies over ALL lists. -/

/-- Generic Inv-transport: if `SInv` is preserved by every single `update` step
(under an order-stable per-op fact `P`), it holds at the fold of *any* list of
`P`-ops from any `SInv`-state.  This covers every ⚑ state of the convergence
induction: peeled prefixes, bubbled prefixes, and mid-bubble hybrids alike. -/
theorem Inv_transport_generic {D : CRDTSig}
    (SInv : D.State → Prop) (P : Op D.AppOp → Prop)
    (hstep : ∀ s o, SInv s → P o → SInv (D.update s o)) :
    ∀ (π : List (Op D.AppOp)) (s : D.State),
      SInv s → (∀ o ∈ π, P o) → SInv (applySeq D s π) := by
  intro π
  induction π with
  | nil => intro s h _; exact h
  | cons o π' ih =>
    intro s h hP
    have h1 : SInv (D.update s o) := hstep s o h (hP o List.mem_cons_self)
    have hP' : ∀ o' ∈ π', P o' := fun o' ho' => hP o' (List.mem_cons_of_mem _ ho')
    exact ih (D.update s o) h1 hP'

/-- Prefix form: `SInv` holds at every prefix-fold of an enumeration. -/
theorem Inv_transport_prefix {D : CRDTSig}
    (SInv : D.State → Prop) (P : Op D.AppOp → Prop)
    (hstep : ∀ s o, SInv s → P o → SInv (D.update s o))
    (pfx sfx : List (Op D.AppOp)) (s : D.State)
    (h : SInv s) (hP : ∀ o ∈ pfx ++ sfx, P o) :
    SInv (applySeq D s pfx) :=
  Inv_transport_generic SInv P hstep pfx s h
    (fun o ho => hP o (List.mem_append.mpr (Or.inl ho)))

/-! ## §2 Obligation (A), RGA part: `RgaInv` is preserved by every `do_` step
under **op-only** side conditions

`Inv_doIns`/`Inv_doDel` (`RGA_Reachability_Invariant.lean:73,131`) take
`accurate o s` / `fresh_ts o s` — state-dependent hypotheses that would entangle
(A) with (B).  The re-proofs below isolate the load-bearing content:

* `Ins`: only `t ≠ 0` is used (the stored anchor is `resolve s (a :: pre)`,
  which is 0-or-live by `resolve_zero_or_live` REGARDLESS of path accuracy);
* `Del`: only `x ∉ pre` is used (then `resolve s pre ≠ x`, so the reparent
  target survives the deletion).

Both facts are properties of the op alone (stable under reordering), and both
are consequences of applicability at the *generation* state
(`opOK_of_generation`).  This decouples (A) from (B). -/

/-- Order-stable op-wellformedness: an `Ins` has a nonzero timestamp; a `Del`'s
target does not occur in its own recorded ancestor path. -/
def opOK : Op app_op_t → Prop
  | (t, _, .Ins _ _ _) => t ≠ 0
  | (_, _, .Del pre x) => x ∉ pre

/-- `resolve` returns the root or a member of its candidate list. -/
theorem resolve_mem (s : concrete_st) :
    ∀ cands : List ℕ, resolve s cands = 0 ∨ resolve s cands ∈ cands := by
  intro cands
  induction cands with
  | nil => left; rfl
  | cons c rest ih =>
    simp only [resolve]
    by_cases hc : contains s c = true
    · rw [if_pos hc]; right; exact List.mem_cons_self
    · rw [if_neg hc]
      rcases ih with h | h
      · left; exact h
      · right; exact List.mem_cons_of_mem _ h

/-- `RgaInv` is preserved by an `Ins` given only `t ≠ 0` — NO path accuracy, NO
freshness.  (Mirror of `Inv_doIns` with `resolve_zero_or_live` replacing the
accuracy-derived liveness of the stored anchor.) -/
theorem RgaInv_doIns_opOK (s : concrete_st) (t r e a : ℕ) (pre : List ℕ)
    (h : RgaInv s) (ht0 : t ≠ 0) :
    RgaInv (do_ s (t, r, .Ins e pre a)) := by
  obtain ⟨h0, hwf⟩ := h
  have hdo : do_ s (t, r, .Ins e pre a) = upd s t (e, resolve s (a :: pre)) := by
    simp only [do_]
  rw [hdo]
  set v := resolve s (a :: pre) with hv
  have hvlive : v = 0 ∨ contains s v = true := resolve_zero_or_live s (a :: pre)
  refine ⟨?_, ?_⟩
  · rw [lemma_InDomUpd1, h0, Bool.or_false]
    simp [ht0]
  · intro k hk
    by_cases hkt : k = t
    · have hanck : anc (upd s t (e, v)) k = v := by
        rw [hkt]; simp only [anc]; rw [lemma_SelUpd1]
      rw [hanck]
      rcases hvlive with hv0 | hvl
      · exact Or.inl hv0
      · refine Or.inr ?_
        rw [lemma_InDomUpd1, hvl]; simp only [Bool.or_true]
    · have htk : t ≠ k := fun e' => hkt e'.symm
      have hck : contains s k = true := by
        rw [lemma_InDomUpd1] at hk
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hk
        rcases hk with hh | hh
        · exact absurd hh htk
        · exact hh
      have hanck : anc (upd s t (e, v)) k = anc s k := by
        simp only [anc]
        rw [lemma_SelUpd2 s k t (e, v) (by simp only [bne_iff_ne, ne_eq]; exact htk)]
      rw [hanck]
      rcases hwf k hck with hanc0 | hancl
      · exact Or.inl hanc0
      · refine Or.inr ?_
        rw [lemma_InDomUpd1, hancl]; simp only [Bool.or_true]

/-- `RgaInv` is preserved by a `Del` given only `x ∉ pre` — NO path accuracy.
(Mirror of `Inv_doDel`: the reparent target `resolve s pre` is 0-or-live by
`resolve_zero_or_live`, and `≠ x` because `resolve` lands in `{0} ∪ pre`.) -/
theorem RgaInv_doDel_opOK (s : concrete_st) (t r x : ℕ) (pre : List ℕ)
    (h : RgaInv s) (hx : x ∉ pre) :
    RgaInv (do_ s (t, r, .Del pre x)) := by
  obtain ⟨h0, hwf⟩ := h
  refine ⟨?_, ?_⟩
  · rw [contains_doDel s t r x pre 0, h0, Bool.false_and]
  · intro k hk
    rw [contains_doDel s t r x pre k] at hk
    rw [Bool.and_eq_true] at hk
    obtain ⟨hck, _hkx⟩ := hk
    rw [anc_doDel s t r x pre k]
    have hRsurvive :
        resolve s pre = 0
          ∨ contains (do_ s (t, r, .Del pre x)) (resolve s pre) = true := by
      rcases resolve_zero_or_live s pre with hz | hl
      · exact Or.inl hz
      · refine Or.inr ?_
        have hmem : resolve s pre ∈ pre := by
          rcases resolve_mem s pre with hz | hm
          · exfalso; rw [hz] at hl; rw [h0] at hl; exact Bool.noConfusion hl
          · exact hm
        have hne : resolve s pre ≠ x := fun he => hx (he ▸ hmem)
        rw [contains_doDel s t r x pre (resolve s pre), Bool.and_eq_true]
        exact ⟨hl, by simp only [bne_iff_ne, ne_eq]; exact hne⟩
    by_cases hax : anc s k = x
    · rw [if_pos hax]; exact hRsurvive
    · rw [if_neg hax]
      rcases hwf k hck with hanc0 | hancl
      · exact Or.inl hanc0
      · refine Or.inr ?_
        rw [contains_doDel s t r x pre (anc s k), Bool.and_eq_true]
        exact ⟨hancl, by simp only [bne_iff_ne, ne_eq]; exact hax⟩

/-- Single-step dispatcher: `RgaInv` is preserved by every `do_` step under the
op-only `opOK`. -/
theorem RgaInv_do_opOK (s : concrete_st) (o : Op app_op_t)
    (h : RgaInv s) (hok : opOK o) : RgaInv (do_ s o) := by
  obtain ⟨t, r, op⟩ := o
  cases op with
  | Ins e pre a => exact RgaInv_doIns_opOK s t r e a pre h hok
  | Del pre x => exact RgaInv_doDel_opOK s t r x pre h hok

/-! ### `opOK` is free at generation time

Closing the loop for (A): every event of a genuine conditioned execution
satisfies `opOK`, because applicability at the *generation* state implies it —
`fresh_ts` gives `t ≠ 0` directly, and an accurate path cannot contain its own
leaf (the ancestor chain is a function into `{0} ∪ dom`, terminating at the
absent root, so it is loop-free). -/

/-- Every member of an accurate path has a strictly shorter accurate path
(its suffix). -/
theorem isAncPath_mem_shorter (s : concrete_st) :
    ∀ (p : List ℕ) (y z : ℕ), IsAncPath s y p → z ∈ p →
      ∃ q, IsAncPath s z q ∧ q.length < p.length := by
  intro p
  induction p with
  | nil => intro y z _ hz; exact absurd hz List.not_mem_nil
  | cons c cs ih =>
    intro y z hp hz
    simp only [IsAncPath] at hp
    obtain ⟨_hc, _hcc, hcs⟩ := hp
    rcases List.mem_cons.mp hz with rfl | hz'
    · exact ⟨cs, hcs, Nat.lt_succ_self cs.length⟩
    · obtain ⟨q, hq, hlen⟩ := ih c z hcs hz'
      exact ⟨q, hq, Nat.lt_trans hlen (Nat.lt_succ_self cs.length)⟩

/-- Accurate paths are unique (given the root sentinel is absent): `anc` is a
function, and the head case is forced because a stored `0` is impossible. -/
theorem isAncPath_unique (s : concrete_st) (h0 : contains s 0 = false) :
    ∀ (p q : List ℕ) (y : ℕ), IsAncPath s y p → IsAncPath s y q → p = q := by
  intro p
  induction p with
  | nil =>
    intro q y hp hq
    cases q with
    | nil => rfl
    | cons d ds =>
      simp only [IsAncPath] at hp hq
      obtain ⟨hd, hdc, _⟩ := hq
      rw [hp] at hd
      rw [← hd] at hdc
      rw [h0] at hdc
      exact Bool.noConfusion hdc
  | cons c cs ih =>
    intro q y hp hq
    simp only [IsAncPath] at hp
    obtain ⟨hc, hcc, hcs⟩ := hp
    cases q with
    | nil =>
      simp only [IsAncPath] at hq
      rw [hq] at hc
      rw [← hc] at hcc
      rw [h0] at hcc
      exact Bool.noConfusion hcc
    | cons d ds =>
      simp only [IsAncPath] at hq
      obtain ⟨hd, hdc, hds⟩ := hq
      have hcd : c = d := by rw [← hc, ← hd]
      subst hcd
      rw [ih ds c hcs hds]

/-- An accurate path never contains its own leaf. -/
theorem isAncPath_not_mem (s : concrete_st) (h0 : contains s 0 = false)
    (x : ℕ) (pre : List ℕ) (hpath : IsAncPath s x pre) : x ∉ pre := by
  intro hx
  obtain ⟨q, hq, hlen⟩ := isAncPath_mem_shorter s pre x x hpath hx
  have heq : pre = q := isAncPath_unique s h0 pre q x hpath hq
  rw [heq] at hlen
  exact Nat.lt_irrefl _ hlen

/-- Applicability at the generation state yields the order-stable `opOK` —
so obligation (A) needs nothing from the reordered run. -/
theorem opOK_of_generation (o : Op app_op_t) (s : concrete_st)
    (h0 : contains s 0 = false) (hacc : accurate o s) (hfr : fresh_ts o s) :
    opOK o := by
  obtain ⟨t, r, op⟩ := o
  cases op with
  | Ins e pre a =>
    show t ≠ 0
    have hfr' : t ≠ 0 ∧ contains s t = false := hfr
    exact hfr'.1
  | Del pre x =>
    show x ∉ pre
    have hacc' : (x = 0 ∧ pre = []) ∨ (contains s x = true ∧ IsAncPath s x pre) :=
      hacc
    rcases hacc' with ⟨_, hpre⟩ | ⟨_, hpath⟩
    · rw [hpre]; exact List.not_mem_nil
    · exact isAncPath_not_mem s h0 x pre hpath

/-! ## §3 Packaging: the tombstone-free RGA as a `ConditionedMRDTSig`

`Inv := RgaInv`, `applicable := accurate ∧ fresh_ts` — exactly the Design-3
split validated in `RGA_Reachability_Invariant.lean`.  `rc = Either`
everywhere, so ALL `lo`-edges hinge on `¬ commutesOn`.

NOTE (recorded hosting gap, see G2_FINDINGS.md): the RGA's commutation lemmas
(`rc_non_comm'`, `RGA_Tombstone_Free_MRDT.lean:928`) conclude the observational
`eq`, not Lean `Eq`, so the *positive* `commutesOn` facts for non-vacuous pairs
are not directly available at this signature — the counterexample below only
needs the VACUOUS pairs, which are independent of that gap. -/

noncomputable def RGAM : MRDTSig where
  State := concrete_st
  dec_state := fun a b => Classical.propDecidable (a = b)
  init := init_st
  AppOp := app_op_t
  dec_op := inferInstance
  Query := Unit
  Value := Unit
  update := fun s o => do_ s o
  merge := fun a b => _root_.merge init_st a b
  query := fun _ _ => ()
  rc := fun _ _ => RcRes.Either
  mergeL := fun l a b => _root_.merge l a b
  merge_init_slice := fun _ _ => rfl

noncomputable def RGACondSig : ConditionedMRDTSig where
  toMRDTSig := RGAM
  Inv := RgaInv
  applicable := fun o s => accurate o s ∧ fresh_ts o s

theorem rc_is_Either (o₁ o₂ : Op app_op_t) :
    RGACondSig.rc o₁ o₂ = RcRes.Either := rfl

theorem applySeq_two (s : concrete_st) (o₁ o₂ : Op app_op_t) :
    applySeq RGACondSig.toCRDTSig s [o₁, o₂] = do_ (do_ s o₁) o₂ := rfl

/-- **Obligation (A), discharged for the RGA**: `RgaInv` holds at every
prefix-fold of every enumeration (loOn-respecting or hybrid) of any set of
`opOK` events, starting from `init`.  This is the exact Inv-side input the
conditioned ⚑ sites need. -/
theorem obligation_A_RGA (pfx sfx : List (Op RGACondSig.AppOp))
    (hπ : ∀ o ∈ pfx ++ sfx, opOK o) :
    RgaInv (applySeq RGACondSig.toCRDTSig RGACondSig.init pfx) :=
  Inv_transport_prefix RgaInv opOK
    (fun s o h hok => RgaInv_do_opOK s o h hok)
    pfx sfx RGACondSig.init Inv_init hπ

/-! ## §4 Obligation (B): the counterexample

A genuine single-replica execution: `insOpE` inserts node `1` at the root,
`delOpE` deletes node `1`.  Both are applicable at their generation states
(`insOpE_applicable_at_init`, `delOpE_applicable_after_ins`), and
`vis insOpE delOpE` (program order).  Yet:

* they are **never jointly applicable** — `fresh_ts insOpE s` forces
  `contains s 1 = false`, `accurate delOpE s` forces `contains s 1 = true` —
  so `commutesOn` holds VACUOUSLY in both directions;
* `rc = Either` kills the rc-flavored edge;
* hence the conditioned `lo` (both `Sal.Metatheory.lo` and the set-relative
  `loOnC` the update layer would use) has NO edge between them, both orders are
  admissible, and the folds differ: `[ins, del] ↦ ∅` but `[del, ins] ↦ {1}`. -/

/-- Insert element 65 as node `1` anchored at the root (path `[]`). -/
def insOpE : Op app_op_t := (1, 0, .Ins 65 [] 0)

/-- Delete node `1` (its true ancestor chain at generation time is `[]`). -/
def delOpE : Op app_op_t := (2, 0, .Del [] 1)

theorem ins_ne_del : insOpE ≠ delOpE := by decide

/-- A freshly inserted node is present. -/
theorem contains_doIns_self (s : concrete_st) (t r e a : ℕ) (pre : List ℕ) :
    contains (do_ s (t, r, .Ins e pre a)) t = true := by
  simp only [do_]
  rw [lemma_InDomUpd1]
  simp

/-- **The two admissible orders fold to different states.**
`[ins, del]` yields the empty sequence; `[del, ins]` leaves node `1` alive. -/
theorem folds_differ :
    do_ (do_ init_st insOpE) delOpE ≠ do_ (do_ init_st delOpE) insOpE := by
  intro hEq
  have h1 : contains (do_ (do_ init_st insOpE) delOpE) 1
          = contains (do_ (do_ init_st delOpE) insOpE) 1 :=
    congrArg (fun st => contains st 1) hEq
  have hL : contains (do_ (do_ init_st insOpE) delOpE) 1 = false := by
    show contains (do_ (do_ init_st insOpE) (2, 0, app_op_t.Del [] 1)) 1 = false
    rw [contains_doDel]
    simp
  have hR : contains (do_ (do_ init_st delOpE) insOpE) 1 = true := by
    show contains (do_ (do_ init_st delOpE) (1, 0, app_op_t.Ins 65 [] 0)) 1 = true
    exact contains_doIns_self (do_ init_st delOpE) 1 0 65 0 []
  rw [hL, hR] at h1
  exact Bool.noConfusion h1

/-! ### The counterexample is a genuine execution -/

/-- `insOpE` is applicable (accurate + fresh) at the initial state. -/
theorem insOpE_applicable_at_init :
    accurate insOpE init_st ∧ fresh_ts insOpE init_st := by
  constructor
  · exact Or.inl ⟨rfl, rfl⟩
  · show (1 : ℕ) ≠ 0 ∧ contains init_st 1 = false
    exact ⟨one_ne_zero, by simp [init_st]⟩

/-- `delOpE` is applicable at its generation state (right after `insOpE`):
node `1` is live and its true ancestor chain is `[]`. -/
theorem delOpE_applicable_after_ins :
    accurate delOpE (do_ init_st insOpE) ∧ fresh_ts delOpE (do_ init_st insOpE) := by
  constructor
  · refine Or.inr ⟨?_, ?_⟩
    · show contains (do_ init_st (1, 0, app_op_t.Ins 65 [] 0)) 1 = true
      exact contains_doIns_self init_st 1 0 65 0 []
    · show anc (do_ init_st (1, 0, app_op_t.Ins 65 [] 0)) 1 = 0
      have hdo : do_ init_st (1, 0, app_op_t.Ins 65 [] 0)
               = upd init_st 1 (65, resolve init_st (0 :: [])) := by
        simp only [do_]
      rw [hdo]
      show (sel (upd init_st 1 (65, resolve init_st (0 :: []))) 1).2 = 0
      rw [lemma_SelUpd1]
      show resolve init_st (0 :: []) = 0
      rw [resolve_dead_head init_st 0 [] (by simp [init_st])]
      rfl
  · show True
    trivial

/-! ### Vacuous conditioning: the pair is never jointly applicable -/

/-- The heart of the failure: `fresh_ts insOpE` demands node `1` ABSENT while
`accurate delOpE` demands node `1` PRESENT — no state satisfies both, so the
conditioned commutation quantifier is empty. -/
theorem never_jointly_applicable (s : concrete_st)
    (hIns : accurate insOpE s ∧ fresh_ts insOpE s)
    (hDel : accurate delOpE s ∧ fresh_ts delOpE s) : False := by
  obtain ⟨_, hfr⟩ := hIns
  obtain ⟨hacc, _⟩ := hDel
  have hfr' : (1 : ℕ) ≠ 0 ∧ contains s 1 = false := hfr
  have hacc' : ((1 : ℕ) = 0 ∧ ([] : List ℕ) = []) ∨
      (contains s 1 = true ∧ IsAncPath s 1 []) := hacc
  rcases hacc' with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact one_ne_zero h1
  · rw [hfr'.2] at h1
    exact Bool.noConfusion h1

/-- `commutesOn insOpE delOpE` holds — VACUOUSLY. -/
theorem G2_commutesOn_ins_del : RGACondSig.commutesOn insOpE delOpE := by
  intro s _hInv hIns hDel
  exact (never_jointly_applicable s hIns hDel).elim

/-- `commutesOn delOpE insOpE` holds — VACUOUSLY. -/
theorem G2_commutesOn_del_ins : RGACondSig.commutesOn delOpE insOpE := by
  intro s _hInv hDel hIns
  exact (never_jointly_applicable s hIns hDel).elim

/-! ### The conditioned linearization order loses the edge -/

/-- The set-relative conditioned linearization order: `Sal.Emulation.loOn`
(`Merge_Linearization_Set.lean:159`) with `commutes ↦ commutesOn` — the exact
relation the conditioned update layer would re-run `convergence_on_u` against
(mirrors `Sal.Metatheory.lo`, `MRDTSig.lean:89`, made set-relative). -/
def loOnC (D : ConditionedMRDTSig) (C : Sal.Emulation.Configuration D.toCRDTSig)
    (ev : Set (Op D.AppOp)) (e₁ e₂ : Op D.AppOp) : Prop :=
  (C.vis e₁ e₂ ∧ ¬ D.commutesOn e₁ e₂)
  ∨ ( ¬ C.vis e₁ e₂ ∧ ¬ C.vis e₂ e₁
      ∧ D.rc e₁ e₂ = RcRes.Fst_then_snd
      ∧ ¬ ∃ e₃ ∈ ev, C.vis e₂ e₃ ∧ ¬ D.commutesOn e₂ e₃ )

/-- In ANY configuration and relative to ANY event set, the conditioned
set-relative order has no edge between `insOpE` and `delOpE` in either
direction: the vis-flavor dies on the vacuous `commutesOn`, the rc-flavor dies
on `rc = Either`. -/
theorem no_loOnC_edge (C : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (ev : Set (Op app_op_t)) :
    ¬ loOnC RGACondSig C ev insOpE delOpE
    ∧ ¬ loOnC RGACondSig C ev delOpE insOpE := by
  constructor
  · rintro (⟨_, hnc⟩ | ⟨_, _, hrc, _⟩)
    · exact hnc G2_commutesOn_ins_del
    · rw [rc_is_Either] at hrc
      exact RcRes.noConfusion hrc
  · rintro (⟨_, hnc⟩ | ⟨_, _, hrc, _⟩)
    · exact hnc G2_commutesOn_del_ins
    · rw [rc_is_Either] at hrc
      exact RcRes.noConfusion hrc

/-- Same for the repo's global conditioned `lo` (`MRDTSig.lean:89`). -/
theorem no_metatheory_lo_edge (C : Sal.Emulation.Configuration RGACondSig.toCRDTSig) :
    ¬ Sal.Metatheory.lo RGACondSig C insOpE delOpE
    ∧ ¬ Sal.Metatheory.lo RGACondSig C delOpE insOpE := by
  constructor
  · rintro (⟨_, hnc⟩ | ⟨_, _, hrc, _⟩)
    · exact hnc G2_commutesOn_ins_del
    · rw [rc_is_Either] at hrc
      exact RcRes.noConfusion hrc
  · rintro (⟨_, hnc⟩ | ⟨_, _, hrc, _⟩)
    · exact hnc G2_commutesOn_del_ins
    · rw [rc_is_Either] at hrc
      exact RcRes.noConfusion hrc

/-! ### The concrete configuration

The reachable shape a single replica produces via
`createReplica 0; apply insOpE; apply delOpE` (see `CRDT_TS.lean` `Step.apply`:
the second apply adds exactly the edge `insOpE → delOpE`).  Step-reachability
is noted, not mechanized — the convergence machinery consumes only the
structural fields below, so the refutation targets it verbatim. -/

def evCex : Set (Op app_op_t) := {insOpE, delOpE}

private theorem optL_inv {α : Type} {x y : α} {r : ℕ}
    (h : (if r = 0 then some x else none) = some y) : x = y := by
  by_cases hr : r = 0
  · rw [if_pos hr] at h
    exact Option.some.inj h
  · rw [if_neg hr] at h
    exact absurd h (by simp)

noncomputable def Ccex : Sal.Emulation.Configuration RGACondSig.toCRDTSig where
  N := fun r => if r = 0 then some (do_ (do_ init_st insOpE) delOpE) else none
  L := fun r => if r = 0 then some evCex else none
  vis := fun a b => a = insOpE ∧ b = delOpE
  dom_eq := by
    intro r
    by_cases h : r = 0 <;> simp [h]
  vis_src := by
    intro a b hv
    obtain ⟨rfl, rfl⟩ := hv
    exact ⟨0, evCex, rfl, Set.mem_insert _ _⟩
  vis_tgt := by
    intro a b hv
    obtain ⟨rfl, rfl⟩ := hv
    exact ⟨0, evCex, rfl, Set.mem_insert_of_mem _ rfl⟩
  vis_causal := by
    intro a b r s hv hL _hb
    obtain ⟨rfl, rfl⟩ := hv
    obtain rfl := optL_inv hL
    exact Set.mem_insert _ _
  timestamps_distinct := by
    intro a b r s r' s' hL ha hL' hb hne
    obtain rfl := optL_inv hL
    obtain rfl := optL_inv hL'
    have ha' : a = insOpE ∨ a = delOpE := ha
    have hb' : b = insOpE ∨ b = delOpE := hb
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hne
    · decide
    · decide
    · exact absurd rfl hne
  vis_total_same_replica := by
    intro a b r s r' s' hL ha hL' hb hne _hrep
    obtain rfl := optL_inv hL
    obtain rfl := optL_inv hL'
    have ha' : a = insOpE ∨ a = delOpE := ha
    have hb' : b = insOpE ∨ b = delOpE := hb
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hne
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl hne

theorem Ccex_vis_trans : ∀ {a b c : Op app_op_t},
    Ccex.vis a b → Ccex.vis b c → Ccex.vis a c := by
  intro a b c hab hbc
  obtain ⟨rfl, rfl⟩ := hab
  obtain ⟨h1, _⟩ := hbc
  exact absurd h1 (by decide)

theorem Ccex_vis_irrefl : ∀ a : Op app_op_t, ¬ Ccex.vis a a := by
  rintro a ⟨h1, h2⟩
  exact ins_ne_del (h1.symm.trans h2)

theorem Ccex_ev_in : ∀ a ∈ evCex, a ∈ Ccex.events :=
  fun a ha => ⟨0, evCex, rfl, ha⟩

/-! ### Both orders are admissible -/

theorem perm_ins_del : listPermOf [insOpE, delOpE] evCex := by
  constructor
  · decide
  · intro a
    constructor
    · intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact Set.mem_insert _ _
      · rw [List.mem_singleton] at h
        subst h
        exact Set.mem_insert_of_mem _ rfl
    · intro h
      have h' : a = insOpE ∨ a = delOpE := h
      rcases h' with rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self

theorem perm_del_ins : listPermOf [delOpE, insOpE] evCex := by
  constructor
  · decide
  · intro a
    constructor
    · intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact Set.mem_insert_of_mem _ rfl
      · rw [List.mem_singleton] at h
        subst h
        exact Set.mem_insert _ _
    · intro h
      have h' : a = insOpE ∨ a = delOpE := h
      rcases h' with rfl | rfl
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_cons_self

theorem respects_ins_del (C : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (ev : Set (Op app_op_t)) :
    respects [insOpE, delOpE] (loOnC RGACondSig C ev) := by
  show List.Pairwise (fun a b => ¬ loOnC RGACondSig C ev b a) [insOpE, delOpE]
  refine List.pairwise_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩
  intro b hb
  rw [List.mem_singleton] at hb
  subst hb
  exact (no_loOnC_edge C ev).2

theorem respects_del_ins (C : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
    (ev : Set (Op app_op_t)) :
    respects [delOpE, insOpE] (loOnC RGACondSig C ev) := by
  show List.Pairwise (fun a b => ¬ loOnC RGACondSig C ev b a) [delOpE, insOpE]
  refine List.pairwise_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩
  intro b hb
  rw [List.mem_singleton] at hb
  subst hb
  exact (no_loOnC_edge C ev).1

/-! ### The kill theorem -/

/-- **Gate G2, verdict (B) = FALSE.**  The conditioned analogue of
`convergence_on_u` (`Sigma_LoOn3.lean:372`) — `commutes ↦ commutesOn` inside the
linearization order, all other hypotheses kept (vis-transitivity,
vis-irreflexivity, events-in-configuration) — is REFUTED by the tombstone-free
RGA: the 2-event set `{insOpE, delOpE}` of a genuine single-replica execution
admits two loOnC-respecting enumerations with different folds.

The failure is at the FIRST fold step of the bad enumeration (`delOpE` applied
at `init`, where it is not applicable), i.e. obligation (B) fails already at
ordinary prefix states — before any mid-bubble hybrid subtleties arise. -/
theorem G2_conditioned_convergence_refuted :
    ¬ (∀ (C : Sal.Emulation.Configuration RGACondSig.toCRDTSig)
         (ev : Set (Op RGACondSig.AppOp))
         (π₁ π₂ : List (Op RGACondSig.AppOp)),
        (∀ {a b c : Op RGACondSig.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
        (∀ a : Op RGACondSig.AppOp, ¬ C.vis a a) →
        (∀ a ∈ ev, a ∈ C.events) →
        listPermOf π₁ ev → listPermOf π₂ ev →
        respects π₁ (loOnC RGACondSig C ev) →
        respects π₂ (loOnC RGACondSig C ev) →
        applySeq RGACondSig.toCRDTSig RGACondSig.init π₁
          = applySeq RGACondSig.toCRDTSig RGACondSig.init π₂) := by
  intro hconv
  have h := hconv Ccex evCex [insOpE, delOpE] [delOpE, insOpE]
    Ccex_vis_trans Ccex_vis_irrefl Ccex_ev_in
    perm_ins_del perm_del_ins
    (respects_ins_del Ccex evCex) (respects_del_ins Ccex evCex)
  rw [applySeq_two, applySeq_two] at h
  exact folds_differ h

/-! ### Contrast and the death of route (iii) -/

/-- Unconditioned, the pair genuinely does not commute (witness: `init_st`). -/
theorem insdel_not_commutes_unconditioned :
    ¬ RGACondSig.toCRDTSig.commutes insOpE delOpE :=
  fun h => folds_differ (h init_st)

/-- The UNCONDITIONED binary `loOn` keeps the vis-edge `insOpE → delOpE` —
conditioning (`commutes ↦ commutesOn`) is exactly what deletes it. -/
theorem binary_loOn_keeps_edge (ev : Set (Op app_op_t)) :
    loOn Ccex ev insOpE delOpE :=
  Or.inl ⟨⟨rfl, rfl⟩, insdel_not_commutes_unconditioned⟩

/-- Consequently the unconditioned machinery correctly EXCLUDES the bad
enumeration: `[delOpE, insOpE]` does not respect `loOn Ccex evCex`. -/
theorem binary_respects_excludes_bad_order :
    ¬ respects [delOpE, insOpE] (loOn Ccex evCex) := by
  intro h
  have h1 := (List.pairwise_cons.mp h).1 insOpE List.mem_cons_self
  exact h1 (binary_loOn_keeps_edge evCex)

/-- **Route (iii) — a strengthened state invariant — cannot repair (B)**: every
state visited by the failing enumeration `[delOpE, insOpE]` satisfies `RgaInv`
(obligation (A) holds along it!).  The defect is in `applicable`, which the
`lo`-edge predicate consults only under a quantifier that conditioning makes
vacuous; strengthening `Inv` only shrinks that quantifier further. -/
theorem bad_enumeration_stays_in_Inv :
    RgaInv init_st
    ∧ RgaInv (do_ init_st delOpE)
    ∧ RgaInv (do_ (do_ init_st delOpE) insOpE) := by
  have h1 : RgaInv (do_ init_st delOpE) :=
    RgaInv_do_opOK init_st delOpE Inv_init
      (show (1 : ℕ) ∉ ([] : List ℕ) from List.not_mem_nil)
  refine ⟨Inv_init, h1, ?_⟩
  exact RgaInv_do_opOK (do_ init_st delOpE) insOpE h1
    (show (1 : ℕ) ≠ 0 from one_ne_zero)

/-! ## §5 Axiom audit — all kernel-checked (no `native_decide`) -/

#print axioms obligation_A_RGA
#print axioms opOK_of_generation
#print axioms G2_conditioned_convergence_refuted
#print axioms binary_respects_excludes_bad_order
#print axioms bad_enumeration_stays_in_Inv

/-!
## VERDICT (Gate G2)

**(A) Inv-transport: DISCHARGED, generically and decoupled from (B).**
`Inv_transport_generic` + `RgaInv_do_opOK` prove `RgaInv` at every prefix-fold
of EVERY enumeration (including the ⚑ sites' mid-bubble hybrids) from op-only
side conditions `opOK` (`Ins`: `t ≠ 0`; `Del`: `x ∉ pre`), which
`opOK_of_generation` extracts once from applicability at the generation state.
The published `Inv_doIns`/`Inv_doDel` hypotheses (`accurate`/`fresh_ts`) are
stronger than needed; had they been load-bearing, (A) would have entangled with
(B) and failed with it.

**(B) applicability-transport: FALSE — trichotomy branch (ii).**
`G2_conditioned_convergence_refuted`.  Root cause: *vacuous conditioning* —
creation dependencies (an op referencing a node another op creates) make the
two events never jointly applicable, so `commutesOn` is vacuously true and the
conditioned `lo` drops precisely the vis-edges that creation order needs.
Not a path-staleness phenomenon: the path-carrying design tolerates stale
paths at swap sites (that is what `resolve`-climbing is for); hand-checked
concurrent Ins/Del scenarios converge.  The failure is confined to vis-ordered
create-then-use pairs.

**Monotonicity (kills route (iii)):** `commutesOn` is antitone in the strength
of `(Inv, applicable)` — a stronger condition means a smaller quantification
domain, hence MORE vacuous commutation, hence FEWER `lo`-edges, hence MORE
admissible enumerations.  Conditioning that rescues the commutation VCs
monotonically destroys the linearization order.  `bad_enumeration_stays_in_Inv`
shows the failing enumeration is `Inv`-internal, so no swap-closed state
envelope exists that excludes it.

**What the feasible update layer actually needs** (see G2_FINDINGS.md):
an applicability-aware `lo` — keep the vis-edge `e₁ → e₂` when
`¬ commutesOn e₁ e₂` OR when `e₂`'s applicability depends on `e₁`
(for the RGA an op-syntactic, decidable dependency: `e₂` mentions `e₁`'s
timestamp as Del-target, Ins-anchor, or path member), plus the (A) transport
above as a separate generic obligation.  Alternatively, restrict the
enumeration class to applicability-admissible ones — but then the bubble-sort's
hybrid states must be proved admissible, a new and harder obligation, since
swaps visit states no execution visits.
-/

end Sal.Metatheory.G2Probe
