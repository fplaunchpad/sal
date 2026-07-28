import Sal.ConditionedMRDTs.Framework.Sigma_LoOn3
import Sal.MRDTs.RGA_Rehoming.RGA_Reachability_Invariant

/-!
# The tombstone-free RGA as a conditioned MRDT signature

The signature the whole RGA chain instantiates: `RGAM` (the raw `MRDTSig`:
`do_`, three-way `merge`, `rc = Either`) and `RGACondSig` (its conditioned
extension: `Inv := RgaInv`, `applicable := accurate ∧ fresh_ts` — the Design-3
split validated in `RGA_Reachability_Invariant.lean`), together with the
order-stable op-wellformedness layer that discharges the Inv-transport
obligation:

* `opOK` — the op-only side conditions (`Ins`: `t ≠ 0`; `Del`: `x ∉ pre`),
  derivable once at generation time (`opOK_of_generation`);
* `RgaInv_do_opOK` — `RgaInv` is preserved by every `do_` step under `opOK`
  alone (no path accuracy, no freshness);
* `Inv_transport_generic`/`obligation_A_RGA` — hence `RgaInv` holds at every
  prefix-fold of every enumeration, including mid-bubble hybrids.

`G2_Transport_Probe.lean` keeps the ⚑-site map and the obligation-(B)
refutation; the transport layer itself lives here because the entire chain
consumes it.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Sal.ConditionedMRDTs.RGASig

open Sal.Emulation

variable {α : Type} [DecidableEq α] [Inhabited α]

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
def opOK : Op (app_op_t α) → Prop
  | (t, _, .Ins _ _ _) => t ≠ 0
  | (_, _, .Del pre x) => x ∉ pre

/-- `resolve` returns the root or a member of its candidate list. -/
theorem resolve_mem (s : concrete_st α) :
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
theorem RgaInv_doIns_opOK (s : concrete_st α) (t r : ℕ) (e : α) (a : ℕ) (pre : List ℕ)
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
theorem RgaInv_doDel_opOK (s : concrete_st α) (t r x : ℕ) (pre : List ℕ)
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
theorem RgaInv_do_opOK (s : concrete_st α) (o : Op (app_op_t α))
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
theorem isAncPath_mem_shorter (s : concrete_st α) :
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
theorem isAncPath_unique (s : concrete_st α) (h0 : contains s 0 = false) :
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
theorem isAncPath_not_mem (s : concrete_st α) (h0 : contains s 0 = false)
    (x : ℕ) (pre : List ℕ) (hpath : IsAncPath s x pre) : x ∉ pre := by
  intro hx
  obtain ⟨q, hq, hlen⟩ := isAncPath_mem_shorter s pre x x hpath hx
  have heq : pre = q := isAncPath_unique s h0 pre q x hpath hq
  rw [heq] at hlen
  exact Nat.lt_irrefl _ hlen

/-- Applicability at the generation state yields the order-stable `opOK` —
so obligation (A) needs nothing from the reordered run. -/
theorem opOK_of_generation (o : Op (app_op_t α)) (s : concrete_st α)
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

NOTE (recorded hosting gap): the RGA's commutation lemmas
(`rc_non_comm'`, `RGA_Tombstone_Free_MRDT.lean:928`) conclude the observational
`eq`, not Lean `Eq`, so the *positive* `commutesOn` facts for non-vacuous pairs
are not directly available at this signature — the counterexample below only
needs the VACUOUS pairs, which are independent of that gap. -/

noncomputable def RGAM (α : Type := ℕ) [DecidableEq α] [Inhabited α] : MRDTSig where
  State := concrete_st α
  dec_state := fun a b => Classical.propDecidable (a = b)
  init := init_st (α := α)
  AppOp := app_op_t α
  dec_op := inferInstance
  Query := Unit
  Value := Unit
  update := fun s o => do_ s o
  merge := fun a b => _root_.merge (init_st (α := α)) a b
  query := fun _ _ => ()
  rc := fun _ _ => RcRes.Either
  mergeL := fun l a b => _root_.merge l a b
  merge_init_slice := fun _ _ => rfl

noncomputable def RGACondSig (α : Type := ℕ) [DecidableEq α] [Inhabited α] : ConditionedMRDTSig where
  toMRDTSig := RGAM α
  Inv := RgaInv
  applicable := fun o s => accurate o s ∧ fresh_ts o s

theorem rc_is_Either (o₁ o₂ : Op (app_op_t α)) :
    (RGACondSig α).rc o₁ o₂ = RcRes.Either := rfl

theorem applySeq_two (s : concrete_st α) (o₁ o₂ : Op (app_op_t α)) :
    applySeq (RGACondSig α).toCRDTSig s [o₁, o₂] = do_ (do_ s o₁) o₂ := rfl

/-- **Obligation (A), discharged for the RGA**: `RgaInv` holds at every
prefix-fold of every enumeration (loOn-respecting or hybrid) of any set of
`opOK` events, starting from `init`.  This is the exact Inv-side input the
conditioned ⚑ sites need. -/
theorem obligation_A_RGA (pfx sfx : List (Op (RGACondSig α).AppOp))
    (hπ : ∀ o ∈ pfx ++ sfx, opOK o) :
    RgaInv (applySeq (RGACondSig α).toCRDTSig (RGACondSig α).init pfx) :=
  Inv_transport_prefix RgaInv opOK
    (fun s o h hok => RgaInv_do_opOK s o h hok)
    pfx sfx (RGACondSig α).init Inv_init hπ

/-! ## Axiom audit -/

#print axioms obligation_A_RGA
#print axioms opOK_of_generation

end Sal.ConditionedMRDTs.RGASig
