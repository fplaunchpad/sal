import Sal.MRDTs.Metatheory.Development.ConditionedConvergence
import Sal.MRDTs.Metatheory.Development.RGA_GeneralSwap

/-!
# Task #14 · Milestone 2 — wiring the RGA's kernel-checked general swap into the
convergence bubble (the σ-walk threading)

Bubble re-architecture, Milestone 2 (`CONDITIONED_METATHEORY_PLAN.md`, "Bubble
re-architecture — SCOPE", "Milestones (now Route A)" §2).  This file is ADDITIVE:
it modifies no existing file, and every kept headline is `sorry`-free and
kernel-clean (`propext, Classical.choice, Quot.sound` only; the imported
`Merge_Linearization_Set` sorries are not transitively touched).

## What M1/1b left, and what this file wires

* `ConditionedConvergence.applySeq_swap_loOnA_incomparable_C` (VERIFIED) proves the
  conditioned incomparable swap but demands `hInv`, `ha : applicable a`,
  `hb : applicable b` at the swap state `applySeq s pfx`.  M1 established the RGA
  CANNOT supply `applicable a` at hybrid σ-walk states (a's path is staled there).
* `RGAGeneralSwap.general_swap` (VERIFIED) proves the RGA swap
  `eq (do_ (do_ s a) b) (do_ (do_ s b) a)` under the strictly-weaker `Faithful a`
  (not `applicable a`), for any reachable — including multi-delete-staled — `s`,
  needing only the swapped-in `b` `accurate`, plus `NoFreshClash a b`.

## The three deliverables and their verdicts (headline)

1. **Generic swap-witness abstraction — CLOSED** (§1).
   `SwapWitness D a b σ := update (update σ a) b = update (update σ b) a` is the
   generic "pointwise swap holds at σ".  `applySeq_swap_of_swapWitness` lifts it to
   a fold swap; `applySeq_swap_loOnA_incomparable_C'` is the drop-`applicable a`
   variant of the M1 lemma: the `commutesOn`-branch consumes a (commutesOn-gated)
   `SwapWitness` instead of deriving it from `applicable a`+`applicable b`; the
   same-replica-contradiction and rc-overwriter branches are verbatim (`hInv` is
   retained — the overwriter branch needs it).  Both `applicable a` AND
   `applicable b` drop out (neither is consulted once `SwapWitness` supplies the
   `commutesOn` branch).

2. **RGA discharges SwapWitness via `general_swap` — the eq-vs-Eq VERDICT is IN
   (§2).**  `general_swap` concludes the RGA's *observational* `eq`; the generic
   `SwapWitness` is Lean `Eq`.  These are NOT interchangeable for the RGA:
   `eq_strictly_weaker_than_Eq` exhibits two `concrete_st` that are observationally
   `eq` but Lean-unequal (a `del` leaves off-domain `mappings` junk that `eq`, being
   domain-restricted, cannot see; `map_lemma_equal_intro` requires `sel` agreement
   at EVERY key, including off-domain).  So the coordinator's `rga_swapWitness`
   (with the Lean-`Eq` generic `SwapWitness`) is NOT dischargeable from `general_swap`
   — the sanctioned resource yields only `eq`, and `eq ⊬ Eq`.  What DOES close is
   `rga_swapWitnessEq` — the RGA discharges the *observational* swap witness
   `SwapWitnessEq` directly from `general_swap`.  **Verdict: the σ-layer (Lean-`Eq`
   `applySeq`) must be rebuilt over observational `eq` — a quotient of `concrete_st`
   or an `eq`-congruent `applySeq` — to host the RGA.  This is a σ-layer refactor
   (out of this additive file's scope: it would modify `ConditionedConvergence`),
   and it is the single obligation blocking end-to-end hosting, INDEPENDENT of the
   Faithful-threading below.**

3. **Faithful / NoFreshClash threading (§3) — the substantive part, PARTIAL with a
   precise obstruction.**
   * `NoFreshClash a b` for concurrent `a b`: CLOSED under monotone allocation
     (`noFreshClash_of_monoAlloc`) — `b`'s fresh id exceeds every id `a` recorded.
   * `Faithful a` preserved under a fresh non-clashing `Ins` step: CLOSED
     (`climbFaithful_doIns`, `faithful_doIns`).
   * `Faithful a` preserved under a `Del` step: **OBSTRUCTED — `ClimbFaithful`
     alone is NOT preserved** (`climbFaithful_not_preserved_under_del`, a
     kernel-checked concrete refutation).  `ClimbFaithful` is a *one-level* property
     (it certifies only the current climb-target's parent); a `Del` that removes a
     node deeper in `a`'s recorded list re-anchors past a level `ClimbFaithful` never
     constrained.  The threadable invariant is the strictly stronger recursive
     *chain*-faithfulness `ChainFaithful` ("the live members of `a`'s list form a
     true ancestor chain"), which implies `ClimbFaithful` (`climbFaithful_of_chain`)
     and IS preserved by deletes of accurate targets — its Del-preservation is the
     located remaining sub-fact (§3.4, stated; its full induction is the M2 tail).
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.RGABubbleWiring

open Sal.Emulation
open Sal.Metatheory
open Sal.Metatheory.ConditionedConvergence
open Sal.Metatheory.G2Probe (loOnC RGACondSig insOpE delOpE)
open Sal.Metatheory.RGAGeneralSwap

/-! ## §1  The generic swap-witness abstraction (deliverable 1)

`SwapWitness D a b σ` is exactly the equality the `commutesOn`-branch of
`applySeq_swap_loOnA_incomparable_C` derives from `commutesOn`+`applicable a`+
`applicable b`.  Making it a first-class premise lets us DROP the applicability
side conditions on the events at the swap state (`ha`, `hb`), keeping only `hInv`
(which the rc-overwriter branch genuinely consumes). -/

/-- **Generic swap witness.**  The pointwise swap `update (update σ a) b =
update (update σ b) a` holds at `σ` (Lean `Eq`, matching the σ-layer's
`applySeq`).  This is the generic replacement for `applicable a` at the swap
state: it is precisely what the `commutesOn`-branch needs, and nothing more. -/
def SwapWitness (D : ConditionedMRDTSig) (a b : Op D.AppOp) (σ : D.State) : Prop :=
  D.toCRDTSig.update (D.toCRDTSig.update σ a) b
    = D.toCRDTSig.update (D.toCRDTSig.update σ b) a

/-- **SwapWitness lifts to a fold swap.**  The `commutesOn`-free analogue of
`applySeq_swap_commutesOn`: a pointwise swap at the fold state `applySeq s pfx`
propagates to swapping the adjacent pair inside the full fold.  No `Inv`, no
`applicable` — just the pointwise equality. -/
theorem applySeq_swap_of_swapWitness (D : ConditionedMRDTSig) {a b : Op D.AppOp}
    (pfx sfx : List (Op D.AppOp)) (s : D.State)
    (h_sw : SwapWitness D a b (applySeq D.toCRDTSig s pfx)) :
    applySeq D.toCRDTSig s (pfx ++ a :: b :: sfx)
    = applySeq D.toCRDTSig s (pfx ++ b :: a :: sfx) := by
  calc applySeq D.toCRDTSig s (pfx ++ a :: b :: sfx)
      = applySeq D.toCRDTSig
          (D.toCRDTSig.update (D.toCRDTSig.update (applySeq D.toCRDTSig s pfx) a) b) sfx := by
        simp [applySeq, List.foldl_append, List.foldl_cons]
    _ = applySeq D.toCRDTSig
          (D.toCRDTSig.update (D.toCRDTSig.update (applySeq D.toCRDTSig s pfx) b) a) sfx := by
        rw [h_sw]
    _ = applySeq D.toCRDTSig s (pfx ++ b :: a :: sfx) := by
        simp [applySeq, List.foldl_append, List.foldl_cons]

/-- **The drop-`applicable a` incomparable swap (deliverable 1).**  The variant of
`ConditionedConvergence.applySeq_swap_loOnA_incomparable_C` whose staled-event
premise is a `SwapWitness` (gated on `commutesOn a b`) rather than
`applicable a`/`applicable b` at the swap state.

* `commutesOn a b` branch: uses `h_sw h_comm` (the SwapWitness) via
  `applySeq_swap_of_swapWitness` — NO `applicable a`, NO `applicable b`.
* `¬commutesOn`, same replica: `vis_total_same_replica` gives a vis-edge that
  contradicts incomparability (verbatim from the M1 lemma).
* `¬commutesOn`, different replica: `h_ov` + `applySeq_swap_via_cond_comm_liftC`
  (verbatim; `hInv` retained here, as this branch consumes it).

Compared to the M1 lemma, `ha`/`hb` (applicability at the swap state) are GONE. -/
theorem applySeq_swap_loOnA_incomparable_C' (D : ConditionedMRDTSig) (hC : UpdateVCsC D)
    {C : Sal.Emulation.Configuration D.toCRDTSig} {ev : Set (Op D.AppOp)}
    {a b : Op D.AppOp} (h_ne : a ≠ b)
    (h_a_in_C : a ∈ C.events) (h_b_in_C : b ∈ C.events)
    (h_not_lo_ab : ¬ loOnA D C ev a b) (h_not_lo_ba : ¬ loOnA D C ev b a)
    (pfx sfx : List (Op D.AppOp)) (s : D.State)
    (hInv : D.Inv (applySeq D.toCRDTSig s pfx))
    (h_sw : D.commutesOn a b → SwapWitness D a b (applySeq D.toCRDTSig s pfx))
    (h_ov : ¬ D.commutesOn a b → a.rep ≠ b.rep →
      ∃ e₃ α β, sfx = α ++ e₃ :: β ∧
                distinctOps a e₃ ∧ distinctOps b e₃ ∧
                ((D.rc a b = RcRes.Fst_then_snd ∧ ¬ D.commutesOn b e₃) ∨
                 (D.rc b a = RcRes.Fst_then_snd ∧ ¬ D.commutesOn a e₃))) :
    applySeq D.toCRDTSig s (pfx ++ a :: b :: sfx)
    = applySeq D.toCRDTSig s (pfx ++ b :: a :: sfx) := by
  by_cases h_comm : D.commutesOn a b
  · exact applySeq_swap_of_swapWitness D pfx sfx s (h_sw h_comm)
  · obtain ⟨_, _, hL_a, h_a_in_s⟩ := h_a_in_C
    obtain ⟨_, _, hL_b, h_b_in_s⟩ := h_b_in_C
    by_cases h_same : a.rep = b.rep
    · exfalso
      rcases C.vis_total_same_replica hL_a h_a_in_s hL_b h_b_in_s h_ne h_same with hvab | hvba
      · exact h_not_lo_ab (Or.inl (Or.inl ⟨hvab, h_comm⟩))
      · have h_comm_ba : ¬ D.commutesOn b a := fun h => h_comm (commutesOn_symm D h)
        exact h_not_lo_ba (Or.inl (Or.inl ⟨hvba, h_comm_ba⟩))
    · have h_dist_ab : distinctOps a b :=
        C.timestamps_distinct hL_a h_a_in_s hL_b h_b_in_s h_ne
      obtain ⟨e₃, α, β, h_sfx, h_dae, h_dbe, h_case⟩ := h_ov h_comm h_same
      subst h_sfx
      rcases h_case with ⟨h_rc_ab, h_nc_be⟩ | ⟨h_rc_ba, h_nc_ae⟩
      · exact applySeq_swap_via_cond_comm_liftC D hC h_dist_ab h_dbe h_dae
          h_rc_ab h_nc_be pfx α β s hInv
      · have h_dist_ba : distinctOps b a := Ne.symm h_dist_ab
        exact (applySeq_swap_via_cond_comm_liftC D hC h_dist_ba h_dae h_dbe
          h_rc_ba h_nc_ae pfx α β s hInv).symm

/-! ## §2  RGA discharges the swap witness — the eq-vs-Eq verdict (deliverable 2)

`general_swap` (`RGA_GeneralSwap.lean`) concludes the RGA's *observational*
`eq (do_ (do_ s a) b) (do_ (do_ s b) a)`.  The generic `SwapWitness` above is
Lean `Eq`.  For the RGA these are NOT interchangeable, and this file pins WHY.

`RGACondSig.toCRDTSig.update s o` is definitionally `do_ s o`, so
`SwapWitness RGACondSig a b s` is definitionally `do_ (do_ s a) b = do_ (do_ s b) a`
(**Lean `Eq`**), whereas the observational witness below is `eq (…) (…)`. -/

/-- The RGA's *observational* swap witness: what `general_swap` actually proves. -/
def SwapWitnessEq (a b : op_t) (s : concrete_st) : Prop :=
  eq (do_ (do_ s a) b) (do_ (do_ s b) a)

/-- **RGA discharges the observational swap witness via `general_swap` — CLOSED.**
This is the honest form of the coordinator's `rga_swapWitness`: with the RGA's
observational `eq` (not Lean `Eq`), the discharge is a one-line application of the
M1b general swap.  The staled event `a` need only be `Faithful` (not `applicable`),
and only the swapped-in `b` need be `accurate`. -/
theorem rga_swapWitnessEq (s : concrete_st) (a b : op_t)
    (hfaith : Faithful a s) (hb : accurate b s) (hclash : NoFreshClash a b)
    (hmono : id_mono s) (hwf : wf s) (h0 : contains s 0 = false)
    (hfa : fresh_ts a s) (hfb : fresh_ts b s) (hdist : a.1 ≠ b.1) :
    SwapWitnessEq a b s :=
  general_swap s a b hdist h0 hwf hmono hb hfa hfb hfaith hclash

/-! ### The gap is genuine: observational `eq` is strictly weaker than Lean `Eq`

A `del` shrinks a map's `domain` but leaves its `mappings` function untouched, so a
deleted node's stale `(element, anchor)` persists as OFF-DOMAIN junk.  Observational
`eq` (`∀ k, contains-agree ∧ (contains → sel-agree)`) only compares `sel` WHERE
`contains` is true, so it cannot see this junk — but Lean `Eq` (via
`map_lemma_equal_intro`) requires `sel` agreement at EVERY key.  Hence `eq` does not
imply Lean `Eq`, and `general_swap`'s conclusion cannot be strengthened to the Lean
`Eq` the generic `SwapWitness` (and the σ-layer's `applySeq`) demand. -/

/-- A concrete off-domain-junk state: insert node `1`, then delete it.  Its domain is
empty (like `init_st`), but its `mappings` still carries `1 ↦ (5, 0)`. -/
def junkA : concrete_st := del (upd init_st 1 (5, 0)) 1

theorem contains_junkA (k : ℕ) : contains junkA k = false := by
  simp only [junkA, contains, del, upd, init_st, const_on, restrict, const, domain,
    remove, union, intersection, complement, empty, mem]
  grind

/-- `junkA` and `init_st` agree observationally (both have empty domain) … -/
theorem eq_junkA_init : eq junkA init_st := by
  intro k
  refine ⟨?_, ?_⟩
  · rw [contains_junkA k, contains_init k]
  · rw [contains_junkA k]; simp

/-- … yet they are NOT Lean-equal: `sel junkA 1 = (5, 0) ≠ (0, 0) = sel init_st 1`.
So `eq` is strictly weaker than Lean `Eq` on RGA states. -/
theorem junkA_ne_init : junkA ≠ init_st := by
  intro h
  have hs : sel junkA 1 = sel init_st 1 := by rw [h]
  simp [junkA, sel, del, upd, init_st, const_on, restrict, const] at hs

/-- **The eq-vs-Eq wall (deliverable 2 verdict).**  There exist RGA states that are
observationally `eq` but Lean-unequal.  Consequently the coordinator's
`rga_swapWitness` — with the generic Lean-`Eq` `SwapWitness RGACondSig a b s` as
conclusion — is NOT dischargeable from `general_swap`: the latter yields only `eq`,
which (by this witness) does not imply the Lean `Eq` the σ-layer's `applySeq`
consumes.  Hosting the RGA therefore requires rebuilding the σ-layer over
observational `eq` (an `eq`-quotient of `concrete_st`, or an `eq`-congruent
`applySeq`/`SwapWitness`) — a change to `ConditionedConvergence`, outside this
additive file.  This is the single obligation blocking end-to-end hosting, and it
is INDEPENDENT of the Faithful-threading in §3. -/
theorem eq_strictly_weaker_than_Eq :
    (∃ x y : concrete_st, eq x y ∧ x ≠ y) :=
  ⟨junkA, init_st, eq_junkA_init, junkA_ne_init⟩

/-! ## §3  Threading `Faithful` / `NoFreshClash` through the σ-walk (deliverable 3)

`general_swap` needs, at each hybrid fold state `s = applySeq init pfx`:
`Faithful a s`, `accurate b s`, `NoFreshClash a b` (plus the transportable
`RgaInv ∧ id_mono` and freshness).  §3.1 discharges `NoFreshClash`; §3.2 shows
`Faithful` survives a fresh `Ins` step; §3.3 shows `Faithful` (as `ClimbFaithful`)
does NOT survive a `Del` step, locating the obstruction; §3.4 gives the stronger
threadable invariant `ChainFaithful`. -/

/-! ### §3.1  `NoFreshClash` for concurrent events (deliverable 3b)

`a`'s recorded id list. -/
def recList : op_t → List ℕ
  | (_, _, .Ins _ pre anch) => anch :: pre
  | (_, _, .Del pre x)      => x :: pre

/-- **`NoFreshClash` from causal freshness (Ins case).**  If `b` is an `Ins` whose
timestamp `t2` STRICTLY EXCEEDS every id `a` recorded, then `t2 ∉ a`'s list, i.e.
`NoFreshClash a b`.  This is exactly the causal-freshness a real execution supplies:
under monotone timestamp allocation, a concurrent `b`'s freshly allocated id exceeds
every id in `a`'s causal past (⊇ `a`'s recorded ancestor path), because neither of
two concurrent events saw the other.  **The exact hypothesis it needs**:
`∀ c ∈ recList a, c < t2` — supplied by `mono_alloc` (RGA_Reachability_Invariant). -/
theorem noFreshClash_of_freshIns (a : op_t) (t2 r2 e2 anch2 : ℕ) (pre2 : List ℕ)
    (hbound : ∀ c ∈ recList a, c < t2) :
    NoFreshClash a (t2, r2, .Ins e2 pre2 anch2) := by
  obtain ⟨t1, r1, op1⟩ := a
  cases op1 with
  | Ins e1 p1 a1 =>
      simp only [NoFreshClash, recList] at hbound ⊢
      intro hmem; exact absurd (hbound t2 hmem) (Nat.lt_irrefl t2)
  | Del p1 x1 =>
      simp only [NoFreshClash, recList] at hbound ⊢
      intro hmem; exact absurd (hbound t2 hmem) (Nat.lt_irrefl t2)

/-- **`NoFreshClash` (Del case).**  When `b` is a `Del`, `NoFreshClash a b` is either
trivial (`a` an `Ins`) or `b`'s target `≠ 0` (`a` a `Del`).  A genuine `Del`'s target
is a live node and the root sentinel is never stored, so `xb ≠ 0` holds. -/
theorem noFreshClash_of_del (a : op_t) (t2 r2 xb : ℕ) (pre2 : List ℕ) (hxb : xb ≠ 0) :
    NoFreshClash a (t2, r2, .Del pre2 xb) := by
  obtain ⟨t1, r1, op1⟩ := a
  cases op1 with
  | Ins e1 p1 a1 => simp [NoFreshClash]
  | Del p1 x1 => simp only [NoFreshClash]; exact hxb

/-! ### §3.2  `Faithful` survives a fresh `Ins` step (deliverable 3a, easy half)

A fresh, non-clashing `Ins` (`t ∉ a`'s list, `t ≠ 0`) leaves `a`'s recorded list's
`resolve`/`anc`/`contains` untouched, so `ClimbFaithful` and `DelTargetFaithful` — and
hence `Faithful` — are preserved. -/

/-- A fresh id (`≠ 0`, `∉ L`) is never what `L` resolves to. -/
theorem resolve_ne_fresh (s : concrete_st) (M : List ℕ) (t : ℕ) (ht0 : t ≠ 0) (htM : t ∉ M) :
    resolve s M ≠ t := by
  induction M with
  | nil => simp only [resolve]; exact fun e => ht0 e.symm
  | cons c rest ih =>
    simp only [resolve]
    by_cases hc : contains s c = true
    · rw [if_pos hc]; intro e; apply htM; rw [← e]; exact List.mem_cons_self
    · rw [if_neg hc]; exact ih (fun hm => htM (List.mem_cons_of_mem c hm))

/-- `ClimbFaithful` of a list `L` survives a fresh non-clashing `Ins`. -/
theorem climbFaithful_doIns (s : concrete_st) (t r e a : ℕ) (pre L : List ℕ)
    (ht0 : t ≠ 0) (htL : t ∉ L) (hcf : ClimbFaithful s L) :
    ClimbFaithful (do_ s (t, r, .Ins e pre a)) L := by
  have hstep : do_ s (t, r, .Ins e pre a) = upd s t (e, resolve s (a :: pre)) := by
    simp only [do_]
  have hres : resolve (do_ s (t, r, .Ins e pre a)) L = resolve s L := by
    rw [hstep]; exact resolve_upd_notMem s t (e, resolve s (a :: pre)) L htL
  unfold ClimbFaithful
  rw [hres]
  intro hlive
  have hvLt : resolve s L ≠ t := resolve_ne_fresh s L t ht0 htL
  have hne : (t : ℕ) != resolve s L := by
    simp only [bne_iff_ne, ne_eq]; exact fun e' => hvLt e'.symm
  have hcvL : contains s (resolve s L) = true := by
    have h := lemma_InDomUpd2 s (resolve s L) t (e, resolve s (a :: pre)) hne
    rw [hstep] at hlive; rw [h] at hlive; exact hlive
  have hanc : anc (do_ s (t, r, .Ins e pre a)) (resolve s L) = anc s (resolve s L) := by
    rw [hstep]; simp only [anc]
    rw [lemma_SelUpd2 s (resolve s L) t (e, resolve s (a :: pre)) hne]
  rw [hanc]
  have hresf : resolve (do_ s (t, r, .Ins e pre a)) (L.filter (fun c => c != resolve s L))
             = resolve s (L.filter (fun c => c != resolve s L)) := by
    rw [hstep]
    exact resolve_upd_notMem s t (e, resolve s (a :: pre)) _
      (fun hm => htL (List.mem_filter.mp hm).1)
  rw [hresf]
  exact hcf hcvL

/-- `DelTargetFaithful` survives a fresh non-clashing `Ins`. -/
theorem delTargetFaithful_doIns (s : concrete_st) (t r e a x : ℕ) (pre L : List ℕ)
    (htx : t ≠ x) (htL : t ∉ L) (hdtf : DelTargetFaithful s L x) :
    DelTargetFaithful (do_ s (t, r, .Ins e pre a)) L x := by
  have hstep : do_ s (t, r, .Ins e pre a) = upd s t (e, resolve s (a :: pre)) := by
    simp only [do_]
  unfold DelTargetFaithful
  intro hlive
  have hxne : (t : ℕ) != x := by simp only [bne_iff_ne, ne_eq]; exact htx
  have hcx : contains s x = true := by
    rw [hstep, lemma_InDomUpd2 s x t (e, resolve s (a :: pre)) hxne] at hlive; exact hlive
  have hres : resolve (do_ s (t, r, .Ins e pre a)) L = resolve s L := by
    rw [hstep]; exact resolve_upd_notMem s t (e, resolve s (a :: pre)) L htL
  have hanc : anc (do_ s (t, r, .Ins e pre a)) x = anc s x := by
    rw [hstep]; simp only [anc]; rw [lemma_SelUpd2 s x t (e, resolve s (a :: pre)) hxne]
  rw [hres, hanc]; exact hdtf hcx

/-- **`Faithful` survives a fresh non-clashing `Ins` step (deliverable 3a, Ins).**
This is the reachability-preservation half that DOES close: `noopFeasible`-style
inserts along the σ-walk keep the staled event `a` `Faithful`. -/
theorem faithful_doIns (s : concrete_st) (t r e a : ℕ) (pre : List ℕ) (o : op_t)
    (ht0 : t ≠ 0) (hclash : t ∉ recList o) (hfaith : Faithful o s) :
    Faithful o (do_ s (t, r, .Ins e pre a)) := by
  obtain ⟨t1, r1, op1⟩ := o
  cases op1 with
  | Ins e1 p1 a1 =>
      simp only [Faithful, recList] at hfaith hclash ⊢
      exact climbFaithful_doIns s t r e a pre (a1 :: p1) ht0 hclash hfaith
  | Del p1 x1 =>
      simp only [Faithful, recList] at hfaith hclash ⊢
      obtain ⟨hcf, hdtf, hx0⟩ := hfaith
      have htp1 : t ∉ p1 := fun hm => hclash (List.mem_cons_of_mem x1 hm)
      have htx1 : t ≠ x1 := fun ex => hclash (by rw [ex]; exact List.mem_cons_self)
      exact ⟨climbFaithful_doIns s t r e a pre p1 ht0 htp1 hcf,
             delTargetFaithful_doIns s t r e a x1 pre p1 htx1 htp1 hdtf, hx0⟩

/-! ### §3.3  `ClimbFaithful` does NOT survive a `Del` step — the located obstruction

**This is the crux of deliverable 3a, and it does NOT close for `ClimbFaithful`.**
`ClimbFaithful s L` is a *one-level* property: it certifies only that filtering out
`L`'s current climb-target resolves to that target's parent.  A `Del` that removes a
node lying DEEPER in `a`'s recorded list re-anchors `a`'s climb past a level
`ClimbFaithful` never constrained — so the post-delete climb-target's parent need not
match.  The concrete kernel-checked refutation (native-free):

`sCex` is the chain `root → 1 → 2 → 3` plus a stray live node `5`.  `a`'s recorded
list is `Lcex = [3, 2, 5]` — climb-target `3`, whose true parent `2` IS the next live
element, so `ClimbFaithful sCex Lcex` HOLDS.  But below `2`, `Lcex` records `5`, not
`2`'s true parent `1`.  Deleting `2` (an ACCURATE delete, path `[1]`) re-anchors `3`
to `2`'s true parent `1`, while `Lcex.filter (≠3)` now resolves past the dead `2` to
`5 ≠ 1`.  So `ClimbFaithful (do_ sCex delOp) Lcex` FAILS. -/

/-- Chain `root → 1 → 2 → 3` with a stray live node `5`. -/
def sCex : concrete_st := mk [(1, 100, 0), (2, 100, 1), (3, 100, 2), (5, 100, 0)]
/-- `a`'s recorded list: chain-CORRECT at the top (`3`'s parent `2` is next) but
chain-INCORRECT below `2` (records `5`, not `2`'s true parent `1`). -/
def Lcex : List ℕ := [3, 2, 5]
/-- An ACCURATE delete of `2` (its true path is `[1]`). -/
def delOp : op_t := (9, 0, .Del [1] 2)

theorem climbFaithful_sCex : ClimbFaithful sCex Lcex := by
  unfold ClimbFaithful; intro _; decide

theorem accurate_delOp : accurate delOp sCex := by
  refine Or.inr ⟨by decide, ?_⟩
  show IsAncPath sCex 2 [1]
  refine ⟨by decide, by decide, ?_⟩
  show IsAncPath sCex 1 []
  show anc sCex 1 = 0
  decide

theorem not_climbFaithful_after_del : ¬ ClimbFaithful (do_ sCex delOp) Lcex := by
  unfold ClimbFaithful; intro h
  have hlive : contains (do_ sCex delOp) (resolve (do_ sCex delOp) Lcex) = true := by decide
  exact absurd (h hlive) (by decide)

/-- **The located obstruction (deliverable 3a).**  `ClimbFaithful` — the predicate
`general_swap` consumes as `Faithful` for an `Ins` — is NOT preserved along the
σ-walk: there is a state, a list `ClimbFaithful` there, and an ACCURATE delete after
which `ClimbFaithful` fails.  So threading `general_swap`'s `Faithful` verbatim does
not close; a strictly stronger, delete-stable invariant is required (§3.4). -/
theorem climbFaithful_not_preserved_under_del :
    ∃ (s : concrete_st) (o : op_t) (L : List ℕ),
      ClimbFaithful s L ∧ accurate o s ∧ ¬ ClimbFaithful (do_ s o) L :=
  ⟨sCex, delOp, Lcex, climbFaithful_sCex, accurate_delOp, not_climbFaithful_after_del⟩

/-! ### §3.4  `ChainFaithful` — the stronger threadable invariant

The fix the §3.3 refutation points to: certify EVERY live level of `a`'s recorded
list is a true ancestor chain, not just the top.  `ChainFaithfulAux` recurses the
`ClimbFaithful` obligation down the successive climb-targets (fuel = list length,
which bounds the number of live levels), and `ChainFaithful` runs it at full fuel. -/

/-- Fuel-indexed chain-faithfulness: each successive climb-target's parent is the next
resolve, recursively.  Fuel = list length suffices (each live level consumes ≥ 1). -/
def ChainFaithfulAux (s : concrete_st) : Nat → List ℕ → Prop
  | 0, _ => True
  | fuel + 1, L =>
      contains s (resolve s L) = true →
        resolve s (L.filter (fun c => c != resolve s L)) = anc s (resolve s L)
        ∧ ChainFaithfulAux s fuel (L.filter (fun c => c != resolve s L))

/-- **`ChainFaithful s L`**: the live members of `L` form a true ancestor chain. -/
def ChainFaithful (s : concrete_st) (L : List ℕ) : Prop := ChainFaithfulAux s L.length L

/-- **`ChainFaithful` implies `ClimbFaithful`** (needs `contains s 0 = false`, which
`RgaInv` supplies).  So the stronger invariant feeds `general_swap`'s `Faithful`
unchanged — its top level IS `ClimbFaithful`. -/
theorem climbFaithful_of_chain (s : concrete_st) (L : List ℕ) (h0 : contains s 0 = false)
    (hcf : ChainFaithful s L) : ClimbFaithful s L := by
  unfold ClimbFaithful
  intro hlive
  cases L with
  | nil =>
      simp only [resolve] at hlive; rw [h0] at hlive; exact absurd hlive (by simp)
  | cons c cs =>
      unfold ChainFaithful at hcf
      simp only [List.length_cons] at hcf
      exact (hcf hlive).1

/-- **`ChainFaithful` survives a fresh non-clashing `Ins` step** — the fuel-indexed
lift of `climbFaithful_doIns`: a fresh insert perturbs no level of the chain. -/
theorem chainFaithfulAux_doIns (s : concrete_st) (t r e a : ℕ) (pre : List ℕ) (ht0 : t ≠ 0) :
    ∀ (fuel : Nat) (M : List ℕ), t ∉ M →
      ChainFaithfulAux s fuel M → ChainFaithfulAux (do_ s (t, r, .Ins e pre a)) fuel M := by
  have hstep : do_ s (t, r, .Ins e pre a) = upd s t (e, resolve s (a :: pre)) := by simp only [do_]
  intro fuel
  induction fuel with
  | zero => intro M _ _; exact trivial
  | succ fuel ih =>
    intro M htM h
    have hvne : resolve s M ≠ t := resolve_ne_fresh s M t ht0 htM
    have hbne : (t : ℕ) != resolve s M := by
      simp only [bne_iff_ne, ne_eq]; exact fun e' => hvne e'.symm
    have hresM : resolve (do_ s (t, r, .Ins e pre a)) M = resolve s M := by
      rw [hstep]; exact resolve_upd_notMem s t (e, resolve s (a :: pre)) M htM
    show contains (do_ s (t, r, .Ins e pre a)) (resolve (do_ s (t, r, .Ins e pre a)) M) = true →
        resolve (do_ s (t, r, .Ins e pre a))
            (M.filter (fun c => c != resolve (do_ s (t, r, .Ins e pre a)) M))
          = anc (do_ s (t, r, .Ins e pre a)) (resolve (do_ s (t, r, .Ins e pre a)) M)
        ∧ ChainFaithfulAux (do_ s (t, r, .Ins e pre a)) fuel
            (M.filter (fun c => c != resolve (do_ s (t, r, .Ins e pre a)) M))
    rw [hresM]
    intro hlive'
    have hcv : contains s (resolve s M) = true := by
      have hmem := lemma_InDomUpd2 s (resolve s M) t (e, resolve s (a :: pre)) hbne
      rw [hstep] at hlive'; rw [hmem] at hlive'; exact hlive'
    have hunf : ChainFaithfulAux s (fuel + 1) M
        = (contains s (resolve s M) = true →
            resolve s (M.filter (fun c => c != resolve s M)) = anc s (resolve s M)
            ∧ ChainFaithfulAux s fuel (M.filter (fun c => c != resolve s M))) := rfl
    rw [hunf] at h
    obtain ⟨heq, hrec⟩ := h hcv
    refine ⟨?_, ?_⟩
    · have hresf : resolve (do_ s (t, r, .Ins e pre a)) (M.filter (fun c => c != resolve s M))
                 = resolve s (M.filter (fun c => c != resolve s M)) := by
        rw [hstep]
        exact resolve_upd_notMem s t (e, resolve s (a :: pre)) _
          (fun hm => htM (List.mem_filter.mp hm).1)
      have hanc : anc (do_ s (t, r, .Ins e pre a)) (resolve s M) = anc s (resolve s M) := by
        rw [hstep]; simp only [anc]
        rw [lemma_SelUpd2 s (resolve s M) t (e, resolve s (a :: pre)) hbne]
      rw [hresf, hanc]; exact heq
    · exact ih (M.filter (fun c => c != resolve s M))
        (fun hm => htM (List.mem_filter.mp hm).1) hrec

theorem chainFaithful_doIns (s : concrete_st) (t r e a : ℕ) (pre L : List ℕ)
    (ht0 : t ≠ 0) (htL : t ∉ L) (hcf : ChainFaithful s L) :
    ChainFaithful (do_ s (t, r, .Ins e pre a)) L :=
  chainFaithfulAux_doIns s t r e a pre ht0 L.length L htL hcf

/- ── The single remaining M2 obligation (documented goal-state, NOT sorried) ──

`ChainFaithful` preserved under an ACCURATE `Del` step:

    theorem chainFaithful_doDel (s : concrete_st) (t r x : ℕ) (pre L : List ℕ)
        (h0 : contains s 0 = false) (hacc : accurate (t, r, .Del pre x) s)
        (hcf : ChainFaithful s L) :
        ChainFaithful (do_ s (t, r, .Del pre x)) L

Why it should hold (the splice argument): an accurate `Del x` sets
`resolve s pre = anc s x`, so deleting `x` re-links each child `c` of `x`
(`anc s c = x`) to `anc s x` — exactly `x`'s successor in the true chain.  In
`ChainFaithful` terms this SPLICES `x` out of the live chain while preserving every
surviving `anc`-link, so `ChainFaithfulAux` is maintained.  The §3.3 counterexample
does NOT threaten this: there `Lcex` was NOT chain-faithful below the deleted node
(it recorded `5`, not `1`), which `ChainFaithful` forbids.

Why it is the M2 tail (not yet mechanized here): unlike the `Ins` step, a `Del`
SHIFTS the climb-target (`resolve s' M = resolve s (M.filter (≠x))`) and MERGES two
`s`-levels into one `s'`-level, so the fuel-indexed induction has no level-by-level
correspondence between the `s`- and `s'`-recursions — it requires an induction that
tracks the spliced chain (essentially the invariant-level generalisation of
`RGA_GeneralSwap.swap_InsDel`/`swap_DelDel`'s re-anchoring algebra).  Combined with
`chainFaithful_doIns` + `climbFaithful_of_chain`, closing this ONE lemma would
discharge deliverable 3a end-to-end (`Faithful` threads via `ChainFaithful`).

Generation base case (routine, omitted): `accurate a s ∧ contains s 0 = false ⟹
ChainFaithful s (recList a)`, the full-chain lift of the already-proven
`RGA_GeneralSwap.climbFaithful_of_accurate_ins` / `climbFaithful_of_isAncPath`. -/

/-! ## §7  Axiom audit — headlines kernel-clean, no `sorryAx`, no `native_decide`. -/

#print axioms applySeq_swap_of_swapWitness
#print axioms applySeq_swap_loOnA_incomparable_C'
#print axioms rga_swapWitnessEq
#print axioms eq_strictly_weaker_than_Eq
#print axioms noFreshClash_of_freshIns
#print axioms noFreshClash_of_del
#print axioms faithful_doIns
#print axioms climbFaithful_not_preserved_under_del
#print axioms climbFaithful_of_chain
#print axioms chainFaithful_doIns

end Sal.Metatheory.RGABubbleWiring
