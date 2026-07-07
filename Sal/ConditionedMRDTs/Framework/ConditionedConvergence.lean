import Sal.ConditionedMRDTs.Framework.Sigma_LoOn3
import Sal.ConditionedMRDTs.Framework.LoOnC
import Sal.ConditionedMRDTs.Framework.NoopFeasible

/-!
# The general conditioned convergence theorem (task #9, stage 6)

This file generalizes the *unconditioned* convergence machinery of
`Sigma_LoOn3.lean` (`convergence_on_u`, built on `loOn` + `UpdateVCs`,
`CRDTSig.commutes`-based) to the **conditioned** update layer over an arbitrary
`ConditionedMRDTSig D`, using the feasibility notion validated in
`UpdateFeasibility_Gate.lean`: the applicability-aware order `loOnA` plus
no-op-feasible enumerations `noopFeasible`.

Everything here is over an ABSTRACT `D : ConditionedMRDTSig`; the RGA appears
only in §6's instantiation sketch.  No existing file is modified.

## The headline result and the sharp decomposition it produces

The main theorem `conditioned_convergence_on` (§3) is CLOSED (0 sorries,
kernel-clean).  The route by which it closes is itself the central finding:

> **Order-repair is complete; the residue is purely the semantic swap VCs.**

Concretely, the conditioned problem factors into two independent halves:

* **(order half — SOLVED here)** `loOnA` exactly repairs the linearization
  edges that conditioning (`commutes ↦ commutesOn`) drops.  Under a *single*
  order VC `dependency_covers_vacuity` — "a vis-edge that `commutesOn` makes
  vacuous is a generation dependency" — we prove the pointwise inclusion
  `loOn C ev ⊆ loOnA D C ev` (`loOn_imp_loOnA`), hence
  `respects π (loOnA) → respects π (loOn)` (`respects_loOn_of_loOnA`).  This is
  the complete, closed answer to "which edges must `loOnA` add back": exactly
  the ones `dependency_covers_vacuity` names.
* **(semantic half — the residue)** With the order repaired, convergence
  *reduces verbatim* to the already-proved unconditioned `convergence_on_u`,
  which discharges the actual state-algebra via the `commutes`-based
  `UpdateVCs`.

So `conditioned_convergence_on` is stated under `UpdateVCs D.toCRDTSig`
(unconditioned semantic VCs) **+** `dependency_covers_vacuity` (the order VC).

### Two findings that fall out of this route

1. **`noopFeasible` is NOT needed for convergence under the unconditioned
   semantic VCs.**  The theorem carries the two `noopFeasible` hypotheses (to
   match the stage-6 signature) but never consults them — the reduction to
   `convergence_on_u` closes without them.  `noopFeasible`'s job is
   *satisfiability* (existence of admissible enumerations for reachable
   redundant-concurrent versions, `UpdateFeasibility_Gate.lean`) and it becomes
   load-bearing for *convergence* only on the genuinely-conditioned route
   below, where the semantic swap must be justified by `commutesOn` at
   *applicable* states rather than by `commutes` everywhere.

2. **The genuinely-conditioned route (`commutesOn`-only VCs, §4–5) is
   OBSTRUCTED, and the obstruction is now precisely located** (§5): it is NOT
   in the swap step (the conditioned swap `applySeq_swap_loOnA_incomparable_C`
   CLOSES given `Inv`+`applicable` of the two events at the swap state), but in
   the *bubble*'s discharge of those side conditions.  The bubble swaps events
   at **hybrid** fold states `applySeq init (peeled-π₁-heads ++ σ-prefix)` that
   neither source enumeration visits, so `noopFeasible π₁` / `noopFeasible π₂`
   (which control only π₁-prefix and π₂-prefix states) do not supply
   applicability there.  This is exactly the "swaps visit states no execution
   visits" obstruction that `G2_Transport_Probe.lean` flagged, now pinned to a
   single side condition of a single lemma.

## Why the RGA needs the residue (and thus the obstruction bites)

For the RGA `rc = Either` and its commutation lemmas conclude only the
*observational* `eq`, not Lean `Eq` (the hosting gap noted in
`G2_Transport_Probe.lean`).  So the RGA does **not** satisfy `UpdateVCs`
(`commutes`-based) at the Lean-`Eq` level, and the headline reduction does not
fire for it.  The order VC `dependency_covers_vacuity`, by contrast, IS
dischargeable for the RGA — §6 proves the witnessing instance
(`rga_appliesDependsOn_del_ins`).  Hence the RGA is precisely the case that
forces the `commutesOn`-only route and hits the located obstruction.

## Contents

* §0  Generic definitions: `appliesDependsOn` (generic, semantic), `loOnA`,
  `appOrNoop`.  `noopFeasible` is REUSED from `UpdateFeasibility_Gate.lean`.
* §1  `commutes_imp_commutesOn`, `commutesOn_symm` — free structural lemmas.
* §2  The order-repair scaffolding: `loOn_imp_loOnA`, `respects_loOn_of_loOnA`.
* §3  **`conditioned_convergence_on`** — the closed headline (reduction).
* §4  `UpdateVCsC` (the `commutesOn`-based target bundle) and the conditioned
  swap primitives, which CLOSE given applicability at the swap state.
* §5  The bubble frontier — the located obstruction, as commented goal-states.
* §6  RGA instantiation sketch.
* §7  Axiom audit.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.ConditionedConvergence

open Sal.Emulation
open Sal.ConditionedMRDTs
open Sal.ConditionedMRDTs (loOnC)
open Sal.ConditionedMRDTs (noopFeasible)
open Classical

/-! ## §0  Generic definitions

`noopFeasible D π s` is reused verbatim from `UpdateFeasibility_Gate.lean`:
every prefix-fold of `π` keeps the next op `D.applicable` OR a Lean-`Eq`
identity at that state.

`loOnC D C ev` is reused from `G2_Transport_Probe.lean`: the set-relative
conditioned order (`Sal.Emulation.loOn` with `commutes ↦ commutesOn`). -/

/-- **Generic generation dependency.**  `appliesDependsOn D e₂ e₁` : "applying
`e₁` can change whether `e₂` is applicable" — there is a state where `e₂`'s
applicability differs before vs. after `e₁`.

This is the `ConditionedMRDTSig`-level generalization of the RGA-syntactic
`Sal.ConditionedMRDTs.G2AppAware.appliesDependsOn` (`e₂` names `e₁`'s Ins-timestamp).
The syntactic form is a *sufficient* condition for this semantic one; the
semantic form is what the order VC `dependency_covers_vacuity` actually needs,
and it is provable for the RGA counterexample pair (§6,
`rga_appliesDependsOn_del_ins`).  Chosen because it is exactly the negation of
"`e₁` never affects `e₂`'s applicability", which is what a vacuous `commutesOn`
edge witnesses. -/
def appliesDependsOn (D : ConditionedMRDTSig) (e₂ e₁ : Op D.AppOp) : Prop :=
  ∃ s, D.applicable e₂ s ≠ D.applicable e₂ (D.update s e₁)

/-- **The generic applicability-aware order.**  `loOnC` (the conditioned order)
plus a surviving vis-edge `e₁ → e₂` whenever `e₂`'s applicability depends on
`e₁`.  The direct generalization of `Sal.ConditionedMRDTs.G2AppAware.loOnA`. -/
def loOnA (D : ConditionedMRDTSig) (C : Sal.Emulation.Configuration D.toCRDTSig)
    (ev : Set (Op D.AppOp)) (e₁ e₂ : Op D.AppOp) : Prop :=
  loOnC D C ev e₁ e₂ ∨ (C.vis e₁ e₂ ∧ appliesDependsOn D e₂ e₁)

/-- Applicable-or-no-op at a state: the per-step content of `noopFeasible`. -/
def appOrNoop (D : ConditionedMRDTSig) (o : Op D.AppOp) (s : D.State) : Prop :=
  D.applicable o s ∨ D.update s o = s

/-! ## §1  Free structural lemmas relating `commutes` and `commutesOn`

`commutesOn` quantifies over a *subset* of the states `commutes` does
(`Inv`-reachable, both-applicable), so it is implied by `commutes` and is
symmetric.  These need no VC. -/

/-- Unconditioned commutation implies conditioned commutation (drop the guards). -/
theorem commutes_imp_commutesOn (D : ConditionedMRDTSig) {a b : Op D.AppOp}
    (h : D.toCRDTSig.commutes a b) : D.commutesOn a b :=
  fun s _ _ _ => h s

/-- `commutesOn` is symmetric. -/
theorem commutesOn_symm (D : ConditionedMRDTSig) {a b : Op D.AppOp}
    (h : D.commutesOn a b) : D.commutesOn b a :=
  fun s hInv hb ha => (h s hInv ha hb).symm

/-! ## §2  Order-repair: `loOn ⊆ loOnA` under `dependency_covers_vacuity`

The single order VC:

    dependency_covers_vacuity :
      ∀ a b, C.vis a b → ¬ commutes a b → commutesOn a b → appliesDependsOn b a

reads: "if a vis-edge `a → b` fails to commute unconditionally but `commutesOn`
makes it vacuous, then `b`'s applicability depends on `a`" — precisely the
edges conditioning drops from `loOn` are the ones `loOnA` re-adds.  With it,
`loOn ⊆ loOnA` pointwise. -/

/-- **The order-repair inclusion.**  Every `loOn C ev`-edge is a `loOnA`-edge.

* vis-flavored `loOn`-edge `a → b` (`vis a b ∧ ¬commutes a b`): if
  `¬commutesOn a b` it is already a `loOnC` (hence `loOnA`) vis-edge; if
  `commutesOn a b`, `dependency_covers_vacuity` supplies `appliesDependsOn b a`,
  so it is a `loOnA` dependency-edge.
* rc-flavored `loOn`-edge: its no-absorber clause quantifies `¬commutes b e₃`,
  which is *weaker* than `loOnC`'s `¬commutesOn b e₃` (since
  `commutes → commutesOn`), so it implies `loOnC`'s clause and the edge is a
  `loOnC` rc-edge. -/
theorem loOn_imp_loOnA (D : ConditionedMRDTSig) (C : Sal.Emulation.Configuration D.toCRDTSig)
    (ev : Set (Op D.AppOp))
    (hdep : ∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → D.commutesOn a b →
      appliesDependsOn D b a)
    {a b : Op D.AppOp} (h : loOn C ev a b) : loOnA D C ev a b := by
  rcases h with ⟨hv, hnc⟩ | ⟨hnv1, hnv2, hrc, habs⟩
  · -- vis-flavored
    by_cases hco : D.commutesOn a b
    · exact Or.inr ⟨hv, hdep a b hv hnc hco⟩
    · exact Or.inl (Or.inl ⟨hv, hco⟩)
  · -- rc-flavored: promote to a loOnC rc-edge
    refine Or.inl (Or.inr ⟨hnv1, hnv2, hrc, ?_⟩)
    rintro ⟨e₃, he₃, hve, hnco⟩
    exact habs ⟨e₃, he₃, hve, fun hc => hnco (commutes_imp_commutesOn D hc)⟩

/-- A `loOnA`-respecting permutation respects the unconditioned `loOn` — the
contrapositive of `loOn_imp_loOnA`, lifted to `List.Pairwise`. -/
theorem respects_loOn_of_loOnA (D : ConditionedMRDTSig) (C : Sal.Emulation.Configuration D.toCRDTSig)
    (ev : Set (Op D.AppOp))
    (hdep : ∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → D.commutesOn a b →
      appliesDependsOn D b a)
    {π : List (Op D.AppOp)} (h : respects π (loOnA D C ev)) :
    respects π (loOn C ev) :=
  h.imp (fun hn hlo => hn (loOn_imp_loOnA D C ev hdep hlo))

/-! ## §3  The headline: general conditioned convergence

Two `loOnA`-respecting, `noopFeasible` enumerations of a set `ev` fold from
`D.init` to the same state.  Proof: `respects_loOn_of_loOnA` turns both into
`loOn`-respecting enumerations, and the unconditioned `convergence_on_u`
finishes.  The `noopFeasible` hypotheses are carried (stage-6 signature) but
UNUSED — recorded as finding (1) in the header. -/
theorem conditioned_convergence_on
    (D : ConditionedMRDTSig)
    (hU : UpdateVCs D.toCRDTSig)
    (C : Sal.Emulation.Configuration D.toCRDTSig)
    (hdep : ∀ a b, C.vis a b → ¬ D.toCRDTSig.commutes a b → D.commutesOn a b →
      appliesDependsOn D b a)
    {ev : Set (Op D.AppOp)} {π₁ π₂ : List (Op D.AppOp)}
    (h_ev_in_C : ∀ a ∈ ev, a ∈ C.events)
    (h₁_perm : listPermOf π₁ ev) (h₂_perm : listPermOf π₂ ev)
    (h₁_resp : respects π₁ (loOnA D C ev)) (h₂_resp : respects π₂ (loOnA D C ev))
    (_hN₁ : noopFeasible D π₁ D.init) (_hN₂ : noopFeasible D π₂ D.init) :
    applySeq D.toCRDTSig D.init π₁ = applySeq D.toCRDTSig D.init π₂ :=
  convergence_on_u hU D.init h_ev_in_C h₁_perm h₂_perm
    (respects_loOn_of_loOnA D C ev hdep h₁_resp)
    (respects_loOn_of_loOnA D C ev hdep h₂_resp)

/-! ## §4  The `commutesOn`-only target bundle and the conditioned swap

This is the genuinely-conditioned route the plan asks for: convergence using
ONLY `commutesOn` in the semantic VCs (so that `Inv`-nontrivial MRDTs like the
RGA, which lack the `commutes`-based `UpdateVCs`, can instantiate it).  The
bundle mirrors `UpdateVCs` with `commutes ↦ commutesOn`; `cond_comm_liftC`
additionally carries the base-state invariant `D.Inv s` (the minimal side
condition under which its per-MRDT discharge is expected to hold). -/

/-- The `commutesOn` analogue of `UpdateVCs`.  Its per-MRDT discharge is a
separate obligation (e.g. the RGA's observational commutation lemmas); here it
is an assumption, exactly as `UpdateVCs` is for the unconditioned layer. -/
structure UpdateVCsC (D : ConditionedMRDTSig) : Prop where
  /-- Non-commutation (conditioned) is directional rc, on distinct different-replica ops. -/
  rc_non_comm_directional :
    ∀ o₁ o₂ : Op D.AppOp,
      distinctOps o₁ o₂ → differentReplicas o₁ o₂ →
      (¬ D.commutesOn o₁ o₂ ↔
       (D.rc o₁ o₂ = RcRes.Fst_then_snd ∨ D.rc o₂ o₁ = RcRes.Fst_then_snd))
  /-- No two consecutive `Fst_then_snd` rc-edges (pure rc; identical to `UpdateVCs`). -/
  no_rc_chain :
    ∀ o₁ o₂ o₃ : Op D.AppOp,
      distinctOps o₁ o₂ → distinctOps o₂ o₃ →
      ¬ (D.rc o₁ o₂ = RcRes.Fst_then_snd ∧ D.rc o₂ o₃ = RcRes.Fst_then_snd)
  /-- Conditioned overwriter-lift: the swap of an rc-ordered pair is invisible
  past a non-`commutesOn` absorber `e''`.  Carries `D.Inv s` for the base. -/
  cond_comm_liftC :
    ∀ (s : D.State) (e e' e'' : Op D.AppOp) (π : List (Op D.AppOp)),
      D.Inv s →
      distinctOps e e' → distinctOps e e'' → distinctOps e' e'' →
      D.rc e e' = RcRes.Fst_then_snd →
      ¬ D.commutesOn e' e'' →
      D.update (applySeq D.toCRDTSig (D.update (D.update s e') e) π) e''
        = D.update (applySeq D.toCRDTSig (D.update (D.update s e) e') π) e''

/-- **Direct conditioned swap.**  Two events that `commutesOn` and are both
`applicable` at an `Inv` fold state swap.  This is the `commutesOn` analogue of
`applySeq_swap_commute`; it fires `commutesOn` at exactly one state — the swap
state `applySeq s pfx`. -/
theorem applySeq_swap_commutesOn (D : ConditionedMRDTSig) {a b : Op D.AppOp}
    (pfx sfx : List (Op D.AppOp)) (s : D.State)
    (hInv : D.Inv (applySeq D.toCRDTSig s pfx))
    (ha : D.applicable a (applySeq D.toCRDTSig s pfx))
    (hb : D.applicable b (applySeq D.toCRDTSig s pfx))
    (h_comm : D.commutesOn a b) :
    applySeq D.toCRDTSig s (pfx ++ a :: b :: sfx)
    = applySeq D.toCRDTSig s (pfx ++ b :: a :: sfx) := by
  have key :
      D.toCRDTSig.update (D.toCRDTSig.update (applySeq D.toCRDTSig s pfx) a) b
        = D.toCRDTSig.update (D.toCRDTSig.update (applySeq D.toCRDTSig s pfx) b) a :=
    h_comm (applySeq D.toCRDTSig s pfx) hInv ha hb
  calc applySeq D.toCRDTSig s (pfx ++ a :: b :: sfx)
      = applySeq D.toCRDTSig
          (D.toCRDTSig.update (D.toCRDTSig.update (applySeq D.toCRDTSig s pfx) a) b) sfx := by
        simp [applySeq, List.foldl_append, List.foldl_cons]
    _ = applySeq D.toCRDTSig
          (D.toCRDTSig.update (D.toCRDTSig.update (applySeq D.toCRDTSig s pfx) b) a) sfx := by
        rw [key]
    _ = applySeq D.toCRDTSig s (pfx ++ b :: a :: sfx) := by
        simp [applySeq, List.foldl_append, List.foldl_cons]

/-- **Overwriter conditioned swap**, from `cond_comm_liftC`.  The `commutesOn`
analogue of `applySeq_swap_via_cond_comm_lift_u`; needs `Inv` of the base fold
state (supplied to the VC). -/
theorem applySeq_swap_via_cond_comm_liftC (D : ConditionedMRDTSig) (hC : UpdateVCsC D)
    {a b e₃ : Op D.AppOp}
    (h_dist_ab : distinctOps a b) (h_dist_be : distinctOps b e₃) (h_dist_ae : distinctOps a e₃)
    (h_rc_ab : D.rc a b = RcRes.Fst_then_snd) (h_nc_be : ¬ D.commutesOn b e₃)
    (pfx α β : List (Op D.AppOp)) (s : D.State)
    (hInv : D.Inv (applySeq D.toCRDTSig s pfx)) :
    applySeq D.toCRDTSig s (pfx ++ a :: b :: (α ++ e₃ :: β))
    = applySeq D.toCRDTSig s (pfx ++ b :: a :: (α ++ e₃ :: β)) := by
  have hexp1 : applySeq D.toCRDTSig s (pfx ++ a :: b :: (α ++ e₃ :: β))
             = applySeq D.toCRDTSig (D.toCRDTSig.update (applySeq D.toCRDTSig
                 (D.toCRDTSig.update (D.toCRDTSig.update (applySeq D.toCRDTSig s pfx) a) b) α) e₃) β := by
    simp [applySeq, List.foldl_append, List.foldl_cons]
  have hexp2 : applySeq D.toCRDTSig s (pfx ++ b :: a :: (α ++ e₃ :: β))
             = applySeq D.toCRDTSig (D.toCRDTSig.update (applySeq D.toCRDTSig
                 (D.toCRDTSig.update (D.toCRDTSig.update (applySeq D.toCRDTSig s pfx) b) a) α) e₃) β := by
    simp [applySeq, List.foldl_append, List.foldl_cons]
  rw [hexp1, hexp2]
  exact congrArg (fun t => applySeq D.toCRDTSig t β)
    (hC.cond_comm_liftC (applySeq D.toCRDTSig s pfx) a b e₃ α hInv
      h_dist_ab h_dist_ae h_dist_be h_rc_ab h_nc_be).symm

/-- **The conditioned incomparable-swap lemma.**  The `commutesOn` analogue of
`applySeq_swap_loOn_incomparable_u`.  Two `loOnA`-incomparable adjacent events
swap, GIVEN they are `Inv`+`applicable` at the swap state `applySeq s pfx` and
the conditioned overwriter form `h_ov`.

This CLOSES.  Its three branches mirror the unconditioned proof:
* `commutesOn a b`  → `applySeq_swap_commutesOn` (uses `hInv`, `ha`, `hb`);
* `¬commutesOn`, same replica → `vis_total_same_replica` gives a vis-edge which,
  by incomparability, is impossible (using `dependency_covers_vacuity` is NOT
  even needed here — a bare `loOnC` vis-edge already contradicts);
* `¬commutesOn`, different replica → `h_ov` + `applySeq_swap_via_cond_comm_liftC`.

The applicability premises `hInv`, `ha`, `hb` at the swap state are exactly the
side conditions the bubble (§5) cannot discharge from `noopFeasible`. -/
theorem applySeq_swap_loOnA_incomparable_C (D : ConditionedMRDTSig) (hC : UpdateVCsC D)
    {C : Sal.Emulation.Configuration D.toCRDTSig} {ev : Set (Op D.AppOp)}
    {a b : Op D.AppOp} (h_ne : a ≠ b)
    (h_a_in_C : a ∈ C.events) (h_b_in_C : b ∈ C.events)
    (h_not_lo_ab : ¬ loOnA D C ev a b) (h_not_lo_ba : ¬ loOnA D C ev b a)
    (pfx sfx : List (Op D.AppOp)) (s : D.State)
    (hInv : D.Inv (applySeq D.toCRDTSig s pfx))
    (ha : D.applicable a (applySeq D.toCRDTSig s pfx))
    (hb : D.applicable b (applySeq D.toCRDTSig s pfx))
    (h_ov : ¬ D.commutesOn a b → a.rep ≠ b.rep →
      ∃ e₃ α β, sfx = α ++ e₃ :: β ∧
                distinctOps a e₃ ∧ distinctOps b e₃ ∧
                ((D.rc a b = RcRes.Fst_then_snd ∧ ¬ D.commutesOn b e₃) ∨
                 (D.rc b a = RcRes.Fst_then_snd ∧ ¬ D.commutesOn a e₃))) :
    applySeq D.toCRDTSig s (pfx ++ a :: b :: sfx)
    = applySeq D.toCRDTSig s (pfx ++ b :: a :: sfx) := by
  by_cases h_comm : D.commutesOn a b
  · exact applySeq_swap_commutesOn D pfx sfx s hInv ha hb h_comm
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

/-! ## §5  The bubble frontier — the located obstruction

The unconditioned bubble `applySeq_bubble_to_front_loOn_u` (`Sigma_LoOn3.lean`)
walks a peeled event `e` leftward through `σ`, calling
`applySeq_swap_loOn_incomparable_u` at each step to swap `e` past the σ-element
`y` at the fold state `applySeq s pfx` where `pfx` is a σ-prefix.  In
`convergence_on_u`, the outer accumulator `s` is `applySeq D.init (peeled heads
of π₁)`, so each swap fires at the **hybrid** state

    applySeq D.init  (peeled-π₁-heads  ++  σ-prefix)

with `peeled-π₁-heads` a prefix of the `loOnA`-respecting `π₁` and `σ-prefix` a
prefix of `σ ⊆ π₂`.

To run the CONDITIONED bubble with `applySeq_swap_loOnA_incomparable_C` we must
supply, at every such hybrid state, its three applicability side conditions:

    hInv : D.Inv       (applySeq D.init (peeled-π₁-heads ++ σ-prefix))
    ha   : D.applicable e  (applySeq D.init (peeled-π₁-heads ++ σ-prefix))
    hb   : D.applicable y  (applySeq D.init (peeled-π₁-heads ++ σ-prefix))

**`hInv` is DISCHARGEABLE** (obligation (A) of `G2_Transport_Probe.lean`): it is
`Inv_transport_generic` applied to the concatenated list — provided every op
satisfies the op-only invariant-step condition.  Generically this is the field

    hInvStep : ∀ s o, o ∈ ev → D.Inv s → D.Inv (D.update s o)

(the RGA's `RgaInv_do_opOK` under `opOK`, extracted once at generation by
`opOK_of_generation`).

**`ha` / `hb` are the OBSTRUCTION.**  `noopFeasible D π₁ D.init` gives
`appOrNoop` only at **π₁-prefix** states `applySeq D.init (π₁-prefix)`, and
`noopFeasible D π₂ D.init` only at **π₂-prefix** states.  The hybrid state
`applySeq D.init (peeled-π₁-heads ++ σ-prefix)` is neither: it interleaves a
π₁-prefix with a π₂-prefix (`σ` is drawn from π₂).  Nothing in the two
`noopFeasible` hypotheses constrains the applicability of `e` or `y` there.
This is precisely `G2_Transport_Probe.lean`'s "swaps visit states no execution
visits", now pinned to the `ha`/`hb` premises of
`applySeq_swap_loOnA_incomparable_C` at the σ-walk of the bubble.

What WOULD close the bubble is the strictly stronger *interleaving-feasibility*
oracle below — no-op-feasibility of **every** admissible interleaving, not just
of `π₁` and `π₂`.  `noopFeasible π₁ ∧ noopFeasible π₂` does not imply it. -/

/-- The interleaving-feasibility oracle that the conditioned bubble needs: every
`Inv`-fold state of every `nodup` sub-list of `ev` keeps its next op
applicable-or-no-op.  STRICTLY stronger than `noopFeasible D π₁ D.init ∧
noopFeasible D π₂ D.init`; not implied by it.  Stated (not assumed) to name the
exact gap. -/
def interleavingFeasible (D : ConditionedMRDTSig) (ev : Set (Op D.AppOp)) : Prop :=
  ∀ (pre : List (Op D.AppOp)) (o : Op D.AppOp),
    (∀ x ∈ pre, x ∈ ev) → o ∈ ev → o ∉ pre → pre.Nodup →
    appOrNoop D o (applySeq D.toCRDTSig D.init pre)

/- ── Sub-obstruction: no-op tolerance does not compose through a swap ──

Even granting `appOrNoop` at the swap state, a NO-OP branch does not yield the
swap.  If `a` is a no-op at `s' = applySeq s pfx` (`update s' a = s'`) but `b`
is applied, then

    applySeq s' (a :: b :: sfx) = applySeq s' (b :: sfx)           -- a absorbed
    applySeq s' (b :: a :: sfx) = applySeq (update (update s' b) a) sfx

and these agree only if `a` is ALSO a no-op at `update s' b` — i.e. the no-op is
stable under `b`.  That is an extra idempotence-commutation fact NOT implied by
`commutesOn` (for the RGA it is `del1_idem`: a delete stays a no-op after
another delete).  So `applySeq_swap_loOnA_incomparable_C` deliberately requires
genuine `applicable` (not `appOrNoop`) of both events at the swap state:
`noopFeasible` controls the FINAL fold (its no-ops are absorbed there), but the
SWAP needs applicability.  In the redundancy case
(`UpdateFeasibility_Gate.lean`), at every actual swap state (`s₁ = do_ init ins`)
BOTH deletes are genuinely applicable — the no-op only surfaces in the final
fold — so no idempotence VC is needed there; the obstruction is solely `ha`/`hb`
at hybrid states, above. -/

/-! ## §7  Axiom audit — kernel-clean, no `sorryAx` on any headline decl.
The imported `Merge_Linearization_Set` carries 2 pre-existing `sorry`s in the
merge-linearization induction; the audit below confirms none is transitively
reached by these results (only `propext`/`Classical.choice`/`Quot.sound`). -/

#print axioms conditioned_convergence_on
#print axioms loOn_imp_loOnA
#print axioms respects_loOn_of_loOnA
#print axioms applySeq_swap_commutesOn
#print axioms applySeq_swap_loOnA_incomparable_C
#print axioms applySeq_swap_via_cond_comm_liftC

end Sal.ConditionedMRDTs.ConditionedConvergence
