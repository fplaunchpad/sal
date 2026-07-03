# The conditioned metatheory: plan (OQ3 route reunification × OQ4 feasible update layer)

*2026-07-03. Companion to the T-journal (`MRDT_METATHEORY_DRAFT.md`). Umbrella framing:
OQ3, OQ4 (and OQ6's covering invariant) are one question — **what may the contract
assume, and who proves it?** The contract becomes parameterized by
`(Inv, applicable, 𝒞)`: a state invariant, a generation-time guard (both already in
`ConditionedMRDTSig`, `MRDTSig.lean:63`), and a closure strength. The §8 class map of the
note becomes a two-axis table. Two go/no-go gates run first; everything else is staged
behind them.*

## Gate G1 (OQ3): does a closure-preserving peel exist? — **REFUTED on paper**

The naive reunification route — re-run the `JoinLemma3` induction with full-closure
hypotheses (`JoinLemma3F`, `VC_Set.lean:191`) — needs to peel an event `e` from a fully
causally closed `U` such that

1. `e` is `loOn(U)`-maximal (it may be placed last), and
2. `e` is vis-maximal in `U` (so `U ∖ {e}` stays *fully* closed — closure is about
   vis-predecessors, so the peeled event must have **no** vis-successors, commuting or
   not; `loOn`-maximality only excludes the non-commuting ones).

**Counterexample (4 events, 2-key add-wins skeleton).** Keys `x, y`; cross-key ops
commute; per key, `rem ≁ add` and `rem →rc add`. Replica `p` runs `A_y` then `R_x`;
replica `q` runs `A_x` then `R_y`; no communication; the final merge's version has
`U = {A_y, R_x, A_x, R_y}` (LCA `v₀`; fully causally closed).

- vis edges: `A_y → R_x` (program order at `p`), `A_x → R_y` (at `q`).
- `loOn(U)` rc-edges: `R_x → A_x` (concurrent, key `x`; `A_x`'s only vis-successor
  `R_y` **commutes** with it — cross-key — so no absorber, edge survives). Symmetrically
  `R_y → A_y`.
- No vis∧¬commutes lo-edges (`A_y ⇌ R_x`, `A_x ⇌ R_y`, cross-key).

The union graph contains the cycle

```
A_y →vis R_x →rc A_x →vis R_y →rc A_y
```

so: `loOn(U)`-maximal events = `{A_x, A_y}`; vis-maximal events = `{R_x, R_y}`;
**intersection empty**. No single-event peel preserves full closure. (The weak route is
untouched: peeling `A_x` keeps both sides `¬commutes`-closed — this configuration is
handled by `JoinLemma3` today. The obstruction is only against the *strengthened*
closure.)

**Consequences.**
- OQ3's "we expect, routine" in the note is wrong as stated; erratum after
  mechanization.
- Reunification must change the *induction*, not just the hypotheses. Candidate
  redesigns, in order of preference:
  - **(a) Block peel**: peel a maximal same-replica suffix (or a `vis`-closed
    antichain-suffix) instead of one event; the block's removal preserves full closure
    by construction; the delta laws must then redistribute a *block* delta —
    plausibly what `redistribute`'s three-component form already supports.
  - **(b) Wider induction class**: induct over "fully-closed set minus a
    `loOn`-downset" so the IH applies to `U ∖ {e}` even when it is not fully closed.
  - **(c) Disjunctive contract** (minimum viable): a typeclass with two instances —
    VC-route (weak closure) and direct-`JoinLemma3F` (EWFlag-style) — one bridge to
    adequacy. Packaging, not reunification; fallback if (a)/(b) stall.

**Mechanization plan (task #1)**: `Development/Reunification_Peel_Obstruction.lean` —
concrete 2-key skeleton, the four events, `vis` as the two program-order pairs; prove
full closure of `U`, the two surviving rc-edges, the cycle, and
`¬∃ e ∈ U, loOnMaximal e ∧ visMaximal e`. Kernel-checked kill-test, style of
`Impossibility.lean`.

## Gate G2 (OQ4): permutation-transport of the RGA invariant — **verdict in** (`G2_Transport_Probe.lean`, kernel-clean)

**(A) Inv-transport: PROVABLE, unconditionally, decoupled from (B).** The load-bearing
content of `Inv_doIns`/`Inv_doDel` is order-stable and op-only (`Ins` needs `t ≠ 0`, `Del`
needs target present at generation) — `RgaInv` transports along every permutation and
mid-bubble hybrid (`obligation_A_RGA`).

**(B) the NAIVE conditioned convergence is FALSE** (`G2_conditioned_convergence_refuted`,
kernel-clean). Swapping `commutes ↦ commutesOn` inside the linearization order, keeping all
other convergence hypotheses, is refuted by a 2-event RGA execution: `insOpE`(node 1) then
`delOpE`(node 1). They are *never jointly applicable* (`fresh_ts` wants node 1 absent,
`accurate` wants it present), so `commutesOn` holds **vacuously**, the conditioned `lo` drops
the `ins→del` edge, and both `[ins,del]` and `[del,ins]` respect it while folding to
different states. The unconditioned `loOn` keeps the edge (`binary_loOn_keeps_edge`) — the
substitution alone introduces the failure. Strengthening `Inv` cannot repair it: conditioning
is *antitone* (a smaller `commutesOn` domain removes edges), and the bad enumeration's every
state already satisfies `RgaInv` (`bad_enumeration_stays_in_Inv`) — **route (iii) is dead.**

**But this is a yellow gate, not red.** The refuted statement quantifies over *all*
loOnC-respecting enumerations, including `[del,ins]` — which folds `del` at `init`, where
`del` is **not applicable** (the docstring flags this). So the refutation kills the *naive
transcription*, not the feasible-update-layer program. Two candidate repairs, and the real
OQ4 is to pick between them (task #7):
- **(a) applicability-aware `lo`**: a vis-edge `e₁→e₂` survives whenever `e₂`'s applicability
  *depends on* `e₁` (generation dependency; RGA-syntactic: `e₂` names `e₁`'s timestamp as
  Del-target / Ins-anchor / path member), not only when `¬commutesOn`.
- **(b) applicability-restricted convergence**: quantify convergence over enumerations whose
  every prefix keeps the next op applicable — `[del,ins]` is then excluded as an invalid fold,
  not by `lo`.

Are (a) and (b) equivalent? Likely closely related; determining it and re-probing the chosen
form is the gate's live continuation. Caveat: `Ccex` is hand-built (Step-reachability noted,
not mechanized) — valid against `convergence_on_u` as stated (arbitrary config + structural
hypotheses), but a reachability-restricted convergence would need `Ccex` shown reachable
(evidently is: single replica, ins then del).

### (superseded framing) Gate G2 as originally posed

The feasible update layer needs: every intermediate state of every `loOn`-respecting
enumeration of a reachable event set satisfies `Inv` (so `commutesOn`
(`MRDTSig.lean:73`) fires at every ⚑ swap site of the convergence induction).
Building blocks already mechanized on the data-type side
(`RGA_Reachability_Invariant.lean`): `Inv_doIns`/`Inv_doDel`, `Inv_merge` under
`id_mono l`, `id_mono` reachable under monotone allocation. The gate: state transport
against `Sigma_LoOn3` and check whether the swap steps (cond-comm bubbling) stay inside
`Inv` — the risk is swaps visiting states no *execution* visits.

Orthogonal to G1 (order-theoretic vs semantic); attack in parallel.

## Stages (behind the gates)

1. **`JoinLemma3C 𝒞`** — DONE (`JoinLemma3C.lean`, task #2). Closure-indexed Join Lemma,
   both instances definitional. Block peels (redesign (a)) **kernel-refuted at every
   granularity** (`no_proper_back_block`/`no_proper_front_block`). Order-theoretic half of
   route (b) built (`AlmostClosed`, peel-stability, peel-existence).
2. **Route (b) state side** — DONE (`JoinLemma3F_Of_AlmostClosed.lean`, task #6),
   **obstructed, not closed**. Findings, kernel-checked:
   - `AlmostClosed` is a *strengthening* of weak closure (`weakClosure_of_almostClosed`), so
     the class alone is useless for reunification — `JoinLemma3A` follows from `JoinLemma3`
     for free and does not help EWFlag. Only *weakening* the VCs helps: `CDVC3A` /
     `FeasibleDeltaVCs3A` (⊂ weakClosure quantifiers, strictly weaker, existing discharges
     port).
   - The two-sided peel over a *common* `U` is fully mechanized (`CommonU.peel_exists`) — the
     G1 kill-test does **not** obstruct the peel. The obstruction **migrated to
     initialization (P0)**: `JoinLemma3F` gives only *individually* fully-closed sides, which
     do **not** admit a common `U` (`killTest_no_common_U`) — the surviving cross-side rc-edge
     `R_x →loOn A_x` leaves the complement not-`loOn(U)`-upward-closed. P0′: independent-witness
     maximality (`loOn(evᵢ)`) ≠ union maximality (`loOn(ev₁∪ev₂)`). P5 (orthogonal): the CD
     `B`-argument `σ(↓e∖e)` is only weakly closed, needs re-founding on the *full* downset
     `↓⁺e` (changes `CDVC3A`).
   - **Recommendation:** route (c) *disjunctive contract* — needs no new mathematics
     (`JoinLemma3C` already unifies the two statements); or carry `CommonU` as data in the
     Join hypothesis and re-base the downset on `↓⁺e`.
3. **OQ4 design fork** — DONE (`G2_Applicability_Aware.lean`, task #7). Verdict, kernel-checked:
   **(b) applicability-restricted convergence is strictly more general than (a)
   applicability-aware `lo`** (`separating_inequivalence`: 3 events, two concurrent deletes —
   the missed constraint is a *negative/anti-dependency* between the deletes that a positive
   creation-reference relation cannot express). Adopt (b) as the *definition* of feasibility;
   (a) is a decidable per-MRDT sufficient condition where applicability is positive
   create-before-use. **Deeper surprise (open):** for genuinely reachable versions with
   *redundant concurrent ops* (two concurrent deletes of one node), **no** enumeration is
   `applicabilityValid` — (b)'s strict "applicable at every prefix" is unsatisfiable — so the
   real feasibility notion must tolerate idempotent/absorbed re-application ("applicable OR
   no-op here"). This is the refined OQ4.
4. **Framework spine (route c)** — DONE (`ConditionedContract.lean`, task #8),
   **kernel-checked, "no new mathematics" confirmed.** `ra_linearizable3_of_joinC 𝒞`:
   store versions are fully causally closed, so `JoinLemma3C D 𝒞` applies for any `𝒞` that
   full closure implies; both existing bridges factor through it verbatim
   (`ra_linearizable3_of_join_viaC`, `ra_linearizable3_of_joinF_viaC`). Contract bundle
   `ConditionedContract` + smart constructors `ofVCs`/`ofJoinF`; production instances routed
   through: OR-set at `(weak,⊤)` (`ORSet_adequate_viaContract`), EWFlag at `(full,⊤)`
   (`EWFlag_adequate_viaContract`). One honest correction to the plan's phrasing: "fully-closed
   ⇒ 𝒞-closed for arbitrary 𝒞" is FALSE — it holds exactly when `fullClosure ⟹ 𝒞` (a
   side-condition `closure_below_full`); weak and full both satisfy it, so it costs nothing at
   the corners. Class map: `(weak,⊤)` = all set-shaped + counters + RGA(tombstone) + Peritext;
   `(full,⊤)` = EWFlag; the `Inv`-nontrivial column is empty (the update-layer hole).
5. **Update-layer feasibility notion** — GATE PASSED (`UpdateFeasibility_Gate.lean`, task #4),
   kernel-checked. The correct notion is **applicability-aware order `loOnA` + no-op-feasible
   enumeration** (each step applicable OR identity) — NOT task #7's strict `applicabilityValid`.
   The two repairs are complementary: the order excludes dependency-violating replays that mere
   no-op tolerance re-admits (breaks convergence); no-op tolerance admits harmless redundant ops
   that strict applicability rejects (breaks satisfiability). Verified convergent-and-satisfiable
   on both the dependency case (ins/del, `dependency_case_converges`) and the redundancy case
   (concurrent deletes, `redundancy_case_converges_and_satisfiable`), where each single repair
   fails one (`plain_loOnC_noopFeasible_diverges`, `no_applicabilityValid_enum`). Sub-finding:
   RGA `del`@init is a genuine no-op (`del_at_init_noop`, `rfl`, axiom-free), so `noopFeasible`
   is well-defined. Caveat: the redundancy case's concurrency is proved config-generally (all ops
   rid 0 can't be genuinely concurrent in a well-formed single-rid config), reusing task #7's
   config-general reductions — the order-theoretic content holds, but a concrete two-replica
   reachable config is not constructed.
6. **General conditioned convergence** — DONE (`ConditionedConvergence.lean`, task #9),
   **order-half closed, RGA obstruction localized.** The problem factors cleanly:
   - **Order half (solved):** `conditioned_convergence_on` (kernel-clean) reduces conditioned
     convergence to the *unconditioned* `convergence_on_u`, via a SINGLE order VC
     `dependency_covers_vacuity` (`vis a b → ¬commutes a b → commutesOn a b → appliesDependsOn b a`)
     and the inclusion `loOn ⊆ loOnA`. A single order VC repairs *all* the vacuously-dropped
     edges. Finding: `noopFeasible` is orthogonal to convergence under this route (it is for
     *satisfiability*), and the reduction consumes the *unconditioned* `UpdateVCs`.
   - **Semantic half (RGA, one located obstruction):** the RGA has no unconditioned `UpdateVCs`
     (rc = Either; commutation is observational `eq`, not Lean `Eq` — the hosting gap), so it
     forces the `commutesOn`-only route. There the *swap* closes (`applySeq_swap_loOnA_incomparable_C`,
     all branches), but the *bubble* cannot discharge the swap's applicability premises
     (`applicable a`, `applicable b`) at the HYBRID interleaved states of the σ-walk —
     `noopFeasible π₁`/`π₂` control only their own prefixes, not the interleaving. This is G2's
     "swaps visit states no execution visits," now pinned to the `ha`/`hb` premises of ONE lemma.
     The named closer: an `interleavingFeasible` oracle (a per-MRDT obligation).
7. **REMAINING (the last gate):** does `interleavingFeasible` HOLD for the RGA (→ hosting closes,
   bounded re-mechanization) or is it itself false/hard (→ the RGA needs a bubble that only
   produces execution-reachable interleavings, a genuine architecture change)? This is the final
   fork; the research question is now localized to it.

## Net verdict of the investigation

Both open questions' *obvious* routes are kernel-refuted, and each leaves one precise design
choice:
- **OQ3 reunification:** (a) block-peel dead, (b) wider-induction obstructed at initialization
  → **route (c) disjunctive contract** is the low-risk path (no new math), OR the CommonU-as-
  data / ↓⁺e re-founding is the ambitious one.
- **OQ4 feasible update layer:** naive conditioning dead, (b)-feasibility is the right frame
  but must be refined to **applicable-or-no-op** to cover reachable redundant-concurrent
  versions.
Neither is a completionist grind; both are now design decisions for the researcher.

## Dependency order

Update-layer conditioning is the deeper change (it re-founds convergence, which
everything consumes): fix its *interface* first even though its discharge (G2) runs in
parallel with G1's redesign work. The closure-indexed merge layer re-bases on it.

## Risk register

- G1 redesign (a): `redistribute` may not iterate cleanly over blocks — check on the
  counter first (inclusion–exclusion should be block-agnostic).
- G2: cond-comm swaps may exit `Inv` even when all execution states satisfy it; if so,
  `Inv` must be weakened to a swap-closed envelope (find it, or prove none exists —
  either is a finding).
- Scope control: if both gates go badly, land (c) — the disjunctive contract — and
  publish the two counterexamples as the honest boundary of the theory.
