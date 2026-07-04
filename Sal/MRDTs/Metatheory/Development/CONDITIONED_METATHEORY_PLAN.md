# The conditioned metatheory: plan (OQ3 route reunification × OQ4 feasible update layer)

*2026-07-03. Companion to the T-journal (`MRDT_METATHEORY_DRAFT.md`). Umbrella framing:
OQ3, OQ4 (and OQ6's covering invariant) are one question — **what may the contract
assume, and who proves it?** The contract becomes parameterized by
`(Inv, applicable, 𝒞)`: a state invariant, a generation-time guard (both already in
`ConditionedMRDTSig`, `MRDTSig.lean:63`), and a closure strength. The §8 class map of the
note becomes a two-axis table. Two go/no-go gates run first; everything else is staged
behind them.*

## Cross-cutting insights (2026-07-03, from analyzing the whole arc)

Five patterns the individual gates did not show; the first is the paper-shaped reframe.

1. **The Neem methodology systematically over-specifies; every correction demotes an
   obligation to the weakest thing the soundness proof consumes.** One thesis, not five
   repairs: set-relative order → canonical states → closure-indexed contract →
   `loOnA + noopFeasible` → `interleavingFeasible` sufficient-not-necessary. Cause: VC
   catalogues are written *forward* (from the data type) instead of *backward* (from the
   proof). The right discipline: extract the weakest local condition the global argument
   consumes, then refute the natural stronger candidates (the counterexamples ARE the
   minimality proofs). Reframes the note from "8 corrected VCs" to "a method for finding
   minimal VC sets." No new mechanization — a framing of what is already proved.
2. **Convergence and satisfiability are separate concerns.** Mechanized: `noopFeasible` is
   orthogonal to convergence (it is for *satisfiability*). Strict `applicabilityValid` broke
   by bundling them. The *order* (`loOnA`) forces convergence; *no-op tolerance* guarantees a
   witness exists. Two independent obligations.
3. **`id_mono` is the RGA's single unifying invariant** (grounded: `RGA_Reachability_Invariant.lean:232`,
   and the merge proof already uses its strict-decrease for climb termination). The update-side
   general swap lemma (milestone 1b) and the merge-side `wf`-preservation are plausibly the SAME
   structural fact: under `id_mono` the ancestor chain is strictly-decreasing/well-founded, so a
   `Del` can only shorten it, never relocate laterally — the path above a climb-target stays real
   regardless of accumulated deletes. Being tested in task #13.
4. **The class map is 3-dimensional** (delta-class × closure-strength × state-invariant), and
   most cells are empty. Inhabited: (group/lattice, weak, ⊤), (feasible, full, ⊤); the entire
   Inv≠⊤ plane holds only the RGA-in-progress. A structure theorem (which cells inhabited / provably
   empty) would tell a designer what tier their merge shape forces. Speculative, cheap to sketch.
5. **Both defeaters share a cycle shape** — the §3.3 defeater and the OQ3 peel-obstruction are both
   4-event configs with an alternating `A→R→A→R` cycle in vis∪rc that set-relativity breaks.
   Conjecture: a config defeats bottom-up peeling iff its config-level vis∪rc graph has a cycle
   through non-commuting events (`no-rc-chain` forbids this *within* a version's `lo^E`, not across
   the config). Would characterize exactly when the closure-indexed contract is NEEDED vs when plain
   bottom-up suffices — two ad-hoc counterexamples → one boundary theorem.

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
7. **Final gate — ANSWERED** (`RGA_Rehoming_Gate.lean`, task #10, kernel-clean). Verdict:
   **`interleavingFeasible` is FALSE for the RGA, but the RGA converges anyway** — the oracle is
   sufficient, not necessary. Chain: a concurrent `Del` rehomes nodes and stales a concurrent
   `Ins`'s path (`rehoming_stales_path`); the staled `Ins` is neither applicable nor a no-op
   (`staled_ins_not_noop`, `staled_ins_not_applicable`) — it re-anchors at the nearest live
   ancestor, i.e. *exactly* where `Del` rehomed. So `not_interleavingFeasible_RGA`. **But**
   `orders_converge` (an instance of the RGA's proved `insdel_comm`) and
   `full_enumerations_converge` show the two `loOnA`-admissible linearizations agree regardless
   (`verdict_oracle_false_but_converges`). The obstruction is NOT unreachability
   (`[insA,insB,delA]` is a legitimate causal prefix) — it is that the §5 bubble demands
   *pointwise applicability at hybrid fold states*, while the RGA only supplies *semantic
   commutation* (`insdel_comm`) at the both-applicable common causal base.
8. **The genuine research frontier (open):** re-architect the peel bubble to fire each swap at
   the semantic-commutation state (the transposed pair's last common causally-prior fold, where
   both are applicable), consuming `insdel_comm` directly — NOT at a hybrid state that already
   staled one event. A "reachability-restricted bubble" in the *swap-state* sense. This closes
   the tombstone-free RGA (it converges); the work is bounded but non-trivial. `interleavingFeasible`
   as stated in stage 6 is simply too strong for a path-carrying / rehoming CRDT.

## Bubble re-architecture — SCOPE (stage 8 detail)

**The resource.** The RGA proves `commutes_with'` (`RGA_Tombstone_Free_MRDT.lean:331`):
`∀ s, contains s 0 = false → accurate o1 s → accurate o2 s → fresh_ts o1 s → fresh_ts o2 s → eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)`
— a **∀-state** commutation, but gated on *both* ops `accurate` (+ `fresh`) at `s`, and up to
observational `eq` (not Lean `Eq`). Instances `insins_comm`/`insdel_comm`/`deldel_comm` proved.
This VC, and only this, is what the new bubble may consume.

**Decisive sub-question — GATE FIRST (cheap, ~1 pass).** The generic bubble swaps an adjacent
`loOnA`-incomparable pair `(a,b)` at the fold state `σ` they sit at; `commutes_with'` discharges
it iff both are `accurate` at σ. So: **does `do_ (do_ σ a) b = do_ (do_ σ b) a` hold at *staled* σ
(one of a,b inaccurate), or only at both-accurate σ?**
- **∀-state (holds even staled):** EASY — RGA proves a stronger unconditioned swap VC, drop the
  applicability premise from `applySeq_swap_loOnA_incomparable_C`, existing generic bubble closes
  unchanged (~days). Unlikely (`commutes_with'` is gated precisely because unconditioned failed),
  but check.
- **Accurate-only (likely):** RGA convergence does not decompose into pointwise swaps at arbitrary
  states — `full_enumerations_converge` holds *globally* (endpoints agree via re-anchoring) without
  every intermediate swap being valid. Re-architecture needed; two routes.

**Route A — base-anchored generic bubble.** Restructure `applySeq_bubble_to_front_loOn` so each
swap fires at the pair's *common causal base* (fold of shared `loOnA`-predecessors, both `accurate`
by construction), then transports up. Generic. Risk: intervening events between base and pair break
the "prefix = base" alignment; the transport step may itself need `commutes_with'` at staled states
— regressing to the same obstruction. Weeks; genuine non-closure risk.

**Route B — convergence as a conditioned VC (RECOMMENDED).** Make convergence a bundle field
`ConvergenceVC` (all `loOnA`-respecting `noopFeasible` enumerations of a backward-closed set fold to
`eq` states). Flat/unconditioned types discharge it via the existing bubble (one wrapper theorem
`UpdateVCs ⟹ ConvergenceVC`). The RGA discharges it *directly* by a **global normal-form argument**:
every `loOnA`-respecting enumeration reduces to the timestamp-sorted (fully-`accurate`) canonical
enumeration by base-justified swaps; the canonical one is unique. Mirrors the closure-indexed
contract's philosophy and the EWFlag bespoke-`JoinLemma3F` precedent; `full_enumerations_converge`
is the 4-event proof-of-concept. Framework change ~days; RGA normal-form discharge ~1–2 weeks, and
it stays inside the RGA's own `accurate` states where `commutes_with'` fires.

**MILESTONE 1 VERDICT (done, kernel-checked): nuanced ROUTE A selected.** Two gates:
- `RGA_SwapAtStaled_Gate.lean` (empty-path, degenerate — collapses to root): swap holds, but
  proved a FAILURE when the swapped-in op `b` is inaccurate (`staled_swap_would_fail_if_b_inaccurate`)
  ⇒ the `b`-accurate premise is *necessary*.
- `RGA_SwapAtStaled_NonEmptyPath_Gate.lean` (the real case): `insE = Ins 40 [2,1] 3`, anchor n3
  deleted, `climb_target_moves` (3→2 — genuine state-dependent re-anchoring). With `b` accurate
  and adversarial (`bDel` deletes the climb-target n2), the swap HOLDS (`swap_delN2_holds`) — the
  doubly-deleted chain's eager rehoming exactly compensates the extra climb hop. So the `b`-accurate
  premise is *sufficient* even in the hardest re-anchoring case.
- **Structural mechanism (why, not just that):** the anchor is the HEAD of `resolve`'s list, so an
  `Ins`'s climb short-circuits at its still-live anchor; a single delete that kills the anchor
  cannot also rehome the anchor's own ancestors, so the path *above* the climb-target stays real
  and compensation is exact.
- **Verdict:** the staled event need NOT be accurate; the swap VC needs only the *swapped-in* op
  accurate. So drop the staled-event applicability premise from
  `applySeq_swap_loOnA_incomparable_C` and use the existing generic bubble — **Route A (nuanced)**,
  not Route B.
- **Residual (evidence, not universal proof):** (i) the general `∀ staled-a, accurate-b ⟹ swap`
  lemma is unproven — the structural argument must become an induction on `resolve`/paths; (ii)
  σ_staled tested is a SINGLE delete; a σ with MULTIPLE accumulated concurrent deletes staling
  a's path above the climb-target is untested and is where the single-delete structural argument
  does not obviously extend — check it inside the general lemma. This is the real remaining work.

**Milestones (now Route A):**
1. GATE the staled-swap sub-question — DONE (both files above; verdict nuanced Route A).
1b. General swap VC — DONE (`RGA_GeneralSwap.lean`, task #13, kernel-clean). Result in two parts:
   - **The VC as I stated it is FALSE** (`naive_general_swap_false`): `id_mono s → wf s →
     accurate b s → swap`, ∀ a, fails — counterexample at `init`, `a = Ins 40 [7] 3` whose
     recorded path names `b`'s fresh id 7. `id_mono` constrains the *state* but NOT the *recorded
     path* the op carries; the failure is a fresh-id reference. **This refutes insight 3's "id_mono
     tames it" — id_mono is necessary-ish but not the lever.**
   - **With the right conditioning it CLOSES**, ∀ op-combo, ∀ reachable (incl. multi-delete-staled)
     s (`general_swap`): the levers are `Faithful a s` (path-faithfulness — strictly weaker than
     `accurate`, `faithful_of_accurate`; survives delete-rehoming, which is its design) + `NoFreshClash a b`
     (b's fresh id ∉ a's recorded path — the causal-freshness a real execution supplies, exactly what
     the counterexample violates). All four combos proved; **Del/Del closed** (the flagged hard case)
     via a one-sided `collapse`. `resolve_mono_under_delete` proved. Multi-delete residual settled
     (`multidelete_swap_crosscheck`, 2-delete chain).
   - **Refutes the "update-swap = merge-wf same fact" conjecture (insight 3):** different levers —
     merge-wf uses id_mono as a *fuel bound* for `climb`; update-swap uses *path faithfulness*
     (`resolve` walks a finite recorded list, terminates free); id_mono is used update-side ONLY in
     Del/Del, ONLY for acyclicity. Cousins, not the same fact.
2. Framework: add `ConvergenceVC` field; prove `UpdateVCs ⟹ ConvergenceVC`; re-point
   `conditioned_convergence_on` consumers to it; the 9 discharges still compile via the wrapper.
   NOW the enabling swap lemma exists (`general_swap`): wire it into
   `applySeq_swap_loOnA_incomparable_C`, replacing `accurate a` by `Faithful a` and dropping the
   staled-event applicability premise. Downstream obligation this exposes (the real M2 work):
   **`Faithful a` and `NoFreshClash a b` must thread through the σ-walk** — `Faithful` is a
   reachability property preserved along `loOnA`-respecting folds (its delete-rehoming-stability is
   why it should, where the too-strong `interleavingFeasible` did not), and concurrent events never
   fresh-clash (causal freshness).
3. RGA discharge `RGA_ConvergenceVC` by normal-form reduction (`insins/insdel/deldel_comm`). Crux:
   the canonicalizing swaps each land at a both-`accurate` state — Route A's alignment risk, but
   now with `id_mono` + rehoming determinism available to close it concretely.
4. Wire RGA → `ConditionedContract` → RA-linearizability (the `(·, RgaInv)` cell).

## M2 wiring — DONE, RGA does NOT yet host; frontier precisely mapped (`RGA_BubbleWiring.lean`, task #14, kernel-clean)

Plumbing closed; then M2 surfaced a **verified wall** and refuted two sub-conjectures. Three
obligations remain for RGA hosting, all precisely located:

- **Plumbing (CLOSED):** `SwapWitness` abstraction + `applySeq_swap_loOnA_incomparable_C'` — the
  generic incomparable-swap with the staled-event applicability premise DROPPED (drops both
  `applicable a` and `applicable b`; keeps `hInv` for the rc-overwriter branch). The bubble can now
  consume a `SwapWitness` instead of pointwise applicability.
- **(A) eq-vs-Eq — OVERSTATED (2026-07-04, KC challenge; walked back).** The M2 agent's "provable
  wall" conflated two claims: `eq_strictly_weaker_than_Eq` (kernel-true — `eq ≠ Eq` as *relations*,
  because insert-then-delete leaves off-domain junk that `del`+`init` differ on) does NOT bear on
  *convergence*. Convergence needs `eq` only if two lo-respecting orders of the SAME event set fold
  to junk-differing states. **Tested empirically (raw `do_`, `_references`-free scratch): they do
  NOT.** Three convergent pairs — the M1 `full_enum` transposition AND an adversarial
  delete-a-node-early-vs-late construction designed to freeze different anchors — all produce
  BYTE-IDENTICAL states including junk (deleted nodes' stored anchors normalize identically via
  rehome-on-delete / climb-on-insert). `map_lemma_equal_intro` (`Map_Extended.lean:153`) confirms
  `eq` vs `Eq` differ ONLY on off-domain junk, and that junk is order-independent for convergent
  pairs (written in shared causal history, normalized by rehoming). **So the RGA almost certainly
  converges up to structural `Eq`, and the existing Eq-based σ-layer hosts it with NO eq-quotient
  rebuild.** `general_swap` was stated up-to-`eq` by Peepul convention (matching the RGA's own
  `insins/insdel/deldel_comm`), not necessity. Residual (evidence, not proof): re-prove the RGA
  swaps / convergence as Lean `Eq` — needs a manual all-keys argument (`map_equal` isn't decidable),
  bounded work, very likely true. IF it turns out some convergent pair genuinely differs in junk,
  THEN adopt Peepul's observational `eq` (below); but no such pair is known and the evidence is
  against it. **(A) is downgraded from dominant blocker to likely non-issue.**

  *Peepul fallback framing (only if `Eq` re-proof fails):* the correct notion would be Peepul's
  convergence-modulo-observable-behavior (PLDI 2022, arXiv 2203.14518, `_references/peepul_src/pldi.tex`):
  observational equivalence `σ₁ ∼ σ₂` (= the RGA's `eq`), lift it + `do_`/`merge` congruence to the
  conditioned signature, restate convergence over `D.eq`. The RGA's OR-set-as-BST-rebalancing is the
  paper's own example of why. Kept as the principled Plan B.

  *(Original — now superseded — "provable wall" text:)* it is Peepul's convergence-modulo-observable-behavior, which
  Sal's metatheory failed to adopt. `eq_strictly_weaker_than_Eq` (kernel-clean): for `concrete_st`,
  `eq x y ∧ x ≠ y` — witness `del (upd init 1 (5,0)) 1` vs `init` (both empty-domain, so
  observationally `eq`, but `del` leaves off-domain junk in `mappings`, so Lean-unequal).
  `general_swap` yields only observational `eq`; the σ-layer (`ConditionedConvergence`,
  `Sigma_LoOn3`) is Lean-`Eq`-based. **KC's reframe (grounded in Peepul, PLDI 2022, arXiv
  2203.14518, `_references/peepul_src/pldi.tex`):** the correct target was never structural `Eq`.
  Peepul Def "observational equivalence" `σ₁ ∼ σ₂` = every operation returns the same value on both
  (= the RGA's `eq`: agreement on `contains`/`sel`), and "convergence modulo observable behavior" =
  branches converge to `∼`-equivalent, not structurally-equal, states. Peepul's own example is an
  OR-set-as-BST where branches rebalance differently — structurally unequal, observationally equal;
  **the RGA's dead-node junk is that example one level up.** `∼` is provable from the operations
  (the RGA already proves every commutation up-to-`eq`, `eq_symm`, `merge_idem` up-to-`eq`); it is
  NOT a signature field yet (per-RDT `def eq`, `RGA_..._MRDT.lean:154`) and the metatheory never
  references it. **Fix (de-risked, principled): lift `eq` + its equivalence + `do_`/`merge`
  congruence to the conditioned signature, restate convergence over `D.eq`; the RGA discharges the
  congruence from its existing eq-lemmas, flat types trivially. No quotient types, no soundness
  change — just adopting the equivalence discipline KC's own prior work established.** This is
  Insight 1 once more (over-specification, here in the equality relation) — and it unblocks hosting
  for ANY swap, independent of (B)/(C).
- **(B) `general_swap`'s `Faithful` is too weak to THREAD (verified), fix partially mechanized.**
  `climbFaithful_not_preserved_under_del` (kernel-clean counterexample): `ClimbFaithful` is a
  one-level property, not a delete-invariant — a delete deeper in the recorded list re-anchors past
  a level it never constrained. Refutes "`Faithful` threads." Fix: the stronger `ChainFaithful`
  (every live level a true ancestor chain); `climbFaithful_of_chain` (feeds `general_swap`
  unchanged) and `chainFaithful_doIns` PROVED; **`chainFaithful_doDel` is the single remaining
  Faithful lemma** (documented goal, splice argument, not sorried). `NoFreshClash` threads
  (`noFreshClash_of_freshIns`/`_of_del`) under monotone allocation.
- **(C) both-staled risk (analysis-level, unverified).** `general_swap` is asymmetric — one event
  `Faithful`, the other `accurate`. At a hybrid σ-walk state BOTH swapped events can be staled
  (M1's `rehoming_stales_path`), so `general_swap` may not even apply there; a both-`Faithful` swap
  lemma may be needed. NOT mechanized either way — the live risk for whether Route A's swap even
  fires at every bubble state.

**Net:** hosting the tombstone-free RGA is a multi-obligation project dominated by an `eq`-quotient
σ-layer rebuild (A), then `chainFaithful_doDel` (B), then possibly a both-`Faithful` swap (C). This
is the honest cost — substantially more than "wiring," and the eq-quotient (A) is the natural next
milestone as it unblocks everything downstream.

**Risk register.** (a) The normal-form crux (M3) is Route A's alignment problem again; the bet is
`id_mono` + rehoming determinism close it concretely where the generic version can't — unproven,
the main risk. (b) `eq`-vs-`Eq`: `commutes_with'` is observational `eq`; the σ-layer is `Eq`-based,
so a quotient / `eq`-respecting rebuild may be needed (a known RGA-hosting friction, independent of
the bubble). (c) If M1 = accurate-only AND M3 does not close, the honest outcome is: the RGA
converges but is not hostable by a *swap-based* convergence proof — pointing at a non-swap
convergence argument, itself a publishable boundary result.

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
