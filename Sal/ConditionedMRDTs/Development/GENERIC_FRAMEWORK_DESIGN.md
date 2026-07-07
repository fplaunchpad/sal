# The generic conditioned metatheorem — design

*2026-07-05. Makes "conditioned VCs ⇒ RA-linearizability" generic over `ConditionedMRDTSig`, with the
`≈`-quotient as a datatype-agnostic functor, so state-dependent MRDTs (RGA now, Peritext later) are
INSTANCES, not bespoke proofs. Prioritized ahead of the remaining flat MRDTs (MVR, AW-PQ) per KC —
once this exists they discharge through it cheaply.*

## What is already generic (reuse, do not rebuild)

- `ra_linearizable3_of_joinC (D : ConditionedMRDTSig) : JoinLemma3C D → IsRALinearizable3 D` —
  Inv-conditioned Join ⇒ RA-lin over STRUCTURAL `=`. Proved, generic, 9 flat instances
  (`ConditionedContract.lean` / `Adequacy.lean` / `MRDT_Instances.lean`).

The ONE gap: it concludes RA-lin over Lean `=`. State-dependent datatypes converge only up to
observational `≈`. Bridge that generically.

## The generic `≈`-quotient functor `D ↦ D≈`

Input: `D : ConditionedMRDTSig` + two VCs the datatype supplies:
- **`CongVC D`** (the congruence VC C's counterexample forced): `merge` (and `do`) respect `≈` on
  `Inv`-states —
  `Inv l → Inv l' → Inv a → Inv a' → Inv b → Inv b' → l≈l' → a≈a' → b≈b' → mergeL l a b ≈ mergeL l' a' b'`
  (and the `do` analog — usually already have it). **Note it is conditioned on `Inv`** — the
  full-type version is FALSE for the RGA (`merge_eq_congr_l_fails`), true on `wf∧id_mono∧forest`.
- **`EqEquiv D`**: `≈` is an equivalence on `State` (trivial for the RGA: `eq_equiv`).

Construction:
- `QState D := Quotient (setoid from ≈)`, or the `Inv`-subtype quotient `Quotient (≈ on {s // Inv s})`
  — carry `Inv` so `CongVC`'s hypotheses are available (this is the reachable-subfamily refinement C
  established as necessary). Choose the subtype-quotient so lifts have `Inv` in scope.
- `qdo`, `qmerge` via `Quotient.lift`/`lift₃` using `CongVC` (+ the `do` congruence). Preservation of
  `Inv` under `do`/`merge` (the datatype's `inv_step`) lets the subtype-quotient close.
- Assemble `D≈ : ConditionedMRDTSig` with `State := QState D`, `do := qdo`, `merge := qmerge`,
  `init := ⟦init⟧`, `Inv`/`applicable`/`rc`/`lo` lifted (they are `≈`-invariant — a VC, `InvInvVC`,
  trivial/observable for the RGA: the `qInv`/`qapplicable` C built).

## The transfer theorem (generic)

> **`joinC_quotient`:** `D`'s `≈`-Join (`JoinLemma3C` stated up to `≈`) ⇒ `JoinLemma3C D≈` (over `=`).

By definition of the quotient, `=` on `QState` IS `≈` downstairs, so `D`'s `≈`-equation
`mergeL l a b ≈ fold …` becomes the literal `=`-equation in `D≈`. The proof is `Quotient.sound`/`ind`
bookkeeping — no datatype specifics. (This is where the ≈-Join the RGA proves, A+B, becomes usable.)

> **`RA_linearizable_up_to_eq`:** `D` with `EqEquiv + CongVC + InvInvVC + ≈-JoinLemma3C` ⇒ `D` is
> RA-linearizable up to `≈` (each version state `≈ σ*(E)`).

Proof: `joinC_quotient` gives `JoinLemma3C D≈`; `ra_linearizable3_of_joinC D≈` gives
`IsRALinearizable3 D≈` (over `=` on `QState`); read back through the quotient — `⟦state v⟧ = ⟦σ*(E)⟧`
in `QState` means `state v ≈ σ*(E)` in `D`. Done. **This is the generic conditioned metatheorem.**

## `app`-conditioning (check first, may be free)

`ra_linearizable3_of_joinC` already carries `D.Inv`. Determine whether it also ranges the Join /
adequacy over `D.applicable`, or whether `applicable` only gates the execution model (M2). If the
template's Join is already stated for the datatype's own reachable ops (which are applicable by
construction), `app`-conditioning may need nothing at the metatheorem level — it lives in the
execution-model discharge of the VC. Report which. If a genuine extension is needed, add `applicable`
to the template's reachability the same way `Inv` is carried.

## Instances (validation)

- **RGA** (the exercise): supply `EqEquiv` (`eq_equiv`, C), `CongVC` (from `climb_aux_walk` — merge
  ≈-congruent on `wf∧id_mono∧forest`, C established the shape), `InvInvVC` (`qInv`/`qapplicable`, C),
  and the `≈`-Join (A `RGA_update_convergence_canon`/`CanonFoldOK` for convergence + B
  `eq_merge_two_sided_final` for merge=fold, modulo `CanonBirthBridge`). → RGA RA-lin up to `≈`.
  This instantiation is the generic framework's proof-of-work; needs A/B closed.
- **Flat MRDTs** (MVR, AW-PQ later): `≈` = `=`, so `CongVC`/`EqEquiv`/`InvInvVC` are trivial and the
  quotient is the identity; they discharge the `=`-Join directly and get RA-lin from the SAME generic
  theorem. This is why they become cheap AFTER the framework.

## Build order

1. Generic quotient functor `D ↦ D≈` (+ `qdo`/`qmerge` via `CongVC`) — over `ConditionedMRDTSig`.
2. `joinC_quotient` transfer + `RA_linearizable_up_to_eq` (the metatheorem).
3. `app`-conditioning check/extension.
4. Instantiate at the RGA (after A/B) → RGA RA-lin up to `≈`.
5. (Later) MVR, AW-PQ via the identity-quotient path.

## Risk

The functor + transfer is standard `Quotient` bookkeeping over the signature — LOW research risk (C
already did the RGA-specific version and found the one real constraint, `CongVC`-on-`Inv`). The two
watch-points: (a) the subtype-quotient (`Inv`-carrying) vs plain quotient — pick the one where
`CongVC`'s `Inv` hypotheses are in scope at the lift; (b) whether `ra_linearizable3_of_joinC`'s exact
`JoinLemma3C` shape matches the `≈`-Join the RGA proves (A/B) after the quotient — the same
shape-adapter risk flagged for the RGA assembly. Both bookkeeping, not walls.
