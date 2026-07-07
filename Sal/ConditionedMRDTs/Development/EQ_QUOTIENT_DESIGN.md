# The observational-≈ quotient σ-layer (M5) — design

*2026-07-04. The last conceptual piece of the conditioned metatheorem: let a datatype that converges
only up to observational `≈` instantiate the structural-`=` metatheorem template. Verified against
`Adequacy.lean` (its `IsRALinearizable3` / Join Lemma are stated over Lean `=`), so this is a real
construction, not transcription.*

## The problem, precisely

The proved template `ra_linearizable3_of_joinC` (`ConditionedContract.lean` / `Adequacy.lean`)
concludes `IsRALinearizable3`, defined with **structural** equality: `applySeq init π = s`, and its
Join Lemma is `s = mergeL B t (update B e)`. The tombstone-free RGA converges only up to
observational `≈` (`eq`): merged/folded states agree on all observable behaviour but may carry
different dead-node residue. So the RGA's convergence results (`eq_merge_two_sided`, the simultaneous
induction, everything) are `≈`-statements and do **not** directly feed a `=`-based bridge.

Two ways to reconcile (established earlier):

1. **Re-prove the bridge over `≈`.** Replace `=` by `≈` throughout `Adequacy.lean` and re-prove.
   Requires `≈` a congruence for `update`/`mergeL` (have: `do_eq_congr`, `applySeqR_eq_congr`), but is
   a substantial re-proof of a large, currently kernel-clean file, and forks the metatheory into
   `=`-version and `≈`-version. Rejected.
2. **Quotient the state by `≈`** — adopted. Present the RGA's state type to the metatheorem as
   `Q := Quotient (≈-setoid)`. Then `=` on `Q` *is* `≈` on the underlying states, so the existing
   `=`-based template applies to `Q` **unchanged**. The metatheory stays single-version and generic.

## The construction

### 1. The setoid and quotient

`≈` (`eq` on `concrete_st`) is proved an equivalence (refl/symm/trans exist or are immediate). Form
`instance rgaSetoid : Setoid concrete_st := ⟨eq, eq_equiv⟩` and `def QState := Quotient rgaSetoid`.

### 2. Lift the operations (needs `≈`-congruence — have it)

`do_` and `mergeL` must respect `≈` to descend to `QState`:
- `do_`: `a ≈ b → do_ a o ≈ do_ b o` is `do_eq_congr`. Lift: `qdo : QState → op → QState` via
  `Quotient.lift`/`map`.
- `mergeL`: needs `l ≈ l' → a ≈ a' → b ≈ b' → mergeL l a b ≈ mergeL l' a' b'`. The single-argument
  congruences are the merge `eq`-congruence lemmas (present/derivable from the merge bridge work);
  compose to the ternary congruence, then `Quotient.lift₃` to `qmerge`.
- `init` lifts to `⟦init_st⟧`.

### 3. The `QState` MRDT satisfies the template VCs over `=`

Instantiate `ConditionedMRDTSig` (or the flat `MRDTSig` the template consumes) with
`State := QState`, `do := qdo`, `merge := qmerge`, `init := ⟦init_st⟧`, lifting `Inv`/`applicable`
through the quotient (they must be `≈`-invariant — check; `wf`/`id_mono`/`accurate` are observable so
should be). Then:
- **Join Lemma over `=` on `QState`** ⟺ the RGA's **`≈`-merge-linearization** (`eq_merge_two_sided`):
  `⟦mergeL l a b⟧ = ⟦fold l π⟧` in `QState` is *by definition of the quotient* `mergeL l a b ≈ fold l π`
  — exactly the proved (once `hBN`/`FoldBirthChain` close) statement. So the RGA's `≈`-Join **is** the
  `QState` `=`-Join. No re-proof.
- **Convergence over `=` on `QState`** ⟺ the RGA's `≈`-convergence (the simultaneous induction):
  `⟦fold init π₁⟧ = ⟦fold init π₂⟧` ⟺ `fold init π₁ ≈ fold init π₂`. Same.

### 4. Apply the template

Feed the `QState` instance + its `=`-Join to `ra_linearizable3_of_joinC` (Inv-conditioned; add the
`app`-conditioning — the second genuinely-new generic piece, orthogonal to the quotient). Conclude
`IsRALinearizable3` for the `QState` RGA: every version's `QState` equals (`=`, i.e. `≈` downstairs)
`σ*(E)`. Reading it back through the quotient: the concrete RGA state is `≈ σ*(E)` — RA-linearizability
up to observational equivalence, Def 2.1 of the proof doc. SEC follows.

## What must be checked (the real work, not transcription)

1. **`eq_equiv`**: `eq` is refl/symm/trans (likely trivial/present).
2. **Ternary `mergeL` `≈`-congruence**: compose the per-argument congruences. The `l`-argument and
   branch-argument congruences come from the merge bridge; confirm all three exist or prove the
   missing one. *This is the most likely to need real work.*
3. **`Inv`/`applicable` are `≈`-invariant** (so they lift): `wf`, `id_mono`, `contains 0=false`,
   `accurate`, `fresh_ts` should each be preserved under `≈` (observable). Check `accurate` especially
   — it references `contains`/`IsAncPath`, which are observable, so it should be `≈`-invariant.
4. **The template's other VC fields** (`rc`, `lo`, `commutesOn`) lift or are stated on events, not
   states, so unaffected.
5. **`app`-conditioning** of the template (orthogonal): the generic template carries `Inv`; extend it
   to also carry `applicable` and range the Join/convergence over applicable ops. This is the second
   new generic piece; may be a small generalization of `ra_linearizable3_of_joinC` or already latent
   in `ConditionedMRDTSig`.

## Order / dependency

- Depends on the RGA `≈`-convergence (simultaneous induction) and `≈`-merge-linearization
  (`eq_merge_two_sided` with `hBN` discharged) being CLOSED — they are the `QState` `=`-Join and
  `=`-convergence. Do this AFTER those land.
- Independent of both: steps 1–3 (setoid, lifts, invariance checks) can be scaffolded now, but the
  payoff theorems need the RGA results.
- Output: `RGA_is_RA_linearizable` (the RGA instance) via the template on `QState`, and — the headline
  deliverable — the generic `conditioned_metatheorem : conditioned VCs ⇒ RA-lin` with `QState`-style
  `≈`-quotient as the mechanism that lets `≈`-converging instances (RGA) plug in.

## Risk

Low-to-moderate. The `≈`-congruences are the only real proof obligation and the update/merge work
already produced most of them. The quotient machinery is standard Lean (`Quotient.lift`/`map`). The
`app`-conditioning is a template generalization. No open *mathematical* question — the RGA `≈`-results
ARE the `QState` `=`-results by definition of the quotient.
