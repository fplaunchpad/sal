# LWW convergence-side audit — circularity / vacuity of the RA-linearizability VCs

Companion to `READSIDE_INDEPENDENCE_AUDIT.md`. That audit found the *read-side*
"intent" theorems could be circular (machine-checked but self-referential). This
one audits the *convergence side* — the 24 RA-linearizability VCs themselves — for
the analogous failure modes. Convergence has different circularity vectors than the
read side; each is checked below.

**Scope.** LWW family, three variants that all carry the canonical 24-VC schema:

| Variant | File | `Σ` | `eq` |
|---|---|---|---|
| LWW-Register | `Sal/CRDTs/LWW_Register/LWW_Register_CRDT.lean` | `ℕ × ℕ` (ts, value) | `a = b` (identity) |
| LWW-Element-Set | `Sal/CRDTs/LWW_Element_Set/LWW_Element_Set_CRDT.lean` | `map ℕ ℕ × map ℕ ℕ` (addTs, remTs) | pointwise `contains`+`mysel` |
| LWW-Map | `Sal/CRDTs/LWW_Map/LWW_Map_CRDT.lean` | `map ℕ (ℕ × ℕ)` (key → (ts,value)) | pointwise `contains`+`mysel` |

There is **no dedicated MRDT LWW variant** with its own 24-VC discharge (grep
`Sal/MRDTs` for LWW returns only `Add_Win_Priority_Queue_ReadSide` and
`Peritext_ReadSide`, where LWW appears as a read-side *component*, not a datatype
with its own convergence proof). The relevant MRDT-side artifact is the kill-test
`Sal/ConditionedMRDTs/Refutations/LWW_Merge_Needs_Timestamps.lean`, discussed under
the meta-statement.

**Verification performed (evidence, not assertion).** `#print axioms` was run on all
24 VCs of each variant (LWW-Register was `lake build`-ed first; its oleans were not
in the cached tree). Results below are load-bearing to the "clean" verdicts.

---

## Vector 1 — coarse `eq`/`≈` (vacuous VCs)

The 24 VCs are stated as `eq (merge …) (merge …)` / `eq (do_ …) (do_ …)`. If `eq`
were too coarse (extreme `eq _ _ = True`) the VCs would hold vacuously. Classification:

- **LWW-Register: JUSTIFIED (identity).** `def eq (a b) := a = b` (line 37). The VCs
  are genuine propositional equalities of `(ts,value)` pairs. You cannot construct
  two `eq`-related states that read differently, because `eq` *is* structural
  identity. `value_convergent` (`eq s₁ s₂ → value s₁ = value s₂`) is `by subst; rfl`.
  Not coarse.

- **LWW-Element-Set: JUSTIFIED (domain-relative, but proven to imply the read).**
  `eq a b` requires, for all `id`, `contains` and `mysel` to agree on *both* maps
  (lines 60–62). This is coarser than raw representation-identity (two different map
  encodings with the same contains/mysel are `eq`), which is *desirable*
  observation-relativity, not vacuity. Adversarial test: `lookup s id :=
  mysel (fst s) id > mysel (snd s) id` reads only the two `mysel` values that `eq`
  pins — so `eq` cannot relate two states that `lookup` differently. This is proven,
  not just argued: `lookup_convergent` (`LWW_Element_Set_ReadSide.lean:61`,
  `eq s₁ s₂ → (lookup s₁ id ↔ lookup s₂ id)`). Note `eq` is in fact *finer* than
  lookup-equivalence (it also pins the `contains` flag), so if anything it errs
  toward safety. Not coarse.

- **LWW-Map: JUSTIFIED (domain-relative, implies the read).** `eq a b :=
  ∀ k, contains a k = contains b k ∧ mysel a k = mysel b k` (line 36). `lookup s k :=
  Prod.snd (mysel s k)`; `lookup_convergent` (`LWW_Map_ReadSide.lean:30`) discharges
  `eq ⟹ lookup`. Same shape as Element-Set. Not coarse.

**Verdict (Vector 1): all three JUSTIFIED.** No `eq` is too coarse; each either *is*
identity or is proven to imply lookup/observational equivalence.

---

## Vector 2 — modified `do_`/`merge`/`rc` (the displaced-difficulty trap)

The repo's recorded instance of this trap: the tombstone-free RGA's `commutes_with'`
had accuracy + `eq` baked into the *VC statement*, so "the VCs pass" was an artifact
of editing the VCs (memo: *VC modification displaces difficulty*).

LWW is **not** that. In all three files:

- `do_`, `merge`, `rc`, `eq`, `lex_max`, `commutes_with` are each defined **once**, at
  top level, and every VC references those same top-level symbols. Grep for local
  redefinitions (`let do_`, `let merge`, `where do_`, `:= fun s o =>`) inside theorem
  bodies of the two primary targets returns nothing.
- `commutes_with` is the **honest, unmodified** predicate
  `∀ s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)` (Register line 81, Element-Set
  line 102) — no extra `accurate`/`applicable`/`eq` hypothesis is smuggled in, unlike
  the RGA `commutes_with'`. So `rc_non_comm` constrains the real `do_`.
- `merge` is defined as the same `lex_max` / per-key `max` that `do_` installs
  (Register line 87 uses the very `lex_max` of line 57 that `do_` uses at line 68).
  The VCs are stated over the datatype's actual operators.

**Verdict (Vector 2): clean.** The VCs are over the same `do_`/`merge`/`rc` the
datatype uses. Not the displaced-difficulty trap.

---

## Vector 3 — vacuous-vs-load-bearing under `rc = Either`

All three variants set `rc _ _ = Either` unconditionally. Consequently, in every VC:

- a hypothesis `rc X Y = Fst_then_snd` is **FALSE**;
- `(rc X Y = Fst_then_snd ∨ rc X Y = Either)` is **TRUE** (right disjunct);
- `rc X Y ≠ Either` is **FALSE**;
- `(rc o ob ≠ Either ∨ rc o ol = Fst_then_snd)` is **FALSE ∨ FALSE = FALSE**;
- `∃ o, rc o ol = Fst_then_snd` is **FALSE** (no op ever yields `Fst_then_snd`);
- `¬(rc … = Fst_then_snd ∧ …)` is **TRUE**.

So every VC whose hypothesis *requires* an ordering (`Fst_then_snd`, `≠ Either`, or a
`Fst_then_snd`-witness) has an **unsatisfiable antecedent** and is discharged
ex falso — VACUOUS. VCs whose antecedent is satisfiable (or absent) genuinely
constrain `lex_max`/`max` — LOAD-BEARING. The VC statements are identical across the
three variants (the canonical enumeration), so the split is the same for all three.

### The 24 VCs — classification (identical for Register / Element-Set / Map)

| # | VC | rc-hypothesis under `rc≡Either` | class |
|---|---|---|---|
| 1 | `rc_non_comm` | `rc=Either ↔ commutes_with` ⟹ **proves** `commutes_with` | **LOAD-BEARING** |
| 2 | `no_rc_chain` | `¬(Either=Fst ∧ Either=Fst)` — trivially true | VACUOUS-BUT-SOUND |
| 3 | `cond_comm_base` | needs `rc o1 o2=Fst` (false) ∧ `rc o2 o3≠Either` (false) | VACUOUS-BUT-SOUND |
| 4 | `merge_comm` | none — real `lex_max` commutativity | **LOAD-BEARING** |
| 5 | `merge_idem` | none — real `lex_max` idempotence | **LOAD-BEARING** |
| 6 | `base_2op` | `(Fst ∨ Either)` = true → real merge/do_ eq | **LOAD-BEARING** |
| 7 | `ind_lca_2op` | `(Fst ∨ Either)` = true → real | **LOAD-BEARING** |
| 8 | `inter_right_base_2op` | needs `rc ob ol=Fst` (false) | VACUOUS-BUT-SOUND |
| 9 | `inter_left_base_2op` | needs `rc o2 o1=Fst` ∧ `rc ob ol=Fst` (false) | VACUOUS-BUT-SOUND |
| 10 | `inter_right_2op` | needs `rc ob ol=Fst` (false) | VACUOUS-BUT-SOUND |
| 11 | `inter_left_2op` | needs `rc o2 o1=Fst` (false) | VACUOUS-BUT-SOUND |
| 12 | `inter_lca_2op` | needs `∃o, rc o ol=Fst` (false) | VACUOUS-BUT-SOUND |
| 13 | `ind_right_2op` | needs `rc o2 o1=Fst` (false) | VACUOUS-BUT-SOUND |
| 14 | `ind_left_2op` | `(Fst ∨ Either)` = true → real | **LOAD-BEARING** |
| 15 | `base_1op` | none — real merge/do_ eq at init | **LOAD-BEARING** |
| 16 | `ind_lca_1op` | only `distinct` + IH — real | **LOAD-BEARING** |
| 17 | `inter_right_base_1op` | needs `rc ob ol=Fst` (false) | VACUOUS-BUT-SOUND |
| 18 | `inter_left_base_1op` | needs `rc ob ol=Fst` (false) | VACUOUS-BUT-SOUND |
| 19 | `inter_right_1op` | needs `rc ob ol=Fst` (false) | VACUOUS-BUT-SOUND |
| 20 | `inter_left_1op` | needs `rc ob ol=Fst` (false) | VACUOUS-BUT-SOUND |
| 21 | `inter_lca_1op` | needs `∃o, rc o ol=Fst` ∧ `∃o, rc o oi=Fst` (false) | VACUOUS-BUT-SOUND |
| 22 | `ind_left_1op` | only `distinct` + IH — real | **LOAD-BEARING** |
| 23 | `ind_right_1op` | only `distinct` + IH — real | **LOAD-BEARING** |
| 24 | `lem_0op` | none — `do_` distributes over `merge` | **LOAD-BEARING** |

**Count: 11 LOAD-BEARING, 13 VACUOUS-BUT-SOUND, 0 SUSPECT.**

Load-bearing set: `rc_non_comm`, `merge_comm`, `merge_idem`, `base_2op`,
`ind_lca_2op`, `ind_left_2op`, `base_1op`, `ind_lca_1op`, `ind_left_1op`,
`ind_right_1op`, `lem_0op`. These are the real algebra of `lex_max`/`max`: it is a
commutative-associative-idempotent join (`merge_comm`/`merge_idem`), `do_` commutes
with itself (`rc_non_comm`'s forward direction proves `commutes_with`), and `do_`
distributes over `merge` (`lem_0op`); the `base`/`ind`/`inter_lca` members are the
induction skeleton that lifts these facts along an execution.

**Two independent corroborations of the split (not just my reading of the antecedents):**

1. **Proof-shape.** The VCs the authors closed with an *explicit* `rcases … <;>
   simp <;> grind` (rather than `by sal`) are exactly load-bearing members
   (`ind_lca_2op`, `ind_left_2op`, `ind_left_1op`, `ind_right_1op` in Register;
   additionally `base_2op`, `base_1op`, `ind_lca_1op`, `lem_0op` in Element-Set — the
   Element-Set `base_2op` even carries the comment *"Uncovered by the sal
   silent-sorry guard; direct proof"*, i.e. it needed genuine work). The vacuous ones
   are dispatched by `by sal` stage-1 `grind` killing the false antecedent.

2. **Axiom footprint (Register / Element-Set).** `#print axioms` shows the vacuous
   VCs depend only on `[propext, Quot.sound]` while the load-bearing ones additionally
   pull in `Classical.choice` (the `max`/lattice reasoning). This split matches the
   table exactly (the lone exception is `no_rc_chain`, trivially true yet carrying
   `Classical.choice`). For LWW-Map every VC carries `Classical.choice` because all
   proofs route through the map machinery / `merge_do_lex_max`, so the footprint
   heuristic does not separate there — but the antecedent analysis is definitional and
   identical.

### Is the vacuity SOUND (`rc = Either` justified by real commutativity)?

Yes. `rc = Either` is legitimate **iff** every pair of ops genuinely commutes, so that
no ordering is ever needed and the 13 ordering VCs are *correctly* empty rather than
dodged. The commutativity is separately and genuinely proven:

- `rc_non_comm` (kernel-clean) establishes `commutes_with o1 o2 =
  ∀ s, eq (do_ (do_ s o1) o2) (do_ (do_ s o2) o1)` for distinct-ts / different-replica
  ops — precisely the question posed: **does `do_ (do_ s o1) o2 = do_ (do_ s o2) o1`
  hold? It does.** For the Register, `do_`'s install is `lex_max s (ts,v)`, and
  `lex_max` is `max` under the total lexicographic order on `ℕ×ℕ`, hence commutative,
  associative and idempotent — so installs commute even at equal timestamps (ties
  broken by larger value, deterministically). For Element-Set/Map the install is
  per-key `max`, likewise a commutative idempotent join; `Add`/`Remove` touch disjoint
  maps.
- `merge_comm` and `lem_0op` (both LOAD-BEARING, kernel-clean) independently witness
  the same join structure at the `merge` level.

So the 13 vacuous VCs are **VACUOUS-BUT-SOUND**: each certifies nothing *by itself*,
but the commutativity that makes `rc = Either` the right choice is proven elsewhere in
the same file. None is SUSPECT — there is no ordering being silently skipped, because
under a genuine join there is no ordering to get right.

---

## Vector 4 — admits / sorry / axioms

- **No `sorry`/`admit` in any LWW `_CRDT.lean`.** (The single grep hit is a *comment*
  in `LWW_Element_Set_CRDT.lean:158` — "Uncovered by the sal silent-sorry guard;
  direct proof" — describing why that VC is proved directly, not a `sorry`.)
- **No Blaster/Z3 stage-2 admit.** The `sal` tactic's stage 2 (Blaster) closes goals
  via `MVarId.admit` → `sorryAx`, enlarging the TCB to Z3; stages 1 and 3 are guarded
  against `sorryAx`. `#print axioms` on **all 24 VCs of all three variants** returns
  only subsets of `{propext, Classical.choice, Quot.sound}` — the three standard Lean
  axioms — with **zero `sorryAx`**. The Aristotle-assisted intermediate lemma
  `merge_do_lex_max` (LWW-Map) is likewise clean `[propext, Classical.choice,
  Quot.sound]`.
- **The LWW family is NOT among the README's Blaster-admit RDTs** (`OR_Set`,
  `OR_Set_Efficient`, `Add_Win_Priority_Queue`, `Multi_Valued_Register`). Confirmed
  clean by direct axiom check.

`#print axioms` evidence (representative; full runs on all 24 × 3 done):

```
LWW_Register  merge_comm      : [propext, Classical.choice, Quot.sound]
LWW_Register  cond_comm_base  : [propext, Quot.sound]              -- vacuous
LWW_Element_Set  lem_0op      : [propext, Classical.choice, Quot.sound]
LWW_Map  merge_do_lex_max     : [propext, Classical.choice, Quot.sound]
(no theorem in any of the three depends on sorryAx / Blaster / Z3)
```

**Verdict (Vector 4): LWW is clean at the per-datatype VC layer.**

### Caveat — the framework bridge that would *consume* the 24 VCs is not closed for LWW

This is a convergence-side gap worth stating honestly, though it is not circularity:

- No CRDT in `Sal/CRDTs/` — LWW included — instantiates the parametric
  `SatisfiesVCs D` structure or invokes the bridge `ra_linearizable_of_vcs`. The LWW
  "convergence proof" *is* the 24 standalone theorems; the step "24 VCs ⟹ every
  reachable configuration is RA-linearizable" is the paper's meta-theorem, appealed to
  but not wired per-datatype.
- The generic bridge `ra_linearizable_of_vcs`
  (`Sal/CRDTs/Metatheory/Merge_Linearization.lean:4525`) is itself **not fully
  mechanized**: its Merge case delegates to `merge_linearization_exists`, which carries
  live `sorry`s (`Merge_Linearization.lean:2816, 2987, 3003, 3009, 4440–4446`; the
  file header and `Development/BLUEPRINT.md` count 6 real `sorry`s in the bridge). The
  base/Apply/Query cases are complete.

So "LWW's 24 VCs are kernel-clean" is true and verified; "therefore LWW is
RA-linearizable" rests on the paper's meta-theorem, whose Lean bridge is complete only
in the non-Merge cases in *this* repo. (The conditioned MRDT track under
`ConditionedMRDTs/` re-derives an end-to-end route for the flat datatypes through a
different, closed metatheorem, but the flat-CRDT `LWW_*` files here are not routed
through it.)

---

## Vector 5 — the self-referential meta-point (stated explicitly for LWW)

RA-linearizability certifies: *the merged/replayed state equals the fold of the ops
under `do_`* — i.e. LWW converges to the state `lex_max` (Register) / per-key `max`
(Set/Map) selects: **the write with the maximal timestamp**. This equals the
**intended** last-writer-wins semantics only because of three things the convergence
proof does **not** and **cannot** certify:

1. **`do_` is correct by inspection.** `do_` = `lex_max` install = "keep the pair with
   the newer ts". It is simple enough to read off as "install the later write". The
   VCs verify it converges; they do not — and need not — verify it is the *right*
   effect, because a human confirms the one-line `max` is LWW by inspection. (Contrast
   a datatype whose `do_` is complex enough that "converges to its own fold" is a weak
   guarantee — the general `oq:linspec` limit.)

2. **Timestamps are assumed to encode "later".** The proof takes `ts` as given and
   `distinct_ops` (global uniqueness) as an axiom of the execution model. That the
   numeric `ts` order matches real happens-before "later" is an **external
   spec assumption** (Lamport/causal clock allocation). Convergence to the max-`ts`
   write is only *last-writer*-wins if `max ts` really is the last writer. This is
   sharpened, not assumed away, by the kill-test `lww_merge_needs_timestamps`
   (`ConditionedMRDTs/Refutations/`, kernel-checked): a metadata-free LWW (state = plain
   value) admits **no** three-way merge, because two executions can present identical
   value triples under opposite ts orders. The timestamp is *load-bearing metadata*,
   forced into the state — the convergence proof relies on it but says nothing about
   its meaningfulness.

3. **The tie-break is a chosen convention, not "writer wins".** At equal `ts`,
   Register's `lex_max` picks the larger *value* (an arbitrary totalization, disclosed
   in the docstring, made irrelevant in practice by `distinct_ops`); Element-Set/Map
   resolve add-vs-remove ties by strict `>` (remove-wins-on-tie — the docstring notes
   the classical LWW-Set lets this vary). These are spec *choices* the convergence
   proof carries but does not justify as "correct".

**Honest classification of LWW convergence:** *genuinely proven* SEC / strong eventual
convergence (11 real algebraic VCs over `lex_max`/`max`, kernel-clean) **+**
intended-semantics-by-inspection-of-a-trivial-`do_` **+** one unstated spec assumption
(timestamp meaningfulness / clock faithfulness), plus a disclosed tie-break
convention. This is the exact convergence-side parallel to the read-side `oq:linspec`
finding: the machine certifies convergence to *this datatype's own fold*; that the
fold *is* LWW is a by-inspection + external-assumption judgement, not a theorem.

---

## Load-bearing summary (one paragraph, honest)

LWW's convergence-side RA-linearizability is a **genuine guarantee, modulo stated
assumptions** — not vacuous and not circular. The `eq` is JUSTIFIED in all three
variants (identity for the Register; domain-relative but *proven* to imply the read
for Element-Set and Map). The VCs are stated over the datatype's real
`do_`/`merge`/`rc` (not a modified copy — this is not the RGA displaced-difficulty
trap). Of the 24 VCs, **11 are load-bearing** real algebra of the `lex_max`/`max`
join and **13 are vacuous** because `rc = Either` makes their ordering antecedents
unsatisfiable — but that vacuity is **sound**, because the commutativity that
justifies `rc = Either` (`rc_non_comm`, `merge_comm`, `lem_0op`; `do_ (do_ s o1) o2 =
do_ (do_ s o2) o1` genuinely holds since install is a total-order `max`) is separately
and kernel-cleanly proven. All 72 VCs (24 × 3 variants) plus `merge_do_lex_max` are
kernel-clean with zero `sorryAx` — LWW is not among the suite's Blaster-admit RDTs.
The honest residue is not circularity but (a) an *external* assumption the proof cannot
discharge — that timestamps encode "later" (made vivid by the `lww_merge_needs_
timestamps` kill-test) — and (b) an *engineering* gap: the generic bridge
`ra_linearizable_of_vcs` that turns the 24 VCs into "every reachable config is
RA-linearizable" still carries `sorry`s in its Merge case, and LWW is not wired to it,
so "LWW is RA-linearizable" currently rests on the paper's meta-theorem rather than a
per-datatype mechanized capstone.

---

## Recommended actions

1. **Document the timestamp-meaningfulness assumption where the LWW capstone is
   presented.** State explicitly that convergence certifies "converges to the max-`ts`
   write", and that "max-`ts` = last writer" is an external clock-faithfulness
   assumption (cite `lww_merge_needs_timestamps`). This is the convergence-side twin of
   the read-side `oq:linspec` disclosure and should sit next to it.

2. **Don't oversell "24 VCs closed".** For every `rc = Either` datatype (LWW, OR-Set,
   G-Set, PN-Counter, …) 13 of the 24 are vacuous under an unsatisfiable
   ordering antecedent; the real content is the 11-VC join algebra plus the
   commutativity that licenses `rc = Either`. A one-line note "13/24 hold vacuously by
   `rc = Either`; the guarantee is carried by the 11 join-algebra VCs + `rc_non_comm`"
   would make the count honest without diminishing the (genuine) result.

3. **Record the bridge gap.** The claim "the per-datatype 24 VCs ⟹ RA-linearizability"
   is, in this repo, mediated by `ra_linearizable_of_vcs`, whose Merge case is `sorry`,
   and no `LWW_*` file instantiates `SatisfiesVCs`. Either wire LWW to the (completed)
   conditioned metatheorem or annotate that the flat-CRDT capstone is the paper's
   meta-theorem, not a mechanized per-datatype theorem. (Documentation, not a proof
   obligation — but it prevents "kernel-clean VCs" being read as "kernel-clean
   RA-linearizability".)

4. **Tie-break conventions:** already disclosed in the docstrings; no action beyond
   keeping those docstrings when the files move.
