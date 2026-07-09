# Read-side independence audit

**Scope.** Every Tier-C read-side / intent theorem in the suite, and the `≈`
(observational equivalence) of every conditioned instance, classified for
whether it *constrains behaviour* (can catch a `do_`/`merge`/read bug) or merely
*restates the implementation*.

**Why this exists.** `Peritext_Composed/MarkIntent.lean`'s original `mark_*_no_leak`
was a machine-checked theorem that "held" while the mechanism it claimed to bound
actually leaked: it restated where `resolve` climbs (tree ancestry) instead of
specifying intended document position (retraction `91628ca`). The note's
`oq:linspec` states the general limit: **RA-linearizability certifies convergence
to the datatype's OWN `do_`-fold, not correctness of that fold** — a defect in
`do_` appears identically in the concurrent state and its fold and is certified
as agreement. Only an *independent* spec (positional claim, cross-computation
membership relation, literal-oracle execution, paper-example correspondence)
catches a `do_` bug. This audit hunts the whole suite for the same circularity.

**Method.** For each theorem I read the statement, the docstring's *claim*, and
enough of the proof to tell whether it (a) unfolds `do_`/the read and asserts a
tautology, (b) has an unsatisfiable or vacuous hypothesis, (c) is bounded so
weakly the buggy behaviour still satisfies it, or (d) genuinely relates two
independent computations. For `≈`: `CongVC.query_congr`
(`GenericEqQuotient.lean:111`) *is* the `≈ → query-eq` obligation and a required
field of the framework's `CongVC` bundle — so its (non-vacuous) discharge =
JUSTIFIED.

---

## Summary table

Classification key: **IND** = independent (constrains behaviour, can catch a
`do_`/`merge`/read bug); **CIRC** = circular/vacuous (restates the read's own
definition or a constructor; catches nothing); **PART** = partial (independent
about one axis — usually read↔state faithfulness — but silent on the risky axis,
usually order/position under deletion); **JUST/UNJUST** = `≈` justified /
unjustified as query-preserving.

### A. Read-side / intent theorems

| RDT (file) | theorem | class | what bug it would / wouldn't catch |
|---|---|---|---|
| **Peritext flat** `Sal/MRDTs/Peritext_with_tombstones/Peritext_ReadSide.lean` | `insert_within_span_in_span_visible` (Ex 1) + `_cross_subtree_` | IND | char inserted after an in-span char & left of `endId` comes out in-span; internally proves `after_of s_post (ts,rid) c_after = true` from `do_`, so a `do_ Insert` recording the wrong anchor breaks it |
| | `in_span_visible_propagate` / `_of_reach` | IND | positional propagation lemmas feeding Ex 1 |
| | `partial_overlap_all_adds_formatted_visible` (Ex 2) | IND | all-adds cover ⇒ formatted; catches a resolver dropping an add. PART on position (assumes `in_span`) |
| | `different_type_adds_coexist_visible` (Ex 3) | IND | two markTypes coexist; catches per-type merge bug |
| | `add_wins_over_concurrent_remove_visible` (Ex 5+) / `formatted_visible_of_lww_add_winner` | IND | higher-opId Add wins over Remove; catches a remove-wins-on-tie bug |
| | `no_add_cover_implies_unformatted_visible` (Ex 5−) | IND | no covering add ⇒ unformatted; catches a resolver inventing formatting |
| | `ex7_bold_older_sibling_in_span` / `bold_expand_in_span_visible` (Ex 7) | IND | boundary insert expands under bold; positional via `opid_max` order |
| | `ex8_link_descendant_not_in_span_visible` / `_of_wf` (Ex 8−) | IND | post-`endId` insert **excluded** under link; catches a read that lets links expand |
| | `ex8_link_descendant_visible_lt_endId` | CIRC | one-liner = `visible_lt.parent_child` renamed; catches nothing |
| | `anchors_survive_tombstones_visible` | IND | `Remove c_rm` leaves a different char's formatting unchanged; catches a Remove corrupting bystanders |
| | `startId_in_span_visible` / `endId_in_span_visible` | PART | endpoints in their own degenerate span; structural |
| | `readRichText_visible_convergent`, `formatted_visible_convergent`, `is_rga_traversal_convergent`, `readRichText_list_eq_of_traversal_eq` | PART | convergence-at-read; MRDT `eq` lifts to `s₁=s₂` so trivial; well-definedness, not positional |
| | *(removed)* `expand_contract_*` vs `in_span_boundary` | **CIRC (precedent)** | prior wrong-spec: theorems "true" against a boundary predicate encoding the *opposite* of paper expand/contract; already deleted (lines 84–92). Same trap as `mark_no_leak` |
| **RGA tombstone-free** `Sal/MRDTs/RGA/RGA_Tombstone_Free_ReadSide.lean` | `document_sound` | PART | read emits only `contains`-live ids; but the read *filters by* `contains`, so this is read↔state faithfulness — silent on whether the state / order is intended |
| | `mem_document_of_live` / `mem_document_iff` | PART | read = exactly the live **set**; says **nothing about order** — and order is precisely where tombstone-free rehoming bites |
| | `del_not_in_document` | IND | after `Del x`, `x` not read; catches a Del that fails to delete or a read showing tombstones |
| | `del_document_mem` | IND | read-membership after `Del x` = old minus `x` |
| | `document_convergent` / `readText_convergent` | IND/JUST | full **ordered** read equal under `eq`; this is the real `≈→read-eq` witness (see B) |
| | SPOT `ins_intent_document` / `_readText` | IND | literal oracle: insert 10 after 5 ⇒ `[5,10]` — positional, human-authored expected value |
| | SPOT `leaf_del_preserves_order` | IND | literal: leaf delete = old read filtered |
| | SPOT `del_can_reorder_survivors` | IND (**refutation**) | literal: general order-preservation is **FALSE** — rehoming reorders survivors. The honest exposure of the order gap |
| | SPOT `merge_document` / `merge_convergent_read` | IND | literal merge-read outcomes |
| **AWPQ** `Sal/MRDTs/Add_Win_Priority_Queue/..._ReadSide.lean` | `add_wins_over_concurrent_rmv` | IND | 3-way merge keeps a fresh Add over concurrent Rmv; catches merge dropping `a\l` |
| | `lookup_after_add`, `is_empty_init`, `inc_creates_inc_record` | IND (shallow) | exercise `do_ Add`/`Inc`/`init`; catch wrong-element / empty-init bugs |
| | `inc_increases_acquired` | IND | `acquired += amount`; **but specifies summation, not paper's Most-Change-Win** (faithfulness caveat, `docs/aw-crpq-vs-paper.md`) |
| | `innate_record_unique` | PART | well-definedness of the LWW-max predicate; silent on `do_` |
| | `lookup_convergent`, `is_{innate,empty,acquired,priority,get_max}_convergent` | PART | `≈→query-eq` with `≈ = =` (`unfold eq; subst; rfl`); trivial, not intent |
| **OR-Set** & **OR-Set-Efficient** `Sal/MRDTs/OR_Set*/..._ReadSide.lean` | `add_wins_over_concurrent_remove` | IND | fresh tag in `a\l` survives concurrent Rem; catches add-wins merge failure |
| | `lookup_after_add`, `add_then_remove_extinguishes` | IND | `do_ Add`⇒live; `Add;Rem`⇒not-live; catch a Rem that fails to filter |
| | `lookup_convergent` | PART | `≈==` trivial |
| **MVR** `Sal/MRDTs/Multi_Valued_Register/..._ReadSide.lean` | `concurrent_writes_both_visible` | IND | both concurrent writes survive merge (MVR headline); catches a merge dropping one |
| | `sequential_write_supersedes_value` | IND | covering snapshot ⇒ old value not visible; catches a Write that fails to supersede |
| | `visible_after_write`, `sequential_write_supersedes_witness` | IND | `do_ Write` exercised |
| | `is_visible_value_convergent` | PART | `≈==` trivial |
| **LWW-Element-Set** `Sal/CRDTs/LWW_Element_Set/..._ReadSide.lean` | `lookup_after_add_with_fresh_ts` | IND | Add at ts>rem ⇒ live; catches a merge taking min or `do_` miswriting ts |
| | `remove_at_higher_ts_extinguishes` | IND | Remove at ts≥add ⇒ not live |
| | `latest_write_wins` | **CIRC** | proved by `rfl`; docstring: *"just `lookup`'s definition restated"*. Catches nothing |
| | `equal_ts_remove_wins` | PART | tie convention; property of the predicate |
| | `lookup_convergent` | PART | `≈→query-eq` non-trivially (uses `mysel` congruence); honest |
| **PeritextTF** `Sal/ConditionedMRDTs/MRDT_Instances/Peritext_Composed/MarkIntent.lean` | `mark_start_in_recorded` / `mark_end_in_recorded` | CIRC | = `resolve_eq_zero_or_mem`: "resolve returns a member of the list it searches" — restates `resolve`'s own def; honestly re-glossed as "containment" |
| | `mark_start_live` / `mark_end_live` | CIRC | = `resolve_live_of_ne_zero`: "resolve returns a live char" — restates `resolve`'s def |
| | `mark_start_within_recorded_ancestry` / `_end_` | **PART (honest)** | under accuracy, endpoint ∈ {root, anchor, issue-time ancestors}. *Bounds* the leak; docstring now states it does **not** prevent backward drift. This is the corrected `mark_no_leak` |

### B. `≈` of each conditioned instance (`≈ → query-eq`)

| Instance | `≈` (`EqEquiv.eqv`) | signature `query` | class | justification |
|---|---|---|---|---|
| Flat instances via `FlatGeneric` — GOSet, GOMap, GSet, Counter, IOC, PN, EWFlag, ORSet, ORSetE, ORSetCore, AWPQ, MVR, RGA-tombstoned, flat Peritext, FWWRegister | `eqOfEq D = ⟨Eq, …⟩` (**`≈ = =`**) | various (`fun s _ => s`) | **JUST** | `congVCEq.query_congr : s=s' → query s q = query s' q`, trivial |
| **BoundedCounter** | `eqOfEq` (`≈ = =`) | `fun s r => s.1 r - s.2 r` (real) | **JUST** | `≈ = =` ⇒ query_congr trivial even though query is non-trivial |
| **BudgetCart** | `eqOfEq` (`≈ = =`) | remaining-budget over `alloc` | **JUST** | `≈ = =` |
| **FWWRegister** | `eqOfEq` (`≈ = =`) | `fun s _ => s` | **JUST** | `≈ = =` |
| **MergeableQueue** | `= ` on **canonical single-list** state (uses `IsRALinearizable3`, non-`Eq`) | `fun s _ => s.head?` (real) | **JUST** (caveated) | query is a function of state under `=`. **Caveat**: real Peepul is two-list; the docstring notes "two-list balancing is an `≈`-away" — that coarser `≈` would owe a genuine `head?`-congruence not proved here |
| **RGA_TombstoneFree** | `rgaEqEquiv' = ⟨eq, eq_equiv⟩` — **coarser than `=`** (domain-relative) | **`fun _ _ => ()`** (trivial!) | **JUST-but-VACUOUS** | framework `query_congr` holds because the signature query observes nothing. The real read (`document`, ordered) is proved `≈`-invariant *separately* by `document_convergent` in the read-side. The capstone alone certifies **nothing observable** |
| **PeritextTF** | `prodEqEquiv rgaEqEquiv' = ≈₁ × Eq` — **coarser than `=`** | product default (RGA proj trivial) | **JUST** (render) | the meaningful read is `peritextRender`; `peritextRender_congr` (`Render.lean:67`) proves `(≈₁×Eq)`-related states render identically — the standalone `query_congr`. **Well-definedness only**, not positional correctness |

---

## Findings (prose)

### 1. The one hard circular theorem: `latest_write_wins` (LWW)
`latest_write_wins : lookup s id ↔ mysel (fst s) id > mysel (snd s) id` is proved
`by rfl` and its docstring admits it is "just `lookup`'s definition restated." It
is CIRCULAR by construction: `lookup` *is* `mysel (fst s) id > mysel (snd s) id`.
It catches no bug in `do_`, `merge`, or the read. It is presented (name + "the
LWW-Element-Set headline") as if it were the LWW guarantee; it is not. The genuine
LWW content is in `lookup_after_add_with_fresh_ts` and
`remove_at_higher_ts_extinguishes`, which do exercise `do_`.

### 2. MarkIntent is now honestly labeled — confirmed, no residual overclaim
The re-glossed `mark_*_within_recorded_ancestry` docstrings state, in the file
header and per-theorem, that they are a **containment bound, not a no-leak
guarantee**, that tree-ancestry climbing leaks formatting backward under anchor
deletion, and that the intended positional guarantee "is not proved here and does
not hold for the frozen-path design" (§4). This matches PART. The two families
`mark_*_in_recorded` and `mark_*_live` are, strictly, CIRCULAR — they restate what
`resolve` does by definition (returns a member of its candidate list; returns a
live char) — but they are correctly presented as "structural containment," not as
intent. **No residual overclaim.** (This is the fixed version of the bug that
motivated the audit.)

### 3. RGA_TF read-side: membership is faithful, ORDER is the silent axis
`document_sound` / `mem_document_iff` / `del_document_mem` establish the read is
exactly the live **set** (no ghosts, no hidden live element, delete removes its
target). These are the "faithful to state" axis and are PART: they say nothing
about whether the *order* the user reads is the intended document order — and
order is exactly where tombstone-freedom is lossy. The suite is honest about this:
the order facts live in `RGA_Tombstone_Free_SPOT.lean` as literal `native_decide`
executions, and `del_can_reorder_survivors` **proves the general
order-preservation claim FALSE** (deleting a node rehomes its children and
re-sorts survivors). That refutation is the single most valuable read-side
artifact in the RGA files — it is the honest analogue of what the Peritext
`mark_no_leak` retraction should have been from the start. `document_convergent`
is genuinely load-bearing (it proves the *ordered* read is `≈`-invariant, order
included), and is the actual `≈→query-eq` witness the trivial signature query does
not provide.

### 4. Flat Peritext: independent positional theorems on top of a *hand-checked*
### encoding
The Ex 1/2/3/5/7/8 theorems are INDEPENDENT relative to the read projection —
`in_span_visible` is built from the RGA visible-order relations (`visible_lt`,
`bold_expand_reach`) over `after_of`, and the theorems relate `do_ Insert`/`Remove`
outcomes and mark-resolution to span membership in ways that would catch a
wrong-anchor insert, a remove-wins resolver, or a link that wrongly expands. The
Ex 8 negative (`ex8_link_descendant_not_in_span_visible`) and
`anchors_survive_tombstones_visible` are the strongest (they *exclude* / *preserve*
behaviour). **But** the whole edifice's *paper-faithfulness* rests on
`in_span_visible` being the correct encoding of the paper's positional semantics,
which is checked by the `docs/peritext-vs-paper.md` example table and the SPOT
literal executions — not by an independent Lean oracle. The file itself records a
prior incident of exactly the audit's failure mode: four `expand_contract_*`
theorems were "true about the boundary approximation but its `endSide`/`after_of
endId` clause encodes the opposite of the paper's expand/contract semantics" and
were deleted. That is a second machine-checked-but-wrong-spec event in this suite;
it argues the encoding-faithfulness of `in_span_visible` should not be treated as
settled by the theorems alone.

### 5. The `≈` discipline is structurally enforced — but two instances route the
### observable content *around* the signature query
The framework makes `query_congr` a required field of `CongVC`, so a coarse `≈`
cannot be admitted without a `≈→query-eq` proof. Every flat instance takes
`≈ = =` (`eqOfEq`), discharging it trivially. The two genuinely coarse `≈`
instances do **not** discharge it on the signature query:
- **RGA_TF** sets `query := fun _ _ => ()`, so the framework obligation is vacuous
  and the capstone "RA-linearizable up to `≈`" certifies nothing a user observes.
  The observable guarantee is entirely in the separately-proved `document_convergent`.
- **PeritextTF** carries the observable content in `peritextRender_congr`, a
  standalone theorem, explicitly labeled "well-definedness only."

Both are *defensible* (the content exists, just not in the capstone), but both are
a presentational trap: "verified RA-linearizable up to `≈`" reads as "the read
converges" only if the reader also knows about `document_convergent` /
`peritextRender_congr`. The README is honest for PeritextTF (row caveated,
`oq:linspec`); the RGA_TF trivial-query gap is the closest thing in the suite to an
UNJUSTIFIED-as-presented `≈`.

### 6. Faithfulness caveats that are independent-but-of-the-wrong-spec
`inc_increases_acquired` (AWPQ) is a genuine arithmetic intent theorem
(`acquired += amount`) but specifies **summation**, whereas the paper's acquired
resolution is Most-Change-Win. It would catch an implementation bug against *its
own* summation spec, but that spec is not the paper's. Same family:
`is_acquired`/`is_priority`/`is_get_max` are independent specs of a non-paper
reading. These are not circular — they are honest about a modelled divergence
(`docs/aw-crpq-vs-paper.md`) — but they should not be cited as "the AW-priority-
queue is verified against the paper."

---

## Load-bearing summary

**Genuinely constrains behaviour (would catch a `do_`/`merge`/read bug):**
- The merge/`do_` headline theorems for the flat data types: OR-Set(×2)
  `add_wins_over_concurrent_remove` / `add_then_remove_extinguishes`, MVR
  `concurrent_writes_both_visible` / `sequential_write_supersedes_value`, AWPQ
  `add_wins_over_concurrent_rmv` / `inc_increases_acquired`, LWW
  `lookup_after_add_with_fresh_ts` / `remove_at_higher_ts_extinguishes`.
- RGA_TF `del_not_in_document`, `del_document_mem`, `document_convergent`, and
  **all** the SPOT literal executions — especially the refutation
  `del_can_reorder_survivors`.
- Flat Peritext Ex 1/2/3/5/7 positive, Ex 5/8 negative, `anchors_survive_tombstones`.
- The `≈` of every flat instance (`= `), plus MergeableQueue, PeritextTF
  (`peritextRender_congr`), and RGA_TF (`document_convergent`).

**Restates the implementation / does not constrain `do_` (currently presented as
if it were a guarantee, to varying degrees):**
- `latest_write_wins` (LWW) — `rfl`; named as the "headline." **The one to fix.**
- `ex8_link_descendant_visible_lt_endId` — a renamed constructor.
- MarkIntent `mark_*_in_recorded` / `mark_*_live` — restate `resolve`'s definition
  (but now honestly labeled "containment," so low-risk).
- All `*_convergent` theorems whose `≈ = =` — honest, but they are `≈→query-eq`
  plumbing, not intent; the names ("convergence at the read") do not overclaim.

**`≈` obligations that are vacuous / routed around the capstone:**
- RGA_TF signature `query := fun _ _ => ()` — the capstone's `query_congr` is
  vacuous; real content in `document_convergent`.
- PeritextTF — real content in `peritextRender_congr` (well-definedness only, and
  the *positional* correctness is the open `oq:linspec` leak).

**Silent on the risky axis (PART):**
- RGA_TF membership theorems say nothing about read **order** (the rehoming cost).
- Peritext MarkIntent containment says nothing about **preventing** backward drift.
- These two are the same shape as the `mark_no_leak` bug and are the read-side
  frontier `oq:linspec` names.

---

## Recommended actions (specify, do not implement)

1. **`latest_write_wins` (LWW).** Retract or re-gloss exactly as `mark_no_leak`
   was: either delete it (it is `rfl`) or rename to `lookup_unfold` / `lookup_def`
   and drop the "LWW-Element-Set headline" gloss. The real headline is already
   covered by the two ts-conditioned theorems.

2. **RGA_TF read order.** State an *independent* order spec that
   `del_can_reorder_survivors` violates as a visible failure — e.g. a
   `document`-vs-*intended-linearization* correspondence, or at minimum promote the
   SPOT refutation into the note as the explicit statement that
   membership-convergence does **not** imply order-preservation across `Del`. Wire
   `document_convergent` into the note/README as the actual `≈→read-eq` witness so
   the capstone's trivial signature query is not read as "the read converges."

3. **RGA_TF / PeritextTF `≈` presentation.** Add a one-line note at each capstone
   theorem that the signature `query` is trivial and the observable guarantee is
   `document_convergent` / `peritextRender_congr` respectively. (Prevents the
   "verified up to `≈`" ⇒ "read converges" misreading.)

4. **Peritext `in_span_visible` faithfulness.** Given the deleted
   `expand_contract_*` precedent, treat the encoding as a *hypothesis* to be
   pinned by literal oracles: add a small SPOT-style `native_decide` file that
   checks `in_span_visible` / `formatted_visible` against hand-authored expected
   outputs for the paper's Fig-1/Fig-6 scenarios (the analogue of
   `RGA_Tombstone_Free_SPOT.lean`). This is the independent check the current
   theorems lack.

5. **PeritextTF positional intent (the `oq:linspec` frontier).** The genuine
   intent theorem — a mark's span is exactly the surviving image of its original
   span, no backward leak — needs a **document-order** rehoming read against which
   the frozen-path leak is a visible failure. Specify that read (nearest surviving
   neighbour in reading order, gravity-aware) and its intent theorem; do not
   strengthen the existing containment theorems (no strengthening recovers it for
   the frozen-path design — established in `MarkIntent.lean` §4).

6. **MergeableQueue.** If the instance is meant to model Peepul's two-list queue,
   the coarse structural `≈` (two encodings, same `head?`) is the honest one and
   owes a `head?`-congruence lemma. Until then, state that the verified artifact is
   the *single-list canonical* queue (`≈ = =`), not the two-list Peepul queue.

7. **AWPQ acquired.** Label `inc_increases_acquired` / `is_acquired` /
   `is_priority` as summation-semantics (independent but non-paper), per
   `docs/aw-crpq-vs-paper.md`, wherever they are cited as verification against the
   paper.

---

## Counts (over the tabulated substantive theorems)

- **INDEPENDENT:** ~39 (flat-set/register/queue/MVR/AWPQ merge+`do_` headlines;
  RGA_TF `del_*` + `document_convergent` + 6 SPOT literals; Peritext Ex 1/2/3/5/7/8−
  + anchors-survive).
- **CIRCULAR / VACUOUS:** 6 substantive (`latest_write_wins`;
  `ex8_link_descendant_visible_lt_endId`; MarkIntent `mark_*_in_recorded` ×2,
  `mark_*_live` ×2) + 1 deleted precedent (`expand_contract_*`).
- **PARTIAL:** ~13 (RGA_TF membership ×3 — silent on order; MarkIntent
  `within_recorded_ancestry` ×2 — containment not stasis; Peritext endpoint/
  convergence ×6; AWPQ `innate_record_unique`; LWW `equal_ts_remove_wins`), plus
  the family of `≈=` `*_convergent` plumbing theorems (honest, non-intent).
- **`≈` JUSTIFIED:** all instances (every flat via `≈=`; BoundedCounter,
  BudgetCart, FWWRegister via `≈=`; MergeableQueue via canonical `=`; RGA_TF via
  `document_convergent`; PeritextTF via `peritextRender_congr`).
- **`≈` UNJUSTIFIED:** 0 strictly; but **RGA_TF's trivial signature query** makes
  the capstone `query_congr` vacuous, and both coarse-`≈` instances route the
  observable content around the capstone — the presentational risk flagged in
  action items 2–3.

**Single most important finding:** LWW's `latest_write_wins` is a `rfl` theorem
named as the datatype's headline guarantee — the exact `mark_no_leak` pattern
(machine-checked, self-referential, presented as a guarantee), and the only
remaining hard-circular theorem still glossed as intent. Everything else is either
genuinely independent, an honest convergence/containment bound, or already
correctly caveated.

---

## Outcomes (fixes applied)

The three circular/presentational findings presented as guarantees were corrected:

1. **LWW `latest_write_wins` → `lookup_def`** (rename + re-gloss): the `by rfl`
   unfolding is now labeled definitional, not an intent theorem; the crosswalk
   and README attribute the behavioural "latest write wins" property to
   convergence + the two ts-conditioned theorems
   (`lookup_after_add_with_fresh_ts`, `remove_at_higher_ts_extinguishes`).
2. **Peritext `ex8_link_descendant_visible_lt_endId`** (relabel, both CRDT and
   MRDT): given an honest docstring marking it a definitional constructor-helper;
   the Ex 8 guarantee is attributed to the genuine negative theorem
   `ex8_link_descendant_not_in_span_visible_of_wf` in the headers and crosswalk.
   (Symbol not renamed — it is a genuine helper feeding the real theorem, and
   renaming would churn the SPOT files for no semantic gain.)
3. **RGA-TF capstone**: docstring note that `query = Unit` makes its
   `≈`/`query_congr` content structural, and the observable reading guarantee is
   the separate `document_convergent`; read-*order* under deletion is only
   partially pinned (`del_can_reorder_survivors`).

The PARTIAL findings (RGA-TF membership silent on order; the various
`*_convergent` at `≈ = =`) are honest as stated and left as-is.
