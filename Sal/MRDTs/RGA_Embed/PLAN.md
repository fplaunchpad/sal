# RGA_Embed — the embedded-chain RGA mechanization plan

Design + pen-and-paper proofs: `whiteboard/embed-code-design.pdf`.
Python-validated artifact: `whiteboard/litmus/embed_tree.py` — battery clean
except one-sided L19; DAG PBT 120/120 + 300/300; **lockstep read-equal with
the published tombstoned RGA 120/120**. Retention arc that forced the design:
`whiteboard/retention-countermodel.pdf`.

The **absolute-coordinate model**: state = `map ℕ (α × List Bool)`, each id's
value the concatenation of prefix-free codewords along its birth chain — an
immutable birth constant. Del carries no path and rehomes nothing; merge never
climbs; Ins carries the anchor-coordinate prefix **for the proof alone**
(rc = Either commutation totality; ghost on honest states).

Build: `lake env lean Sal/MRDTs/RGA_Embed/<file>.lean` (no `timeout` on this
Mac — run bare). `lake build Sal.MRDTs.RGA_Embed.<Module>` to produce oleans.

## Status

### Layer 0 — code kernel: `Embed_Code.lean` ✅ (0 errors, 0 sorry, kernel-clean)

- `OrderedPrefixCode` — the two properties the datatype consumes (monotone
  wrt `List.Lex (· < ·)` on `List Bool`; prefix-free). All datatype theorems
  are parametric in the structure.
- `unaryCode` instance proved (`enc d = replicate d true ++ [false]`) — the
  Lean twin of the unary mint `I(t)`; unblocks everything downstream.
- ✅ **binary delta code landed** (`Embed_Code_Binary.lean`, kernel-clean):
  `binEnc d = 1^(size d − 1) ++ 0 ++ bitsW (size d − 1) d`, with
  `bitsW` (fixed-width big-endian bit fields), `bitsW_lt` (same-width
  fields compare like the numbers — the MSB lemma, via `testBit_top`),
  `bitsW_inj`, header algebra (`header_lt`, `header_not_prefix`),
  `binEnc_mono`, `binEnc_prefixFree`, `binEnc_length = 2·size − 1` (the
  entropy bound, exactly), and `binaryCode : OrderedPrefixCode`.
  Cross-validated against the Python `C` by `decide` (C(1)/C(2)/C(3)/C(5)).
- ✅ **flipped Elias-δ landed** (`Embed_Code_EliasDelta.lean`, kernel-clean;
  task #77, order-coding note I5): `dEnc d = binEnc (size d) ++
  bitsW (size d − 1) d` — `binEnc` reused as the *header* on the length
  field, glued by `bitLt_append_of_not_prefix` (strict Lex + not-prefix
  survives appends). `dEnc_length = size d + 2·size (size d) − 2`
  (= log δ + O(log log δ)), `dEnc_mono`, `dEnc_prefixFree`,
  `eliasDeltaCode : OrderedPrefixCode`. Capstone inherited with zero new
  proof content: `embed_ra_linearizable3_eliasDelta`
  (`MRDT_Instances/EmbedRGA/EmbedRGA_EliasDelta.lean`, kernel-clean; both
  EmbedRGA files now wired into the `MRDT_Instances` umbrella). Honest
  `decide` battery: the flip loses at δ∈{2,3}∪[8,15], ties {4..7}∪{16..31},
  wins from δ=32 — matching the I1 measurement (traces: wash; the value is
  the theorem).
  All three instances are drop-in: every datatype theorem is code-parametric.

### Layer 1 — MRDT kernel: `RGA_Embed_MRDT.lean` ✅ (0 errors, 0 sorry, kernel-clean)

Mirrors the proved flat RGA's statement shapes
(`Sal/MRDTs/RGA/RGA_Tombstone_Free_MRDT.lean`), radically smaller because
`do_` on Ins is state-independent (no resolve/rehome/climb algebra):

- `insins_comm` (needs only `t1 ≠ t2`), `insdel_comm` (needs `t_ins ≠ x`,
  obtained from `accurate del` + `fresh_ts ins`), `deldel_comm`
  (unconditional) — all commutations **to `eq`**, sel-halves close by `rfl`.
- `rc_non_comm'` — rc = Either honest for every distinct pair.
- `merge_idem` (no wf needed); `merge_comm` under `coherent2` (shared ids
  agree — the immutability invariant).
- `ins_prefix_ghost` — on accurate ops, `do_` = the state-reading `do_run`:
  the prefix is droppable at runtime, indispensable in the VCs.

### Layer 2 — coherence closure ✅ / canonicity (open)

DONE (`RGA_Embed_MRDT.lean`, kernel-clean): `opVal`/`opCoherent`;
`do_coherent` (ops preserve coherence with coherent bystanders) and
`merge_coherent` (merges never invent values) — the immutability invariant
is closed under both transitions; execution-level induction to "all honest
replicas pairwise coherent" belongs to the framework hookup.

OPEN: `merge_of_lca` correspondence — merge = fold of the delta (design
Thm 4 canonicity: state is a function of the event set; `≈` can be `=`).

### Layer 3 — read side ✅ (stability + SPOT) / chain-lex (open)

DONE (`RGA_Embed_ReadSide.lean`):
- `key` (terminator embedding), `keyLt`/`keyLe`, `before` (strict display).
- `sel_do_stable`, `sel_merge_stable`(+`_right`) — value immutability.
- **`before_do_stable`** — S2 step stability, AXIOM-FREE; at `Del` this is
  general delete-order preservation, the clause the flat RGA refutes.
- **`before_merge_stable`(+`_right`)** — S4 pairwise display stability at
  merges (the adopted contract), from value immutability alone. No property
  of the code is used anywhere in the stability layer.
- `document` (mergeSort by descending key over an explicit id list) + SPOT
  by `native_decide`: the flat RGA's reorder witness with the OPPOSITE
  verdict (`del_preserves_order` [6,5,8]→[6,8] where flat reads [8,6]);
  litmus L1 through `do_` ([2,1,3]→[2,3]); the merge read [10,6,22,16];
  both credential-countermodel topologies converging to [10,8,22,16].

DONE (`RGA_Embed_ChainLex.lean`, kernel-clean):
- keyLt strict-total-order algebra (irrefl/asymm/trans/total) + keyLe facts.
- document characterization: `document_perm` (the live filter), `mem_document`,
  `document_pairwise_le` (sorted), **`document_pairwise_before`** (on
  `distinctCoords` states every displayed pair is strictly `before`).
- birth chains: `coordOf`, `enc_ne_nil`, **`coordOf_inj`** (unique
  decodability of prefix-free concatenations — distinct chains have
  distinct coordinates), `chainState_distinctCoords`.
- `lex_first_diff`/`enc_first_diff` (monotone + prefix-free ⟹ every
  codeword comparison is decided at a genuine first differing bit — the
  `nil` escape of `List.Lex` never fires).
- `chainBefore` (ancestors first; larger delta at first divergence — the
  RGA order of the birth tree), `chainBefore_total`, and **the chain-lex
  theorem `display_iff_chainBefore`**: the key comparison of coordinates
  computes exactly `chainBefore`; state-level `before_iff_chainBefore`.

DONE (same file, kernel-clean):
- **chainState closure**: `chainState_ins` (accurate insert + the birth
  record `chainOf t = chainOf a ++ [t−a]` preserves it), `chainState_del`
  (values untouched), `chainState_merge` (values copied) — "every live
  coordinate is a positive chain's coordinate" is closed under all three
  transitions, same shape as the coherence closure.
- **Non-interleaving** (`subtree_convex`): anything displayed between two
  members of a subtree (a coordinate prefix) is in the subtree — the
  litmus g-column as lex convexity (`keyLt_prefix_convex`, code-free) +
  the terminator argument (`sym_prefix_of_key`: a symbol-prefix of a key
  cannot reach past the coordinate, since 3 is outside the alphabet).

Layers 0–3 are now COMPLETE.

### Layer 4 — the conditioned capstone (STARTED)

**Route decided and recorded**: the MERGEABLE-QUEUE route
(`MRDT_Instances/MergeableQueue/MergeableQueue.lean` is the template,
§-for-§). Rationale: the queue's `JoinLemma3At` hook needs canonical
states unique per event set (`Shesha_Join_Refuted` kills it otherwise);
embed's canonicity (design Thm 4) supplies exactly that. NOT the flat
24-VC engine (same-id ins/del does not commute unconditionally — embed is
outside the schema like RGA_TF) and NOT the RGA_TF 55-file chain
(unnecessary: no rehoming exists).

§1 DONE (`Sal/ConditionedMRDTs/MRDT_Instances/EmbedRGA/EmbedRGA.lean`,
builds clean): `EOp`/`ERec`/`EState` (canonical sorted association list —
the framework needs `DecidableEq State`, so the instance uses the document
itself, not the function-based map), `eInsert` (sorted insertion),
`eUpdate` (idempotent-guarded insert / filter delete), `eMerge2` (sorted
2-merge), `eMergeL` (OR-set survival re-canonicalized),
`E Γ : ConditionedMRDTSig` (rc = Either, Inv/applicable trivial per the
queue convention), first mem-lemmas.

§2 DONE (sorted algebra + canonical-form extensionality, builds clean):
`ESorted` (strictly desc by key); `mem_eInsert`/`eInsert_sorted`/
`eUpdate_sorted` (fold steps stay sorted); **`esorted_ext`** — strictly
sorted lists with the same members are EQUAL (why the sorted list is a
canonical state); `mem_eMerge2`/`eMerge2_sorted` (functional induction via
`eMerge2.induct`); `eMergeL_sorted` (merge of canonical inputs is
canonical, given key-injectivity — supplied on chain-generated states by
`coordOf_inj`).

§3 DONE (kernel-clean): `eFold`/`eFold_snoc`; `eIsIns`/`eRecOf`/
`eInsIds`/`eDels` + mem/append lemmas; `EWf` (ins_nodup, del_late,
keys_inj — the last supplied on honest histories by chain-generation +
`coordOf_inj`, §5's job) with prefix closure; `e_fold_rec_sub` (record
provenance, unconditioned); `e_fold_guard_free` (the insert guard never
fires under WF); `e_fold_sorted`; **`e_fold_mem`** (fold membership is
ORDER-FREE: ins present ∧ id never deleted); **`e_fold_canon`** — any two
WF enumerations of one event set fold to the SAME state. The mechanized
canonicity theorem (design Thm 4); the property the join hook lives on.

OWED:
- §3 `EWf` (fresh nonzero ins ids; del targets previously inserted;
  accurate prefixes — reuse chainState vocabulary) + **`e_fold_canon`**:
  fold of any well-formed enumeration = `eCanonList` — THE canonicity
  theorem; needs eInsert/filter/sort commutation algebra (sorted-insert
  into sorted stays sorted — keyLt total order from ChainLex — plus
  `coordOf_inj` for no-key-ties via chain-generation).
- §5 `EHonestCore` (mirror QHonestCore: ts-uniqueness + del-after-ins
  vis + accurate generation) + `e_wf_of_enum`.
- §6 `e_join_at : JoinLemma3At (E Γ) C` — with canonicity this should be
  the SHORT half: merge of canonical states of ev₁, ev₂ over LCA ev₀ =
  canonical state of ev₁ ∪ ev₂ (set algebra on survivors + sorted-merge
  = sort of union), witness enumeration = any loOn-respecting
  interleaving (mirror `q_respects_transfer`).
- §7 `EReach := HonestReach (E Γ) EHonest trivial` → `e_goodConfig3` →
  capstone `embed_ra_linearizable3 : IsRALinearizable3 C`.
- §8 `eApplicable` (ins: anchor live + π = its coordinate + a < ts;
  del: target live) discharges honesty (`eHonest_of_applicable`,
  `eHonest_of_genHonest`) — this is where `accurate` from the map model
  reappears as the generation discipline.
- After the capstone: intent theorems transported to the instance
  (delete-order, non-interleaving via the map-model bridge or directly),
  then the RGA† read-equivalence (the compaction theorem) as its own
  arc.

### Layer 4 — capstones

- Conditioned instance in `Sal/ConditionedMRDTs/MRDT_Instances/` (flat route
  via FlatGeneric_Bridge if the 24-VC engine accepts the shape, else the
  RGA_TombstoneFree conditioned route with HonestDelivery). ✅ DONE
  (`EmbedRGA/EmbedRGA.lean` §§1–9 + `EmbedRGA_EliasDelta.lean`).
- The equivalence target: `read ∘ embed = read ∘ RGA†` on honest executions
  (the compaction theorem — converts the design into a statement about the
  published RGA).

### Layer 5 — RGA† read-equivalence (task #75) — IN PROGRESS, recon done 2026-07-15

Tested form: Python lockstep read-equality at every apply/merge/read,
120/120 (`contest_tree.py`). Lean recon findings:

- **RGA† = `Sal/MRDTs/RGA_with_tombstones`**: state = (insert-record set,
  tombstone set); `do_` = set-add / tombstone-add, so the fold is an
  event-set function up to permutation (both components are unions) —
  the cheap first lemma.
- **RGA†'s read is relational**: `visible` (inserted ∧ not tombstoned),
  `after_of` (birth edge), `visible_lt` (inductive: `parent_child` |
  `sibling` by id `>` | `left_descendant_of_sibling` | `trans`) — the RGA
  traversal order on the FULL birth forest (constructors don't require
  visibility — good: matches chain-lex on chains with dead prefixes),
  filtered by `visible` at read. Sibling tiebreak is id `>` = ts `>`
  (ids are timestamps in both models) = embed's larger-first.
- **Embed's read**: `document` = sort by descending coordinate = chain-lex
  (`display_iff_chainBefore`, ChainLex).

Plan (`RGA_Embed_ReadEquiv.lean`, new; imports ChainLex + RGA† ReadSide):
1. Op translation `EOp → RGA† op_t` (Ins x π a ↦ insert-after, π DROPPED —
   the ghost earns its name); `rgaFold ρ`; permutation-invariance lemma.
2. Edge bridge: `after_of (rgaFold ρ) c p ↔ ins c after p ∈ ρ ↔` the
   embed chainState birth edge — both trees are THE birth tree of ρ.
3. Membership bridge: `visible (rgaFold ρ) t ↔ contains (embed fold) t`
   (both = inserted ∖ deleted; embed side exists as `e_fold_mem` /
   model-layer closures).
4. **The meat** — order equivalence, for a ≠ b in ρ's birth tree, under
   honesty (anchors present-and-earlier ⟹ chains well-defined, unique ts):
   `visible_lt (rgaFold ρ) a b ↔ chainBefore (chainOf a) (chainOf b)`.
   Soundness (→): induct on the `visible_lt` derivation — `parent_child`
   = prefix rule; `sibling` = first-difference-newer; `left_descendant_of_
   sibling` = prefix ∘ first-difference; `trans` = chainBefore transitivity
   (proved in ChainLex). Completeness (←): case-split `chainBefore` —
   proper prefix ⟹ a chain of `parent_child`+`trans`; first difference at
   the shared anchor p ⟹ the two divergent children are siblings under p
   ⟹ `sibling`/`left_descendant_of_sibling` + `trans` down to a and b.
5. Capstone: `document (embed fold ρ)` = THE `visible_lt`-sorted
   enumeration of RGA†'s visible ids (uniqueness from chainBefore totality
   + strictly-sorted extensionality) — read-for-read, as sequences.

Risks: the repo `set`/`mem` function-set API in the RGA† fold lemmas
(mechanical but fiddly); completeness needs the divergence-point witness
(build by induction on the shared-prefix length); both models must consume
the SAME op list — the translation in step 1 is where del/ins arity and
the ghost π are reconciled.

## Gotchas

- `omit [DecidableEq α] in` goes BEFORE a theorem's doc comment, not between
  docstring and `theorem`.
- `del` on this repo's `map` removes only from the domain (mappings
  untouched) — sel-halves of del commutations are `rfl` after `simp only`;
  a trailing `grind` errors with "no goals".
- The linter flags unused `[DecidableEq α]` on every theorem that never
  selects on α — most of them, since values are opaque pairs here.
- `decide` cannot reduce the function-based `map` (closures block kernel
  reduction) — SPOT verdicts must use `native_decide` (repo convention;
  adds `Lean.ofReduceBool`/`trustCompiler`, as in the flat RGA's SPOT).
