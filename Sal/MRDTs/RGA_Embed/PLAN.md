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
  Both instances are drop-in: every datatype theorem is code-parametric.

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

OPEN: non-interleaving statement; chainState as a reachability invariant
(mints write prefix ++ codeword — connect `accurate` histories to
`chainState`).

### Layer 4 — capstones

- Conditioned instance in `Sal/ConditionedMRDTs/MRDT_Instances/` (flat route
  via FlatGeneric_Bridge if the 24-VC engine accepts the shape, else the
  RGA_TombstoneFree conditioned route with HonestDelivery).
- The equivalence target: `read ∘ embed = read ∘ RGA†` on honest executions
  (the compaction theorem — converts the design into a statement about the
  published RGA).

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
