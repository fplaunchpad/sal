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
- **Owed**: the binary delta code `C(δ) = 1^(L−1) 0 (δ − leading bit)`
  (entropy-optimal, the `embed-code` mint) as a second instance. Isolated
  arithmetic (Nat.size / same-length MSB comparison); nothing downstream
  changes when it lands.

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

### Layer 2 — reachability/wf (next)

- `coherent2`/`coherent3` as a reachability invariant: honest executions
  produce pairwise-coherent replicas (values immutable ⟹ agreement on shared
  ids). Establish preservation under `do_` and `merge` (the `wf` layer);
  `merge_assoc`-grade lemmas as needed by the engine.
- `merge_of_lca` correspondence: merge = fold of the delta (the design's
  canonicity, Thm 4 — state is a function of the event set; `≈` can be `=`).

### Layer 3 — read side + intent theorems

- Terminator embedding `key : coord → List ℕ` (bits ↦ {1,2}, ++ [3]) and its
  `LinearOrder` (Mathlib `List.Lex` linear order); read = sort desc by key.
- Chain-lex theorem: display order ≡ lex on birth chains (design Cor 2);
  needs unique decodability of prefix-free concatenations (coordinate
  injectivity across distinct ids).
- **L1 delete-order as a SPOT theorem** (the flat RGA provably fails it:
  `tombstone_free_violates_delete_order`); non-interleaving statement.

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
