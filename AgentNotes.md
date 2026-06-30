# Agent notes: RGA MRDT attempts

Read this before touching anything under `Sal/MRDTs/RGA*`. It indexes the
several RGA designs in this repo, records which one is proved, and points at the
per-directory `PLAN.md` files for detail.

## Authoritative, proved result

`Sal/MRDTs/RGA_Tombstone_Free/RGA_Tombstone_Free_MRDT.lean` — tombstone-free RGA with
path-carrying operations, flat-set state `map ℕ (ℕ × ℕ)` (id ↦ element, anchor).

- Deletion physically removes the id from the domain (`del` ⇒ `contains` drops
  it); there is no tombstone/graveyard set in the state.
- Concurrent safety comes from each op carrying its leaf's ancestor path;
  `resolve` climbs the path to the nearest live ancestor when the anchor/target
  was spliced away. This is what replaces tombstones.
- Proof status: builds clean (0 errors, 0 `sorry`). `rc_non_comm'` is proved,
  i.e. every operation pair commutes (`rc = Either` everywhere), via
  `insins_comm`, `insdel_comm`, and `deldel_comm`. Conditioned on well-formed
  histories (`accurate`: the op's claimed path is the true ancestor chain;
  `fresh_ts`; `contains s 0 = false`).
- Build check: `timeout 300 lake env lean Sal/MRDTs/RGA_Tombstone_Free/RGA_Tombstone_Free_MRDT.lean`

## The other RGA designs

| Variant | Where it lives | State | Status |
|---|---|---|---|
| RGA (original) | `Sal/MRDTs/RGA/` (main) | tombstone + read-side projection | committed, 0 sorry; different design, kept |
| RGA_Splice | branch `wip/rga-splice` | flat set, splice delete | predecessor of RGA_Tombstone_Free; `do_`-level non-commutation (`cond_comm_base`); superseded |
| RGA_Tree | branch `wip/rga-tree` | literal inductive tree | WIP, open sorries (MRDT 1, ReadSide 1, Refinement 6; not build-verified) |
| RGA_Tree_Path | branch `wip/rga-tree-path` | inductive tree + ghost path | early WIP, 17 sorry-bearing lines |

Design one-liners:
- RGA_Splice / RGA_Tombstone_Free: flat keyed records, OR-set survival on identities, merge
  reparents survivors by climbing the LCA ancestor chain. RGA_Tombstone_Free adds the op
  path so the single-replica `do_` also commutes.
- RGA_Tree: tree is the primary state, `Remove` excises and re-parents children
  one level up; merge recovers convergence with an LCA-driven orphan walk.
- RGA_Tree_Path: same tree state, each op additionally carries the full
  root-to-target path (ghost in practice: `do_` reads only the target).

## Git organization

main keeps only the proved/working designs:
- `Sal/MRDTs/RGA/` (original tombstone-based MRDT, already committed).
- `Sal/MRDTs/RGA_Tombstone_Free/RGA_Tombstone_Free_MRDT.lean` (proved tombstone-free path-carrying
  RGA).

The broken / superseded / WIP attempts are parked on branches (not lost):
- `wip/rga-splice`     — `Sal/MRDTs/RGA_Splice/RGA_Splice_MRDT.lean`
- `wip/rga-tree`       — `Sal/MRDTs/RGA_Tree/`
- `wip/rga-tree-path`  — `Sal/MRDTs/RGA_Tree_Path/`

To inspect or resume one: `git checkout <branch>`. To read a single file without
switching: `git show <branch>:<path>`.

## Resuming an attempt

- Build a single file (always wrap, the proofs are heavy):
  `timeout 300 lake env lean <path>.lean 2>&1 | tail -40`.
- Do not run `lake build` of a fresh target and do not use worktrees; build the
  specific file.
- "declaration uses sorry" in this repo can be a Z3-validated Blaster admit, not
  necessarily an open goal.
- Each design has a living `PLAN.md` in its directory; update it as work lands.
