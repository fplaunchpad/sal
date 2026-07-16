# Is the tombstone-free RGA payload-parametric?

**Feasibility verdict on generalizing the RGA element type from `ℕ` (character
codepoint) to an arbitrary `α`, so a richer payload (`char ⊎ mark-boundary`) is a
mere instantiation and convergence rides the existing capstone.**

Evidence base:
1. Element-use inventory across the core + the ~40-file conditioned chain.
2. A compiled probe (`RGA_Parametric_Probe.lean`) that re-proves the core
   convergence spine at an opaque `α`.
3. A typeclass / init-default audit.

---

## VERDICT: **PARAMETRIC-MODULO** — element fully opaque; needs only `[DecidableEq α]` + a default `α` for `init_st`

The RGA element is **never inspected**. Its identity is the map key (the
timestamp `ℕ`) and all ordering is by id/anchor (`ℕ`); the element rides in the
`.1` of the value pair `(α × ℕ)` purely as cargo. Every single use is one of:

- **COPIED** — moved from one record to another untouched (`do_ Ins` writes
  `(e, …)`; `do_ Del`'s reparent keeps `ea.1`; `merge`'s `elf` selects the whole
  element from whichever branch owns the id; `sel` destructurings), or
- **EQ-TESTED** — compared for equality as part of the whole-pair observational
  `eq`/`≈`, or in the CanonMatch clause `el s t = e` (a `Prop` equality; needs no
  runtime decidability).

There are **zero INSPECTED uses**: no arithmetic on the element, no ordering by
it, no casing on whether it is zero, no `deriving` beyond `DecidableEq`, and no
theorem whose statement or proof depends on the element being `ℕ` (the only
`ℕ`-pinned items in the whole development are `#eval`/`native_decide` *demo*
theorems in the core file, which are illustrations, not part of the convergence
proof).

The prior to verify — *"the RGA's identity is the node id, ordering is by id NOT
by element, so the element is fully opaque"* — is **CONFIRMED**, adversarially and
by compilation.

The two requirements that keep this from being unqualified `PARAMETRIC` are both
trivial and neither inspects the element:

| Requirement | Why | Cost |
|---|---|---|
| `[DecidableEq α]` | `deriving DecidableEq (app_op_t α)`; the framework's `dec_op := inferInstance` wants `DecidableEq (Op (app_op_t α))`, which reduces to `DecidableEq α` (the `ℕ × ℕ × …` and the `α × ℕ` wrappers are derivable). | Automatic for any concrete payload. |
| a default `α` for `init_st` | `init_st := const_on empty (default, 0)` must supply a *total* `mappings : ℕ → α × ℕ`, so it needs some `α`. The value is at the **empty** domain → **dead default, never read** by any well-formed state, `do_`, or `merge`. Supply via `[Inhabited α]` or an explicit default parameter. | One line; not a semantic dependency. |

Notably the observational `≈` does **not** need `DecidableEq α`: `RGAM.dec_state
:= Classical.propDecidable`, so state-equivalence decidability is classical, and
`eq` compares pairs at the `Prop` level.

---

## 1. Element-use inventory (COPIED / EQ-TESTED / INSPECTED)

### Core (`RGA_Tombstone_Free_MRDT.lean`)

State `concrete_st := map ℕ (ℕ × ℕ)`, `el s t := (sel s t).1`, `anc s t := (sel s t).2`.

| Site | Use | Class |
|---|---|---|
| `do_ (Ins e pre a)` → `upd s t (e, resolve s (a::pre))` | writes `e` into the record; `resolve` reads only anchors/ids | **COPIED** |
| `do_ (Del pre x)` → `iter_upd (fun _ ea => if ea.2 = x then (ea.1, tgt) else ea)` | tests `ea.2` (anchor); keeps `ea.1` (element) untouched | **COPIED** |
| `merge`'s `elf t := if contains l t then el l t else if contains a t then el a t else el b t` | selects the whole element by **id-containment**, never by element value | **COPIED** |
| `sel_doDel`: `(el s k, resolve s pre)` | element carried through a `Del` unchanged | **COPIED** |
| `el_doDel : el (do_ … Del) k = el s k` | states element invariance under `Del` | **EQ-TESTED (=copy)** |
| `deldel_comm`'s `hel` | two `Del` orders yield equal elements | **EQ-TESTED** |
| `eq a b := ∀ k, … contains a k → sel a k = sel b k` | whole-pair equality (incl. element) | **EQ-TESTED** |
| `mk` / `dump` (operational oracle) + `#eval`/`native_decide` demos | concrete `ℕ` codepoints (65, 89, …) | **`ℕ`-pinned, NOT in the proof** |

The `WfOp`/`accurate`/`fresh_ts`/`wf`/`IsAncPath`/`rc` layer never mentions the
element at all (they pattern-match `Ins _ pre a`).

INSPECTED count in core proof: **0**.

### Conditioned chain (`ConditionedMRDTs/MRDT_Instances/RGA_Rehoming/`, ~40 files)

- **18** `el`-reads total (word-boundary grep). Every one is either a merge
  `elf` selection, a `sel s k = (el s k, anc s k)` destructuring rewrite, a
  merge-congruence equality (`RGA_EqQuotient`/`RGA_MergeCong`: merge results
  agree when inputs `≈`), or the CanonMatch clause `el s t = e`. All COPY/EQ.
- Every `Ins e …` binding uses `e` only to write `upd s t (e, …)` (copy) or
  passes it to a lemma that ignores it (`wfOpQ_ins_of_genQ`, where `WfOpGenQ`
  pattern-matches `Ins _ pre a`). In `CanonMatch`/`insertedIn`, `e` is
  existentially bound and equated (`∃ r e p a, (k,r,.Ins e p a) ∈ F`,
  `el s t = e`) — EQ, never inspected.
- The **strengthened invariants that *do* use `<`, `= 0`, `≠`** —
  `WfOpQ` (`resolve s pre < x`, `resolve s (a::pre) < t`), `WfOpGenQ`
  (`x ≠ 0 ∧ ∀ c ∈ pre, c < x`), `id_mono` (`anc s t < t`), `wf`, `RgaInv` —
  operate **exclusively on ids/anchors/timestamps (`ℕ`)**, never the element.
- No `deriving` beyond `DecidableEq`. No `native_decide`/`decide` over states.
  No `Inhabited`/`Zero`/`Ord`/`LinearOrder`/`Repr` requirement on the element
  anywhere.

INSPECTED count in conditioned chain: **0**.

---

## 2. The probe — what actually compiled at `α`

`Sal/ConditionedMRDTs/Development/RGA_Parametric_Probe.lean` transcribes the core
**verbatim** (only element-type annotations changed) with
`variable {α : Type} [DecidableEq α]`, `[Inhabited α]` for init, and
`concrete_st α := map ℕ (α × ℕ)`.

**Result: builds clean (`lake env lean …`, ~3.4 s), 0 errors, 0 `sorry`.** The
only diagnostics are `unusedSectionVars` linter warnings reporting that
`[DecidableEq α]` is *unused* in ~11 of the lemmas — direct evidence that most of
the spine does not even need decidable equality on the element.

Definitions that typechecked at `α`: `concrete_st`, `el`, `anc`, `init_st`,
`resolve`, `app_op_t α` (`deriving DecidableEq` → `[DecidableEq α] → DecidableEq
(app_op_t α)`), `op_t α`, `do_`, `climb_aux`, `climb`, `merge`, `rc`, `eq`, `wf`,
`IsAncPath`, `accurate`, `fresh_ts`, `commutes_with'`, `doDelPF`.

Theorems that typechecked at `α` (proofs copied unchanged):

- `climb_fixpoint`, `merge_idem` — **merge convergence core**
- `ins_path_free`, `del_path_free`, `del_prefix_dispensable` — **path-freedom**
- The full resolve/`IsAncPath` algebra: `resolve_dom_eq`, `resolve_upd_notMem`,
  `upd_comm`, `eq_symm`, `resolve_cons_eq`, `resolve_dead_head`,
  `resolve_live_head`, `isAncPath_resolve`, `isAncPath_self`, `isAncPath_mem`,
  `contains_ne_zero`
- The full `Del` algebra: `contains_doDel`, `sel_doDel`, `resolve_doDel`,
  `el_doDel`, `anc_doDel`, `IsAncPath_unique`, `resolve_filter_ne`,
  `isancpath_resolve_self_filter`, `collapse`
- **The three commutation lemmas** `insins_comm`, `insdel_comm`, `deldel_comm`
- **`rc_non_comm'`** — the load-bearing commutation VC (all pairs commute,
  `rc = Either` everywhere), and `cond_comm_base`, `no_rc_chain`.

Axiom audit at `α` (kernel-clean, no `sorryAx`):

```
'rc_non_comm'' depends on axioms: [propext, Classical.choice, Quot.sound]
'merge_idem'   depends on axioms: [propext, Classical.choice, Quot.sound]
'deldel_comm'  depends on axioms: [propext, Classical.choice, Quot.sound]
```

Nothing failed. No proof reached for a `ℕ`-specific fact about the element. The
`#eval`/`native_decide` demos were dropped (they are ℕ illustrations, and
`native_decide` cannot evaluate at an opaque `α`).

**Scope of the evidence.** The probe *compiles* the entire core spine at `α`
(decisive). The ~40-file conditioned chain is *argued* parametric by the
exhaustive inventory above (no element inspection exists to break), not
recompiled — recompiling it is the refactor itself (§4).

---

## 3. Typeclass + init audit

- **`[DecidableEq α]`** — needed, once, for `deriving DecidableEq (app_op_t α)`
  and the framework's `dec_op`. `DecidableEq (α × ℕ)` and
  `DecidableEq (ℕ × ℕ × app_op_t α)` are *derived*, not separate asks. No hidden
  `DecidableEq`-of-state requirement: `dec_state` is `Classical.propDecidable`.
- **Default element for `init_st`** — `const_on empty (default, 0)` needs a total
  `mappings`, hence some `α`. This is the *only* place an `α` value is
  constructed rather than copied. It sits at the empty domain and is **never read
  from any well-formed state, `do_`, or `merge`** (`merge`'s `elf` and every
  read are gated on `contains … = true`, always false at the empty init).
  Satisfy with `[Inhabited α]` or an explicit `default : α` parameter to
  `RGACore`.
- **No other requirement.** No `Inhabited`/`Zero`/`Ord`/`LinearOrder`/`Repr` on
  the element is used anywhere. The element has **no distinguished value** in any
  proof (there is no "the element 0" case — only "the id/anchor 0" root
  sentinel, which is `ℕ`).

---

## 4. Effort estimate for the full `RGACore α` refactor (~40 files)

**Character: mechanical transcription. Essentially zero new proof obligations.**

The refactor mirrors the `ORSetCore` payload-parametrization already done in this
repo (memo + ORSetCore + Product raw kit). Per file:

- add `variable {α : Type} [DecidableEq α]` (and `[Inhabited α]` where `init_st`
  is constructed);
- `concrete_st → concrete_st α`, `app_op_t → app_op_t α`, `op_t → op_t α`,
  `RGAM → RGAM α`, `RGACondSig' → RGACondSig' α`;
- retype element binders `(e : ℕ) → (e : α)` in signatures;
- `init_st := const_on empty (default, 0)`.

Proof bodies are **unchanged** — the probe demonstrates this for the entire core
spine, and the inventory shows the conditioned lemmas touch the element only in
copy/eq positions, which are transcription-stable.

- **Line-delta:** several hundred small, local edits (type annotations +
  per-file `variable`/`namespace` lines); no proof rewrites. Net new *logic*: one
  line (the `init_st` default).
- **Risk:** low. The three real risk items are all cosmetic/trivial:
  1. `init_st` default (one line, above).
  2. The core file's `#eval`/`native_decide` demos are `ℕ`-pinned — relocate them
     to a thin `RGA α := ℕ` instantiation module or delete.
  3. `unusedSectionVars` linter noise from the many element-agnostic lemmas
     (`omit`/`set_option`, or just accept the warnings).
- The metatheory framework (`GenericEqQuotient`, `GoodConfig3H`, `Configuration`,
  the honest-delivery machinery, all VC discharges) is **already generic over the
  signature `D`** and only ever sees `app_op_t α` as an opaque `AppOp` with
  `DecidableEq` — it carries `α` without change.

This is *engineering* (the last-20%-transcription tail), **not research**: there
is no open question hiding in it. The research content (convergence, the
criss-cross rehoming semantics, RA-linearizability up to `≈`) is invariant under
the payload and is inherited, not re-proved.

---

## 5. Consequence for Peritext

**The fused tombstone-free Peritext design is L0 payload reuse.**

Instantiate `α := char ⊕ boundary` (equivalently an inductive
`inductive PeritextElt | ch : Char → PeritextElt | mark : MarkId → Bool →
PeritextElt`, the `Bool` = open/close), where a mark boundary is an ordinary
**node in the RGA sequence**:

- `DecidableEq α` holds (sum/inductive of decidable pieces) — the one real
  typeclass, discharged automatically.
- A default `α` exists trivially (`Inhabited (char ⊕ boundary)`), covering
  `init_st`.
- The **entire convergence capstone rides the existing proof by instantiation**:
  `rc_non_comm'` (all pairs commute), merge convergence, and RA-linearizability
  up to `≈` (`rga_RA_linearizable_honest`) hold at `α := char ⊕ boundary` because
  their proofs never look at the payload. Marks-as-boundary-nodes get the same
  id-ordered, rehoming/climb-based convergence as characters — for free.

The only Peritext-specific work not covered by payload reuse is the **read-side**
interpretation of boundary nodes into mark ranges (which char lies inside which
`open…close` span). That is a *query* over the already-converged sequence — it
carries **no new convergence VC** (consistent with the read-side independence
being audited in `READSIDE_INDEPENDENCE_AUDIT.md`). In the *fused* design the mark
structure *is* the sequence structure, so sequence convergence *is* mark
convergence; there is no separate `MarkStore` merge to prove (contrast the
composed `RGA ⊗ MarkStore` route).

**Bottom line:** fused tombstone-free Peritext is cheap — an `α`-instantiation of
an already-proved parametric core, not a from-scratch datatype. The cost is the
mechanical `RGACore α` refactor (§4), not new metatheory.
