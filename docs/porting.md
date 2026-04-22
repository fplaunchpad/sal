# Porting an op-based CRDT to Sal

Sal verifies **state-based** CRDTs and MRDTs: each replica holds a state `Σ`, applies operations via a `do_ : Σ → op → Σ` function, and reconciles concurrent updates via a `merge` that joins two states in a lattice (two-way for CRDTs, three-way with an LCA for MRDTs). Op-based CRDTs, by contrast, describe a delivery algorithm — `prepare(state, op)` generates a message, `effect(state, msg)` applies it, and causal delivery is left to the network layer. The two formulations are equivalent in expressive power but the state-based form is what Sal's 24 VCs are written against.

This document describes the recipe I've been using to port op-based CRDTs into the framework, distilled from the recent Peritext, RGA, Bounded Counter, Add-Win CRPQ, and Shopping Cart ports.

## The five-step translation

### 1. Pick `Σ` as "what a replica needs to merge"

Op-based CRDTs describe a delivery algorithm; the state-based port needs a concrete lattice. Two common shapes:

- **Easy case — grow-only collection of ops.** If delivering the same set of ops always produces the same observable state, just let `Σ` be the set of delivered ops keyed by OpId. Merge is set union. Examples in this suite: `Grow_Only_Set_CRDT`, `Grow_Only_Multiset_CRDT`, `LWW_Element_Set_CRDT`.
- **Projected case — digest the op log.** When the observable state only depends on a summary of the log, project to the summary. Examples:
  - `RGA_CRDT` keeps `map OpId (char, afterId, deleted)` rather than the raw insert/remove stream.
  - `Peritext_CRDT` keeps one such RGA for the text plus a flat `set AnchorAttachment` for marks, where `AnchorAttachment := OpId × Bool × MarkOp`.
  - `Bounded_Counter_CRDT` keeps a PN-counter plus a sparse `map (rid × rid) Nat` of quota transfers.

The smaller `Σ` is, the easier the 24 VCs are. Carrying extra metadata that isn't load-bearing for the spec — vector clocks, full op histories — will make grind work harder than it has to.

### 2. Fold `prepare` + `effect` into `do_`

Op-based CRDTs give you two hooks; state-based gives you one. Inline the generated op into the state update:

```lean
def do_ (s : concrete_st) (o : op_t) : concrete_st :=
  match o with
  | (ts, rid, app_op_t.Insert c afterId) => ...
  | (ts, rid, app_op_t.Remove id)        => ...
```

OpIds are `ℕ × ℕ` (timestamp × replica id) by convention — see any existing file. The framework assumes OpIds are unique across the system, which is what op-based CRDTs with Lamport or vector-clock naming already give you.

### 3. `merge` is the lattice join on `Σ`

Usually pointwise union / max / concat of components:

```lean
def merge (a b : concrete_st) : concrete_st :=
  (union (Prod.fst a) (Prod.fst b),       -- set of insert OpIds
   union (Prod.snd a) (Prod.snd b))       -- set of delete OpIds
```

For MRDTs, `merge` takes three arguments `(l a b)` where `l` is the last-common-ancestor; the extra information is what lets MRDTs express causality directly. Causality that op-based CRDTs carry in vector clocks has to be re-encoded in `Σ` itself — either by embedding the causal predecessor in each op (RGA's `afterId` field) or by keeping the delivery order implicit in OpId ordering.

### 4. Define `rc`

`rc o1 o2` says whether `o1 ; o2` and `o2 ; o1` are semantically equivalent:

- `rc_res.Either` — order doesn't matter.
- `rc_res.Fst_then_snd` — `o1` must precede `o2`.

For most op-based CRDTs `rc` is derivable from the op pair syntactically: ops touching disjoint state commute (`Either`); ops on the same key with LWW / max / union semantics dictate the verdict (`Fst_then_snd` if the later op wins).

### 5. `by sal` on the 24 VCs, then iterate

The 24 theorems are uniformly shaped. Copy the skeleton from an existing file of similar shape (registers from a register, sequences from RGA, set-of-ops from Grow-Only Set) and replace the types. Most VCs will close on first `by sal`; the ones that don't get the treatment in the "proof-closing playbook" below.

## Recurring judgment calls

### Don't nest `set` inside a map value

Sal's `set α := α → Bool` representation is designed so grind can discharge membership symbolically — but only as a **top-level** state component. A value of type `map K (set V)` forces grind to prove function equality via `funext`, which typically doesn't terminate on the 24 VCs.

Flatten:

```lean
-- bad: map anchor (set MarkOp)
-- good: set (anchor × MarkOp)  -- equivalently: set AnchorAttachment
```

Peritext is the clearest case in this suite: with the naive nested representation, 5 of 24 VCs were stuck; the flat representation closes all 24 with the same proof skeleton as the other CRDTs.

### Concrete-enough state

Carrying metadata that isn't load-bearing for the spec — full op histories, per-field vector clocks, timestamps that never appear in any `rc` decision — will make both `do_`'s match cases and the grind proofs larger than needed. Prune `Σ` to what actually affects `merge` and observable behavior.

### Decidability everywhere

Every type appearing in `Σ` needs `DecidableEq`. Products of `Nat`, `Bool`, enumerations, and inductive-constructor types with decidable fields are fine. Avoid:

- Function-typed state components (except the one `α → Bool` inside `set`).
- Quotient types.
- Subtypes gated on propositions that aren't decidable.

If you find yourself needing one of these, reconsider the `Σ` decomposition.

### One op, one replica

`do_` fires on one op on one replica. Anything "global" — total counter value, longest-prefix invariants — has to be derivable from `Σ` on each replica independently. Op-based papers are often sloppy about this distinction; Sal forces you to pin it down.

## Proof-closing playbook

When `by sal` doesn't close a VC, reach for these in order:

1. **Per-component decomposition.** If `Σ` is a product of components and `eq` is a conjunction of per-component equalities, split the goal and discharge each component independently:
   ```lean
   := by
     intro h
     rcases o1 with ⟨_, _, _ | _ | _ | _⟩ <;> rcases o2 with ⟨_, _, _ | _ | _ | _⟩ <;>
       refine ⟨?_, ?_, ?_, ?_⟩ <;> intro k <;>
       simp +decide [*] at h ⊢
     all_goals grind
   ```
   This is kernel-verifiable (no Blaster), so it's the preferred first fallback. Used throughout Peritext, Shopping Cart, Bounded Counter.
2. **Flatten nested sets.** If a component is `map K (set V)`, refactor `Σ` to `set (K × V)`. See the Peritext insight above.
3. **Aristotle-generated intermediate lemma.** For VCs where the top-level goal is unwieldy but an auxiliary fact would make it trivial, ask Aristotle for the lemma, prove it, and `exact`/`apply` it. `LWW_Map_CRDT` uses this technique with `merge_do_lex_max` and `lem_0op_aux` — the main theorem then becomes a one-liner.
4. **TODO sorry with diagnostic.** If you're stuck, leave a `sorry` with the failing `grind` state / tactic output pasted into the comment. Easier to pick back up; also useful signal for what the next framework improvement should target. See `f336cb5` for the template.

## Worked reference

For a recent minimal example of a **set-of-ops** port, see `Sal/CRDTs/Grow_Only_Set_CRDT.lean` — `Σ` is just a `set OpId`, `do_` adds, `merge` unions. For a **projected-log** port with causality embedded in ops, see `Sal/CRDTs/RGA_CRDT.lean`. For the **nested-to-flat refactor** story, compare the git history of `Sal/CRDTs/Peritext_CRDT.lean` at commits `7b435af` → `19dcef1` → `3243ae6`.
