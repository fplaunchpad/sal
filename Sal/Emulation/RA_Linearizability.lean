import Sal.Emulation.CRDT_TS

/-!
# RA-linearizability for state-based CRDTs

Specialises the Sal paper's Def. lin (lin.tex §3.2) to the 2-way-merge
CRDT transition system in `CRDT_TS.lean`. For every active replica,
its head state must be obtained by applying some permutation of its
seen events, respecting the linearization relation `lo_C`.

The bridge theorem "24 VCs ⟹ RA-linearizable" is stated at the bottom
as `ra_linearizable_of_vcs`, stubbed with `sorry`. Mechanizing its proof
is the main remaining task of this phase.
-/

namespace Sal.Emulation

open CRDTSig

section
variable (D : CRDTSig)

/-- Apply a sequence of events to a state, left-to-right.
Paper notation: $\pi(\sigma)$. -/
def applySeq (s : D.State) (π : List (Op D.AppOp)) : D.State :=
  π.foldl D.update s

variable {D}

/-- Appending lemma for `applySeq`: extending a sequence by one event
is the same as applying the event to the final state. -/
theorem applySeq_append_single (s : D.State) (π : List (Op D.AppOp))
    (e : Op D.AppOp) :
    applySeq D s (π ++ [e]) = D.update (applySeq D s π) e := by
  simp [applySeq, List.foldl_append]

/-- Conditional commutativity (lin.tex §3.2, Definition).
`e ⇄^{e''} e'` means swapping `e` and `e'` is observationally invisible
to any future event sequence ending in `e''`. -/
def conditionallyCommute (e e' e'' : Op D.AppOp) : Prop :=
  ∀ (s : D.State) (π : List (Op D.AppOp)),
    D.update (applySeq D (D.update (D.update s e') e) π) e''
    = D.update (applySeq D (D.update (D.update s e) e') π) e''

/-- App-ops `o, o'` conditionally commute with respect to `o''` if every
triple of events at those ops do. -/
def appOpsCondCommute (o o' o'' : D.AppOp) : Prop :=
  ∀ e e' e'' : Op D.AppOp,
    e.op = o → e'.op = o' → e''.op = o'' →
    conditionallyCommute e e' e''

variable (D)

/-- `rc-non-comm(D)` (lin.tex §3.2). Every pair of non-commuting app-ops
is ordered by `rc` in at least one direction. -/
def rcNonComm : Prop :=
  ∀ o₁ o₂ : D.AppOp,
    ¬ D.appOpsCommute o₁ o₂ ↔
      (∀ e₁ e₂ : Op D.AppOp, e₁.op = o₁ → e₂.op = o₂ →
         D.rc e₁ e₂ = RcRes.Fst_then_snd ∨ D.rc e₂ e₁ = RcRes.Fst_then_snd)

/-- `cond-comm(D)` (lin.tex §3.2). Whenever `rc` orders `o₁ → o₂` and
`o₂` doesn't commute with some `o₃`, then `o₁, o₂` conditionally commute
w.r.t. `o₃`. Rules out the `lo`-cycle pathology of
Fig. conditional-commutativity. -/
def condComm : Prop :=
  ∀ o₁ o₂ o₃ : D.AppOp,
    (∀ e₁ e₂ : Op D.AppOp, e₁.op = o₁ → e₂.op = o₂ →
       D.rc e₁ e₂ = RcRes.Fst_then_snd) →
    ¬ D.appOpsCommute o₂ o₃ →
    appOpsCondCommute o₁ o₂ o₃

variable {D}

/-- The linearization relation `lo_C` (lin.tex Definition: Linearization
relation).

```
  e₁ -lo_C-> e₂
  ⟺  (e₁ -vis(C)-> e₂  ∧  ¬(e₁ ⇄ e₂))
  ∨  (e₁ ||_C e₂  ∧  e₁ -rc-> e₂
       ∧  ¬ ∃ e₃. e₂ -vis(C)-> e₃  ∧  ¬(e₂ ⇄ e₃))
```

First disjunct: a visible non-commuting pair is ordered by `vis`.
Second: concurrent non-commuting pairs are ordered by `rc`, unless `e₂`
is already "overwritten" by a later non-commuting `e₃`. -/
def lo (C : Configuration D) (e₁ e₂ : Op D.AppOp) : Prop :=
  (C.vis e₁ e₂ ∧ ¬ D.commutes e₁ e₂)
  ∨ ( ¬ C.vis e₁ e₂ ∧ ¬ C.vis e₂ e₁
      ∧ D.rc e₁ e₂ = RcRes.Fst_then_snd
      ∧ ¬ ∃ e₃, C.vis e₂ e₃ ∧ ¬ D.commutes e₂ e₃ )

/-- `π` is a permutation-list of the set `E`: every event in `π` is in
`E`, every event in `E` is in `π`, and `π` has no duplicates. -/
def listPermOf {α : Type} (π : List α) (E : Set α) : Prop :=
  π.Nodup ∧ ∀ a, a ∈ π ↔ a ∈ E

/-- `π` respects `R`: if `R b a` then `b` does not come strictly before
`a` in `π`. Matches the paper's "π extends R".

Note: `R` need not be transitive (Sal's `lo` is not), so we cannot use
`List.Sorted` — we state the constraint elementwise via `List.Pairwise`. -/
def respects {α : Type} (π : List α) (R : α → α → Prop) : Prop :=
  π.Pairwise (fun a b => ¬ R b a)

/-- **RA-linearizability of a configuration** (Sal paper's Def. lin,
specialised to the 2-way-merge CRDT TS).

For every active replica `r` with head state `s` and event set `E`,
there is a permutation `π` of `E` that respects `lo_C` and witnesses
`π(σ₀) = s`. -/
def IsRALinearizable (C : Configuration D) : Prop :=
  ∀ (r : Replica) (s : D.State) (E : Set (Op D.AppOp)),
    C.N r = some s → C.L r = some E →
    ∃ π : List (Op D.AppOp),
      listPermOf π E ∧ respects π (lo C) ∧ applySeq D D.init π = s

/-- **RA-linearizability of an execution.** Every configuration along
the execution is RA-linearizable. -/
def IsRALinearizableExec
    (init : Configuration D)
    (τ : List (Label D × Configuration D)) : Prop :=
  IsRALinearizable init ∧ ∀ lc, lc ∈ τ → IsRALinearizable lc.2

/-! ## The 24 VCs

Transcribed from `Sal/CRDTs/Grow_Only_Set_CRDT.lean`, which is the
canonical enumeration. Field names match the theorem names in that file
so the correspondence is mechanical.

Helpers `distinctOps` (fresh timestamps) and `differentReplicas` inline
the boolean predicates `distinct_ops` / `get_rid o1 != get_rid o2` used
in the existing Sal code as Prop-level conjunctions. -/

/-- Two events have distinct timestamps. Sal paper enforces global
uniqueness, so this always holds between any two events in an
execution. -/
def distinctOps {D : CRDTSig} (o₁ o₂ : Op D.AppOp) : Prop :=
  o₁.time ≠ o₂.time

/-- Two events originated at different replicas. -/
def differentReplicas {D : CRDTSig} (o₁ o₂ : Op D.AppOp) : Prop :=
  o₁.rep ≠ o₂.rep

/-- The 24 VCs of the Sal paper. Each field is the parametric,
signature-level version of the corresponding per-CRDT theorem in
`Sal/CRDTs/*.lean`. -/
structure SatisfiesVCs (D : CRDTSig) : Prop where
  /-- rc-nonComm semantic characterization: at distinct timestamps and
  replicas, `rc = Either` iff the two events commute. -/
  rc_non_comm :
    ∀ o₁ o₂ : Op D.AppOp,
      distinctOps o₁ o₂ → differentReplicas o₁ o₂ →
      (D.rc o₁ o₂ = RcRes.Either ↔ D.commutes o₁ o₂)

  /-- rc is not transitively ordering: no three events form an
  `rc = Fst_then_snd` chain. -/
  no_rc_chain :
    ∀ o₁ o₂ o₃ : Op D.AppOp,
      distinctOps o₁ o₂ → distinctOps o₂ o₃ →
      ¬ (D.rc o₁ o₂ = RcRes.Fst_then_snd ∧
         D.rc o₂ o₃ = RcRes.Fst_then_snd)

  /-- Base case for conditional commutativity: if `rc o₁ o₂ =
  Fst_then_snd` and `o₂` doesn't commute with `o₃`, then `o₁` and `o₂`
  can be swapped provided `o₃` follows. -/
  cond_comm_base :
    ∀ (s : D.State) (o₁ o₂ o₃ : Op D.AppOp),
      distinctOps o₁ o₂ → distinctOps o₂ o₃ → distinctOps o₁ o₃ →
      D.rc o₁ o₂ = RcRes.Fst_then_snd →
      D.rc o₂ o₃ ≠ RcRes.Either →
      D.update (D.update (D.update s o₁) o₂) o₃
        = D.update (D.update (D.update s o₂) o₁) o₃

  /-- `merge` is commutative. -/
  merge_comm : ∀ a b : D.State, D.merge a b = D.merge b a

  /-- `merge` is idempotent. -/
  merge_idem : ∀ s : D.State, D.merge s s = s

  /-- Base step of the bottom-up 2-op induction: for independent ops on
  `init`, pushing `o₁` through `merge` is sound. -/
  base_2op :
    ∀ o₁ o₂ : Op D.AppOp,
      (D.rc o₂ o₁ = RcRes.Fst_then_snd ∨ D.rc o₂ o₁ = RcRes.Either) →
      differentReplicas o₁ o₂ → distinctOps o₁ o₂ →
      D.merge (D.update D.init o₁) (D.update D.init o₂)
        = D.update (D.merge D.init (D.update D.init o₂)) o₁

  /-- LCA induction step for the 2-op bottom-up rule: extends the
  hypothesis from `l` to `do l ol`. -/
  ind_lca_2op :
    ∀ (l : D.State) (o₁ o₂ ol : Op D.AppOp),
      (D.rc o₂ o₁ = RcRes.Fst_then_snd ∨ D.rc o₂ o₁ = RcRes.Either) →
      differentReplicas o₁ o₂ →
      distinctOps o₁ o₂ → distinctOps o₁ ol → distinctOps o₂ ol →
      D.merge (D.update l o₁) (D.update l o₂)
        = D.update (D.merge l (D.update l o₂)) o₁ →
      D.merge (D.update (D.update l ol) o₁) (D.update (D.update l ol) o₂)
        = D.update (D.merge (D.update l ol) (D.update (D.update l ol) o₂)) o₁

  /-- Right-side base case for a single `ob` interposed. -/
  inter_right_base_2op :
    ∀ (a b : D.State) (o₁ o₂ ob ol : Op D.AppOp),
      (D.rc o₂ o₁ = RcRes.Fst_then_snd ∨ D.rc o₂ o₁ = RcRes.Either) →
      differentReplicas o₁ o₂ →
      D.rc ob ol = RcRes.Fst_then_snd → differentReplicas ob ol →
      distinctOps o₁ o₂ → distinctOps o₁ ob → distinctOps o₁ ol →
      distinctOps o₂ ob → distinctOps o₂ ol → distinctOps ob ol →
      D.merge (D.update a o₁) (D.update b o₂)
        = D.update (D.merge a (D.update b o₂)) o₁ →
      D.merge (D.update a o₁) (D.update (D.update b ob) o₂)
        = D.update (D.merge a (D.update (D.update b ob) o₂)) o₁ →
      D.merge (D.update (D.update a ol) o₁) (D.update (D.update b ol) o₂)
        = D.update (D.merge (D.update a ol) (D.update (D.update b ol) o₂)) o₁ →
      D.merge (D.update (D.update a ol) o₁)
              (D.update (D.update (D.update b ob) ol) o₂)
        = D.update (D.merge (D.update a ol)
                            (D.update (D.update (D.update b ob) ol) o₂)) o₁

  /-- Left-side base case, symmetric to `inter_right_base_2op`. -/
  inter_left_base_2op :
    ∀ (a b : D.State) (o₁ o₂ ob ol : Op D.AppOp),
      D.rc o₂ o₁ = RcRes.Fst_then_snd →
      D.rc ob ol = RcRes.Fst_then_snd →
      differentReplicas o₂ o₁ → differentReplicas ob ol →
      distinctOps o₁ o₂ → distinctOps o₁ ob → distinctOps o₁ ol →
      distinctOps o₂ ob → distinctOps o₂ ol → distinctOps ob ol →
      D.merge (D.update (D.update a ol) o₁) (D.update (D.update b ol) o₂)
        = D.update (D.merge (D.update a ol) (D.update (D.update b ol) o₂)) o₁ →
      D.merge (D.update (D.update (D.update a ob) ol) o₁)
              (D.update (D.update b ol) o₂)
        = D.update (D.merge (D.update (D.update a ob) ol)
                            (D.update (D.update b ol) o₂)) o₁

  /-- Inductive step for the right-side interposition, extending by
  one more op `o`. -/
  inter_right_2op :
    ∀ (a b : D.State) (o₁ o₂ ob ol o : Op D.AppOp),
      (D.rc o₂ o₁ = RcRes.Fst_then_snd ∨ D.rc o₂ o₁ = RcRes.Either) →
      differentReplicas o₁ o₂ →
      D.rc ob ol = RcRes.Fst_then_snd → differentReplicas ob ol →
      (D.rc o ob ≠ RcRes.Either ∨ D.rc o ol = RcRes.Fst_then_snd) →
      distinctOps o₁ o₂ → distinctOps o₁ ob → distinctOps o₁ ol →
      distinctOps o₁ o →
      distinctOps o₂ ob → distinctOps o₂ ol → distinctOps o₂ o →
      distinctOps ob ol → distinctOps ob o → distinctOps ol o →
      differentReplicas o ol →
      D.merge (D.update (D.update a ol) o₁)
              (D.update (D.update (D.update b ob) ol) o₂)
        = D.update (D.merge (D.update a ol)
                            (D.update (D.update (D.update b ob) ol) o₂)) o₁ →
      D.merge (D.update (D.update a ol) o₁)
              (D.update (D.update (D.update (D.update b o) ob) ol) o₂)
        = D.update (D.merge (D.update a ol)
                      (D.update (D.update (D.update (D.update b o) ob) ol) o₂)) o₁

  /-- Inductive step for the left-side interposition. -/
  inter_left_2op :
    ∀ (a b : D.State) (o₁ o₂ ob ol o : Op D.AppOp),
      D.rc o₂ o₁ = RcRes.Fst_then_snd →
      D.rc ob ol = RcRes.Fst_then_snd →
      differentReplicas o₂ o₁ → differentReplicas ob ol →
      (D.rc o ob ≠ RcRes.Either ∨ D.rc o ol = RcRes.Fst_then_snd) →
      distinctOps o₁ o₂ → distinctOps o₁ ob → distinctOps o₁ ol →
      distinctOps o₁ o →
      distinctOps o₂ ob → distinctOps o₂ ol → distinctOps o₂ o →
      distinctOps ob ol → distinctOps ob o → distinctOps ol o →
      differentReplicas o ol →
      D.merge (D.update (D.update (D.update a ob) ol) o₁)
              (D.update (D.update b ol) o₂)
        = D.update (D.merge (D.update (D.update a ob) ol)
                            (D.update (D.update b ol) o₂)) o₁ →
      D.merge (D.update (D.update (D.update (D.update a o) ob) ol) o₁)
              (D.update (D.update b ol) o₂)
        = D.update (D.merge (D.update (D.update (D.update a o) ob) ol)
                            (D.update (D.update b ol) o₂)) o₁

  /-- LCA-side 2-op inductive step. -/
  inter_lca_2op :
    ∀ (a b : D.State) (o₁ o₂ ol : Op D.AppOp),
      (D.rc o₂ o₁ = RcRes.Fst_then_snd ∨ D.rc o₂ o₁ = RcRes.Either) →
      differentReplicas o₁ o₂ →
      distinctOps o₁ o₂ → distinctOps o₁ ol → distinctOps o₂ ol →
      (∃ o, D.rc o ol = RcRes.Fst_then_snd) →
      D.merge (D.update (D.update a ol) o₁) (D.update b ol)
        = D.update (D.merge (D.update a ol) (D.update b ol)) o₁ →
      D.merge (D.update a o₁) (D.update b o₂)
        = D.update (D.merge a (D.update b o₂)) o₁ →
      D.merge (D.update (D.update a ol) o₁) (D.update (D.update b ol) o₂)
        = D.update (D.merge (D.update a ol) (D.update (D.update b ol) o₂)) o₁

  /-- 2-op right-hand inductive step: extend by one more op `o₂'` on b. -/
  ind_right_2op :
    ∀ (a b : D.State) (o₁ o₂ o₂' : Op D.AppOp),
      D.rc o₂ o₁ = RcRes.Fst_then_snd →
      differentReplicas o₁ o₂ →
      distinctOps o₁ o₂ → distinctOps o₁ o₂' → distinctOps o₂ o₂' →
      D.merge (D.update a o₁) (D.update b o₂)
        = D.update (D.merge a (D.update b o₂)) o₁ →
      D.merge (D.update a o₁) (D.update (D.update b o₂') o₂)
        = D.update (D.merge a (D.update (D.update b o₂') o₂)) o₁

  /-- 2-op left-hand inductive step: extend by one more op `o₁'` on a. -/
  ind_left_2op :
    ∀ (a b : D.State) (o₁ o₂ o₁' : Op D.AppOp),
      (D.rc o₂ o₁ = RcRes.Fst_then_snd ∨ D.rc o₂ o₁ = RcRes.Either) →
      differentReplicas o₁ o₂ →
      distinctOps o₁ o₂ → distinctOps o₁ o₁' → distinctOps o₂ o₁' →
      D.merge (D.update a o₁) (D.update b o₂)
        = D.update (D.merge a (D.update b o₂)) o₁ →
      D.merge (D.update (D.update a o₁') o₁) (D.update b o₂)
        = D.update (D.merge (D.update a o₁') (D.update b o₂)) o₁

  /-- Base case for the 1-op bottom-up induction: merge with `init`
  on the right commutes with `do init o1` on the left. -/
  base_1op :
    ∀ o₁ : Op D.AppOp,
      D.merge (D.update D.init o₁) D.init
        = D.update (D.merge D.init D.init) o₁

  /-- LCA induction for the 1-op rule. -/
  ind_lca_1op :
    ∀ (l : D.State) (o₁ ol : Op D.AppOp),
      distinctOps o₁ ol →
      D.merge (D.update l o₁) l = D.update (D.merge l l) o₁ →
      D.merge (D.update (D.update l ol) o₁) (D.update l ol)
        = D.update (D.merge (D.update l ol) (D.update l ol)) o₁

  /-- Right-side base case for the 1-op rule. -/
  inter_right_base_1op :
    ∀ (a b : D.State) (o₁ ob ol : Op D.AppOp),
      D.rc ob ol = RcRes.Fst_then_snd → differentReplicas ob ol →
      distinctOps o₁ ob → distinctOps o₁ ol → distinctOps ob ol →
      (D.rc ob o₁ = RcRes.Fst_then_snd →
         D.merge (D.update a o₁) (D.update b ob)
           = D.update (D.merge a (D.update b ob)) o₁) →
      D.merge (D.update (D.update a ol) o₁) (D.update b ol)
        = D.update (D.merge (D.update a ol) (D.update b ol)) o₁ →
      D.merge (D.update (D.update a ol) o₁) (D.update (D.update b ob) ol)
        = D.update (D.merge (D.update a ol) (D.update (D.update b ob) ol)) o₁

  /-- Left-side base case for the 1-op rule. -/
  inter_left_base_1op :
    ∀ (a b : D.State) (o₁ ob ol : Op D.AppOp),
      D.rc ob ol = RcRes.Fst_then_snd → differentReplicas ob ol →
      distinctOps o₁ ob → distinctOps o₁ ol → distinctOps ob ol →
      D.merge (D.update (D.update a ol) o₁) (D.update b ol)
        = D.update (D.merge (D.update a ol) (D.update b ol)) o₁ →
      D.merge (D.update (D.update (D.update a ob) ol) o₁) (D.update b ol)
        = D.update (D.merge (D.update (D.update a ob) ol)
                            (D.update b ol)) o₁

  /-- Right-side inductive step for the 1-op rule. -/
  inter_right_1op :
    ∀ (a b : D.State) (o₁ ob ol o : Op D.AppOp),
      D.rc ob ol = RcRes.Fst_then_snd → differentReplicas ob ol →
      (D.rc o ob ≠ RcRes.Either ∨ D.rc o ol = RcRes.Fst_then_snd) →
      distinctOps o₁ ob → distinctOps o₁ ol → distinctOps o₁ o →
      distinctOps ob ol → distinctOps ob o → distinctOps ol o →
      differentReplicas o ol →
      D.merge (D.update (D.update a ol) o₁) (D.update (D.update b ob) ol)
        = D.update (D.merge (D.update a ol) (D.update (D.update b ob) ol)) o₁ →
      D.merge (D.update (D.update a ol) o₁)
              (D.update (D.update (D.update b o) ob) ol)
        = D.update (D.merge (D.update a ol)
                      (D.update (D.update (D.update b o) ob) ol)) o₁

  /-- Left-side inductive step for the 1-op rule. -/
  inter_left_1op :
    ∀ (a b : D.State) (o₁ ob ol o : Op D.AppOp),
      D.rc ob ol = RcRes.Fst_then_snd → differentReplicas ob ol →
      (D.rc o ob ≠ RcRes.Either ∨ D.rc o ol = RcRes.Fst_then_snd) →
      distinctOps o₁ ob → distinctOps o₁ ol → distinctOps o₁ o →
      distinctOps ob ol → distinctOps ob o → distinctOps ol o →
      differentReplicas o ol →
      D.merge (D.update (D.update (D.update a ob) ol) o₁) (D.update b ol)
        = D.update (D.merge (D.update (D.update a ob) ol)
                            (D.update b ol)) o₁ →
      D.merge (D.update (D.update (D.update (D.update a o) ob) ol) o₁)
              (D.update b ol)
        = D.update (D.merge (D.update (D.update (D.update a o) ob) ol)
                            (D.update b ol)) o₁

  /-- LCA-side inductive step for the 1-op rule. -/
  inter_lca_1op :
    ∀ (a b : D.State) (o₁ ol oi : Op D.AppOp),
      distinctOps o₁ ol → distinctOps o₁ oi → distinctOps ol oi →
      (∃ o, D.rc o ol = RcRes.Fst_then_snd) →
      (∃ o, D.rc o oi = RcRes.Fst_then_snd) →
      D.merge (D.update (D.update a oi) o₁) (D.update b oi)
        = D.update (D.merge (D.update a oi) (D.update b oi)) o₁ →
      D.merge (D.update (D.update a ol) o₁) (D.update b ol)
        = D.update (D.merge (D.update a ol) (D.update b ol)) o₁ →
      D.merge (D.update (D.update (D.update a oi) ol) o₁)
              (D.update (D.update b oi) ol)
        = D.update (D.merge (D.update (D.update a oi) ol)
                            (D.update (D.update b oi) ol)) o₁

  /-- 1-op left-hand inductive step: extend by one more op `o₁'` on a. -/
  ind_left_1op :
    ∀ (a b : D.State) (o₁ o₁' ol : Op D.AppOp),
      distinctOps o₁ o₁' → distinctOps o₁ ol → distinctOps o₁' ol →
      D.merge (D.update a o₁) (D.update b ol)
        = D.update (D.merge a (D.update b ol)) o₁ →
      D.merge (D.update (D.update a o₁') o₁) (D.update b ol)
        = D.update (D.merge (D.update a o₁') (D.update b ol)) o₁

  /-- 1-op right-hand inductive step: extend by one more op `o₂'` on b. -/
  ind_right_1op :
    ∀ (a b : D.State) (o₂ o₂' ol : Op D.AppOp),
      distinctOps o₂ o₂' → distinctOps o₂ ol → distinctOps o₂' ol →
      D.merge (D.update a ol) (D.update b o₂)
        = D.update (D.merge (D.update a ol) b) o₂ →
      D.merge (D.update a ol) (D.update (D.update b o₂') o₂)
        = D.update (D.merge (D.update a ol) (D.update b o₂')) o₂

  /-- Zero-op closure: a single op applied on both sides pushes out of
  `merge`. -/
  lem_0op :
    ∀ (a b : D.State) (ol : Op D.AppOp),
      D.merge (D.update a ol) (D.update b ol)
        = D.update (D.merge a b) ol

/-! ### Bridge theorem — base case -/

/-- The initial configuration is RA-linearizable: only replica `0` is
active, its state is `σ₀`, and its event set is empty, so `π = []`
witnesses RA-lin. -/
theorem initConfig_RA_lin (D : CRDTSig) : IsRALinearizable (initConfig D) := by
  intro r s E hN hL
  by_cases hr : r = 0
  · subst hr
    simp [initConfig] at hN hL
    refine ⟨[], ⟨List.nodup_nil, fun a => ?_⟩, List.Pairwise.nil, ?_⟩
    · constructor
      · intro h; exact (List.not_mem_nil h).elim
      · intro h; rw [← hL] at h; exact h.elim
    · simpa [applySeq] using hN
  · simp [initConfig, hr] at hN

/-! ### Bridge theorem — trivial-step cases

These are factored as lemmas that take the *ingredients* of a step
(equations about `N`, `L`, `vis`) rather than a `Step` hypothesis.
That avoids reconstructing the constructor in the main induction and
makes Lean happy about matching implicit arguments. -/

/-- `CreateReplica` preserves RA-lin: the new replica has state `σ₀`
and no events, so `π = []` works; other replicas are unchanged. -/
theorem RA_lin_preserved_createReplica
    {D : CRDTSig} {C C' : Configuration D} {r : Replica}
    (hN   : C'.N = updateRep C.N r D.init)
    (hL   : C'.L = updateRep C.L r ∅)
    (hvis : C'.vis = C.vis)
    (hRA : IsRALinearizable C) :
    IsRALinearizable C' := by
  intro r' s E hN' hL'
  rw [hN] at hN'
  rw [hL] at hL'
  by_cases hr' : r' = r
  · -- Fresh replica: state is `D.init`, events are empty.
    subst hr'
    simp [updateRep] at hN' hL'
    refine ⟨[], ⟨List.nodup_nil, fun a => ?_⟩, List.Pairwise.nil, ?_⟩
    · constructor
      · intro h; exact (List.not_mem_nil h).elim
      · intro h; rw [← hL'] at h; exact h.elim
    · simpa [applySeq] using hN'
  · -- Old replica: fall back to the IH witness; `lo` is unchanged
    -- since `vis` is unchanged.
    simp [updateRep, hr'] at hN' hL'
    obtain ⟨π, hperm, hresp, heq⟩ := hRA r' s E hN' hL'
    refine ⟨π, hperm, ?_, heq⟩
    have hlo : lo C' = lo C := by unfold lo; rw [hvis]
    rw [hlo]; exact hresp

/-! ### Bridge theorem — Apply case -/

/-- **Monotonicity of `lo` under Apply.** If the new visibility equals
the old plus a set of edges `(x, e)` for `x ∈ ev`, then on any pair
`(p, q)` with `p, q ≠ e`, `lo C'` implies `lo C`.

Intuition: the new edges only terminate at `e`, and the only way a pair
involving elements other than `e` can be affected by `lo` is via the
"∃ e₃" witness in the second disjunct. More witnesses in C' can only
*falsify* the `¬ ∃ e₃ …` conjunct, shrinking `lo`. -/
theorem lo_shrink_under_apply
    {D : CRDTSig} {C C' : Configuration D}
    {e : Op D.AppOp} {ev : Set (Op D.AppOp)}
    (hvis : C'.vis = fun a b => C.vis a b ∨ (ev a ∧ b = e))
    {p q : Op D.AppOp} (_hp : p ≠ e) (hq : q ≠ e)
    (h : lo C' p q) : lo C p q := by
  unfold lo at h ⊢
  rw [hvis] at h
  rcases h with ⟨hv, hnc⟩ | ⟨hnv₁, hnv₂, hrc, hnex⟩
  · -- First disjunct of `lo C' p q`: vis_C' p q ∧ ¬commutes p q.
    rcases hv with hvC | ⟨_, hqe⟩
    · exact Or.inl ⟨hvC, hnc⟩
    · exact absurd hqe hq
  · -- Second disjunct.
    refine Or.inr ⟨?_, ?_, hrc, ?_⟩
    · intro hvC; exact hnv₁ (Or.inl hvC)
    · intro hvC; exact hnv₂ (Or.inl hvC)
    · rintro ⟨e₃, hvC, hnc3⟩
      exact hnex ⟨e₃, Or.inl hvC, hnc3⟩

/-- `Apply` preserves RA-lin. For the replica that applied the op,
append the fresh event to its IH witness (shown below via `π_old ++ [e]`).
For other replicas, the IH witness still works because `lo` only shrinks
(per `lo_shrink_under_apply`).

NOTE: the full mechanized proof is TODO (see PLAN.md step 3). The
overall structure here reflects the paper's argument, with three
`sorry` gaps — all guarded by stated lemmas that we know how to
discharge on paper. Top-level shape is correct and downstream files
can already call this lemma. -/
theorem RA_lin_preserved_apply
    {D : CRDTSig} {C C' : Configuration D}
    {t : Timestamp} {r : Replica} {o : D.AppOp}
    {s : D.State} {ev : Set (Op D.AppOp)}
    (h_s : C.N r = some s)
    (h_ev : C.L r = some ev)
    (h_fresh_t : ∀ e', e' ∈ C.events → Op.time e' ≠ t)
    (hN   : C'.N = updateRep C.N r (D.update s (t, r, o)))
    (hL   : C'.L = updateRep C.L r (ev ∪ {(t, r, o)}))
    (hvis : C'.vis = fun a b => C.vis a b ∨ (ev a ∧ b = (t, r, o)))
    (hRA : IsRALinearizable C) :
    IsRALinearizable C' := by
  intro r' s' E' hN' hL'
  rw [hN] at hN'
  rw [hL] at hL'
  by_cases hr' : r' = r
  · -- Replica r: witness is `π_old ++ [e]` where `e = (t, r, o)`.
    rcases hr' with rfl
    simp [updateRep] at hN' hL'
    obtain ⟨π_old, hperm_old, hresp_old, heq_old⟩ := hRA r' s ev h_s h_ev
    -- `e` not in `ev` (freshness), hence not in `π_old`.
    have he_notin_ev : (t, r', o) ∉ ev := by
      intro hev
      exact h_fresh_t (t, r', o) ⟨r', ev, h_ev, hev⟩ rfl
    have he_notin_old : (t, r', o) ∉ π_old := by
      intro hmem
      exact he_notin_ev ((hperm_old.2 _).mp hmem)
    refine ⟨π_old ++ [(t, r', o)], ?_, ?_, ?_⟩
    · -- listPermOf
      refine ⟨?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hperm_old.1, by simp, ?_⟩
        intro a ha hae hae_mem heq
        rw [List.mem_singleton] at hae_mem
        subst hae_mem
        exact he_notin_old (heq ▸ ha)
      · intro a
        rw [List.mem_append, List.mem_singleton, ← hL']
        constructor
        · rintro (h | rfl)
          · exact Or.inl ((hperm_old.2 a).mp h)
          · exact Or.inr rfl
        · rintro (h | rfl)
          · exact Or.inl ((hperm_old.2 a).mpr h)
          · exact Or.inr rfl
    · -- respects
      rw [respects, List.pairwise_append]
      refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
      · -- Pairwise on π_old (shrink under apply)
        refine hresp_old.imp_of_mem ?_
        intro a b ha hb hab hlo'
        have ha_ne : a ≠ (t, r', o) := fun h => he_notin_old (h ▸ ha)
        have hb_ne : b ≠ (t, r', o) := fun h => he_notin_old (h ▸ hb)
        exact hab (lo_shrink_under_apply hvis hb_ne ha_ne hlo')
      · -- Frontier: ∀ a ∈ π_old, ∀ f ∈ [e], ¬ lo C' f a.
        intro a ha f hf
        rw [List.mem_singleton] at hf
        subst hf
        intro hlo
        have ha_ev : ev a := (hperm_old.2 a).mp ha
        unfold lo at hlo
        rw [hvis] at hlo
        rcases hlo with ⟨hv, _⟩ | ⟨_, hnv₂, _, _⟩
        · rcases hv with hvC | ⟨_, ha_eq⟩
          · -- vis_C (t, r', o) a: requires a "vis only over C.events"
            -- invariant on reachable configurations. Left as sorry;
            -- see PLAN.md step 3 note.
            sorry
          · exact he_notin_old (ha_eq ▸ ha)
        · exact hnv₂ (Or.inr ⟨ha_ev, rfl⟩)
    · -- applySeq
      rw [applySeq_append_single, heq_old]; exact hN'
  · -- Other replica: state and events unchanged; `lo` shrinks on π.
    simp [updateRep, hr'] at hN' hL'
    obtain ⟨π, hperm, hresp, heq⟩ := hRA r' s' E' hN' hL'
    refine ⟨π, hperm, ?_, heq⟩
    -- respects π (lo C'): each x ∈ π has x ∈ E' ⊆ C.events, so by
    -- freshness `Op.time x ≠ t`, hence `x ≠ (t, r, o)`.
    have h_fresh_in_pi : ∀ x ∈ π, x ≠ (t, r, o) := by
      intro x hx hxe
      have hx_in_E : x ∈ E' := (hperm.2 x).mp hx
      have hx_in_C : x ∈ C.events := ⟨r', E', hL', hx_in_E⟩
      have : Op.time x = t := by simp [hxe, Op.time]
      exact h_fresh_t x hx_in_C this
    refine hresp.imp_of_mem ?_
    intro a b ha hb hab hlo'
    exact hab (lo_shrink_under_apply hvis
      (h_fresh_in_pi b hb) (h_fresh_in_pi a ha) hlo')

/-! ### Bridge theorem — Merge case (TODO)

The most complex case. Given RA-lin witnesses `π₁` for `r₁`'s state and
`π₂` for `r₂`'s state, build a witness for `merge(s₁, s₂)` at event
set `ev₁ ∪ ev₂`. Follows the bottom-up linearization template (paper
§3.3 and appendix §A.2–A.4); uses the 24 VCs. Scaffolded here so
downstream files can already depend on the lemma signature. -/
theorem RA_lin_preserved_merge
    {D : CRDTSig} {C C' : Configuration D} (hVC : SatisfiesVCs D)
    {r₁ r₂ : Replica} {s₁ s₂ : D.State}
    {ev₁ ev₂ : Set (Op D.AppOp)}
    (h_s₁  : C.N r₁ = some s₁) (h_s₂  : C.N r₂ = some s₂)
    (h_ev₁ : C.L r₁ = some ev₁) (h_ev₂ : C.L r₂ = some ev₂)
    (hN   : C'.N = updateRep C.N r₁ (D.merge s₁ s₂))
    (hL   : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
    (hvis : C'.vis = C.vis)
    (hRA : IsRALinearizable C) :
    IsRALinearizable C' := by
  sorry

open LabeledTS in
/-- **Bridge theorem (Sal paper, bottom-up linearization).** If a CRDT
`D` satisfies the 24 VCs, every configuration reachable in `S_D` is
RA-linearizable.

Proof plan (lin.tex §3.3 + appendix.tex §A.2): induction on the
execution. CreateReplica and Query are immediate; Apply extends the
linearization by one event; Merge is the load-bearing case. The four
per-rule preservation lemmas above assemble the induction. -/
theorem ra_linearizable_of_vcs
    (D : CRDTSig) (hVC : SatisfiesVCs D)
    (C : Configuration D)
    (hReach : (labeledTS D).ReachableFrom (initConfig D) C) :
    IsRALinearizable C := by
  induction hReach with
  | refl => exact initConfig_RA_lin D
  | tail _ hs ih =>
    obtain ⟨ℓ, hstep⟩ := hs
    cases hstep with
    | createReplica _ _ hN hL hvis =>
      exact RA_lin_preserved_createReplica hN hL hvis ih
    | apply h_s h_ev h_fresh_t _ hN hL hvis =>
      exact RA_lin_preserved_apply h_s h_ev h_fresh_t hN hL hvis ih
    | merge h_s₁ h_s₂ h_ev₁ h_ev₂ _ hN hL hvis =>
      exact RA_lin_preserved_merge hVC h_s₁ h_s₂ h_ev₁ h_ev₂ hN hL hvis ih
    | query _ _ => exact ih

end

end Sal.Emulation
