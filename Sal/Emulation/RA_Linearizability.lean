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

open LabeledTS in
/-- **Bridge theorem (Sal paper, bottom-up linearization).** If a CRDT
`D` satisfies the 24 VCs, every configuration reachable in `S_D` is
RA-linearizable.

Proof plan (lin.tex §3.3 + appendix.tex §A.2): induction on the
execution. CreateReplica and Query are immediate. Apply extends the
linearization by one event (TODO step 3). Merge is the load-bearing
case — uses the bottom-up template and the 24 VCs (TODO step 4). -/
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
    | apply => sorry  -- step 3
    | merge => sorry  -- step 4
    | query _ _ => exact ih

end

end Sal.Emulation
