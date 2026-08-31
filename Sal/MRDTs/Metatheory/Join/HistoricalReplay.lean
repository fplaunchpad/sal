import Sal.MRDTs.Framework.Base.ReplayContext

/-!
# Replay order and historical verification conditions

This file contains the update fold, the historical global replay order, and
the archived 24-condition bundle. These definitions inspect a `ReplayContext`;
they do not define a second execution semantics. Per-version MRDT adequacy is
proved over the version-DAG execution in `Adequacy.lean`.
-/

namespace Sal.MRDTs.Foundation

section
variable (D : UpdateSig)
variable [ReplayPolicy D]

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
         D.replayOrder e₁ e₂ = RcRes.Fst_then_snd ∨ D.replayOrder e₂ e₁ = RcRes.Fst_then_snd)

/-- `cond-comm(D)` (lin.tex §3.2). Whenever `rc` orders `o₁ → o₂` and
`o₂` doesn't commute with some `o₃`, then `o₁, o₂` conditionally commute
w.r.t. `o₃`. Rules out the `lo`-cycle pathology of
Fig. conditional-commutativity. -/
def condComm : Prop :=
  ∀ o₁ o₂ o₃ : D.AppOp,
    (∀ e₁ e₂ : Op D.AppOp, e₁.op = o₁ → e₂.op = o₂ →
       D.replayOrder e₁ e₂ = RcRes.Fst_then_snd) →
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
def lo (C : ReplayContext D) (e₁ e₂ : Op D.AppOp) : Prop :=
  (C.vis e₁ e₂ ∧ ¬ D.commutes e₁ e₂)
  ∨ ( ¬ C.vis e₁ e₂ ∧ ¬ C.vis e₂ e₁
      ∧ D.replayOrder e₁ e₂ = RcRes.Fst_then_snd
      ∧ ¬ ∃ e₃, C.vis e₂ e₃ ∧ ¬ D.commutes e₂ e₃ )

/-! ## The 24 VCs

Transcribed from the archived grow-only-set case study, which supplied the
canonical enumeration. Field names preserve that mechanical correspondence.

Helpers `distinctOps` (fresh timestamps) and `differentReplicas` inline
the boolean predicates `distinct_ops` / `get_rid o1 != get_rid o2` used
in the existing Sal code as Prop-level conjunctions. -/

/-- Two events have distinct timestamps. Sal paper enforces global
uniqueness, so this always holds between any two events in an
execution. -/
def distinctOps {D : UpdateSig} (o₁ o₂ : Op D.AppOp) : Prop :=
  o₁.time ≠ o₂.time

/-- Two events originated at different replicas. -/
def differentReplicas {D : UpdateSig} (o₁ o₂ : Op D.AppOp) : Prop :=
  o₁.rep ≠ o₂.rep

/-- The 24 VCs of the Sal paper. Each field is the parametric,
signature-level version of the corresponding per-datatype theorem in the
archived standalone case studies. -/
structure HistoricalReplayVCs (D : UpdateSig) [ReplayPolicy D]
    [HistoricalBinaryMerge D] : Prop where
  /-- rc-nonComm semantic characterization: at distinct timestamps and
  replicas, `rc = Either` iff the two events commute. -/
  rc_non_comm :
    ∀ o₁ o₂ : Op D.AppOp,
      distinctOps o₁ o₂ → differentReplicas o₁ o₂ →
      (D.replayOrder o₁ o₂ = RcRes.Either ↔ D.commutes o₁ o₂)

  /-- rc-nonComm directional form (paper lin.tex:387). At distinct
  timestamps, non-commutativity is equivalent to being `rc`-ordered in
  some direction. This is strictly stronger than `rc_non_comm` (which
  only constrains the `Either` case for different-replica events).

  Note: this version omits the `differentReplicas` premise of the
  weak `rc_non_comm`. The convergence proof's overwriter argument
  needs `rc`-ordering for arbitrary `¬commute` pairs (including
  same-replica events that arise as overwriters via causal chains).
  For typical CRDTs (LWW, OR-set, etc.) same-replica events are
  rc-ordered by timestamp; for trivially-commutative CRDTs (G-Set)
  the directional form holds vacuously since `¬commute` is impossible. -/
  rc_non_comm_directional :
    ∀ o₁ o₂ : Op D.AppOp,
      distinctOps o₁ o₂ →
      (¬ D.commutes o₁ o₂ ↔
       (D.replayOrder o₁ o₂ = RcRes.Fst_then_snd ∨ D.replayOrder o₂ o₁ = RcRes.Fst_then_snd))

  /-- rc is not transitively ordering: no three events form an
  `rc = Fst_then_snd` chain. -/
  no_rc_chain :
    ∀ o₁ o₂ o₃ : Op D.AppOp,
      distinctOps o₁ o₂ → distinctOps o₂ o₃ →
      ¬ (D.replayOrder o₁ o₂ = RcRes.Fst_then_snd ∧
         D.replayOrder o₂ o₃ = RcRes.Fst_then_snd)

  /-- Base case for conditional commutativity: if `rc o₁ o₂ =
  Fst_then_snd` and `o₂` doesn't commute with `o₃`, then `o₁` and `o₂`
  can be swapped provided `o₃` follows. -/
  cond_comm_base :
    ∀ (s : D.State) (o₁ o₂ o₃ : Op D.AppOp),
      distinctOps o₁ o₂ → distinctOps o₂ o₃ → distinctOps o₁ o₃ →
      D.replayOrder o₁ o₂ = RcRes.Fst_then_snd →
      D.replayOrder o₂ o₃ ≠ RcRes.Either →
      D.update (D.update (D.update s o₁) o₂) o₃
        = D.update (D.update (D.update s o₂) o₁) o₃

  /-- `merge` is commutative. -/
  merge_comm : ∀ a b : D.State, D.historicalMerge a b = D.historicalMerge b a

  /-- `merge` is idempotent. -/
  merge_idem : ∀ s : D.State, D.historicalMerge s s = s

  /-- Base step of the bottom-up 2-op induction: for independent ops on
  `init`, pushing `o₁` through `merge` is sound. -/
  base_2op :
    ∀ o₁ o₂ : Op D.AppOp,
      (D.replayOrder o₂ o₁ = RcRes.Fst_then_snd ∨ D.replayOrder o₂ o₁ = RcRes.Either) →
      differentReplicas o₁ o₂ → distinctOps o₁ o₂ →
      D.historicalMerge (D.update D.init o₁) (D.update D.init o₂)
        = D.update (D.historicalMerge D.init (D.update D.init o₂)) o₁

  /-- GCA induction step for the 2-op bottom-up rule: extends the
  hypothesis from `l` to `do l ol`. -/
  ind_base_2op :
    ∀ (l : D.State) (o₁ o₂ ol : Op D.AppOp),
      (D.replayOrder o₂ o₁ = RcRes.Fst_then_snd ∨ D.replayOrder o₂ o₁ = RcRes.Either) →
      differentReplicas o₁ o₂ →
      distinctOps o₁ o₂ → distinctOps o₁ ol → distinctOps o₂ ol →
      D.historicalMerge (D.update l o₁) (D.update l o₂)
        = D.update (D.historicalMerge l (D.update l o₂)) o₁ →
      D.historicalMerge (D.update (D.update l ol) o₁) (D.update (D.update l ol) o₂)
        = D.update (D.historicalMerge (D.update l ol) (D.update (D.update l ol) o₂)) o₁

  /-- Right-side base case for a single `ob` interposed. -/
  inter_right_base_2op :
    ∀ (a b : D.State) (o₁ o₂ ob ol : Op D.AppOp),
      (D.replayOrder o₂ o₁ = RcRes.Fst_then_snd ∨ D.replayOrder o₂ o₁ = RcRes.Either) →
      differentReplicas o₁ o₂ →
      D.replayOrder ob ol = RcRes.Fst_then_snd → differentReplicas ob ol →
      distinctOps o₁ o₂ → distinctOps o₁ ob → distinctOps o₁ ol →
      distinctOps o₂ ob → distinctOps o₂ ol → distinctOps ob ol →
      D.historicalMerge (D.update a o₁) (D.update b o₂)
        = D.update (D.historicalMerge a (D.update b o₂)) o₁ →
      D.historicalMerge (D.update a o₁) (D.update (D.update b ob) o₂)
        = D.update (D.historicalMerge a (D.update (D.update b ob) o₂)) o₁ →
      D.historicalMerge (D.update (D.update a ol) o₁) (D.update (D.update b ol) o₂)
        = D.update (D.historicalMerge (D.update a ol) (D.update (D.update b ol) o₂)) o₁ →
      D.historicalMerge (D.update (D.update a ol) o₁)
              (D.update (D.update (D.update b ob) ol) o₂)
        = D.update (D.historicalMerge (D.update a ol)
                            (D.update (D.update (D.update b ob) ol) o₂)) o₁

  /-- Left-side base case, symmetric to `inter_right_base_2op`. -/
  inter_left_base_2op :
    ∀ (a b : D.State) (o₁ o₂ ob ol : Op D.AppOp),
      D.replayOrder o₂ o₁ = RcRes.Fst_then_snd →
      D.replayOrder ob ol = RcRes.Fst_then_snd →
      differentReplicas o₂ o₁ → differentReplicas ob ol →
      distinctOps o₁ o₂ → distinctOps o₁ ob → distinctOps o₁ ol →
      distinctOps o₂ ob → distinctOps o₂ ol → distinctOps ob ol →
      D.historicalMerge (D.update (D.update a ol) o₁) (D.update (D.update b ol) o₂)
        = D.update (D.historicalMerge (D.update a ol) (D.update (D.update b ol) o₂)) o₁ →
      D.historicalMerge (D.update (D.update (D.update a ob) ol) o₁)
              (D.update (D.update b ol) o₂)
        = D.update (D.historicalMerge (D.update (D.update a ob) ol)
                            (D.update (D.update b ol) o₂)) o₁

  /-- Inductive step for the right-side interposition, extending by
  one more op `o`. -/
  inter_right_2op :
    ∀ (a b : D.State) (o₁ o₂ ob ol o : Op D.AppOp),
      (D.replayOrder o₂ o₁ = RcRes.Fst_then_snd ∨ D.replayOrder o₂ o₁ = RcRes.Either) →
      differentReplicas o₁ o₂ →
      D.replayOrder ob ol = RcRes.Fst_then_snd → differentReplicas ob ol →
      (D.replayOrder o ob ≠ RcRes.Either ∨ D.replayOrder o ol = RcRes.Fst_then_snd) →
      distinctOps o₁ o₂ → distinctOps o₁ ob → distinctOps o₁ ol →
      distinctOps o₁ o →
      distinctOps o₂ ob → distinctOps o₂ ol → distinctOps o₂ o →
      distinctOps ob ol → distinctOps ob o → distinctOps ol o →
      differentReplicas o ol →
      D.historicalMerge (D.update (D.update a ol) o₁)
              (D.update (D.update (D.update b ob) ol) o₂)
        = D.update (D.historicalMerge (D.update a ol)
                            (D.update (D.update (D.update b ob) ol) o₂)) o₁ →
      D.historicalMerge (D.update (D.update a ol) o₁)
              (D.update (D.update (D.update (D.update b o) ob) ol) o₂)
        = D.update (D.historicalMerge (D.update a ol)
                      (D.update (D.update (D.update (D.update b o) ob) ol) o₂)) o₁

  /-- Inductive step for the left-side interposition. -/
  inter_left_2op :
    ∀ (a b : D.State) (o₁ o₂ ob ol o : Op D.AppOp),
      D.replayOrder o₂ o₁ = RcRes.Fst_then_snd →
      D.replayOrder ob ol = RcRes.Fst_then_snd →
      differentReplicas o₂ o₁ → differentReplicas ob ol →
      (D.replayOrder o ob ≠ RcRes.Either ∨ D.replayOrder o ol = RcRes.Fst_then_snd) →
      distinctOps o₁ o₂ → distinctOps o₁ ob → distinctOps o₁ ol →
      distinctOps o₁ o →
      distinctOps o₂ ob → distinctOps o₂ ol → distinctOps o₂ o →
      distinctOps ob ol → distinctOps ob o → distinctOps ol o →
      differentReplicas o ol →
      D.historicalMerge (D.update (D.update (D.update a ob) ol) o₁)
              (D.update (D.update b ol) o₂)
        = D.update (D.historicalMerge (D.update (D.update a ob) ol)
                            (D.update (D.update b ol) o₂)) o₁ →
      D.historicalMerge (D.update (D.update (D.update (D.update a o) ob) ol) o₁)
              (D.update (D.update b ol) o₂)
        = D.update (D.historicalMerge (D.update (D.update (D.update a o) ob) ol)
                            (D.update (D.update b ol) o₂)) o₁

  /-- GCA-side 2-op inductive step. -/
  inter_base_2op :
    ∀ (a b : D.State) (o₁ o₂ ol : Op D.AppOp),
      (D.replayOrder o₂ o₁ = RcRes.Fst_then_snd ∨ D.replayOrder o₂ o₁ = RcRes.Either) →
      differentReplicas o₁ o₂ →
      distinctOps o₁ o₂ → distinctOps o₁ ol → distinctOps o₂ ol →
      (∃ o, D.replayOrder o ol = RcRes.Fst_then_snd) →
      D.historicalMerge (D.update (D.update a ol) o₁) (D.update b ol)
        = D.update (D.historicalMerge (D.update a ol) (D.update b ol)) o₁ →
      D.historicalMerge (D.update a o₁) (D.update b o₂)
        = D.update (D.historicalMerge a (D.update b o₂)) o₁ →
      D.historicalMerge (D.update (D.update a ol) o₁) (D.update (D.update b ol) o₂)
        = D.update (D.historicalMerge (D.update a ol) (D.update (D.update b ol) o₂)) o₁

  /-- 2-op right-hand inductive step: extend by one more op `o₂'` on b. -/
  ind_right_2op :
    ∀ (a b : D.State) (o₁ o₂ o₂' : Op D.AppOp),
      D.replayOrder o₂ o₁ = RcRes.Fst_then_snd →
      differentReplicas o₁ o₂ →
      distinctOps o₁ o₂ → distinctOps o₁ o₂' → distinctOps o₂ o₂' →
      D.historicalMerge (D.update a o₁) (D.update b o₂)
        = D.update (D.historicalMerge a (D.update b o₂)) o₁ →
      D.historicalMerge (D.update a o₁) (D.update (D.update b o₂') o₂)
        = D.update (D.historicalMerge a (D.update (D.update b o₂') o₂)) o₁

  /-- 2-op left-hand inductive step: extend by one more op `o₁'` on a. -/
  ind_left_2op :
    ∀ (a b : D.State) (o₁ o₂ o₁' : Op D.AppOp),
      (D.replayOrder o₂ o₁ = RcRes.Fst_then_snd ∨ D.replayOrder o₂ o₁ = RcRes.Either) →
      differentReplicas o₁ o₂ →
      distinctOps o₁ o₂ → distinctOps o₁ o₁' → distinctOps o₂ o₁' →
      D.historicalMerge (D.update a o₁) (D.update b o₂)
        = D.update (D.historicalMerge a (D.update b o₂)) o₁ →
      D.historicalMerge (D.update (D.update a o₁') o₁) (D.update b o₂)
        = D.update (D.historicalMerge (D.update a o₁') (D.update b o₂)) o₁

  /-- Base case for the 1-op bottom-up induction: merge with `init`
  on the right commutes with `do init o1` on the left. -/
  base_1op :
    ∀ o₁ : Op D.AppOp,
      D.historicalMerge (D.update D.init o₁) D.init
        = D.update (D.historicalMerge D.init D.init) o₁

  /-- GCA induction for the 1-op rule. -/
  ind_base_1op :
    ∀ (l : D.State) (o₁ ol : Op D.AppOp),
      distinctOps o₁ ol →
      D.historicalMerge (D.update l o₁) l = D.update (D.historicalMerge l l) o₁ →
      D.historicalMerge (D.update (D.update l ol) o₁) (D.update l ol)
        = D.update (D.historicalMerge (D.update l ol) (D.update l ol)) o₁

  /-- Right-side base case for the 1-op rule. -/
  inter_right_base_1op :
    ∀ (a b : D.State) (o₁ ob ol : Op D.AppOp),
      D.replayOrder ob ol = RcRes.Fst_then_snd → differentReplicas ob ol →
      distinctOps o₁ ob → distinctOps o₁ ol → distinctOps ob ol →
      (D.replayOrder ob o₁ = RcRes.Fst_then_snd →
         D.historicalMerge (D.update a o₁) (D.update b ob)
           = D.update (D.historicalMerge a (D.update b ob)) o₁) →
      D.historicalMerge (D.update (D.update a ol) o₁) (D.update b ol)
        = D.update (D.historicalMerge (D.update a ol) (D.update b ol)) o₁ →
      D.historicalMerge (D.update (D.update a ol) o₁) (D.update (D.update b ob) ol)
        = D.update (D.historicalMerge (D.update a ol) (D.update (D.update b ob) ol)) o₁

  /-- Left-side base case for the 1-op rule. -/
  inter_left_base_1op :
    ∀ (a b : D.State) (o₁ ob ol : Op D.AppOp),
      D.replayOrder ob ol = RcRes.Fst_then_snd → differentReplicas ob ol →
      distinctOps o₁ ob → distinctOps o₁ ol → distinctOps ob ol →
      D.historicalMerge (D.update (D.update a ol) o₁) (D.update b ol)
        = D.update (D.historicalMerge (D.update a ol) (D.update b ol)) o₁ →
      D.historicalMerge (D.update (D.update (D.update a ob) ol) o₁) (D.update b ol)
        = D.update (D.historicalMerge (D.update (D.update a ob) ol)
                            (D.update b ol)) o₁

  /-- Right-side inductive step for the 1-op rule. -/
  inter_right_1op :
    ∀ (a b : D.State) (o₁ ob ol o : Op D.AppOp),
      D.replayOrder ob ol = RcRes.Fst_then_snd → differentReplicas ob ol →
      (D.replayOrder o ob ≠ RcRes.Either ∨ D.replayOrder o ol = RcRes.Fst_then_snd) →
      distinctOps o₁ ob → distinctOps o₁ ol → distinctOps o₁ o →
      distinctOps ob ol → distinctOps ob o → distinctOps ol o →
      differentReplicas o ol →
      D.historicalMerge (D.update (D.update a ol) o₁) (D.update (D.update b ob) ol)
        = D.update (D.historicalMerge (D.update a ol) (D.update (D.update b ob) ol)) o₁ →
      D.historicalMerge (D.update (D.update a ol) o₁)
              (D.update (D.update (D.update b o) ob) ol)
        = D.update (D.historicalMerge (D.update a ol)
                      (D.update (D.update (D.update b o) ob) ol)) o₁

  /-- Left-side inductive step for the 1-op rule. -/
  inter_left_1op :
    ∀ (a b : D.State) (o₁ ob ol o : Op D.AppOp),
      D.replayOrder ob ol = RcRes.Fst_then_snd → differentReplicas ob ol →
      (D.replayOrder o ob ≠ RcRes.Either ∨ D.replayOrder o ol = RcRes.Fst_then_snd) →
      distinctOps o₁ ob → distinctOps o₁ ol → distinctOps o₁ o →
      distinctOps ob ol → distinctOps ob o → distinctOps ol o →
      differentReplicas o ol →
      D.historicalMerge (D.update (D.update (D.update a ob) ol) o₁) (D.update b ol)
        = D.update (D.historicalMerge (D.update (D.update a ob) ol)
                            (D.update b ol)) o₁ →
      D.historicalMerge (D.update (D.update (D.update (D.update a o) ob) ol) o₁)
              (D.update b ol)
        = D.update (D.historicalMerge (D.update (D.update (D.update a o) ob) ol)
                            (D.update b ol)) o₁

  /-- GCA-side inductive step for the 1-op rule. -/
  inter_base_1op :
    ∀ (a b : D.State) (o₁ ol oi : Op D.AppOp),
      distinctOps o₁ ol → distinctOps o₁ oi → distinctOps ol oi →
      (∃ o, D.replayOrder o ol = RcRes.Fst_then_snd) →
      (∃ o, D.replayOrder o oi = RcRes.Fst_then_snd) →
      D.historicalMerge (D.update (D.update a oi) o₁) (D.update b oi)
        = D.update (D.historicalMerge (D.update a oi) (D.update b oi)) o₁ →
      D.historicalMerge (D.update (D.update a ol) o₁) (D.update b ol)
        = D.update (D.historicalMerge (D.update a ol) (D.update b ol)) o₁ →
      D.historicalMerge (D.update (D.update (D.update a oi) ol) o₁)
              (D.update (D.update b oi) ol)
        = D.update (D.historicalMerge (D.update (D.update a oi) ol)
                            (D.update (D.update b oi) ol)) o₁

  /-- 1-op left-hand inductive step: extend by one more op `o₁'` on a. -/
  ind_left_1op :
    ∀ (a b : D.State) (o₁ o₁' ol : Op D.AppOp),
      distinctOps o₁ o₁' → distinctOps o₁ ol → distinctOps o₁' ol →
      D.historicalMerge (D.update a o₁) (D.update b ol)
        = D.update (D.historicalMerge a (D.update b ol)) o₁ →
      D.historicalMerge (D.update (D.update a o₁') o₁) (D.update b ol)
        = D.update (D.historicalMerge (D.update a o₁') (D.update b ol)) o₁

  /-- 1-op right-hand inductive step: extend by one more op `o₂'` on b. -/
  ind_right_1op :
    ∀ (a b : D.State) (o₂ o₂' ol : Op D.AppOp),
      distinctOps o₂ o₂' → distinctOps o₂ ol → distinctOps o₂' ol →
      D.historicalMerge (D.update a ol) (D.update b o₂)
        = D.update (D.historicalMerge (D.update a ol) b) o₂ →
      D.historicalMerge (D.update a ol) (D.update (D.update b o₂') o₂)
        = D.update (D.historicalMerge (D.update a ol) (D.update b o₂')) o₂

  /-- Zero-op closure: a single op applied on both sides pushes out of
  `merge`. -/
  lem_0op :
    ∀ (a b : D.State) (ol : Op D.AppOp),
      D.historicalMerge (D.update a ol) (D.update b ol)
        = D.update (D.historicalMerge a b) ol

  /-- **`cond-comm` lift (paper lin.tex §3.2, property `cond-comm`).**

  The Sal paper assumes `cond-comm` holds at the convergence level,
  `cond_comm_base` is the 3-event base case, and this field is the
  semantic extension to arbitrary intervening events. The paper's
  convergence proof (appendix §A.1) invokes `cond-comm` directly to
  flip `e₁`, `e₂` in a permutation when there's an overwriter `e₃`
  somewhere later in the sequence.

  For most CRDTs, this is **vacuous** (rc = Either for all app-op
  pairs, making the `rc o₁ o₂ = Fst_then_snd` premise unsatisfiable).
  For CRDTs with non-trivial rc, this needs to be verified from
  `cond_comm_base` + other VCs via induction on the intervening
  sequence, a theorem the Sal paper treats as implicit and does not
  explicitly prove.

  The standalone `conditionallyCommute` def above captures this
  property at the event level; `condComm` lifts it to app-ops. This
  field is equivalent to `condComm D` specialised to events. -/
  cond_comm_lift :
    ∀ (s : D.State) (e e' e'' : Op D.AppOp) (π : List (Op D.AppOp)),
      distinctOps e e' → distinctOps e e'' → distinctOps e' e'' →
      D.replayOrder e e' = RcRes.Fst_then_snd →
      ¬ D.commutes e' e'' →
      D.update (applySeq D (D.update (D.update s e') e) π) e''
        = D.update (applySeq D (D.update (D.update s e) e') π) e''

  /-- **Merge-init identity.** The initial state `D.init` is the bottom
  element of the CRDT's state lattice: merging with it leaves any state
  unchanged.

  This property is a fundamental lattice axiom that is NOT derivable
  from the other 24 VCs, the VCs only constrain `merge` when both
  arguments have at least one `update` applied.  The Sal paper treats
  this as implicit (init is the lattice bottom by definition), but the
  mechanization needs it as an explicit axiom. -/
  merge_init :
    ∀ s : D.State, D.historicalMerge D.init s = s

  /-- **Merge-peel commutativity** (paper's `BottomUpTemplate`,
  `overview.tex:202`, specialised to 2-way merge).

  When event `e` commutes with every event that produced `b` (i.e.,
  `b = applySeq D.init π` for some `π` in which all events commute
  with `e`), the merge equation can peel `e` from the left side:
  `merge (update a e) b = update (merge a b) e`.

  This is the peel rule for the all-commuting carving case. The 24 VCs'
  `ind_right_2op` requires `rc = Fst_then_snd`, which doesn't fire
  when all events commute (e.g., G-Set). The paper's BottomUpTemplate
  is stated unconditionally; this conditional form is its
  specialisation.

  For typical CRDTs (G-Set, OR-set with same-element pairs, etc.) the
  property is a direct lattice fact (set union associativity / similar).
  For CRDTs with non-commuting ops, the hypothesis activates only when
  it actually holds, and the conclusion is the standard peel. -/
  merge_peel_comm :
    ∀ (a : D.State) (e : Op D.AppOp) (π : List (Op D.AppOp)),
      (∀ x ∈ π, D.commutes e x) →
      D.historicalMerge (D.update a e) (applySeq D D.init π)
        = D.update (D.historicalMerge a (applySeq D D.init π)) e

  /-- **Shared-element 1-op peel.** When both replicas have applied
  the same event `ol` and the left replica has additionally applied
  `o₁`, peeling `o₁` out of the merge is sound:

  ```
  merge(update(update(a, ol), o₁), update(b, ol))
    = update(merge(update(a, ol), update(b, ol)), o₁)
  ```

  This is a CRDT-lattice property (follows from join associativity /
  commutativity for typical CRDTs) that the existing 24 VCs cannot
  derive: every VC extending a single side requires `distinctOps`
  between the new operation and the other side's tail operation.
  When both sides share `ol`, this requires `distinctOps ol ol`
  which is always false; the only "shared GCA event" VC,
  `ind_base_1op`, requires both sides to have the same base state
  (which doesn't hold when each side has its own π_a / π_b prefix).

  Consumed by `merge_peel_shared` (the 2-op shared-event peel) which
  is in turn consumed by Case 3a-shared sub-cases of
  `distinct_last_case`. Vacuous for trivial-rc CRDTs (Grow-Only Set). -/
  shared_peel_1op :
    ∀ (o₁ ol : Op D.AppOp), distinctOps o₁ ol →
      ∀ (a b : D.State),
        D.historicalMerge (D.update (D.update a ol) o₁) (D.update b ol)
          = D.update (D.historicalMerge (D.update a ol) (D.update b ol)) o₁

end

end Sal.MRDTs.Foundation
