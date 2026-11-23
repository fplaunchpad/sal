import LeanProofs1.Interface.Implementation
import LeanProofs1.Soundness.SequentialSpec
import Mathlib.Data.Finset.Lattice.Basic

/-!
# AegisSheet: the implementation and the specification

The AegisSheet row of Table 1, following Appendix `app:dt-aegis-sheet`.
Rows and columns have stable identities with observed-remove presence, cells
retain concurrent values, events record inverse actions for undo, and purge
markers mask pre-cutoff cell values.

```
  Sigma = Finset (Op AppOp),   sigma0 = empty
  update(E, e) = E union {e},  merge(l, a, b) = a union b
```

The state is the **event set itself**, and the query is a declarative
function of it. That is why `rc` is empty here with no qualification: an
update is a set insertion, so every pair of events commutes at every state.

The query has six components: the live row and column identity sets, the
position map for each axis, the cell value map, and the range value map.
Position sets are computed even for identities that are not live, and equal
maximum timestamps retain all tied positions.

No proof appears in this file. Every obligation is in `VCs.lean`.

## Where the event data lives

The appendix writes an event as `e = (t, r, (S, c))` and the query reads
`t_e` off it. Definition 4 hands the specification the operation, not the
event, so `AppOp` carries `time` and `rep` beside the seen set and the
command, and `issuance` pins them to the issuing event's own. On every
certified execution this is the appendix's tuple. It is the same deviation
RGA makes for the identity an insertion allocates, and it lets `Sigma` be
the operation set the query already treats it as.
-/

namespace LeanProofs1.Implementations.AegisSheet

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs1.Interface

/-- An axis. -/
inductive Axis where
  | row
  | column
  deriving DecidableEq, Repr

/-- The kind of an axis effect. -/
inductive Kind where
  | insert
  | move
  | remove
  | restore
  deriving DecidableEq, Repr

/-- `pi_row(i,j) = i` and `pi_column(i,j) = j`. -/
def proj : Axis → Nat × Nat → Nat
  | .row, z => z.1
  | .column, z => z.2

/-- A range tuple: first row, last row, first column, last column. -/
abbrev RangeTuple := Nat × Nat × Nat × Nat

/-- The four effect forms. -/
inductive Effect where
  | axis (k : Kind) (al : Axis) (i : Nat) (b h : Option Nat)
  | cell (i j : Nat) (B A W : Finset Nat)
  | range (i : Nat) (b h : Option RangeTuple) (W : Finset Nat)
  | purge (c : Nat) (C : Finset (Nat × Nat)) (F : Finset (Nat × Nat × Nat))
      (R : Finset Nat)
  deriving DecidableEq

/-- `c = direct(a)` or `c = undo(u, a)`. -/
inductive Command where
  | direct (a : Effect)
  | undo (u : Nat) (a : Effect)
  deriving DecidableEq

/-- `a_e`: the effect, in either case. Undo adds an inverse event rather
than erasing its target. -/
def Command.effect : Command → Effect
  | .direct a => a
  | .undo _ a => a

/-- `O_type`: the issuing event's timestamp and replica, the seen
timestamps, and the command. -/
structure AppOp where
  time : Nat
  rep : Nat
  seen : Finset Nat
  cmd : Command
  deriving DecidableEq

/-- An event: an operation with its timestamp and replica. -/
abbrev Event := Op AppOp

/-- The six-component view the query returns. -/
abbrev View :=
  Set Nat × Set Nat × (Nat → Set Nat) × (Nat → Set Nat)
    × (Nat → Nat → Set Nat) × (Nat → Set RangeTuple)

/-- `type = < O_type, Q_type, Val_type >`. -/
@[reducible] def type : MRDTType where
  OType := AppOp
  decOType := inferInstance
  QType := Unit
  ValType := View

/-- `Sigma`: a finite event set. -/
abbrev St := Finset AppOp

/-- `a_e`. -/
def eff (e : AppOp) : Effect := e.cmd.effect

/-! ## The declarative query

Every definition below reads the event set directly. None of them is
incremental, and none of them consults an issuance guard.
-/

variable (E : St)

/-- `N_alpha(E)`: the identities an axis effect names. -/
def known (al : Axis) : Set Nat :=
  {i | ∃ e ∈ E, ∃ k b h, eff e = .axis k al i b h}

/-- `K_{alpha i}(E)`: the token set. Positioning axis effects, cell effects
on that line, and timestamps covered by a purge all contribute. -/
def tokens (al : Axis) (i : Nat) : Set Nat :=
  {t | (∃ e ∈ E, ∃ k b p, eff e = .axis k al i b (some p) ∧ e.time = t)
      ∨ (∃ e ∈ E, ∃ u v B A W,
            eff e = .cell u v B A W ∧ proj al (u, v) = i ∧ e.time = t)
      ∨ (∃ e ∈ E, ∃ c C F R z,
            eff e = .purge c C F R ∧ (t, z) ∈ F ∧ proj al z = i)}

/-- `D_{alpha i}(E)`: the seen sets of the removals of that line. -/
def removedBy (al : Axis) (i : Nat) : Set Nat :=
  {t | ∃ e ∈ E, ∃ k b, eff e = .axis k al i b none ∧ t ∈ e.seen}

/-- `L_{alpha i}(E) = K \ D`. -/
def liveTokens (al : Axis) (i : Nat) : Set Nat :=
  tokens E al i \ removedBy E al i

/-- `l_{alpha i}(E)`: the identity is known and has a surviving token. -/
def axisLive (al : Axis) (i : Nat) : Prop :=
  i ∈ known E al ∧ (liveTokens E al i).Nonempty

/-- `P_{alpha i}(E)`: the timestamped positions. -/
def positions (al : Axis) (i : Nat) : Set (Nat × Nat) :=
  {z | ∃ e ∈ E, ∃ k b, eff e = .axis k al i b (some z.2) ∧ e.time = z.1}

/-- `Q_{alpha i}(E)`: the positions at a maximal timestamp. Equal maximum
timestamps retain all tied positions. -/
def axisPositions (al : Axis) (i : Nat) : Set Nat :=
  {p | ∃ t, (t, p) ∈ positions E al i
        ∧ ¬ ∃ z ∈ positions E al i, t < z.1}

/-- `X_C(E, e)` for a cell event at `(i, j)`: a later cell effect names its
timestamp, or a purge covers its coordinate at or below the cutoff. -/
def cellOverwritten (i j : Nat) (e : AppOp) : Prop :=
  (∃ f ∈ E, ∃ u v B A W, eff f = .cell u v B A W ∧ e.time ∈ W)
    ∨ (∃ f ∈ E, ∃ c C F R,
          eff f = .purge c C F R ∧ (i, j) ∈ C ∧ e.time ≤ c)

/-- `X_R(E, e)`: a range effect names its timestamp. -/
def rangeOverwritten (e : AppOp) : Prop :=
  ∃ f ∈ E, ∃ u b h W, eff f = .range u b h W ∧ e.time ∈ W

/-- `T_C(E, i, j)`: the active cell timestamps at a coordinate. Even an
empty after-set contributes one. -/
def cellActive (i j : Nat) : Set Nat :=
  {t | ∃ e ∈ E, ∃ B A W,
        eff e = .cell i j B A W ∧ ¬ cellOverwritten E i j e ∧ e.time = t}

/-- `T_R(E, i)`: the active range timestamps. -/
def rangeActive (i : Nat) : Set Nat :=
  {t | ∃ e ∈ E, ∃ b h W,
        eff e = .range i b h W ∧ ¬ rangeOverwritten E e ∧ e.time = t}

/-- `C_E(i,j)`: the surviving cell values, empty unless both lines are
live. -/
def cellValues (i j : Nat) : Set Nat :=
  {v | (axisLive E .row i ∧ axisLive E .column j)
        ∧ ∃ e ∈ E, ∃ B A W,
            eff e = .cell i j B A W ∧ ¬ cellOverwritten E i j e ∧ v ∈ A}

/-- `R_E(i)`: the surviving range values. -/
def rangeValues (i : Nat) : Set RangeTuple :=
  {z | ∃ e ∈ E, ∃ b W,
        eff e = .range i b (some z) W ∧ ¬ rangeOverwritten E e}

/-- `q(E, ())`: the six components. -/
def view : View :=
  ({i | axisLive E .row i}, {j | axisLive E .column j},
   axisPositions E .row, axisPositions E .column,
   cellValues E, rangeValues E)

/-! ## The tuple -/

/-- `do(E, t, r, o)`: the event joins the set. -/
def step (E : St) (e : Event) : St := insert e.op E

/-- `merge(l, a, b)`: the ancestor is ignored. -/
def mergeState (_l a b : St) : St := a ∪ b

/-- `rc` is empty, as the appendix states. Here it is empty without
qualification: `do` is a set insertion. -/
def rc : AppOp → AppOp → OrderResult := fun _ _ => OrderResult.Either

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`.

Reducible so that `D.Sigma` unfolds to `St` during instance search. -/
@[reducible] def D : Impl type where
  Sigma := St
  decSigma := inferInstance
  sigma0 := ∅
  do_ := step
  merge := mergeState
  query E _ := view E
  rc := rc

/-! ## The independent sequential specification

The independent state keeps the same data in named components rather than
as an event set. `K` and `P` are kept per axis identity, `V` per
coordinate, `Z` per range, and `M` is the purge-marker set. Each is a
function into a set, so "fields not explicitly assigned retain their
values" is literal function update.
-/

/-- `s = (N_alpha, K_{alpha i}, P_{alpha i}, V_{ij}, Z_i, M)`. -/
structure SpecState where
  N : Axis → Set Nat
  K : Axis → Nat → Set Nat
  P : Axis → Nat → Set (Nat × Nat)
  V : Nat → Nat → Set (Nat × Nat)
  Z : Nat → Set (Nat × RangeTuple)
  M : Set Effect

/-- Initially every set is empty. -/
def SpecState.empty : SpecState :=
  ⟨fun _ => ∅, fun _ _ => ∅, fun _ _ => ∅, fun _ _ => ∅, fun _ => ∅, ∅⟩

/-- Update one axis-indexed family at one identity. -/
def setAt {β : Type} (f : Axis → Nat → Set β) (al : Axis) (i : Nat)
    (x : Set β) : Axis → Nat → Set β :=
  fun a' i' => if a' = al ∧ i' = i then x else f a' i'

/-- The axis effect. -/
def axisStep (s : SpecState) (t : Nat) (S : Finset Nat) (al : Axis)
    (i : Nat) (h : Option Nat) : SpecState :=
  let nextN : Axis → Set Nat := fun a' => if a' = al then s.N a' ∪ {i} else s.N a'
  match h with
  | some p =>
      { s with
        N := nextN,
        K := setAt s.K al i (s.K al i ∪ {t}),
        P := setAt s.P al i (s.P al i ∪ {(t, p)}) }
  | none =>
      { s with
        N := nextN,
        K := setAt s.K al i (s.K al i \ {u | u ∈ S}) }

/-- The cell effect. Both lines become known and gain a token. -/
def cellStep (s : SpecState) (t i j : Nat) (A W : Finset Nat) : SpecState :=
  { s with
    V := fun i' j' =>
      if i' = i ∧ j' = j
        then {z ∈ s.V i j | z.1 ∉ W} ∪ {z | z.1 = t ∧ z.2 ∈ A}
        else s.V i' j',
    N := (fun a' => match a' with
      | .row => s.N .row ∪ {i}
      | .column => s.N .column ∪ {j}),
    K := (fun a' i' => match a' with
      | .row => if i' = i then s.K .row i ∪ {t} else s.K .row i'
      | .column => if i' = j then s.K .column j ∪ {t} else s.K .column i') }

/-- The range effect. -/
def rangeStep (s : SpecState) (t i : Nat) (h : Option RangeTuple)
    (W : Finset Nat) : SpecState :=
  { s with
    Z := fun i' =>
      if i' = i
        then {z ∈ s.Z i | z.1 ∉ W} ∪ {z | z.1 = t ∧ some z.2 = h}
        else s.Z i' }

/-- The purge effect, simultaneously at all coordinates. -/
def purgeStep (s : SpecState) (m : Effect)
    (F : Finset (Nat × Nat × Nat)) : SpecState :=
  { s with
    V := fun i j => {z ∈ s.V i j | (z.1, i, j) ∉ F},
    M := s.M ∪ {m} }

/-- `F_e(s)`: the applicable effect equation. -/
def specStep (s : SpecState) (e : AppOp) : SpecState :=
  match eff e with
  | .axis _ al i _ hp => axisStep s e.time e.seen al i hp
  | .cell i j _ A W => cellStep s e.time i j A W
  | .range i _ hp W => rangeStep s e.time i hp W
  | .purge _ _ F _ => purgeStep s (eff e) F

/-- `A_alpha`: known with a nonempty token set. -/
def specAxisSet (s : SpecState) (al : Axis) : Set Nat :=
  {i | i ∈ s.N al ∧ (s.K al i).Nonempty}

/-- `Q^s_{alpha i}`. -/
def specPositions (s : SpecState) (al : Axis) (i : Nat) : Set Nat :=
  {p | ∃ t, (t, p) ∈ s.P al i ∧ ¬ ∃ z ∈ s.P al i, t < z.1}

/-- `mask_M(u, i, j)`. -/
def masked (s : SpecState) (u i j : Nat) : Prop :=
  ∃ m ∈ s.M, ∃ c C F R, m = .purge c C F R ∧ (i, j) ∈ C ∧ u ≤ c

/-- `C_s(i,j)`: tested on tokens, not on known identities. -/
def specCellValues (s : SpecState) (i j : Nat) : Set Nat :=
  {v | ((s.K .row i).Nonempty ∧ (s.K .column j).Nonempty)
        ∧ ∃ u, (u, v) ∈ s.V i j ∧ ¬ masked s u i j}

/-- `R_s(i)`. -/
def specRangeValues (s : SpecState) (i : Nat) : Set RangeTuple :=
  {z | ∃ u, (u, z) ∈ s.Z i}

/-- `q(s, ())`. -/
def specView (s : SpecState) : View :=
  (specAxisSet s .row, specAxisSet s .column,
   specPositions s .row, specPositions s .column,
   specCellValues s, specRangeValues s)

/-! ## Issuance

Every helper is evaluated in the causal-origin event set `O`, using the
declarative formulas above.
-/

/-- `T(O)`: the exact causal timestamp summary. -/
def seenSummary (O : St) : Set Nat :=
  {t | (∃ f ∈ O, f.time = t)
      ∨ (∃ f ∈ O, ∃ c C F R z, eff f = .purge c C F R ∧ (t, z) ∈ F)}

/-- `J_{alpha i}(O)`: the live position set. -/
def livePositions (O : St) (al : Axis) (i : Nat) : Set Nat :=
  {p | axisLive O al i ∧ p ∈ axisPositions O al i}

/-- `epsilon`, as a set. -/
def eps {β : Type} : Option β → Set β
  | none => ∅
  | some z => {z}

/-- `Meta(e, O)`. -/
def Meta (e : AppOp) (O : St) : Prop :=
  match eff e with
  | .cell i j _ _ W =>
      ∀ u ∈ W, u < e.time ∧ ∃ f ∈ O, f.time = u
        ∧ ∃ B' A' W', eff f = .cell i j B' A' W'
  | .range i _ _ W =>
      ∀ u ∈ W, u < e.time ∧ ∃ f ∈ O, f.time = u
        ∧ ∃ b' h' W', eff f = .range i b' h' W'
  | .purge c C F _ => ∀ z ∈ F, z.2 ∈ C ∧ z.1 ≤ c
  | .axis _ _ _ _ _ => True

/-- `G_dir(a, r, O)`. -/
def directGuard (a : Effect) (r : Nat) (O : St) : Prop :=
  match a with
  | .axis .insert al i b h => i ∉ known O al ∧ b = none ∧ h ≠ none
  | .axis .move al i b h => livePositions O al i = eps b ∧ b ≠ none ∧ h ≠ none
  | .axis .remove al i b h => livePositions O al i = eps b ∧ b ≠ none ∧ h = none
  | .axis .restore _ _ _ _ => False
  | .cell i j B _ W =>
      axisLive O .row i ∧ axisLive O .column j
        ∧ cellValues O i j = {v | v ∈ B} ∧ cellActive O i j = {t | t ∈ W}
  | .range i b _ W => rangeValues O i = eps b ∧ rangeActive O i = {t | t ∈ W}
  | .purge c C F R =>
      r = 0 ∧ ({0, 1, 2} : Set Nat) ⊆ {t | t ∈ R}
        ∧ (∀ z ∈ F, z.2 ∈ C ∧ z.1 ≤ c
              ∧ ∃ f ∈ O, f.time = z.1
                  ∧ ∃ B' A' W', eff f = .cell z.2.1 z.2.2 B' A' W')
        ∧ ∀ z ∈ C, ¬ axisLive O .row z.1 ∨ ¬ axisLive O .column z.2

/-- `inv(f)`, defined only for nonpurge targets. -/
def inverseFor (f : AppOp) : Option Effect :=
  match eff f with
  | .axis _ al i b h => some (.axis .restore al i h b)
  | .cell i j B _ _ => some (.cell i j ∅ B {f.time})
  | .range i b _ _ => some (.range i none b {f.time})
  | .purge _ _ _ _ => none

/-- A nonpurge effect. -/
def nonpurge : Effect → Prop
  | .purge _ _ _ _ => False
  | _ => True

/-- `G(e, O)`: the exact guard. -/
def guard (e : AppOp) (O : St) : Prop :=
  {t | t ∈ e.seen} = seenSummary O
    ∧ (∀ u ∈ seenSummary O, u < e.time)
    ∧ Meta e O
    ∧ match e.cmd with
      | .direct a => directGuard a e.rep O
      | .undo u a =>
          u ∈ e.seen ∧ ∃ f ∈ O, f.time = u ∧ f.rep = e.rep
            ∧ nonpurge (eff f) ∧ inverseFor f = some a

/-! ## The specification as a machine

The prefix `H` is carried in the state, because `Legal` is a condition on
the whole prefix rather than on one step. The alphabet is **events**, not
operations: `specStep` reads `e.time`, `e.rep` and `e.op.seen`, and the
guard is evaluated at a causal-origin set drawn from the prefix. -/

/-- `Legal(H)`: strictly increasing timestamps, and each event admitted by
the guard at some subset of its own prefix. -/
def Legal (H : List AppOp) : Prop :=
  H.Pairwise (fun a b => a.time < b.time)
    ∧ ∀ i : Fin H.length, ∃ O : St,
        (∀ f ∈ O, f ∈ H.take i.val) ∧ guard H[i] O

/-- `Spec`: the same data in named components rather than as an event set.
The prefix `H` is carried in the state, because `Legal` is a condition on
the whole prefix rather than on one step. -/
def specMachine : HistoryMachine type.OType type.QType type.ValType where
  State := List AppOp × SpecState
  initial := ([], SpecState.empty)
  transition s label t :=
    match label with
    | .update o => Legal (s.1 ++ [o]) ∧ t = (s.1 ++ [o], specStep s.2 o)
    | .query _ answer => t = s ∧ answer = specView s.2

/-- `Spec` as a history language. -/
def historySpec : Soundness.Spec type := specMachine.toSpec

/-- Issuance, as Section 3 takes it: the guard evaluated at the issuing
state, which for this row **is** the causal-origin event set. The first two
conjuncts pin the operation's copy of the timestamp and replica to the
issuing event's own. -/
def issuance : Issuance D.toMRDTSig where
  CanIssue := fun e O => e.op.time = e.time ∧ e.op.rep = e.rep ∧ guard e.op O

end LeanProofs1.Implementations.AegisSheet
