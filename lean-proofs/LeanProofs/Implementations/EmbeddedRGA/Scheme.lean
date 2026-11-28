import LeanProofs_no_spec_non_comm.Interface.Implementation
import LeanProofs_no_spec_non_comm.Soundness.SequentialSpec

/-!
# The embedded-coordinate RGA core

Four rows of Table 1 are the same algorithm over different coordinate
schemes: Embedded RGA, Sided Embedded RGA, Embedded Peritext and Sided
Peritext. This file is that algorithm, parametric in the scheme and in the
payload, and every proof in this folder is about it. A row supplies a
`Scheme` and reads off its tuple.

## What a scheme has to provide

The development consults the coordinate machinery in exactly six places,
so a scheme is exactly those six facts. In particular it does **not** need
monotonicity of the code or the terminator convention: `key_sibling` and
`key_descendant` are what make descending keys the RGA **order**, and
RA-linearizability never asks for them. They are needed for the editor
semantics, which is a separate theorem.

What is needed is **unique decodability**, `cancel`: a coordinate that can
occur determines the codeword that ends it, hence the insertion that wrote
it. That is what stops the sorted insert from ever being forced to break a
tie, and it is exactly what `Negative.lean` shows fails at an arbitrary
state.

```
  Embedded RGA   Sym = Bool   Arg = Unit   code _ d = 1^d 0
  Sided RGA      Sym = Nat    Arg = Side   code R d = 2^d 1, code L d = 4^d 5
```

Read through its key map, Embedded RGA is Sided RGA with every insertion on
the right: its `key (enc d)` is `2^d 1 3`, which is Sided's right band
followed by the terminator. Sided adds the left band `4^d 5`, which the
terminator `3` separates from the right.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.EmbeddedRGA

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

/-! ## The comparison order on keys

Scheme-independent: a key is a list of naturals however the symbols are
encoded. -/

/-- Strict lexicographic order, a proper prefix being smaller. -/
def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x < y then true else if y < x then false else lexLt xs ys

theorem lexLt_irrefl : ∀ u : List Nat, lexLt u u = false
  | [] => rfl
  | x :: xs => by simp only [lexLt, lt_self_iff_false, if_false]; exact lexLt_irrefl xs

theorem lexLt_asymm : ∀ u v : List Nat, lexLt u v = true → lexLt v u = false := by
  intro u
  induction u with
  | nil =>
    intro v h
    cases v with
    | nil => rfl
    | cons y ys => simp [lexLt]
  | cons x xs ih =>
    intro v h
    cases v with
    | nil => simp [lexLt] at h
    | cons y ys =>
      simp only [lexLt] at h ⊢
      split_ifs at h ⊢
      all_goals first
        | rfl
        | omega
        | exact ih ys h
        | simp_all

theorem lexLt_trans : ∀ u v w : List Nat,
    lexLt u v = true → lexLt v w = true → lexLt u w = true := by
  intro u
  induction u with
  | nil =>
    intro v w _ h
    cases w with
    | nil => cases v <;> simp [lexLt] at h
    | cons z zs => simp [lexLt]
  | cons x xs ih =>
    intro v w h k
    cases v with
    | nil => simp [lexLt] at h
    | cons y ys =>
      cases w with
      | nil => simp [lexLt] at k
      | cons z zs =>
        simp only [lexLt] at h k ⊢
        split_ifs at h k ⊢
        all_goals first
          | rfl
          | omega
          | exact ih ys zs h k
          | simp_all

/-- Two keys unrelated by `lexLt` are equal. -/
theorem lexLt_eq_of_not_lt : ∀ u v : List Nat,
    lexLt u v = false → lexLt v u = false → u = v := by
  intro u
  induction u with
  | nil =>
    intro v h k
    cases v with
    | nil => rfl
    | cons y ys => simp [lexLt] at h
  | cons x xs ih =>
    intro v h k
    cases v with
    | nil => simp [lexLt] at k
    | cons y ys =>
      simp only [lexLt] at h k
      split_ifs at h k
      all_goals first
        | (have hxy : x = y := by omega
           subst hxy
           exact congrArg _ (ih ys h k))
        | exact absurd h (by simp)
        | exact absurd k (by simp)

/-- Hence distinct keys are comparable. -/
theorem lexLt_total {u v : List Nat} (h : u ≠ v) :
    lexLt u v = true ∨ lexLt v u = true := by
  by_cases h1 : lexLt u v = true
  · exact Or.inl h1
  · by_cases h2 : lexLt v u = true
    · exact Or.inr h2
    · exact absurd (lexLt_eq_of_not_lt u v (by simpa using h1) (by simpa using h2)) h

/-! ## A coordinate scheme -/

/-- **What a row supplies.** The symbol alphabet, the extra datum an
insertion carries beyond value, anchor coordinate and anchor, the codeword
a step contributes, the comparison key, and the four facts the development
consults. -/
structure Scheme where
  /-- The coordinate alphabet. -/
  Sym : Type
  [decSym : DecidableEq Sym]
  /-- The extra datum an insertion carries: `Unit` for a one-sided row, the
  side for a sided one. -/
  Arg : Type
  [decArg : DecidableEq Arg]
  /-- The codeword an insertion contributes to its coordinate. -/
  code : Arg → Nat → List Sym
  /-- The comparison key of a coordinate. -/
  key : List Sym → List Nat
  /-- Distinct coordinates have distinct keys, so they are always
  comparable. -/
  key_inj : ∀ {c d : List Sym}, key c = key d → c = d
  /-- The coordinates that can occur. -/
  Wf : List Sym → Prop
  /-- The root coordinate can occur. -/
  wf_nil : Wf []
  /-- So can every coordinate an insertion writes. -/
  wf_append : ∀ (p : List Sym) (g : Arg) (d : Nat), Wf (p ++ code g d)
  /-- A codeword is never empty, which is the measure the decodability
  induction descends on. -/
  code_ne_nil : ∀ (g : Arg) (d : Nat), code g d ≠ []
  /-- **Unique decodability.** A coordinate that can occur determines the
  prefix, the extra datum and the clock gap that produced it. -/
  cancel : ∀ {p₁ p₂ : List Sym} {g₁ g₂ : Arg} {d₁ d₂ : Nat}, Wf p₁ → Wf p₂ →
    p₁ ++ code g₁ d₁ = p₂ ++ code g₂ d₂ → p₁ = p₂ ∧ g₁ = g₂ ∧ d₁ = d₂

attribute [instance] Scheme.decSym Scheme.decArg

variable (Γ : Scheme)

/-- A written coordinate is strictly longer than the prefix it extends. -/
theorem Scheme.length_lt (p : List Γ.Sym) (g : Γ.Arg) (d : Nat) :
    p.length < (p ++ Γ.code g d).length := by
  have : (Γ.code g d).length ≠ 0 := fun h =>
    Γ.code_ne_nil g d (List.eq_nil_of_length_eq_zero h)
  simp only [List.length_append]
  omega

/-! ## The tuple -/

/-- A record: identity, payload, coordinate. -/
abbrev Record (α : Type) := Nat × α × List Γ.Sym

/-- `O_type`. -/
inductive AppOp (Γ : Scheme) (α : Type) where
  | ins (value : α) (anchorCoord : List Γ.Sym) (anchor : Nat) (arg : Γ.Arg)
  | del (target : Nat)
  deriving DecidableEq

variable {Γ}
variable {α : Type}

def recKey (z : Record Γ α) : List Nat := Γ.key z.2.2

/-- `Sigma`. -/
abbrev St (Γ : Scheme) (α : Type) := List (Record Γ α)

/-- `I(S)`. -/
def ids (S : St Γ α) : List Nat := S.map (fun z => z.1)

/-- `J`: descending-key insertion. -/
def insertDown (z : Record Γ α) : St Γ α → St Γ α
  | [] => [z]
  | y :: Y => if lexLt (recKey y) (recKey z) then z :: y :: Y else y :: insertDown z Y

/-- `M`: the descending merge. -/
def mergeDown : St Γ α → St Γ α → St Γ α
  | [], Y => Y
  | X, [] => X
  | x :: X, y :: Y =>
      if lexLt (recKey y) (recKey x) then x :: mergeDown X (y :: Y)
      else y :: mergeDown (x :: X) Y

/-- **The row's public observation.** The state, the update and the merge
are the core's; the query is not. The anchored FIFO queue is the core with
`readHead` in place of `payloads`, so the query is a parameter rather than a
fixture. -/
structure QueryOf (Γ : Scheme) (α : Type) where
  /-- `Q_type`. -/
  QType : Type
  [decQ : DecidableEq QType]
  /-- `Val_type`. -/
  VType : Type
  /-- `query`. -/
  read : St Γ α → QType → VType

attribute [instance] QueryOf.decQ

/-- `type = < O_type, Q_type, Val_type >`. -/
@[reducible] def type (Γ : Scheme) (α : Type) [DecidableEq α]
    (Q : QueryOf Γ α) : MRDTType where
  OType := AppOp Γ α
  decOType := inferInstance
  QType := Q.QType
  ValType := Q.VType

/-- `do`. An insertion whose identity is already live is a no-op. -/
def step (S : St Γ α) (e : Op (AppOp Γ α)) : St Γ α :=
  match e.op with
  | .ins v p a g =>
      if e.time ∈ ids S then S
      else insertDown (e.time, v, p ++ Γ.code g (e.time - a)) S
  | .del x => S.filter (fun z => z.1 ≠ x)

/-- `merge`: surviving records of each branch, merged in descending order. -/
def mergeState (l a b : St Γ α) : St Γ α :=
  mergeDown (a.filter (fun z => z.1 ∈ ids b || !(z.1 ∈ ids l)))
    (b.filter (fun z => !(z.1 ∈ ids l) && !(z.1 ∈ ids a)))

/-- `q(S)`: the payload list. -/
def payloads (S : St Γ α) : List α := S.map (fun z => z.2.1)

/-- `rc` is empty, as the appendix states for every row of this family. -/
def rcOf : AppOp Γ α → AppOp Γ α → OrderResult := fun _ _ => OrderResult.Either

/-- `D_type = < Sigma, sigma0, do, merge, query, rc >`, at an arbitrary
`rc`, because the negative results speak about more than one choice. -/
def D [DecidableEq α] (Q : QueryOf Γ α)
    (rc : AppOp Γ α → AppOp Γ α → OrderResult) : Impl (type Γ α Q) where
  Sigma := St Γ α
  decSigma := inferInstance
  sigma0 := []
  do_ := step
  merge := mergeState
  query := Q.read
  rc := rc

/-- The tuple with the empty `rc`. Every proof in this folder is about this
one, and every row of the family is an instance. -/
abbrev Dα (Γ : Scheme) (α : Type) [DecidableEq α] (Q : QueryOf Γ α) :
    Impl (type Γ α Q) := D Q rcOf

/-- The payload-list query, which every row of the family but the anchored
queue uses. -/
def payloadQuery (Γ : Scheme) (α : Type) : QueryOf Γ α where
  QType := Unit
  VType := List α
  read := fun S _ => payloads S

/-! ## Issuance -/

/-- Issuance: an insertion anchors at the root or at a live record whose
coordinate it carries, with a clock above the anchor; a deletion names a
live identity. -/
def CoreGuard (e : Op (AppOp Γ α)) (S : St Γ α) : Prop :=
  match e.op with
  | .ins _ p a _ =>
      a < e.time ∧ ((a = 0 ∧ p = []) ∨ ∃ v, ((a, v, p) : Record Γ α) ∈ S)
  | .del x => x ∈ ids S

def issuance [DecidableEq α] (Q : QueryOf Γ α)
    (rc : AppOp Γ α → AppOp Γ α → OrderResult) : Issuance (D Q rc).toMRDTSig where
  CanIssue := CoreGuard

end LeanProofs.NoSpecNonComm.Implementations.EmbeddedRGA
