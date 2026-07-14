import Sal.ConditionedMRDTs.Metatheory.HonestReach
import Sal.MRDTs.RGA_Embed.RGA_Embed_ChainLex
import Sal.MRDTs.RGA_Embed.Embed_Code_Binary

/-!
# The embedded-chain RGA as a conditioned MRDT instance — §1, the datatype

Route decision (recorded): the **mergeable-queue route**, not the RGA_TF
55-file chain. The queue's `JoinLemma3At` hook requires canonical states to
be *unique per event set* (`Shesha_Join_Refuted` shows the hook is false
without it; the queue was immune because its canonical states are unique).
The embedded-chain RGA has exactly that property — coordinates are birth
constants and the display is their sort, so the state is a function of the
event set (design doc Thm 4; `q_fold_canon`'s analogue) — which is why this
instance exists at all.

The framework needs `DecidableEq State`, so the instance state is the
**canonical sorted association list** — the document itself, records
`(id, element, coordinate)` strictly descending by key — rather than the
function-based map of `Sal/MRDTs/RGA_Embed/RGA_Embed_MRDT.lean`. The two
present the same datatype; the kernel theorems (commutation, stability,
chain-lex) live on the map model, and the fold-canonicity theorem of this
file's later sections is what makes the list state canonical.

Sections mirror `MRDT_Instances/MergeableQueue/MergeableQueue.lean`:
§1 datatype (this file's content) · §2 event helpers + canonical list ·
§3 well-formed enumerations + fold = canon · §5 honest histories ·
§6 the Join (the merge is its own linearization witness) · §7 capstone via
`HonestReach` · §8 `applicable` discharges honesty. See `PLAN.md`.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode keyLt keyLe key unaryCode binaryCode)

/-! ## §1  The datatype -/

inductive EOp : Type where
  | ins (e : ℕ) (π : List Bool) (a : ℕ)   -- element, coordinate prefix, anchor
  | del (x : ℕ)
deriving DecidableEq

/-- A record: `(id, element, absolute coordinate)`. -/
abbrev ERec : Type := ℕ × ℕ × List Bool

/-- State: the document — records strictly descending by key. Canonical
single-list form (sortedness is the `Inv`-grade invariant, established by
fold-canonicity in §3, not baked into the type). -/
abbrev EState : Type := List ERec

def eIds (s : EState) : List ℕ := s.map Prod.fst

/-- The coordinate an insert writes — a function of the op alone (the carried
prefix + the delta codeword; design doc §3: the prefix is for the proof). -/
def eCoord (Γ : OrderedPrefixCode) (o : Op EOp) : List Bool :=
  match o.2.2 with
  | .ins _ π a => π ++ Γ.enc (o.1 - a)
  | .del _     => []

/-- Sorted insertion, descending by key: the newcomer goes before the first
record with a strictly smaller key. -/
def eInsert (r : ERec) : EState → EState
  | [] => [r]
  | x :: xs =>
      if keyLt (key x.2.2) (key r.2.2) then r :: x :: xs
      else x :: eInsert r xs

/-- Insert places the record at its sorted position (idempotent on a present
id); delete removes the record wherever it sits. Strictness about *which*
target lives in the honesty layer (§8), not in the effect. -/
def eUpdate (Γ : OrderedPrefixCode) (s : EState) (o : Op EOp) : EState :=
  match o.2.2 with
  | .ins e π a =>
      if o.1 ∈ eIds s then s
      else eInsert (o.1, e, π ++ Γ.enc (o.1 - a)) s
  | .del x => s.filter (fun r => decide (r.1 ≠ x))

/-- Merge of two sorted lists, descending by key (ties cannot occur between
distinct ids on chain-generated states — `coordOf_inj`). -/
def eMerge2 : EState → EState → EState
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
      if keyLt (key y.2.2) (key x.2.2) then x :: eMerge2 xs (y :: ys)
      else y :: eMerge2 (x :: xs) ys
termination_by xs ys => xs.length + ys.length

/-- Ternary merge: OR-set survival (values immutable, so each survivor's
record is read off whichever input holds it), re-canonicalized by the sorted
2-merge. Branch `a` contributes its survivors (shared with `b`, or new since
`l`); branch `b` contributes its own news not already contributed. -/
def eMergeL (l a b : EState) : EState :=
  eMerge2
    (a.filter (fun r => decide (r.1 ∈ eIds b ∨ r.1 ∉ eIds l)))
    (b.filter (fun r => decide (r.1 ∉ eIds l ∧ r.1 ∉ eIds a)))

/-- The embedded-chain RGA, parametric in the code (instantiate at
`binaryCode` for the entropy-optimal artifact, `unaryCode` for hand
computation). `Inv`/`applicable` are trivially true — as in the queue, the
honesty discipline lives in the configuration layer (§5/§8), not the
signature. -/
def E (Γ : OrderedPrefixCode) : ConditionedMRDTSig where
  State := EState
  dec_state := inferInstance
  init := []
  AppOp := EOp
  dec_op := inferInstance
  Query := Unit
  Value := List ℕ
  update := eUpdate Γ
  merge := fun a b => eMergeL [] a b
  query := fun s _ => s.map (fun r => r.2.1)
  rc := fun _ _ => RcRes.Either
  mergeL := eMergeL
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem E_core_update (Γ : OrderedPrefixCode) (s : EState) (o : Op EOp) :
    (E Γ).toCRDTSig.update s o = eUpdate Γ s o := rfl

theorem E_rc_either (Γ : OrderedPrefixCode) (o₁ o₂ : Op EOp) :
    (E Γ).toCRDTSig.rc o₁ o₂ = RcRes.Either := rfl

/-! ## §1½  First list algebra -/

theorem mem_eIds_eInsert {r : ERec} {t : ℕ} : ∀ {s : EState},
    t ∈ eIds (eInsert r s) ↔ t ∈ eIds s ∨ t = r.1
  | [] => by simp [eInsert, eIds]
  | x :: xs => by
      by_cases h : keyLt (key x.2.2) (key r.2.2) = true
      · simp only [eInsert, if_pos h, eIds, List.map_cons, List.mem_cons]
        tauto
      · simp only [eInsert, if_neg h, eIds, List.map_cons, List.mem_cons]
        have ih := @mem_eIds_eInsert r t xs
        simp only [eIds] at ih
        rw [ih]
        tauto

theorem mem_eIds_update_del {Γ : OrderedPrefixCode} {s : EState} {ts r x t : ℕ} :
    t ∈ eIds (eUpdate Γ s (ts, r, .del x)) ↔ t ∈ eIds s ∧ t ≠ x := by
  simp only [eUpdate, eIds, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hm := List.mem_of_mem_filter hp
    have hx := List.of_mem_filter hp
    simp at hx
    exact ⟨⟨p, hm, rfl⟩, hx⟩
  · rintro ⟨⟨p, hp, rfl⟩, hne⟩
    exact ⟨p, List.mem_filter.mpr ⟨hp, by simpa using hne⟩, rfl⟩

end Sal.ConditionedMRDTs
