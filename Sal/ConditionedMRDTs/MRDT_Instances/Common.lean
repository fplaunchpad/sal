import Sal.ConditionedMRDTs.Metatheory.Adequacy

/-!
# Shared kernel for the flat instance discharges

The Boolean `bor_*` tautology kernel used by the four LCA-inclusive grow-only
unions (Grow-Only Set, Grow-Only Map, tombstone RGA, Peritext), together with
the Phase-2 catalog-sweep overview it was introduced with.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-! # Phase 2: the production catalog sweep (T11)

Six further production MRDTs, all in the **commuting class**: `rc = Either`
everywhere and all update pairs commute. Four are LCA-inclusive grow-only
unions (`mergeL l a b = l ∪ a ∪ b`, componentwise) — Grow-Only Set, Grow-Only
Map, RGA (tombstone), Peritext — for which every merge law is a Boolean
tautology (the `bor_*` kernel below); two are the counter group form
(`mergeL l a b = a + b − l`) — Increment-Only Counter, PN-Counter. All six
land end-to-end via the single arbitration capstone
`ra_linearizable3_via_capstone` (feeding `feasibleDeltaVCs3_of_delta` and
`cdVC3_of_all_comm` as the merge content).

Faithfulness notes: `set α = α → Bool` mirrors as before; Grow-Only Map's
`map ℕ (set ℕ)` is mirrored uncurried as `(ℕ × ℕ) → Bool` (its
`mysel`-observable semantics); Peritext's `MarkOp`/`AnchorAttachment`
structures are flattened to tuples (componentwise identical fields). -/

/-! ## The Boolean kernel for LCA-inclusive unions -/

theorem bor_rc (a b c : Bool) :
    ((a || b) || c) = ((a || c) || b) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem bor_comm (l a b : Bool) :
    (l || (a || b)) = (l || (b || a)) := by
  cases l <;> cases a <;> cases b <;> rfl

theorem bor_init (s : Bool) : (false || (false || s)) = s := by
  cases s <;> rfl

theorem bor_0op (l a b d : Bool) :
    ((l || d) || ((a || d) || (b || d))) = ((l || (a || b)) || d) := by
  cases l <;> cases a <;> cases b <;> cases d <;> rfl

theorem bor_peel (f a g d : Bool) :
    (f || ((a || d) || g)) = ((f || (a || g)) || d) := by
  cases f <;> cases a <;> cases g <;> cases d <;> rfl

theorem bor_redis (m x0 x1 x2 c : Bool) :
    ((m || (x0 || c)) || ((m || (x1 || c)) || (m || (x2 || c))))
      = (m || ((x0 || (x1 || x2)) || c)) := by
  cases m <;> cases x0 <;> cases x1 <;> cases x2 <;> cases c <;> rfl

theorem bor_lredis (l m x c y : Bool) :
    (l || ((m || (x || c)) || y)) = (m || ((l || (x || y)) || c)) := by
  cases l <;> cases m <;> cases x <;> cases c <;> cases y <;> rfl

end Sal.ConditionedMRDTs
