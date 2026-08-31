import Sal.MRDTs.Framework.Base.Replay

/-!
# Replay context

The replay metatheory depends only on replica-indexed event sets, event
visibility, timestamp uniqueness, and same-replica visibility order. It does not
define an operational semantics: MRDT execution, versions, parents, and merge
bases live in `Sal.MRDTs.Framework.Execution`.

An MRDT configuration projects to this context when invoking the reusable
ordering and canonical-state lemmas.
-/

namespace Sal.MRDTs.Foundation

/-- The part of an MRDT configuration inspected by replay-order proofs.

`ReplayContext` deliberately contains no labels, transition relation, initial
configuration, version graph, or merge operation. -/
structure ReplayContext (D : UpdateSig) where
  L : Replica → Option (Set (Op D.AppOp))
  vis : Op D.AppOp → Op D.AppOp → Prop
  /-- Distinct observed events have distinct timestamps. -/
  timestamps_distinct :
    ∀ {a b : Op D.AppOp} {r s r' s'},
      L r = some s → s a → L r' = some s' → s' b →
      a ≠ b → a.1 ≠ b.1
  /-- Distinct events issued by one replica are visibility-comparable. -/
  vis_total_same_replica :
    ∀ {a b : Op D.AppOp} {r s r' s'},
      L r = some s → s a → L r' = some s' → s' b →
      a ≠ b → a.2.1 = b.2.1 → vis a b ∨ vis b a

namespace ReplayContext

/-- Set of events observed anywhere in the replay context. -/
def events {D : UpdateSig} (C : ReplayContext D) : Set (Op D.AppOp) :=
  fun e => ∃ r s, C.L r = some s ∧ s e

end ReplayContext

end Sal.MRDTs.Foundation
