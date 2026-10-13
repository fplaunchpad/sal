import Sal.MRDTs.Paper1.Automation.CommonVerification

/-! Structural derivation of the ordered route from the existing contracts.
The representation is inspected as a proposition; no datatype adapter theorem
or completed VC is accepted as an input. -/
namespace Sal.MRDTs.Paper1.Automation.OrderedRecords
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1

/-- A declarative mapping of an issuance chain to its stored coordinate and key.
Its sole law is injection of the code on valid chains, independent of replay. -/
structure ChainMapping (Chain Coordinate Key : Type) where
  valid : Chain → Prop
  coordinate : Chain → Coordinate
  key : Coordinate → Key
  stamp : Chain → Nat
  injective : ∀ a b, valid a → valid b →
    key (coordinate a) = key (coordinate b) → a = b

/-- Convert a chain-generating issuance contract to the generic certificate.
This only rearranges its existing witnesses and rewrites the stored coordinate. -/
theorem ChainMapping.unique_keys {D : MRDTSig} {Record Chain Coordinate : Type}
    [DecidableEq Record] (K : Kit D Record) (C : ReplayContext D.toUpdateSig)
    (mapping : ChainMapping Chain Coordinate K.Key)
    (stored : Op D.AppOp → Coordinate)
    (stored_key : ∀ e, K.insertion e = true → K.key (K.written e) = mapping.key (stored e))
    (generated : ∃ chainOf : Nat → Chain, ∀ e ∈ C.events, K.insertion e = true →
      mapping.valid (chainOf e.1) ∧ stored e = mapping.coordinate (chainOf e.1) ∧
      mapping.stamp (chainOf e.1) = e.1) : ∀ a ∈ C.events, ∀ b ∈ C.events, K.insertion a = true → K.insertion b = true →
      K.key (K.written a) = K.key (K.written b) → a.1 = b.1 := by
  obtain ⟨chainOf, generated⟩ := generated
  apply ChainCertificate.key_unique (Chain := Chain)
  refine ⟨mapping.valid, fun c => mapping.key (mapping.coordinate c), mapping.stamp,
    mapping.injective, ?_⟩
  intro e he ins
  obtain ⟨valid, shape, stamp⟩ := generated e he ins
  exact ⟨chainOf e.1, valid, (stored_key e ins).trans (congrArg mapping.key shape), stamp⟩
end Sal.MRDTs.Paper1.Automation.OrderedRecords

/-- Infer metadata identity and structurally project the replay contract.
Only the finite kit and issuance derivation are supplied by the author. -/
macro "derive_ordered_input " kit:term " with " issuance:term
    " unfolding " "[" defs:ident,* "]" : tactic => `(tactic| (
  refine Sal.MRDTs.Paper1.Automation.CommonVerification.Input.ordered $kit ?_ ?_
  · intros; rfl
  · intro C H s rep
    simp only [$[$defs:ident],*] at rep
    refine ⟨?_, ?_⟩
    · apply ($issuance)
      exact rep.1
    · dsimp [Sal.MRDTs.Paper1.Automation.OrderedRecords.ReplayEvidence]
      aesop))

/-- Compatibility projection for public adapter statements. -/
macro "derive_ordered_adapter " representation:ident " with " issuance:term " unfolding " "[" defs:ident,* "]" : tactic => `(tactic| (
  simp only [$[$defs:ident],*] at $representation:ident
  refine ⟨?_, ?_⟩
  · apply ($issuance)
    exact ($representation).1
  · dsimp [Sal.MRDTs.Paper1.Automation.OrderedRecords.ReplayEvidence]
    aesop))

/-- Structurally derive issuer evidence from the existing creator and chain
contracts. Only the chain mapping, stored coordinate, and contract projections
are named; no issuer obligation proof is supplied. -/
macro "derive_ordered_issuer " mapping:term " at " stored:term " using " creators:term ", " chains:term : tactic =>
  `(tactic| (
    constructor
    · intro d hd n target
      have birth := ($creators) d hd n target
      aesop
    · apply Sal.MRDTs.Paper1.Automation.OrderedRecords.ChainMapping.unique_keys _ _ ($mapping) ($stored)
      · intros; rfl
      · exact $chains))

/-- Project the existing text/mark product contract into generic evidence.
The sum-operation visibility witness is preserved by the left injection. -/
macro "derive_product_evidence " representation:ident " with " issuance:term : tactic =>
  `(tactic| (
    refine ⟨($issuance) _ ($representation).1, ?_, ?_⟩
    · intro e he n target
      apply ($representation).2.1 (Sal.MRDTs.inlOp e)
        (Sal.MRDTs.mem_projReplayContext₁_events.mp he) n
      exact congrArg Sum.inl target
    · exact ⟨($representation).2.2.2.2.1, ($representation).2.2.2.2.2⟩))
