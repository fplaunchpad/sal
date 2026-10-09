import Sal.MRDTs.Paper1.Automation.EmbeddedOrderedPrimitives
import Sal.MRDTs.Paper1.Automation.SidedOrderedPrimitives
import Sal.MRDTs.Paper1.Automation.OrderedRecordRules

/-! Explicit helper selection registry for finite raw ordered-record goals.
Only raw list primitives are registered: no replay, representation, VC, Join
or issuer correctness theorem. Registrations are part of the supplied effort. -/
open Sal.MRDTs.Instances.EmbedRGA Sal.MRDTs.Instances.SidedEmbedRGA

attribute [ordered_algorithm_simps, ordered_generic_simps, aesop (rule_sets := [OrderedGeneric]) norm simp]
  Sal.MRDTs.Paper1.Automation.EmbeddedPrimitives.insertion
  Sal.MRDTs.Paper1.Automation.EmbeddedPrimitives.merging
  Sal.MRDTs.Paper1.Automation.SidedPrimitives.insertion
  Sal.MRDTs.Paper1.Automation.SidedPrimitives.merging
attribute [ordered_generic_simps, aesop (rule_sets := [OrderedGeneric]) norm simp]
  Sal.MRDTs.Paper1.Automation.OrderedLists.mem_insert
  Sal.MRDTs.Paper1.Automation.OrderedLists.mem_merge2
  List.mem_toFinset
attribute [aesop (rule_sets := [OrderedGeneric]) safe apply] List.Pairwise.filter

attribute [ordered_record_simps, aesop (rule_sets := [OrderedRecord]) norm simp]
  mem_eInsert mem_eMerge2 mem_sInsert mem_sMerge2 List.mem_toFinset
attribute [aesop (rule_sets := [OrderedRecord]) safe apply]
  eInsert_sorted eMerge_sorted esorted_ext sInsert_sorted sMerge_sorted ssorted_ext List.Pairwise.filter

/-- Shared conversion of finite carrier equality into raw list membership. -/
theorem ordered_record_membership {R : Type} [DecidableEq R] {s t : List R}
    (same : s.toFinset = t.toFinset) : ∀ p, p ∈ s ↔ p ∈ t := by
  intro p
  have h : p ∈ s.toFinset ↔ p ∈ t.toFinset := by rw [same]
  simpa only [List.mem_toFinset] using h
set_option aesop.warn.applyIff false in
attribute [aesop (rule_sets := [OrderedRecord, OrderedGeneric]) safe apply] ordered_record_membership

/-- Select raw helpers by their conclusion shape and solve remaining finite
membership/order premises using the local assumptions and generic rules. -/
macro "ordered_record" : tactic => `(tactic| (aesop (rule_sets := [OrderedRecord, -default]) (config := { warnOnNonterminal := false }) <;> grind))

macro "ordered_record_simp" : tactic => `(tactic| try simp only [ordered_record_simps, List.mem_filter, decide_eq_true_eq])

attribute [ordered_order] Sal.MRDTs.Paper1.Automation.EmbeddedPrimitives.order
attribute [ordered_order] Sal.MRDTs.Paper1.Automation.SidedPrimitives.order

open Lean Elab Tactic in
elab "ordered_apply" : tactic => do
  let certificates ← labelled `ordered_order
  for certificate in certificates do
    let saved ← saveState
    let cert := mkIdent certificate
    try
      evalTactic (← `(tactic| first
        | apply Sal.MRDTs.Paper1.Automation.OrderedLists.insert_pairwise $cert
        | apply Sal.MRDTs.Paper1.Automation.OrderedLists.filtered_merge_pairwise $cert
        | apply Sal.MRDTs.Paper1.Automation.OrderedLists.pairwise_ext $cert))
      return
    catch _ => saved.restore
  throwError "no registered order certificate matches this canonical-list goal"

macro "ordered_generic" : tactic => `(tactic| (
  try simp only [ordered_algorithm_simps]
  first | ordered_apply | skip
  all_goals first
  | assumption
  | (intro x hx; simp only [ne_eq, decide_eq_true_eq]; intro bad
     exact bad.2 (List.mem_map.mpr ⟨x, hx, rfl⟩))
  | (aesop (rule_sets := [OrderedGeneric, -default]) (config := { warnOnNonterminal := false }) <;> grind)))
macro "ordered_generic_simp" : tactic => `(tactic| try simp only [ordered_generic_simps, List.mem_filter, decide_eq_true_eq])
