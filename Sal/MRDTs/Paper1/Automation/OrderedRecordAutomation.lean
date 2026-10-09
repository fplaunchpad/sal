import Sal.MRDTs.Instances.EmbedRGA
import Sal.MRDTs.Instances.SidedEmbedRGA
import Sal.MRDTs.Paper1.Automation.OrderedRecordRules

/-! Explicit helper selection registry for finite raw ordered-record goals.
Only raw list primitives are registered: no replay, representation, VC, Join
or issuer correctness theorem. Registrations are part of the supplied effort. -/
open Sal.MRDTs.Instances.EmbedRGA Sal.MRDTs.Instances.SidedEmbedRGA

attribute [ordered_record_simps, aesop (rule_sets := [OrderedRecord]) norm simp]
  mem_eInsert mem_sInsert mem_eMerge2 mem_sMerge2 List.mem_toFinset
attribute [aesop (rule_sets := [OrderedRecord]) safe apply]
  eInsert_sorted sInsert_sorted eMerge_sorted sMerge_sorted esorted_ext ssorted_ext List.Pairwise.filter

/-- Shared conversion of finite carrier equality into raw list membership. -/
theorem ordered_record_membership {R : Type} [DecidableEq R] {s t : List R}
    (same : s.toFinset = t.toFinset) : ∀ p, p ∈ s ↔ p ∈ t := by
  intro p
  have h : p ∈ s.toFinset ↔ p ∈ t.toFinset := by rw [same]
  simpa only [List.mem_toFinset] using h
set_option aesop.warn.applyIff false in
attribute [aesop (rule_sets := [OrderedRecord]) safe apply] ordered_record_membership

/-- Select raw helpers by their conclusion shape and solve remaining finite
membership/order premises using the local assumptions and generic rules. -/
macro "ordered_record" : tactic => `(tactic| (aesop (rule_sets := [OrderedRecord, -default]) (config := { warnOnNonterminal := false }) <;> grind))

macro "ordered_record_simp" : tactic => `(tactic| try simp only [ordered_record_simps, List.mem_filter, decide_eq_true_eq])
