import Sal.MRDTs.Instances.TreeMoveIncrementalMRDT

namespace Sal.MRDTs.Instances.TreeMove.Incremental
open Sal.MRDTs.Foundation
open Classical

/-- A hand-specified decreasing rank proves absence of cycles independently
of the move implementation. -/
theorem safe_of_rank (t : Tree) (rank : Node → Nat)
    (decreases : ∀ a b, edge t a b → rank b < rank a) : TreeSafe t := by
  intro node path
  have less : ∀ {a b}, Relation.TransGen (edge t) a b → rank b < rank a := by
    intro a b path
    induction path with
    | single h => exact decreases _ _ h
    | tail _ h ih => exact (decreases _ _ h).trans ih
  exact Nat.lt_irrefl _ (less path)

theorem sourceMove_accepts {t : Tree} {m : Move} (safe : TreeSafe t)
    (candidate : TreeSafe (setParent t m.child m.parent m.metadata)) :
    sourceMove t m = setParent t m.child m.parent m.metadata := by
  exact if_neg ((candidate_safe_iff t safe m).mp candidate)

theorem sourceMove_rejects {t : Tree} {m : Move} (rejected : Rejects t m) :
    sourceMove t m = t := if_pos rejected

theorem visible_no_trash {t : Tree}
    (atTrash : t trash = none)
    (noParent : ∀ a v, t a ≠ some (trash,v)) : visibleTree t = t := by
  funext n
  unfold visibleTree
  by_cases hidden : underTrash t n
  · rw [if_pos hidden]
    rcases hidden with equal | path
    · rw [equal,atTrash]
    · obtain ⟨a,_,v,edge⟩ := Relation.TransGen.tail'_iff.mp path
      exact False.elim (noParent a v edge)
  · rw [if_neg hidden]

/-- A node attached directly to the ordinary root is visible even when a
different part of the forest is under trash. -/
theorem visible_at_root {t : Tree} {n : Node} {v : Metadata}
    (ordinary : n ≠ trash) (parent : t n = some (root,v))
    (rootEmpty : t root = none) : visibleTree t n = some (root,v) := by
  have notHidden : ¬ underTrash t n := by
    rintro (equal | path)
    · exact ordinary equal
    obtain ⟨b,⟨w,edge⟩,rest⟩ := Relation.TransGen.head'_iff.mp path
    rw [parent] at edge
    cases Option.some.inj edge
    rcases rest.cases_head with equal | ⟨c,⟨u,edge⟩,_⟩
    · exact (by decide : root ≠ trash) equal
    · rw [rootEmpty] at edge
      cases edge
  simp [visibleTree,notHidden,parent]

/-- On supported distinct timestamps the operational comparison is precisely
Fig.4's timestamp comparison; replica/payload totalization is unreachable. -/
theorem source_comparison {a b : Event} (different : a.time ≠ b.time) :
    eventKey a < eventKey b ↔ a.time < b.time := by
  constructor
  · intro earlier
    by_contra notTime
    have backward : b.time < a.time := lt_of_le_of_ne (Nat.le_of_not_gt notTime) different.symm
    have keyBackward : eventKey b < eventKey a := List.Lex.rel backward
    exact lt_asymm earlier keyBackward
  · intro earlier
    exact List.Lex.rel earlier

/-- Literal Fig.4 apply_op, retained separately to audit that the raw-key
totalization has no effect on source executions with unique timestamps. -/
noncomputable def sourceApply (e : Event) : List LogEntry → Tree → RawState
  | [],t => push ⟨[],t⟩ e
  | entry :: rest,t =>
    if e.time < entry.event.time then
      push (sourceApply e rest (undo entry t)) entry.event
    else push ⟨entry :: rest,t⟩ e

theorem applyRaw_eq_sourceApply (e : Event) (log : List LogEntry) (t : Tree)
    (fresh : ∀ entry ∈ log, e.time ≠ entry.event.time) :
    applyRaw e log t = sourceApply e log t := by
  induction log generalizing t with
  | nil => rfl
  | cons entry rest ih =>
    simp only [applyRaw,sourceApply,source_comparison (fresh entry (by simp))]
    by_cases earlier : e.time < entry.event.time
    · simp only [earlier,ite_true]
      rw [ih _ (fun x hx => fresh x (by simp [hx]))]
    · simp only [earlier,ite_false]

theorem receive_eq_sourceApply (s : RawState) (e : Event)
    (fresh : ∀ entry ∈ s.log, e.time ≠ entry.event.time) :
    receive s e = sourceApply e s.log s.tree := by
  have absent : e ∉ events s := by
    intro present
    obtain ⟨entry,member,equal⟩ := List.mem_map.mp (List.mem_toFinset.mp present)
    exact fresh entry member (congrArg Op.time equal).symm
  rw [receive,if_neg absent]
  exact applyRaw_eq_sourceApply e s.log s.tree fresh

/-- Every actual receive trace belongs to the coherent carrier. No caller
supplies canonicality or a requested observation as an assumption. -/
noncomputable def run (ops : List Event) : RawState := ops.foldl receive initial

theorem run_eq_canonical (ops : List Event) : run ops = canonical ops.toFinset := by
  have empty : initial = canonical ∅ := by simp [canonical,descendingEvents,build,initial]
  rw [run,empty,receive_fold]
  simp

theorem run_coherent (ops : List Event) : Coherent (run ops) := by
  rw [run_eq_canonical]
  simp [Coherent,canonical_events]

theorem run_tree (ops : List Event) : (run ops).tree = render ops.toFinset := by
  rw [run_eq_canonical,canonical_tree]

end Sal.MRDTs.Instances.TreeMove.Incremental
