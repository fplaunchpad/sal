import Sal.MRDTs.Instances.EnableWinsFlag

/-! Neem's Disable-wins_flag/App_mrdt.fst. Its Map_extended.const has universal
Nat domain, so every reachable map has universal domain. A total row function
therefore retains the source's map equality on reachable states. The source
initialises every row to (0,true); the explicit update at key zero is redundant.
True row bits record outstanding disables. The added client query returns
whether the flag is enabled. No query is provided by the source artifact. -/
namespace Sal.MRDTs.Instances.DisableWinsFlag
open Foundation
open Classical

abbrev Action := NeemFlag.Action
abbrev Cell := NeemFlag.Cell
abbrev State := NeemFlag.State

/-- Source Enable clears every disable bit. -/
def enable : Action := .reset
/-- Source Disable advances the issuer's disable counter. -/
def disable : Action := .winning
abbrev initial := NeemFlag.initial true
abbrev update := NeemFlag.update
abbrev mergeFlag := NeemFlag.mergeFlag
abbrev mergeCell := NeemFlag.mergeCell
abbrev merge := NeemFlag.merge

/-- Client Boolean; internal true bits denote disabled, hence the negation. -/
noncomputable def query (s : State) (_ : Unit) : Bool := !NeemFlag.active s

noncomputable abbrev D := NeemFlag.D true true
abbrev generation := NeemFlag.generation true true

@[simp] theorem query_initial : query initial () = false := by
  simp [query,initial,NeemFlag.active_initial]
@[simp] theorem query_enable (s : State) (e : Op Action) (h : e.op = .reset) :
    query (update s e) () = true := by
  rcases e with ⟨ts,rep,op⟩
  simp only [Op.op] at h; subst op
  simp [query,NeemFlag.active_reset]
@[simp] theorem query_disable (s : State) (e : Op Action) (h : e.op = .winning) :
    query (update s e) () = false := by
  rcases e with ⟨ts,rep,op⟩
  simp only [Op.op] at h; subst op
  simp [query,NeemFlag.active_winning]

theorem merge_comm (l a b : State) : merge l a b = merge l b a := by
  funext r
  apply Prod.ext
  · simp [merge,mergeCell,NeemFlag.merge,NeemFlag.mergeCell]; omega
  · simp only [merge,mergeCell,mergeFlag,NeemFlag.merge,NeemFlag.mergeCell,NeemFlag.mergeFlag]
    cases (a r).2 <;> cases (b r).2 <;> simp

theorem merge_idem (s : State) : merge s s s = s := by
  funext r
  apply Prod.ext
  · simp [merge,mergeCell,NeemFlag.merge,NeemFlag.mergeCell]
  · simp only [merge,mergeCell,mergeFlag,NeemFlag.merge,NeemFlag.mergeCell,NeemFlag.mergeFlag]
    cases (s r).2 <;> simp

end Sal.MRDTs.Instances.DisableWinsFlag
