import Sal.MRDTs.Paper1.ConcreteVCExecution
import Sal.MRDTs.Paper1.CertifiedClosedExecution

/-! Neem's corrected flag algorithm: per-replica integer counter and physical
winning bit. The F* `Map_extended.const` has universal domain, so every source
reachable map has universal domain. Total row functions preserve that domain
and source equality exactly. Counter arithmetic and all branches of mergeFlag
are copied from App_mrdt.fst; no operation-log implementation replaces them.
The App_mrdt source exposes no query. `active` interprets its physical bit by
existence, as motivated by Enable-wins semantics in Neem/results.tex. -/
namespace Sal.MRDTs.Instances.NeemFlag
open Foundation

inductive Action where
  | winning
  | reset
  deriving DecidableEq

abbrev Cell := Int × Bool
abbrev State := Nat → Cell

def initial (initialFlag : Bool) : State := fun _ => (0,initialFlag)
def update (s : State) (e : Op Action) : State := match e.op with
  | .winning => fun r => if r = e.2.1 then ((s r).1 + 1,true) else s r
  | .reset => fun r => ((s r).1,false)

def mergeFlag (l a b : Cell) : Bool :=
  if a.2 && b.2 then true
  else if !a.2 && !b.2 then false
  else if a.2 then decide (a.1 > l.1)
  else decide (b.1 > l.1)
def mergeCell (l a b : Cell) : Cell := (a.1 + b.1 - l.1,mergeFlag l a b)
def merge (l a b : State) : State := fun r => mergeCell (l r) (a r) (b r)
noncomputable def active (s : State) : Bool := by
  classical
  exact decide (∃ r, (s r).2 = true)
noncomputable def D (initialFlag : Bool) (invert : Bool := false) : MRDTSig where
  State := State
  dec_state := fun _ _ => Classical.propDecidable _
  init := initial initialFlag
  AppOp := Action
  dec_op := inferInstance
  Query := Unit
  Value := Bool
  update := update
  merge := merge
  query := fun s _ => if invert then !active s else active s

def generation (initialFlag : Bool) (invert : Bool := false) : Issuance (D initialFlag invert) where
  CanIssue := fun _ _ => True

theorem active_true_iff (s : State) : active s = true ↔ ∃ r, (s r).2 = true := by
  classical
  simp [active]

theorem active_initial (initialFlag : Bool) : active (initial initialFlag) = initialFlag := by
  cases initialFlag <;> simp [active,initial]

theorem active_winning (s : State) (ts r : Nat) :
    active (update s (ts,r,.winning)) = true := by
  rw [active_true_iff]
  exact ⟨r,by simp [update,Op.op]⟩
theorem active_reset (s : State) (ts r : Nat) :
    active (update s (ts,r,.reset)) = false := by
  simp [active,update,Op.op]

end Sal.MRDTs.Instances.NeemFlag

namespace Sal.MRDTs.Instances.EnableWinsFlag
abbrev Action := NeemFlag.Action
abbrev State := NeemFlag.State
def enable : Action := .winning
def disable : Action := .reset
abbrev initial := NeemFlag.initial false
abbrev update := NeemFlag.update
abbrev merge := NeemFlag.merge
noncomputable abbrev D := NeemFlag.D false
abbrev generation := NeemFlag.generation false
noncomputable abbrev query := NeemFlag.active
end Sal.MRDTs.Instances.EnableWinsFlag
