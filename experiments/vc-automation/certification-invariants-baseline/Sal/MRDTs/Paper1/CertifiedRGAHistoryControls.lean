import Sal.MRDTs.Paper1.CertifiedRGAHistoryCommutation

namespace Sal.MRDTs.Paper1.CertifiedRGAHistory.Controls
open Foundation Instances.EmbedRGA
open Sal.EmbedRGA

abbrev D := E unaryCode Nat

def seed : Op (EOp Nat) := (1,0,.ins 10 [] 0)
def deletion : Op (EOp Nat) := (2,0,.del 1)
def insertion : Op (EOp Nat) := (3,0,.ins 30 [] 0)
def scratch : EState Nat := [(1,9,[false]),(100,10,[])]

/-- The two labels are issuable successively under the unchanged issuer.
Raw noncommutation nevertheless sees an unsorted scratch state. Both outcomes
are pinned explicitly; neither is taken from the implementation as an oracle. -/
theorem issuer_and_raw_counterexample :
    (generation (α := Nat) unaryCode).CanIssue seed D.init ∧
    (generation (α := Nat) unaryCode).CanIssue deletion (D.update D.init seed) ∧
    (generation (α := Nat) unaryCode).CanIssue insertion (D.update (D.update D.init seed) deletion) ∧
    D.update (D.update scratch insertion) deletion =
      [(3,30,[true,true,true,false]),(100,10,[])] ∧
    D.update (D.update scratch deletion) insertion =
      [(100,10,[]),(3,30,[true,true,true,false])] ∧
    D.update (D.update scratch insertion) deletion ≠
      D.update (D.update scratch deletion) insertion := by
  simp [generation, eApplicable, seed, deletion, insertion]
  native_decide

end Sal.MRDTs.Paper1.CertifiedRGAHistory.Controls
