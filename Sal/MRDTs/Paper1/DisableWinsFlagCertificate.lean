import Sal.MRDTs.Paper1.DisableWinsFlagEvent
import Sal.MRDTs.Paper1.NeemFlagCertificate

namespace Sal.MRDTs.Paper1.DisableWinsFlagEvent
open Foundation Instances.DisableWinsFlag
abbrev policy := NeemFlagEvent.policy
abbrev conditions := NeemFlagEvent.conditions true true
abbrev splitLaws := NeemFlagEvent.splitLaws true true

theorem certifiedV : EventCertifiedSpecificationRAV D policy spec generation :=
  NeemFlagEvent.certifiedV true true

theorem certified : EventCertifiedSpecificationRA D policy spec generation := certifiedV.ordinary
end Sal.MRDTs.Paper1.DisableWinsFlagEvent
