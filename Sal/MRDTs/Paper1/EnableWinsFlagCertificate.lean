import Sal.MRDTs.Paper1.EnableWinsFlagEvent
import Sal.MRDTs.Paper1.NeemFlagCertificate

namespace Sal.MRDTs.Paper1.EnableWinsFlagEvent
open Foundation Instances.EnableWinsFlag
abbrev policy := NeemFlagEvent.policy
abbrev conditions := NeemFlagEvent.conditions false false
abbrev splitLaws := NeemFlagEvent.splitLaws false false

theorem certifiedV : EventCertifiedSpecificationRAV D policy spec generation :=
  NeemFlagEvent.certifiedV false false

theorem certified : EventCertifiedSpecificationRA D policy spec generation := certifiedV.ordinary
end Sal.MRDTs.Paper1.EnableWinsFlagEvent
