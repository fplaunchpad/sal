import Sal.MRDTs.Instances.EnableWinsFlag
import Sal.MRDTs.Paper1.NeemFlagEvent

namespace Sal.MRDTs.Paper1.EnableWinsFlagEvent
open Foundation Instances.EnableWinsFlag
abbrev Event := Op Action
abbrev boolStep := NeemFlagEvent.boolStep false
abbrev machine := NeemFlagEvent.machine false false
abbrev spec := NeemFlagEvent.spec false false
abbrev simulation := NeemFlagEvent.simulation false false
abbrev historySound := NeemFlagEvent.historySound false false
abbrev compatible := NeemFlagEvent.compatible false false
end Sal.MRDTs.Paper1.EnableWinsFlagEvent
