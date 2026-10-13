import Sal.MRDTs.Instances.DisableWinsFlag
import Sal.MRDTs.Paper1.NeemFlagEvent

namespace Sal.MRDTs.Paper1.DisableWinsFlagEvent
open Foundation Instances.DisableWinsFlag
abbrev Event := Op Action
abbrev boolStep := NeemFlagEvent.boolStep true
abbrev machine := NeemFlagEvent.machine true true
abbrev spec := NeemFlagEvent.spec true true
abbrev simulation := NeemFlagEvent.simulation true true
abbrev historySound := NeemFlagEvent.historySound true true
abbrev compatible := NeemFlagEvent.compatible true true
end Sal.MRDTs.Paper1.DisableWinsFlagEvent
