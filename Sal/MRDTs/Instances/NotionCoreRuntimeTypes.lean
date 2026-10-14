import Sal.MRDTs.Instances.NotionCoreStructuralFacts
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

/-! Typed executable keys shared by the native structural core. UTF-16 session
units and text atoms remain explicit naturals; source codecs are outside this
module. No original declaration is changed. -/
namespace Sal.MRDTs.Instances.NotionCoreRuntimeTypes
open NotionRunAllocation (Id)
open NotionCorePayload (BlockKey)
open NotionCoreOriginTree (Origin)

deriving instance BEq, ReflBEq, LawfulBEq, Hashable for NotionRunAllocation.Id
deriving instance BEq, ReflBEq, LawfulBEq, Hashable for BlockKey
deriving instance BEq, ReflBEq, LawfulBEq, Hashable for Origin

abbrev ItemKey := BlockKey × Id
abbrev OriginKey := BlockKey × Origin
end Sal.MRDTs.Instances.NotionCoreRuntimeTypes
