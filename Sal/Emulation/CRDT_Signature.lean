import Sal.ConditionedMRDTs.Framework.Base.CRDT_Signature

/-!
# Forwarding stub: content moved

The CRDT signature core (`Op`, `Timestamp`, `Replica`, `CRDTSig`, `RcRes`,
`applySeq`, …) now lives in the metatheory conditioned tree so it can be
modified there without touching the emulation framework's layout:
`Sal/MRDTs/Metatheory/Development/Emulation/CRDT_Signature.lean`.
All declarations keep the `Sal.Emulation` namespace; this stub keeps every
existing `import Sal.Emulation.CRDT_Signature` working unchanged.
-/
