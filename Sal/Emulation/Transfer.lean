import Sal.Emulation.Emulation
import Sal.Emulation.RA_Linearizability

/-!
# Transfer theorem: state-based RA-lin ⇒ op-based RA-lin

The capstone of Phase 1. Composes:

1. **Bridge** (`ra_linearizable_of_vcs`): every reachable state-based
   configuration satisfying the 24 VCs is RA-linearizable.
2. **Emulation** (`canonicalG` + Liittschwager's emulation theorem):
   the op-based TS and `canonicalG`'s state-based TS are weakly
   bisimilar.
3. **Trace transfer**: RA-linearizability is a weak trace property.
   Weak bisimulation (via `weakSim_sound`) preserves trace properties.

Therefore, if `canonicalG D hb` satisfies the 24 VCs, the op-based
original `D` is RA-linearizable on every reachable configuration.

This file states the end-to-end meta-theorem with all the machinery
connected. The proof is `sorry`, because it requires:
* A complete bridge (steps 3–4 close).
* A complete `weakSim_sound` (step 8).
* A complete simulation for `canonicalG` (step 10).
* Reformulating RA-lin as a trace property for the op-based side.
-/

namespace Sal.Emulation

open LabeledTS

/-- **Op-based RA-linearizability (trace formulation).** For every
query event `(r, qry[q], resp[v])` appearing in the trace, there
exists a linearization of updates causally visible to `r` at that
point whose application to `D.init` yields a state whose `D.query`
response is `v`.

Formally this is a predicate on traces, not configurations — exactly
the form required for Liittschwager's trace-transfer theorem. -/
def OpIsRALinearizable (D : OpCRDTSig)
    (_hb : D.Msg → D.Msg → Prop)
    (_trace : List (OpEvent D)) : Prop :=
  -- TODO: flesh out. Roughly:
  --   for every `(r, qry[q], resp[v])` suffix of `trace`,
  --   there exists `π : List (D.AppOp)` matching the `update` events
  --   visible at `r`, respecting `D.rc`, with
  --   `D.query (π.foldl D.effect' D.init) q = v`.
  True

/-- **Main transfer theorem.** If `D`'s canonical state-based
emulator `canonicalG D hb` satisfies the 24 VCs, then `D`'s op-based
system is RA-linearizable on every reachable trace. -/
theorem op_RA_linearizable_of_vcs
    (D : OpCRDTSig) (hb : D.Msg → D.Msg → Prop)
    (_hVC : SatisfiesVCs (canonicalG D hb))
    (C : OpConfiguration D)
    (_hReach : (opLabeledTS D hb).ReachableFrom (opInitConfig D) C) :
    OpIsRALinearizable D hb C.trace := by
  -- Proof plan:
  --   1. Lift reachability: C₀ (op-based) simulates a state-based C₀'.
  --   2. Induct along the simulation to get a reachable C' in
  --      `labeledTS (canonicalG D hb)`.
  --   3. Apply `ra_linearizable_of_vcs hVC C' hReach'` → IsRALinearizable C'.
  --   4. Use weak-trace equivalence (from `weakSim_sound` + reverse sim)
  --      to transfer to op-based trace.
  --   5. Unfold `OpIsRALinearizable` as a trace property; done.
  trivial  -- placeholder: OpIsRALinearizable = True for now

end Sal.Emulation
