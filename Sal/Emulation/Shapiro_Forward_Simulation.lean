import Sal.Emulation.Conditioned_Network_Progress

/-!
# Forward simulation obligations for Shapiro emulation

The transition plumbing is generic.  The substantive coupling records which
immutable conditioned version was produced by each op message and proves that
replica states, buffers, and that correspondence survive update, query, and
delivery.  From those local laws this file constructs the required `WeakSimM`.
-/

namespace Sal.Emulation

open Sal.ConditionedMRDTs LabeledTS

variable {D : OpCRDTSig} {hb : D.Msg → D.Msg → Prop}

structure ShapiroNetworkCoupling (I : OperationalTransferInput D hb)
    (P : ConditionedNetworkProgress I) where
  rel : OpConfiguration D →
    ConditionedNetworkConfig (shapiroConditionedG D I.schedule) → Prop
  initial : rel (opInitConfig D)
    (conditionedNetworkInit (shapiroConditionedG D I.schedule)
      I.verified.initInv)
  honest : ∀ {O C}, rel O C → I.verified.Honest
    (Sal.ConditionedMRDTs.Configuration.core C.core)
  replica : ∀ {O C}, rel O C → ∀ {r s}, O.replicas r = some s →
    ∃ x : EmulatorState D, C.core.N r = some x ∧ x.materialized = s
  updateEnabled : ∀ {O O' C r op}, rel O C →
    (disciplinedOpLabeledTS D hb).step O (.update r op) O' →
    P.CanUpdate C r op
  updatePreserved : ∀ {O O' C C' r op t}, rel O C →
    (disciplinedOpLabeledTS D hb).step O (.update r op) O' →
    ConditionedNetworkStep (shapiroConditionedG D I.schedule)
      (fun core => I.verified.Honest
        (Sal.ConditionedMRDTs.Configuration.core core))
      C (.apply t r op) C' → rel O' C'
  queryPreserved : ∀ {O O' C r q v}, rel O C →
    (disciplinedOpLabeledTS D hb).step O (.query r q v) O' → rel O' C
  deliveryEnabled : ∀ {O O' C r m}, rel O C →
    (disciplinedOpLabeledTS D hb).step O (.deliver r m) O' →
    ∃ snapshot, P.CanDeliver C r snapshot
  deliveryPreserved : ∀ {O O' C C' r m snapshot}, rel O C →
    (disciplinedOpLabeledTS D hb).step O (.deliver r m) O' →
    P.CanDeliver C r snapshot →
    ConditionedNetworkStep (shapiroConditionedG D I.schedule)
      (fun core => I.verified.Honest
        (Sal.ConditionedMRDTs.Configuration.core core))
      C (.merge r r) C' → rel O' C'

namespace ShapiroNetworkCoupling

/-- The local Shapiro coupling laws entail the datatype-generic forward weak
simulation from disciplined op executions to the conditioned snapshot
network. -/
def forward (K : ShapiroNetworkCoupling I P) :
    WeakSimM (disciplinedOpLabeledTS D hb)
      (conditionedNetworkObservedTS D I)
      (disciplinedOpToConditionedNetworkLabels D I) where
  rel := K.rel
  step := by
    intro O O' C ℓ hrel hstep
    rcases hstep with ⟨hdiscipline, hop⟩
    cases hop with
    | opUpdate hs hm recipients O' htrace hreps hbuf =>
        have hsource : (disciplinedOpLabeledTS D hb).step O
            (.update _ _) O' := ⟨hdiscipline,
          .opUpdate hs hm recipients O' htrace hreps hbuf⟩
        have henabled := K.updateEnabled hrel hsource
        obtain ⟨t, vNew, C', htarget, hhead, hbuffer⟩ :=
          P.update henabled recipients
        refine ⟨C', ?_, K.updatePreserved hrel hsource htarget⟩
        exact WeakSimM.weakStep_of_step
          ⟨.apply t _ _, htarget, rfl⟩
    | opQuery hs hv O' htrace hreps hbuf =>
        have hsource : (disciplinedOpLabeledTS D hb).step O
            (.query _ _ _) O' := ⟨hdiscipline,
          .opQuery hs hv O' htrace hreps hbuf⟩
        obtain ⟨x, hx, hmat⟩ := K.replica hrel hs
        refine ⟨C, ?_, K.queryPreserved hrel hsource⟩
        subst hv
        rw [← hmat]
        exact ConditionedNetworkProgress.queryWeak I (K.honest hrel) hx
    | opDeliver hin henabled hs O' htrace hreps hbuf =>
        have hsource : (disciplinedOpLabeledTS D hb).step O
            (.deliver _ _) O' := ⟨hdiscipline,
          .opDeliver hin henabled hs O' htrace hreps hbuf⟩
        obtain ⟨snapshot, hdeliver⟩ := K.deliveryEnabled hrel hsource
        obtain ⟨C', htarget⟩ := P.deliver hdeliver
        refine ⟨C', ?_, K.deliveryPreserved hrel hsource hdeliver htarget⟩
        exact WeakSimM.weakStep_of_step
          ⟨.merge _ _, htarget, rfl⟩

theorem initialRelated (K : ShapiroNetworkCoupling I P) :
    K.forward.rel (opInitConfig D)
      (conditionedNetworkInit (shapiroConditionedG D I.schedule)
        I.verified.initInv) := K.initial

end ShapiroNetworkCoupling

end Sal.Emulation
