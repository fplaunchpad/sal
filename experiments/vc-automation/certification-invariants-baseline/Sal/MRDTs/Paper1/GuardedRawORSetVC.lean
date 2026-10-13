import Sal.MRDTs.Paper1.Automation.ORSetInputs
import Sal.MRDTs.Paper1.GuardedEqualityVC
import Sal.MRDTs.Paper1.ConcreteORSetAlgebra
import Sal.MRDTs.Paper1.GuardedRawORSetReplay
import Sal.MRDTs.Paper1.ConcreteJoin

namespace Sal.MRDTs.Paper1.EfficientORSet.GuardedRawVC
open Foundation
open Sal.MRDTs.Instances.EfficientORSet
open ConcreteRep
variable {α : Type} [DecidableEq α]

/-- Coherent represented histories supply the exact intersection coverage
needed by the raw local-add equation, without a Join premise. -/
theorem local_add_represented (C : ReplayContext (D α).toUpdateSig)
    (E₁ E₂ : Set (Event α)) (l B t s : State α) (et er : Nat) (x : α)
    (member : (et,er,.add x) ∈ E₁) (absent : (et,er,.add x) ∉ E₂)
    (closed : (ConcreteMRDT.MetadataDependencies.ofConcrete C).Closed E₁)
    (base : Represents C.vis (E₁ ∩ E₂) l)
    (past : Represents C.vis
      ((ConcreteMRDT.MetadataDependencies.ofConcrete C).Past (et,er,.add x) \
        {(et,er,.add x)}) B)
    (other : Represents C.vis E₂ s) :
    merge l (merge B t (update B (et,er,.add x))) s =
      merge B (merge l t s) (update B (et,er,.add x)) := by
  apply GuardedEqualityVC.local_add_eq
  · intro mem
    exact ((past (er,et,x)).mp mem).1.2 rfl
  · intro mem
    exact absent ((base (er,et,x)).mp mem).1.2
  · intro p inPast inOther _ _
    have hp := (past p).mp inPast
    have hs := (other p).mp inOther
    have subset := (ConcreteMRDT.MetadataDependencies.ofConcrete C).past_subset
      E₁ (et,er,.add x) closed member
    apply (base p).mpr
    refine ⟨⟨subset hp.1.1,hs.1⟩,?_⟩
    exact fun deadBase => hs.2 (dead_mono C.vis Set.inter_subset_right deadBase)

theorem live_killed_before_raw (C : ReplayContext (D α).toUpdateSig)
    (U : Set (Event α)) (e : Event α)
    (member : e ∈ U) (supported : ConcreteMRDT.Supported C U)
    (semantic : ∀ x ∈ U, x ≠ e → ¬ paperOrder (EventSpec.conflict α) C U e x)
    (metadata : ∀ x ∈ U, x ≠ e →
      ¬ (ConcreteMRDT.MetadataDependencies.ofConcrete C).before e x) :
    ∀ p : Record α, live C.vis (U \ {e}) p → kills p.1 p.2.2 e →
      C.vis (p.2.1,p.1,SetOp.add p.2.2) e := by
  intro p living kill
  let b : Event α := (p.2.1,p.1,SetOp.add p.2.2)
  have hb : b ∈ U := living.1.1
  have ne : b ≠ e := living.1.2
  have nc := kills_noncomm p e kill ne
  have notforward : ¬ C.vis e b := fun vis => metadata b hb ne
    ⟨vis,fun commute => nc (Foundation.commutes_symm commute)⟩
  rcases e with ⟨t,r,op⟩
  cases op with
  | add x =>
    change r = p.1 ∧ x = p.2.2 at kill
    obtain ⟨r',E,head,mem⟩ := supported b hb
    obtain ⟨q,F,other,member'⟩ := supported (t,r,.add x) member
    exact (C.vis_total_same_replica head mem other member' ne kill.1.symm).resolve_right notforward
  | remove x =>
    change x = p.2.2 at kill
    subst x
    by_contra notback
    apply semantic b hb ne
    refine Or.inr ⟨notforward,notback,⟨p.2.2,rfl,rfl⟩,?_⟩
    rintro ⟨z,hz,vis,conflict⟩
    have killed := RawReplay.raw_noncomm_kills p z conflict
    exact living.2 ⟨z,⟨hz,fun equal => notback (equal ▸ vis)⟩,vis,killed⟩

theorem causal_replay_eq_raw (C : ReplayContext (D α).toUpdateSig)
    (U : Set (Event α)) (a b : State α) (e : Event α)
    (member : e ∈ U) (supported : ConcreteMRDT.Supported C U)
    (closed : (ConcreteMRDT.MetadataDependencies.ofConcrete C).Closed U)
    (semantic : ∀ x ∈ U, x ≠ e → ¬ paperOrder (EventSpec.conflict α) C U e x)
    (metadata : ∀ x ∈ U, x ≠ e →
      ¬ (ConcreteMRDT.MetadataDependencies.ofConcrete C).before e x)
    (ha : Represents C.vis (U \ {e}) a)
    (hb : Represents C.vis
      ((ConcreteMRDT.MetadataDependencies.ofConcrete C).Past e \ {e}) b) :
    merge b a (update b e) = update a e := by
  let M := ConcreteMRDT.MetadataDependencies.ofConcrete C
  have pastSub := M.past_subset U e closed member
  apply merge_update_eq a b e
  · intro p birth mem
    exact ((hb p).mp mem).1.2 birth.symm
  · intro p mem kill
    have living := (ha p).mp mem
    have vis := live_killed_before_raw C U e member supported semantic metadata p living kill
    have dependency : M.before (p.2.1,p.1,SetOp.add p.2.2) e :=
      ⟨vis,kills_noncomm p e kill living.1.2⟩
    apply (hb p).mpr
    refine ⟨⟨Or.inr (.single dependency),living.1.2⟩,?_⟩
    exact fun deadPast => living.2 (dead_mono C.vis
      (show M.Past e \ {e} ⊆ U \ {e} from fun _ hx => ⟨pastSub hx.1,hx.2⟩) deadPast)

theorem local_remove_represented (C : ReplayContext (D α).toUpdateSig)
    (E₁ E₂ : Set (Event α)) (l B t s : State α) (et er : Nat) (x : α)
    (member : (et,er,.remove x) ∈ E₁)
    (closed : (ConcreteMRDT.MetadataDependencies.ofConcrete C).Closed E₁)
    (base : Represents C.vis (E₁ ∩ E₂) l)
    (past : Represents C.vis
      ((ConcreteMRDT.MetadataDependencies.ofConcrete C).Past (et,er,.remove x) \ {(et,er,.remove x)}) B)
    (other : Represents C.vis E₂ s) :
    merge l (merge B t (update B (et,er,.remove x))) s =
      merge B (merge l t s) (update B (et,er,.remove x)) := by
  apply SetMergeAlgebra.local_redistribute
  · intro p inPast _ inOther
    have hp := (past p).mp inPast
    have hs := (other p).mp inOther
    have subset := (ConcreteMRDT.MetadataDependencies.ofConcrete C).past_subset
      E₁ (et,er,.remove x) closed member
    apply (base p).mpr
    refine ⟨⟨subset hp.1.1,hs.1⟩,?_⟩
    exact fun deadBase => hs.2 (dead_mono C.vis Set.inter_subset_right deadBase)
  · intro p notPast updated
    exact False.elim (notPast (Finset.mem_filter.mp updated).1)

/-- All five equality-valued merge VCs. Every equation is proved directly;
no concrete or abstract representation Join theorem is used. -/
theorem mergeVCs : ConcreteMRDT.Raw.MergeVCs (EventSpec.conflict α)
    representation (RawReplay.scheme (α := α)) := by mrdt_verify


#print axioms local_add_represented
#print axioms causal_replay_eq_raw
#print axioms mergeVCs
end Sal.MRDTs.Paper1.EfficientORSet.GuardedRawVC
