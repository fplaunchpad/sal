import Sal.MRDTs.Paper1.AnchoredQueueCoordinates

/-! Causal scheduling facts for the independent FIFO language. These facts
come from head/tail issuance and represented causal pasts, not from assuming
that the desired FIFO history already exists. -/
namespace Sal.MRDTs.Paper1.AnchoredQueue
open Foundation Instances.EmbedRGA Sal.EmbedRGA
open Classical

/-- A named birth has already been removed in an event's causal past. -/
def DeletedBefore (C : Configuration Q) (birth event : Event) : Prop :=
  ∃ d ∈ C.events, C.vis d event ∧ d.op = .del birth.time

/-- A mint replay contains a birth record precisely when its causal past
contains that birth and no removal naming it. -/
theorem mint_record_mem {C : Configuration Q}
    (execution : CertifiedExecution Q issuance C) {event birth : Event}
    (_he : event ∈ C.events) (hb : birth ∈ C.events) (hi : eIsIns birth = true)
    {ops : List Event}
    (perm : listPermOf ops {x ∈ C.events | C.vis x event})
    (ordered : respects ops C.vis) :
    eRecOf unaryCode birth ∈ eFold unaryCode ops ↔
      C.vis birth event ∧ ¬ DeletedBefore C birth event := by
  have honest := eHonest_core (eHonest_of_mint (execution_weaken execution).mintHonest)
  have support : ∀ x ∈ ops, x ∈ C.events := fun x hx => ((perm.2 x).mp hx).1
  have wf := CertifiedRGAVCReplay.Embedded.wellformed_supported unaryCode
    C.replayContext honest ops perm.1 support ordered
  rw [e_fold_mem unaryCode wf]
  constructor
  · rintro ⟨⟨x,hx,hxi,eq⟩,notdel⟩
    have tx : x.time = birth.time := by
      simpa only [eRecOf,Op.time] using congrArg Prod.fst eq.symm
    have same := C.replayContext.ts_unique (support x hx) hb tx
    subst x
    refine ⟨((perm.2 birth).mp hx).2,?_⟩
    rintro ⟨d,hd,vis,shape⟩
    apply notdel
    exact mem_eDels.mpr ⟨d,(perm.2 d).mpr ⟨hd,vis⟩,shape⟩
  · rintro ⟨vis,notdel⟩
    refine ⟨⟨birth,(perm.2 birth).mpr ⟨hb,vis⟩,hi,rfl⟩,?_⟩
    intro deleted
    obtain ⟨d,hd,shape⟩ := mem_eDels.mp deleted
    exact notdel ⟨d,((perm.2 d).mp hd).1,((perm.2 d).mp hd).2,shape⟩

#print axioms mint_record_mem

theorem mint_sorted {C : Configuration Q}
    (execution : CertifiedExecution Q issuance C) {event : Event}
    {ops : List Event}
    (perm : listPermOf ops {x ∈ C.events | C.vis x event})
    (ordered : respects ops C.vis) : ESorted (eFold unaryCode ops) := by
  have honest := eHonest_core (eHonest_of_mint (execution_weaken execution).mintHonest)
  apply e_fold_sorted unaryCode
  exact CertifiedRGAVCReplay.Embedded.wellformed_supported unaryCode
    C.replayContext honest ops perm.1
    (fun x hx => ((perm.2 x).mp hx).1) ordered

/-- A live causal predecessor of an enqueue lies before its fresh record. -/
theorem causal_birth_before_if_not_deleted {C : Configuration Q}
    (execution : CertifiedExecution Q issuance C) {x y : Event}
    (hx : x ∈ C.events) (hy : y ∈ C.events)
    (ix : eIsIns x = true) (iy : eIsIns y = true)
    (causal : C.vis x y) (notdeleted : ¬ DeletedBefore C x y) :
    keyLt (key (eCoord unaryCode y)) (key (eCoord unaryCode x)) = true := by
  obtain ⟨ops,perm,ordered,issued⟩ := execution.mintHonest y hy
  have member := (mint_record_mem execution hy hx ix perm ordered).mpr ⟨causal,notdeleted⟩
  have sorted := mint_sorted execution perm ordered
  rcases y with ⟨t,r,op⟩
  cases op with
  | del target => simp [eIsIns] at iy
  | ins value pref anchor =>
      exact issued_enqueue_after_live (replica := r) (value := value) sorted issued member

/-- Head-only removal prevents a causally later birth from being removed
before all of its birth predecessors. The earlier removal is a witnessed
event in the remover's original causal past. -/
theorem causal_birth_delete_predecessor {C : Configuration Q}
    (execution : CertifiedExecution Q issuance C) {x y d : Event}
    (hx : x ∈ C.events) (hy : y ∈ C.events) (hd : d ∈ C.events)
    (ix : eIsIns x = true) (iy : eIsIns y = true)
    (causal : C.vis x y) (deleted : d.op = .del y.time) :
    DeletedBefore C x d := by
  have good := CertifiedRGAExecution.Embedded.canonicalConfig unaryCode
    (execution_weaken execution)
  have honest := eHonest_core (eHonest_of_mint (execution_weaken execution).mintHonest)
  obtain ⟨birth,hbirth,yd,time,_⟩ := honest.del_has_ins d hd y.time deleted
  have same := C.replayContext.ts_unique hbirth hy time
  subst birth
  by_cases old : DeletedBefore C x y
  · obtain ⟨d',hd',vis,shape⟩ := old
    exact ⟨d',hd',good.vis_trans vis yd,shape⟩
  · have before := causal_birth_before_if_not_deleted execution hx hy ix iy causal old
    by_contra absent
    obtain ⟨ops,perm,ordered,issued⟩ := execution.mintHonest d hd
    have member := (mint_record_mem execution hd hx ix perm ordered).mpr
      ⟨good.vis_trans causal yd,absent⟩
    have sorted := mint_sorted execution perm ordered
    rcases d with ⟨t,r,op⟩
    change op = .del y.time at deleted
    subst op
    obtain ⟨head,observed,target⟩ := Option.map_eq_some_iff.mp issued
    have headmem : head ∈ eFold unaryCode ops := List.mem_of_head? observed
    obtain ⟨b,hb,ib,record⟩ := e_fold_rec_sub unaryCode ops head headmem
    have btime : b.time = y.time := by
      have ht : head.1 = y.time := target
      simpa only [record,eRecOf,Op.time] using ht
    have byeq := C.replayContext.ts_unique ((perm.2 b).mp hb).1 hy btime
    subst b
    have different : eRecOf unaryCode x ≠ head := by
      intro eq
      have xy : x = y := C.replayContext.ts_unique hx hy (by
        simpa only [record,eRecOf,Op.time] using congrArg Prod.fst eq)
      subst x
      exact good.vis_irrefl y causal
    have forbidden := issued_dequeue_no_earlier_live (t := t) (replica := r)
      sorted issued observed member different
    exact forbidden (by simpa only [record,eRecOf] using before)

#print axioms causal_birth_delete_predecessor

/-- Births removed in a causally closed endpoint form a downset of the
causal order on enqueue events. -/
theorem removed_births_causal_downset {C : Configuration Q}
    (execution : CertifiedExecution Q issuance C) {H : Set Event}
    (closed : ∀ a b, C.vis a b → b ∈ H → a ∈ H)
    (support : H ⊆ C.events) {x y : Event}
    (hx : x ∈ C.events) (hy : y ∈ C.events)
    (ix : eIsIns x = true) (iy : eIsIns y = true)
    (causal : C.vis x y) (removed : ∃ d ∈ H, d.op = .del y.time) :
    ∃ d ∈ H, d.op = .del x.time := by
  obtain ⟨d,hd,shape⟩ := removed
  obtain ⟨d',hd',vis,shape'⟩ :=
    causal_birth_delete_predecessor execution hx hy (support hd) ix iy causal shape
  exact ⟨d',closed d' d vis hd,shape'⟩

/-- The endpoint coordinate order respects causal enqueues that survive.
The non-removal premise excludes a visible removal by causal closure. -/
theorem causal_birth_before_if_surviving {C : Configuration Q}
    (execution : CertifiedExecution Q issuance C) {H : Set Event}
    (closed : ∀ a b, C.vis a b → b ∈ H → a ∈ H)
    (support : H ⊆ C.events) {x y : Event}
    (hx : x ∈ H) (hy : y ∈ H)
    (ix : eIsIns x = true) (iy : eIsIns y = true)
    (causal : C.vis x y) (survives : ¬ ∃ d ∈ H, d.op = .del x.time) :
    keyLt (key (eCoord unaryCode y)) (key (eCoord unaryCode x)) = true := by
  apply causal_birth_before_if_not_deleted execution (support hx) (support hy) ix iy causal
  rintro ⟨d,_,vis,shape⟩
  exact survives ⟨d,closed d y vis hy,shape⟩

#print axioms removed_births_causal_downset
#print axioms causal_birth_before_if_surviving
end Sal.MRDTs.Paper1.AnchoredQueue
