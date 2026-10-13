import Sal.MRDTs.Paper1.AnchoredQueueRanks

namespace Sal.MRDTs.Paper1.AnchoredQueue
open Foundation Instances.EmbedRGA Sal.EmbedRGA Classical

structure LiveEndpoint (C : Configuration Q) (H : Set Event) (s : State) where
  live : List Event
  support : ∀ e ∈ live, e ∈ H
  insertions : ∀ e ∈ live, eIsIns e = true
  surviving : ∀ e ∈ live, ¬ HasDeletion H e
  complete : ∀ e ∈ H, eIsIns e = true → ¬ HasDeletion H e → e ∈ live
  nodup : live.Nodup
  representation : s.map (fun r => (r.1,r.2.1)) = live.map History.birthTag
  causalOrder : respects live C.vis

/-- Endpoint survival is derived from the new-framework represented replay,
not assumed from the desired sequential query. -/
theorem stored_birth_mem {C : Configuration Q} (execution : CertifiedExecution Q issuance C)
    {v : Version} {s : State} {H : Set Event} (stored : C.ver v = some (s,H)) {birth : Event}
    (hb : birth ∈ H) (ins : eIsIns birth = true) :
    eRecOf unaryCode birth ∈ s ↔ ¬ HasDeletion H birth := by
  have good := CertifiedRGAExecution.Embedded.canonicalConfig unaryCode (execution_weaken execution)
  have rep := CertifiedRGAExecution.Embedded.representedVersions unaryCode (execution_weaken execution) stored
  obtain ⟨ops,perm,order,fold⟩ := rep.2.2.2.2
  have support : H ⊆ C.events := good.version_events_supported v s H stored
  have honest := eHonest_core (eHonest_of_mint (execution_weaken execution).mintHonest)
  have wf := CertifiedRGAVCReplay.Embedded.wellformed_supported unaryCode C.replayContext honest ops
    perm.1 (fun e he => support ((perm.2 e).mp he)) order
  rw [← fold,e_fold_mem unaryCode wf]
  constructor
  · rintro ⟨_,notdel⟩ removed
    obtain ⟨d,hd,shape⟩ := (hasDeletion_iff H birth).mp removed
    exact notdel (mem_eDels.mpr ⟨d,(perm.2 d).mpr hd,shape⟩)
  · intro notdel
    refine ⟨⟨birth,(perm.2 birth).mpr hb,ins,rfl⟩,?_⟩
    intro deleted
    obtain ⟨d,hd,shape⟩ := mem_eDels.mp deleted
    apply notdel
    exact (hasDeletion_iff H birth).mpr ⟨d,(perm.2 d).mp hd,shape⟩

private theorem stored_record_birth {C : Configuration Q}
    (execution : CertifiedExecution Q issuance C) {v : Version} {s : State} {H : Set Event}
    (stored : C.ver v = some (s,H)) (r : ERec Nat) (hr : r ∈ s) :
    ∃ e, e ∈ H ∧ eIsIns e = true ∧ r = eRecOf unaryCode e ∧ ¬ HasDeletion H e := by
  have rep := CertifiedRGAExecution.Embedded.representedVersions unaryCode (execution_weaken execution) stored
  obtain ⟨ops,perm,_,fold⟩ := rep.2.2.2.2
  have member : r ∈ eFold unaryCode ops := by rw [fold]; exact hr
  obtain ⟨e,he,ins,record⟩ := e_fold_rec_sub unaryCode ops r member
  have hb := (perm.2 e).mp he
  refine ⟨e,hb,ins,record,?_⟩
  exact (stored_birth_mem execution stored hb ins).mp (record ▸ hr)

private theorem rec_tag_eq_birthTag (e : Event) (ins : eIsIns e = true) :
    ((eRecOf unaryCode e).1,(eRecOf unaryCode e).2.1) = History.birthTag e := by
  rcases e with ⟨t,r,op⟩
  cases op with
  | del x => simp [eIsIns] at ins
  | ins value pref anchor => rfl

/-- Recover the exact ordered live-birth suffix from the stored live records.
Only provenance and coordinate order are used in constructing the suffix. -/
noncomputable def liveEndpoint {C : Configuration Q}
    (execution : CertifiedExecution Q issuance C) {v : Version} {s : State} {H : Set Event}
    (stored : C.ver v = some (s,H)) : LiveEndpoint C H s := by
  let birthOf (r : ERec Nat) : Event :=
    if h : r ∈ s then Classical.choose (stored_record_birth execution stored r h)
    else (0,0,.del 0)
  have chosen : ∀ r ∈ s, (birthOf r) ∈ H ∧ eIsIns (birthOf r) = true ∧
      r = eRecOf unaryCode (birthOf r) ∧ ¬ HasDeletion H (birthOf r) := by
    intro r hr
    dsimp [birthOf]
    rw [dif_pos hr]
    exact Classical.choose_spec (stored_record_birth execution stored r hr)
  have good := CertifiedRGAExecution.Embedded.canonicalConfig unaryCode (execution_weaken execution)
  have supported : H ⊆ C.events := good.version_events_supported v s H stored
  have sorted : ESorted s := (stored_valid execution stored).1
  have unique : ∀ a ∈ H, ∀ b ∈ H, a.time = b.time → a = b :=
    fun a ha b hb eq => C.replayContext.ts_unique (supported ha) (supported hb) eq
  refine ⟨s.map birthOf,?_,?_,?_,?_,?_,?_,?_⟩
  · intro e he
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp he
    exact (chosen r hr).1
  · intro e he
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp he
    exact (chosen r hr).2.1
  · intro e he
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp he
    exact (chosen r hr).2.2.2
  · intro e he ins survives
    have member := (stored_birth_mem execution stored he ins).mpr survives
    have c := chosen (eRecOf unaryCode e) member
    have time : (birthOf (eRecOf unaryCode e)).time = e.time := by
      simpa only [eRecOf,Op.time] using (congrArg Prod.fst c.2.2.1).symm
    have same := unique _ c.1 e he time
    exact List.mem_map.mpr ⟨eRecOf unaryCode e,member,same⟩
  · have nodup : s.Nodup := sorted.imp fun {a b} before eq => by
      subst b
      rw [keyLt_irrefl] at before
      contradiction
    apply List.Nodup.map_on _ nodup
    intro a ha b hb eq
    exact (chosen a ha).2.2.1.trans (eq ▸ (chosen b hb).2.2.1.symm)
  · rw [List.map_map]
    apply List.map_congr_left
    intro r hr
    have c := chosen r hr
    exact (congrArg (fun r : ERec Nat => (r.1,r.2.1)) c.2.2.1).trans
      (rec_tag_eq_birthTag _ c.2.1)
  · rw [respects,List.pairwise_map]
    apply sorted.imp_of_mem
    intro a b ha hb before causal
    have ca := chosen a ha
    have cb := chosen b hb
    have after := causal_birth_before_if_surviving execution
      (fun x y vis hy => good.version_events_causal v s H stored x y vis hy)
      supported cb.1 ca.1 cb.2.1 ca.2.1 causal
      (fun removed => cb.2.2.2 ((hasDeletion_iff H _).mpr removed))
    have ka : key a.2.2 = key (eCoord unaryCode (birthOf a)) :=
      congrArg (fun r : ERec Nat => key r.2.2) ca.2.2.1
    have kb : key b.2.2 = key (eCoord unaryCode (birthOf b)) :=
      congrArg (fun r : ERec Nat => key r.2.2) cb.2.2.1
    have ab : keyLt (key a.2.2) (key b.2.2) = true := by
      rw [ka,kb]
      exact after
    rw [keyLt_asymm before] at ab
    contradiction

#print axioms liveEndpoint
end Sal.MRDTs.Paper1.AnchoredQueue
