import Sal.MRDTs.Paper1.RGAClientLocal
import Sal.MRDTs.Instances.RGAGC
import Sal.MRDTs.Paper1.RGAClientFilter

/-! Direct physical-query correspondence for native RGA positional requests.
The original certified apply step supplies its issuer guard and a clock newer
than every observed event. No extra allocation parameter is a client input. -/
namespace Sal.MRDTs.Paper1.RGA.Client.Physical
open Foundation Instances.RGA

set_option maxHeartbeats 2000000

theorem sorted_entries_are_finset_order (entries : List RGAEntry)
    (unique : (entries.map Prod.fst).Nodup)
    (sorted : entries.Pairwise (fun a b => a.1 ≤ b.1)) :
    entries.toFinset.toList.mergeSort (fun a b => a.1 ≤ b.1) = entries := by
  have perm := (List.mergeSort_perm entries.toFinset.toList
    (fun a b : RGAEntry => a.1 ≤ b.1)).trans
      (List.toFinset_toList (List.Nodup.of_map Prod.fst unique))
  have finiteSorted : (entries.toFinset.toList.mergeSort
      (fun a b => a.1 ≤ b.1)).Pairwise (fun a b => a.1 ≤ b.1) := by
    simpa using List.pairwise_mergeSort
      (le := fun a b : RGAEntry => a.1 ≤ b.1)
      (by intro a b c ab bc; exact decide_eq_true (Nat.le_trans (of_decide_eq_true ab) (of_decide_eq_true bc)))
      (by intro a b; by_cases h : a.1 ≤ b.1; simp [h]; simp [h,Nat.le_of_lt (Nat.lt_of_not_ge h)])
      entries.toFinset.toList
  apply List.eq_of_perm_of_sorted ?_ finiteSorted sorted perm
  intro a b ha hb ab ba
  exact List.inj_on_of_nodup_map unique (perm.mem_iff.mp ha) hb (Nat.le_antisymm ab ba)

theorem newest_entry_order (entries : List RGAEntry)
    (unique : (entries.map Prod.fst).Nodup)
    (sorted : entries.Pairwise (fun a b => a.1 ≤ b.1))
    (stamp anchor : Nat) (newer : ∀ entry ∈ entries, entry.1 < stamp) :
    (insert (stamp,anchor) entries.toFinset).toList.mergeSort
      (fun a b => a.1 ≤ b.1) = entries ++ [(stamp,anchor)] := by
  have fresh : stamp ∉ entries.map Prod.fst := by
    rintro member
    obtain ⟨entry,member,same⟩ := List.mem_map.mp member
    exact (Nat.lt_irrefl stamp) (same ▸ newer entry member)
  have uniqueNew : ((entries ++ [(stamp,anchor)]).map Prod.fst).Nodup := by
    simp only [List.map_append,List.map_cons,List.map_nil]
    refine List.nodup_append.mpr ⟨unique,by simp,?_⟩
    intro a ha b hb same
    have eq : a = stamp := same.trans (by simpa only [List.mem_singleton] using hb)
    exact fresh (eq ▸ ha)
  have sortedNew : (entries ++ [(stamp,anchor)]).Pairwise (fun a b => a.1 ≤ b.1) := by
    apply List.pairwise_append.mpr
    exact ⟨sorted,by simp,by simpa using fun a ha => Nat.le_of_lt (newer a ha)⟩
  have same := sorted_entries_are_finset_order (entries ++ [(stamp,anchor)]) uniqueNew sortedNew
  simpa [List.toFinset_append,Finset.union_comm] using same

#print axioms newest_entry_order

theorem physical_listStep (s : RGAM.State) (q : BirthGraveState)
    (represented : birthGraveRel s q) (entries : List RGAEntry)
    (adds : q.adds = entries.toFinset)
    (unique : (entries.map Prod.fst).Nodup)
    (sorted : entries.Pairwise (fun a b => a.1 ≤ b.1))
    (stamp replica : Nat) (op : RGAOp)
    (newer : ∀ entry ∈ entries, entry.1 < stamp)
    (issued : applicable (stamp,replica,op) s) :
    read (RGAM.update s (stamp,replica,op)) = listStep (read s) (stamp,replica,op) := by
  have old : read s =
      (entries.foldl (fun xs e => insertAfter e.2 e.1 xs) []).filter
        (fun id => decide (id ∉ q.grave)) := by
    rw [read_eq_sequence_of_birthGraveRel represented]
    unfold Instances.RGA.sequence
    rw [adds,sorted_entries_are_finset_order entries unique sorted]
  rw [read_eq_sequence_of_birthGraveRel (GC.birthGraveRel_step represented (stamp,replica,op)),old]
  cases op with
  | addAfter anchor =>
    have notGrave : stamp ∉ q.grave := by
      have live := issued.2.2
      rw [represented.2 stamp] at live
      simpa using live
    have anchorKept : anchor = 0 ∨ decide (anchor ∉ q.grave) = true := by
      rcases issued.1 with root | nonroot
      · exact Or.inl root.1
      · right
        have live := nonroot.1
        rw [represented.2 anchor] at live
        simpa using live
    change Instances.RGA.sequence ⟨insert (stamp,anchor) q.adds,q.grave⟩ = _
    unfold Instances.RGA.sequence
    rw [adds,newest_entry_order entries unique sorted stamp anchor newer]
    simpa [List.foldl_append,listStep] using
      ClientFilter.insertAfter_filter (fun id => decide (id ∉ q.grave)) anchor stamp
        (by simp [notGrave]) anchorKept
        (entries.foldl (fun xs e => insertAfter e.2 e.1 xs) [])
  | remove target =>
    change Instances.RGA.sequence ⟨q.adds,insert target q.grave⟩ = _
    simp only [Instances.RGA.sequence,adds,sorted_entries_are_finset_order entries unique sorted,listStep,List.filter_filter]
    apply List.filter_congr
    intro id member
    simp [and_comm]

theorem issued_guard_at {C C' : Configuration RGAM}
    {v : Version} {s : RGAM.State} {E : Set (Op RGAOp)}
    (head : C.head replica = some v) (version : C.ver v = some (s,E))
    (issued : IssuedStep RGAM generation C (.apply stamp replica op) C') :
    applicable (stamp,replica,op) s := by
  cases issued with
  | nonApply raw notApply => exact (notApply stamp replica op rfl).elim
  | @apply _ _ _ _ oldVersion oldState oldHead oldStateAt guard raw =>
    have same := Option.some.inj (oldHead.symm.trans head)
    subst oldVersion
    rw [version] at oldStateAt
    have sameState : s = oldState := Option.some.inj oldStateAt
    subst oldState
    exact guard

/-- Successful positional preparation in an actual certified apply has the
requested effect on the implementation's physical read. Freshness, finite
support and uniqueness are derived from execution, rather than client inputs. -/
theorem certified_prepared {C C' : Configuration RGAM}
    (execution : CertifiedExecution RGAM generation C)
    {v : Version} {s : RGAM.State} {E : Set (Op RGAOp)}
    {stamp replica : Nat} {op : RGAOp} {request : Client.Request}
    (head : C.head replica = some v) (version : C.ver v = some (s,E))
    (one : (certifiedTS RGAM generation).step C (.apply stamp replica op) C')
    (prepared : Client.prepare (read s) stamp replica request = some (stamp,replica,op)) :
    read (RGAM.update s (stamp,replica,op)) = Client.step (read s) stamp request := by
  have good := execution.canonicalConfig (fun _ _ => Instances.RGA.join _)
  obtain ⟨ops,enumerates,_,fold⟩ := good.canonical v s E version
  have wf := versionWellFormed_of_execution execution version
  have perm := canonical_listPermOf enumerates
  have sourceFold := (canonical_fold ops).trans fold
  let q := birthGraveMachine.run (canonical ops)
  let entries := insertEntries (canonical ops)
  have represented : birthGraveRel s q := by
    rw [← sourceFold]
    exact birthGraveSound (canonical ops)
  have adds : q.adds = entries.toFinset := (birthGrave_run_sets (canonical ops)).1
  have unique : (entries.map Prod.fst).Nodup :=
    (insertEntries_nodup perm wf).map_on
      (fun a ha b hb same => insertEntries_time_injective perm wf ha hb same)
  have sorted : entries.Pairwise (fun a b => a.1 ≤ b.1) :=
    insertEntries_sorted (canonical_ordered ops)
  have newer : ∀ entry ∈ entries, entry.1 < stamp := by
    intro entry member
    obtain ⟨oldReplica,oldMember⟩ := mem_insertEntries.mp member
    exact Client.apply_clock_above_observed one.2.1.toRaw _ v s E head version
      ((perm.2 _).mp oldMember)
  have queryUnique : (read s).Nodup := by
    rw [read_eq_sequence_of_birthGraveRel represented]
    unfold Instances.RGA.sequence
    rw [adds,sorted_entries_are_finset_order entries unique sorted]
    exact (ClientFilter.insertFold_nodup entries unique [] (by simp) (by simp)).filter _
  rw [physical_listStep s q represented entries adds unique sorted stamp replica op newer
    (issued_guard_at head version one.2.1)]
  exact ClientFilter.prepared_listStep queryUnique (Client.certified_no_root execution version) prepared

#print axioms physical_listStep
#print axioms certified_prepared

theorem certified_query_prepared {C C' : Configuration RGAM}
    (execution : CertifiedExecution RGAM generation C)
    {v : Version} {s : RGAM.State} {E : Set (Op RGAOp)}
    {stamp replica : Nat} {op : RGAOp} {request : Client.Request}
    (head : C.head replica = some v) (version : C.ver v = some (s,E))
    (one : (certifiedTS RGAM generation).step C (.apply stamp replica op) C')
    (prepared : Client.prepare (read s) stamp replica request = some (stamp,replica,op)) :
    RGAM.query (RGAM.update s (stamp,replica,op)) () = Client.step (read s) stamp request :=
  certified_prepared execution head version one prepared

theorem certified_query_preparedV {C C' : Configuration RGAM}
    (execution : CertifiedExecution RGAM generation C)
    {v : Version} {s : RGAM.State} {E : Set (Op RGAOp)}
    {stamp replica : Nat} {op : RGAOp} {request : Client.Request}
    (head : C.head replica = some v) (version : C.ver v = some (s,E))
    (one : (certifiedTSV RGAM generation).step C (.apply stamp replica op) C')
    (prepared : Client.prepare (read s) stamp replica request = some (stamp,replica,op)) :
    RGAM.query (RGAM.update s (stamp,replica,op)) () = Client.step (read s) stamp request := by
  have ordinary : IssuedStep RGAM generation C (.apply stamp replica op) C' := by
    cases one.2.1 with
    | base issued => exact issued
    | virtual raw noRaw =>
      cases raw with
      | base raw => exact (noRaw raw).elim
  exact certified_query_prepared execution head version ⟨one.1,ordinary,one.2.2⟩ prepared

#print axioms certified_query_prepared
#print axioms certified_query_preparedV
end Sal.MRDTs.Paper1.RGA.Client.Physical
