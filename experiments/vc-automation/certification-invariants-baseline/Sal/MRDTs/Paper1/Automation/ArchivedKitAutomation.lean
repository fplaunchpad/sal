import Sal.MRDTs.Paper1.Automation.GenericArchivedOrderedRecords
import Sal.MRDTs.Paper1.Automation.GenericSortedLists

/-! Archived ordered records derived from executable projection equations.
The interface contains data and raw equations; no replay or VC theorem is an input. -/
namespace Sal.MRDTs.Paper1.Automation.ArchivedOrderedRecords
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1
open OrderedLists
open Classical

structure Description (D : MRDTSig) (Record Archive : Type) where
  live : D.State → List Record
  archive : D.State → Finset Archive
  archive_written : Op D.AppOp → Archive
  insertion : Op D.AppOp → Bool
  id : Record → Nat
  Key : Type
  key : Record → Key
  lt : Record → Record → Bool
  written : Op D.AppOp → Record
  target : Op D.AppOp → Nat → Prop

noncomputable def updateList {D : MRDTSig} {R A : Type} (d : Description D R A)
    (s : D.State) (e : Op D.AppOp) : List R :=
  if d.insertion e then
    if e.1 ∈ (d.live s).map d.id then d.live s else insert d.lt (d.written e) (d.live s)
  else (d.live s).filter (fun p=> decide (¬d.target e (d.id p)))

def mergeList {D : MRDTSig} {R A : Type} (d : Description D R A)
    (l a b : D.State) : List R :=
  merge2 d.lt
    ((d.live a).filter (fun r=>decide (d.id r∈(d.live b).map d.id ∨ d.id r∉(d.live l).map d.id)))
    ((d.live b).filter (fun r=>decide (d.id r∉(d.live l).map d.id ∧ d.id r∉(d.live a).map d.id)))

structure Equations {D : MRDTSig} {R A : Type} [DecidableEq A]
    (d : Description D R A) where
  order : Order d.key d.lt
  initial_live : d.live D.init=[]
  initial_archive : d.archive D.init=∅
  update_live : ∀s e,d.live (D.update s e)=updateList d s e
  merge_live : ∀l a b,d.live (D.merge l a b)=mergeList d l a b
  update_archive : ∀s e,d.archive (D.update s e)=
    if d.insertion e then Insert.insert (d.archive_written e) (d.archive s) else d.archive s
  merge_archive : ∀l a b,d.archive (D.merge l a b)=d.archive a∪d.archive b
  written_id : ∀e,d.id (d.written e)=e.1
  insertion_not_killed : ∀e,d.insertion e=true → ∀n,¬d.target e n
  ext : ∀s t,d.live s=d.live t → d.archive s=d.archive t → s=t

def Equations.kit {D : MRDTSig} {R A : Type} [DecidableEq R] [DecidableEq A]
    (d : Description D R A) (eqs : Equations d) : Kit D R A where
  archive := d.archive
  archive_written := d.archive_written
  archive_add := d.insertion
  archive_init := eqs.initial_archive
  archive_update := eqs.update_archive
  archive_merge := eqs.merge_archive
  carrier := fun s=>(d.live s).toFinset
  id := d.id
  Key := d.Key
  key := d.key
  insertion := d.insertion
  written := d.written
  target := d.target
  ordered := fun s=>Sorted d.lt (d.live s)
  init_carrier := by simp [eqs.initial_live]
  init_ordered := by simp [eqs.initial_live,Sorted]
  written_id := eqs.written_id
  update_provenance := by
    intro s e p hp
    simp only [eqs.update_live,List.mem_toFinset,updateList] at hp
    split at hp
    · split at hp
      · exact Or.inr (List.mem_toFinset.mpr hp)
      · obtain old | born := (mem_insert _ _ _ _).mp hp
        · exact Or.inr (List.mem_toFinset.mpr old)
        · exact Or.inl ⟨by assumption,born⟩
    · exact Or.inr (List.mem_toFinset.mpr (List.mem_of_mem_filter hp))
  update_mem := by
    intro s e fresh p
    have absent : e.1∉(d.live s).map d.id := by
      intro h; obtain ⟨q,hq,id⟩ := List.mem_map.mp h
      exact fresh q (List.mem_toFinset.mpr hq) id
    simp only [eqs.update_live,List.mem_toFinset,updateList]
    cases hi : d.insertion e <;> simp [hi,absent,mem_insert,List.mem_filter]
    simp [eqs.insertion_not_killed e hi]
    tauto
  update_ordered := by
    intro s e hs keys
    rw [eqs.update_live]
    unfold updateList
    split
    · split
      · exact hs
      · exact insert_sorted eqs.order _ _ hs (fun p hp=>keys p (List.mem_toFinset.mpr hp) (by assumption))
    · exact List.Pairwise.filter _ hs
  birth_not_killed := by
    exact fun e ins=>eqs.insertion_not_killed e ins _
  merge_mem := by
    intro l a b al bl ab ba p
    simp only [eqs.merge_live,List.mem_toFinset,mergeList,Certified.cell]
    rw [survivor_mem d.id d.lt _ _ _
      (fun p hp q hq=>al p (List.mem_toFinset.mpr hp) q (List.mem_toFinset.mpr hq))
      (fun p hp q hq=>bl p (List.mem_toFinset.mpr hp) q (List.mem_toFinset.mpr hq))
      (fun p hp q hq=>ab p (List.mem_toFinset.mpr hp) q (List.mem_toFinset.mpr hq))
      (fun p hp q hq=>ba p (List.mem_toFinset.mpr hp) q (List.mem_toFinset.mpr hq))]
    tauto
  merge_ordered := by
    intro l a b ha hb coherent
    rw [eqs.merge_live]
    apply filtered_merge_sorted eqs.order _ _ _ _ ha hb
      (fun p hp q hq=>coherent p (List.mem_toFinset.mpr hp) q (List.mem_toFinset.mpr hq))
    intro p hp
    simp [List.mem_map.mpr ⟨p,hp,rfl⟩]
  ext := by
    intro s t hs ht same archive
    apply eqs.ext s t _ archive
    apply sorted_ext eqs.order _ _ hs ht
    intro p
    have h:p∈(d.live s).toFinset ↔ p∈(d.live t).toFinset := by rw [same]
    simpa only [List.mem_toFinset] using h
end Sal.MRDTs.Paper1.Automation.ArchivedOrderedRecords
