import Sal.MRDTs.Paper1.DistinctOperationFullModel

namespace Sal.MRDTs.Paper1.DistinctOperationFullCounterexample
open Foundation ConcreteMRDT
open Classical

def Shape (E : Set (Op Unit)) (s : Nat) : Prop :=
  (E = ∅ ∧ s = 0) ∨ (E = {a} ∧ s = 1) ∨
  (E = {b} ∧ s = 2) ∨ (E = {a,b} ∧ s = 2)

theorem shape_zero {E : Set (Op Unit)} (h : Shape E 0) : E = ∅ := by
  rcases h with h | h | h | h <;> simp_all

theorem shape_merge {E F : Set (Op Unit)} {s t : Nat}
    (hs : Shape E s) (ht : Shape F t) : Shape (E ∪ F) (max s t) := by
  rcases hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
  rcases ht with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
  simp [Shape, Set.union_comm]
  all_goals right; ext e; simp only [Set.mem_insert_iff,Set.mem_singleton_iff]; tauto

def StoreShape (C : Configuration D) : Prop :=
  ∀ v s E, C.ver v = some (s,E) → Shape E s ∧ Supported C.replayContext E

private theorem allocate_shape {C C' : Configuration D} (old : StoreShape C)
    {r vnew : Nat} {snew : Nat} {Enew : Set (Op Unit)}
    (fresh : C.ver vnew = none)
    (ver : C'.ver = fun v => if v=vnew then some (snew,Enew) else C.ver v)
    (head : C'.head = fun x => if x=r then some vnew else C.head x)
    (shape : Shape Enew snew)
    (sub : ∀ E, C.headEvents r = some E → E ⊆ Enew) : StoreShape C' := by
  have heads := Configuration.headEvents_update_of_store_head_update C C' fresh ver head
  have mono : C.events ⊆ C'.events := by
    rintro e ⟨rep,E,hr,he⟩
    by_cases eq : rep=r
    · subst rep
      exact ⟨r,Enew,by simp [heads,updateRep],sub E hr he⟩
    · exact ⟨rep,E,by simpa [heads,updateRep,eq] using hr,he⟩
  intro v s E hv
  rw [ver] at hv
  dsimp only at hv
  split at hv
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hv)
    exact ⟨shape,fun e he => ⟨r,Enew,by change C'.headEvents r = some Enew; simp [heads,updateRep],he⟩⟩
  · obtain ⟨sh,sup⟩ := old v s E hv
    exact ⟨sh,fun e he => mono (sup e he)⟩

private theorem initial_shape : StoreShape (initConfig D) := by
  intro v s E hv
  change (if v=0 then some (0,∅) else none) = some (s,E) at hv
  split at hv
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hv)
    exact ⟨Or.inl ⟨rfl,rfl⟩,fun _ h => h.elim⟩
  · simp at hv

private theorem raw_shape {C C' : Configuration D} {l : Label D}
    (old : StoreShape C) (step : Step D C l C')
    (allow : ∀ t r o, l = .apply t r o → ∃ v s,
      C.head r = some v ∧ (C.ver v).map Prod.fst = some s ∧ issuance.CanIssue (t,r,o) s) :
    StoreShape C' := by
  cases step with
  | fork freshRep sourceHead sourceVer fresh rank C' vis ver head parents =>
    apply allocate_shape old fresh ver head (old _ _ _ sourceVer).1
    intro E h
    simp [Configuration.headEvents,headEventsFrom,freshRep] at h
  | @apply t r o v s E vn headAt versionAt ft fs fresh rank C' vis ver head parents =>
    obtain ⟨v',s',hh,hs,guard⟩ := allow t r o rfl
    have eqv : v' = v := Option.some.inj (hh.symm.trans headAt)
    subst v'
    have eqs : s = s' := by simpa [versionAt] using hs
    subst s'
    obtain ⟨allowed,zero⟩ := guard
    have empty : E = ∅ := shape_zero (zero ▸ (old v s E versionAt).1)
    apply allocate_shape old fresh ver head
    · rw [empty,Set.empty_union]
      rcases allowed with eq | eq
      · change Shape {(t,r,o)} (Op.time (t,r,o))
        rw [eq]; exact Or.inr (Or.inl ⟨rfl,rfl⟩)
      · change Shape {(t,r,o)} (Op.time (t,r,o))
        rw [eq]; exact Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩))
    · intro F hf
      have eh := C.headEvents_eq_of_head_ver headAt versionAt
      have eq : E = F := Option.some.inj (eh.symm.trans hf)
      subst F
      exact Set.subset_union_left
  | merge h1 h2 v1 v2 gca vb fresh rank1 rank2 C' vis ver head parents =>
    apply allocate_shape old fresh ver head (shape_merge (old _ _ _ v1).1 (old _ _ _ v2).1)
    intro F hf
    have eh := C.headEvents_eq_of_head_ver h1 v1
    have eq := Option.some.inj (eh.symm.trans hf)
    subst F
    exact Set.subset_union_left
  | query hs value => exact old

private theorem issued_shape {C C' : Configuration D} {l : Label D}
    (old : StoreShape C) (step : IssuedStep D issuance C l C') : StoreShape C' := by
  apply raw_shape old step.toRaw
  intro t r o eq
  cases step with
  | nonApply raw no => exact False.elim (no t r o eq)
  | apply hh hs guard raw =>
    cases eq
    exact ⟨_,_,hh,hs,guard⟩

private theorem issuedV_shape {C C' : Configuration D} {l : Label D}
    (old : StoreShape C)
    (step : IssuedStepV D (canonicalVirtualMergeBase D) issuance C l C') : StoreShape C' := by
  cases step with
  | base one => exact issued_shape old one
  | virtual raw no =>
    cases raw with
    | base one => exact False.elim (no one)
    | mergeVirtual h1 h2 v1 v2 fresh rank1 rank2 C' vis ver head parents =>
      apply allocate_shape old fresh ver head (shape_merge (old _ _ _ v1).1 (old _ _ _ v2).1)
      intro F hf
      have eh := C.headEvents_eq_of_head_ver h1 v1
      have eq := Option.some.inj (eh.symm.trans hf)
      subst F
      exact Set.subset_union_left

theorem storeShape {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) issuance C) : StoreShape C := by
  induction reach with
  | init => exact initial_shape
  | step reach before one after ih => exact issuedV_shape ih one

private theorem zero_fold_empty (π : List (Op Unit))
    (allowed : ∀ e ∈ π, e=a ∨ e=b)
    (zero : applySeq D.toUpdateSig D.init π = 0) : π=[] := by
  induction π using List.reverseRecOn with
  | nil => rfl
  | append_singleton pre e ih =>
    have he := allowed e (by simp)
    have time : e.time = 0 := by
      simpa [applySeq, List.foldl_append, D] using zero
    rcases he with rfl | rfl <;> simp [a,b,Op.time] at time

theorem good_of_honest {C : Configuration D} (honest : MintHonest D issuance.CanIssue C) :
    Good C.replayContext := by
  have allowed : ∀ e ∈ C.events, e=a ∨ e=b := by
    intro e he
    obtain ⟨π,hp,ho,hg⟩ := honest e he
    exact hg.1
  refine ⟨?_,allowed⟩
  intro x y edge
  obtain ⟨π,hp,ho,hg⟩ := honest y (C.vis_tgt edge)
  have empty : π=[] := zero_fold_empty π
    (fun e he => allowed e ((hp.2 e).mp he).1) hg.2
  have mem := (hp.2 x).mpr ⟨C.vis_src edge,edge⟩
  simp [empty] at mem

theorem representedVersions (C : Configuration D)
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) issuance C)
    (v : Version) (s : D.State) (E : Set (Op Unit)) (hv : C.ver v = some (s,E)) :
    R C.replayContext E s := by
  obtain ⟨shape,supported⟩ := storeShape reach v s E hv
  exact ⟨good_of_honest reach.mintHonest,supported,shape⟩

#print axioms representedVersions
end Sal.MRDTs.Paper1.DistinctOperationFullCounterexample
