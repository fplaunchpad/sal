import Sal.MRDTs.Instances.EfficientORSetHistory
import Sal.MRDTs.Instances.EfficientORSetHeadGC

/-! # Chronological retirement evidence

History-level query preservation for arbitrarily many retirements. Cuts are
global event sets at collection time, not merge-base materializations.
-/

namespace Sal.MRDTs.Instances.EfficientORSet.HeadGC.Retirement
open Sal.MRDTs.Foundation
open Classical

abbrev Ev := Op (SetOp Nat)
def birth (p : Record Nat) : Ev := (p.2.1, p.1, .add p.2.2)

/-- A globally live witness at a retirement cut protects its later local
replacement chain whenever the discarded record is still semantically live.
The result is either the original witness or an addition after that cut. -/
theorem protected_witness
    (vis : Ev → Ev → Prop) (trans : Transitive vis)
    (clock : ∀ a b, vis a b → a.1 < b.1)
    (E K : Finset Ev) (a d : Record Nat)
    (same : a.2.2 = d.2.2)
    (aHere : birth a ∈ E)
    (aAtCut : live vis (↑K) a)
    (post : ∀ e ∈ E, e ∉ K → vis (birth a) e ∧ vis (birth d) e)
    (dLive : live vis (↑E) d) :
    ∃ q : Record Nat, live vis (↑E) q ∧ q.2.2 = d.2.2 ∧
      (q = a ∨ birth q ∉ K) := by
  let candidates := E.filter fun e => e.2.1 = a.1 ∧ e.2.2 = .add a.2.2 ∧
    (e = birth a ∨ vis (birth a) e)
  have ha : birth a ∈ candidates := by
    apply Finset.mem_filter.mpr
    exact ⟨aHere, rfl, rfl, Or.inl rfl⟩
  obtain ⟨e, he, hmax⟩ := Finset.exists_max_image candidates (fun e => e.1) ⟨birth a, ha⟩
  obtain ⟨heE, her, heop, heafter⟩ := Finset.mem_filter.mp he
  let q : Record Nat := (e.2.1, e.1, a.2.2)
  have hbq : birth q = e := by
    rcases e with ⟨t,r,op⟩
    simp only [q, birth, Prod.mk.injEq] at *
    simp_all
  have hqe : q.2.2 = d.2.2 := same
  have hqLive : live vis (↑E) q := by
    refine ⟨?_, ?_⟩
    · change birth q ∈ E
      rw [hbq]
      exact heE
    · rintro ⟨z, hz, hv, hk⟩
      have hez : vis e z := by
        change vis (birth q) z at hv
        rwa [hbq] at hv
      have haz : vis (birth a) z := by
        rcases heafter with h | h
        · exact h ▸ hez
        · exact trans h hez
      cases hzop : z.2.2 with
      | add y =>
          have hk' : z.2.1 = e.2.1 ∧ y = a.2.2 := by
            simpa [kills, hzop, q] using hk
          have hzc : z ∈ candidates := by
            exact Finset.mem_filter.mpr ⟨hz, hk'.1.trans her,
              by rw [hzop, hk'.2], Or.inr haz⟩
          exact (Nat.not_lt_of_ge (hmax z hzc)) (clock e z hez)
      | remove y =>
          have hy : y = a.2.2 := by simpa [kills, hzop, q] using hk
          by_cases hzK : z ∈ K
          · exact aAtCut.2 ⟨z, hzK, haz, by simp [kills, hzop, hy]⟩
          · exact dLive.2 ⟨z, hz, (post z hz hzK).2,
              by simp [kills, hzop, hy, same]⟩
  refine ⟨q, hqLive, hqe, ?_⟩
  rcases heafter with h | h
  · left
    have hb : birth q = birth a := hbq.trans h
    rcases a with ⟨r,t,x⟩
    rcases q with ⟨r',t',x'⟩
    simpa [birth, Prod.mk.injEq, and_comm, and_left_comm, and_assoc] using hb
  · right
    intro hqK
    have heK : e ∈ K := by simpa [hbq] using hqK
    exact aAtCut.2 ⟨e, heK, h, by simp [kills, heop, her]⟩

/-- Evidence recorded when d is appended to the chronological retirement
list. It says nothing about compact query results. -/
structure CutEvidence (vis : Ev → Ev → Prop) (E : Finset Ev)
    (earlier : Finset (Record Nat)) (d : Record Nat) where
  witness : Record Nat
  cut : Finset Ev
  different : witness ≠ d
  same : witness.2.2 = d.2.2
  witnessHere : birth witness ∈ E
  witnessLive : live vis (↑cut) witness
  witnessNotRetired : witness ∉ earlier
  discardedAtCut : birth d ∈ cut
  earlierAtCut : ∀ p ∈ earlier, birth p ∈ cut
  post : ∀ e ∈ E, e ∉ cut → vis (birth witness) e ∧ vis (birth d) e

theorem witness_not_retired
    (vis : Ev → Ev → Prop) (trans : Transitive vis)
    (clock : ∀ a b, vis a b → a.1 < b.1)
    (E : Finset Ev) (earlier : Finset (Record Nat)) (d : Record Nat)
    (cut : CutEvidence vis E earlier d) (hd : live vis (↑E) d) :
    ∃ q, live vis (↑E) q ∧ q.2.2 = d.2.2 ∧ q ∉ insert d earlier := by
  obtain ⟨q, hq, same, hafter⟩ := protected_witness vis trans clock E cut.cut
    cut.witness d cut.same cut.witnessHere cut.witnessLive cut.post hd
  refine ⟨q, hq, same, ?_⟩
  intro hret
  rcases Finset.mem_insert.mp hret with heq | hold
  · subst q
    rcases hafter with h | h
    · exact cut.different h.symm
    · exact h cut.discardedAtCut
  · rcases hafter with h | h
    · exact cut.witnessNotRetired (h ▸ hold)
    · exact h (cut.earlierAtCut q hold)

/-- A chronological retirement log, checked against one final semantic
history. There is no bound on the number of cuts or events in that history. -/
inductive Log (vis : Ev → Ev → Prop) (E : Finset Ev) :
    Finset (Record Nat) → Prop where
  | empty : Log vis E ∅
  | retire {earlier d} : Log vis E earlier →
      CutEvidence vis E earlier d → Log vis E (insert d earlier)

theorem log_preserves_elements
    (vis : Ev → Ev → Prop) (trans : Transitive vis)
    (clock : ∀ a b, vis a b → a.1 < b.1)
    (E : Finset Ev) (s : State Nat)
    (represented : Represents vis (↑E) s)
    {retired : Finset (Record Nat)} (log : Log vis E retired) :
    elements (s \ retired) = elements s := by
  induction log with
  | empty => simp
  | @retire earlier d log cut ih =>
      have step : elements ((s \ earlier).erase d) = elements (s \ earlier) := by
        by_cases hd : d ∈ s
        · obtain ⟨q, hq, same, hn⟩ := witness_not_retired vis trans clock E earlier d
            cut ((represented d).mp hd)
          have hne : q ≠ d := fun h => hn (Finset.mem_insert.mpr (Or.inl h))
          have hnot : q ∉ earlier := fun h => hn (Finset.mem_insert.mpr (Or.inr h))
          exact GCResearch.erase_elements d q (s \ earlier)
            (Finset.mem_sdiff.mpr ⟨(represented q).mpr hq, hnot⟩) hne same
        · have hds : d ∉ s \ earlier := fun h => hd (Finset.mem_sdiff.mp h).1
          rw [Finset.erase_eq_of_notMem hds]
      have heq : s \ insert d earlier = (s \ earlier).erase d := by
        ext p
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        tauto
      rw [heq, step, ih]

/-- Actual heads may retain some globally retired records. The proof needs
only a lower bound by the globally unretired projection, not synchronized GC. -/
theorem compact_query_correct
    (vis : Ev → Ev → Prop) (trans : Transitive vis)
    (clock : ∀ a b, vis a b → a.1 < b.1)
    (E : Finset Ev) (full compact : State Nat)
    (represented : Represents vis (↑E) full)
    {retired : Finset (Record Nat)} (log : Log vis E retired)
    (lower : full \ retired ⊆ compact) (upper : compact ⊆ full) :
    elements compact = elements full := by
  have eq := log_preserves_elements vis trans clock E full represented log
  apply Finset.Subset.antisymm
  · exact Finset.image_subset_image upper
  · rw [← eq]
    exact Finset.image_subset_image lower

#print axioms protected_witness
#print axioms log_preserves_elements
#print axioms compact_query_correct

end Sal.MRDTs.Instances.EfficientORSet.HeadGC.Retirement
