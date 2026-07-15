import Sal.ConditionedMRDTs.MRDT_Instances.MergeableQueue.MergeableQueue
import Sal.ConditionedMRDTs.MRDT_Instances.SeqSpec_Flat

/-!
# Sequential-spec soundness — tier 2: the mergeable queue (task #79 / #65)

The Peepul queue, single-replica, against the naive functional FIFO: enq
pushes the value at the back, deq pops the head. The RDT's deq removes by
TAG; the two agree under the sequential honesty the datatype itself
prescribes (`applicable`'s head-check: a deq names the current head), and
the proof needs one discovered invariant: **tags are nodup** — freshness
of enqueue stamps survives filtering, and is exactly what makes
filter-by-tag pop precisely one element.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation

/-- Sequential honesty for queue histories: enqueue stamps are fresh, and
every dequeue names the current head's tag (the `applicable` head-check,
at each point of the history). -/
def qOK (ρ : List (Op QOp)) : Prop :=
  ∀ (σ : List (Op QOp)) (o : Op QOp) (τ : List (Op QOp)),
    ρ = σ ++ o :: τ →
    (∀ v, o.2.2 = QOp.enq v → o.1 ∉ qTags (seqFold Q σ)) ∧
    (∀ t, o.2.2 = QOp.deq t → ∃ v rest, seqFold Q σ = (t, v) :: rest)

theorem qOK_prefix {ρ : List (Op QOp)} {o : Op QOp}
    (h : qOK (ρ ++ [o])) : qOK ρ := by
  intro σ o' τ heq
  exact h σ o' (τ ++ [o]) (by rw [heq]; simp)

/-- The naive sequential FIFO over values. -/
def qSpecStep (S : List ℕ) (o : Op QOp) : List ℕ :=
  match o.2.2 with
  | .enq v => S ++ [v]
  | .deq _ => S.tail

def qSpecFold (ρ : List (Op QOp)) : List ℕ :=
  ρ.foldl qSpecStep []

theorem qSpecFold_snoc (ρ : List (Op QOp)) (o : Op QOp) :
    qSpecFold (ρ ++ [o]) = qSpecStep (qSpecFold ρ) o := by
  unfold qSpecFold
  rw [List.foldl_append]
  rfl

/-- **The discovered invariant: tags are nodup.** Fresh enqueue stamps
append disjointly; dequeue filters, and nodup survives sublists. -/
theorem q_tags_nodup {ρ : List (Op QOp)} (hOK : qOK ρ) :
    (qTags (seqFold Q ρ)).Nodup := by
  induction ρ using List.reverseRecOn with
  | nil => exact List.nodup_nil
  | append_singleton ρ o ih =>
      have hnd := ih (qOK_prefix hOK)
      rw [seqFold_snoc, Q_core_update]
      obtain ⟨ts, r, op⟩ := o
      cases op with
      | enq v =>
          have hfresh := (hOK ρ (ts, r, .enq v) [] (by simp)).1 v rfl
          have hnd' : (List.map Prod.fst (seqFold Q ρ)).Nodup := hnd
          simp only [qUpdate]
          rw [if_neg hfresh]
          simp only [qTags, List.map_append, List.map_cons, List.map_nil]
          rw [List.nodup_append]
          refine ⟨hnd', by simp, ?_⟩
          intro a ha b hb
          simp at hb
          subst hb
          exact fun h => hfresh (h ▸ ha)
      | deq t =>
          simp only [qUpdate]
          exact hnd.sublist (List.Sublist.map _ List.filter_sublist)

/-- **The mergeable queue, sequentially = a plain FIFO.** Under the
datatype's own sequential discipline (fresh stamps; deq names the head),
the value sequence of the fold is exactly the naive queue program. -/
theorem queue_seq_sound {ρ : List (Op QOp)} (hOK : qOK ρ) :
    (seqFold Q ρ).map Prod.snd = qSpecFold ρ := by
  induction ρ using List.reverseRecOn with
  | nil => rfl
  | append_singleton ρ o ih =>
      have IH := ih (qOK_prefix hOK)
      rw [seqFold_snoc, Q_core_update, qSpecFold_snoc]
      obtain ⟨ts, r, op⟩ := o
      cases op with
      | enq v =>
          have hfresh := (hOK ρ (ts, r, .enq v) [] (by simp)).1 v rfl
          simp only [qUpdate, qSpecStep]
          rw [if_neg hfresh]
          rw [List.map_append, IH]
          rfl
      | deq t =>
          obtain ⟨v, rest, hhead⟩ :=
            (hOK ρ (ts, r, .deq t) [] (by simp)).2 t rfl
          have hnd := q_tags_nodup (qOK_prefix hOK)
          rw [hhead] at hnd
          have htrest : t ∉ qTags rest := by
            rw [show qTags ((t, v) :: rest) = t :: qTags rest from rfl]
              at hnd
            exact (List.nodup_cons.mp hnd).1
          simp only [qUpdate, qSpecStep]
          rw [hhead]
          rw [show ((t, v) :: rest).filter (fun x => decide (x.1 ≠ t)) =
              rest.filter (fun x => decide (x.1 ≠ t)) from by simp]
          rw [List.filter_eq_self.mpr ?_]
          · rw [← IH, hhead]
            rfl
          · intro x hx
            simp only [ne_eq, decide_eq_true_eq]
            intro hxt
            exact htrest (hxt ▸ List.mem_map.mpr ⟨x, hx, rfl⟩)

end Sal.ConditionedMRDTs
