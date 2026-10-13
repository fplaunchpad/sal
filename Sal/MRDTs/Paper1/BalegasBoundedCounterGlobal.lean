import Sal.MRDTs.Paper1.BalegasBoundedCounterCertificate
import Sal.MRDTs.Framework.FiniteEvents

/-! Global means the union of all issued events, not one stored snapshot.
Finite causal enumeration makes the independent escrow conservation theorem
apply to this union even when no replica has received all operations. -/
namespace Sal.MRDTs.Paper1.BalegasBoundedCounterEvent
open Foundation Instances.BalegasBoundedCounter
open Classical

noncomputable def globalValue (K : Int) (events : Finset Event) : Int :=
  K + events.sum scalarDelta

theorem all_events_safe {n : Nat} {K : Int} [EventOrder (D n K).toUpdateSig]
    {C : Configuration (D n K)} (hG : CanonicalConfig C)
    (honest : HonestAppOn (D n K) (fun e s => applicable n s e) C)
    (finite : C.events.Finite) :
    ∃ ops : List Event, listPermOf ops C.events ∧ respects ops C.vis ∧
      Legal n (initialAccounts K) ops ∧
      (∀ r, 0 ≤ (run K ops).balance r) ∧
      Conserved n K (run K ops) ∧
      K ≤ globalValue K finite.toFinset := by
  let original := finite.toFinset.toList
  obtain ⟨ops,hperm,hvis⟩ := exists_respecting_perm (R := C.vis)
    (fun hab hbc => hG.vis_trans hab hbc) hG.vis_irrefl original
  have hp : listPermOf ops C.events := by
    refine ⟨hperm.nodup (Finset.nodup_toList _),?_⟩
    intro e
    exact hperm.mem_iff.symm.trans (by simp [original])
  have legal := causal_legal_on hG honest (fun _ h => h)
    (fun _ _ h _ => C.vis_src h) hp hvis
  obtain ⟨safe,conserved,bound⟩ := legal_run_safe legal
  refine ⟨ops,hp,hvis,legal,safe,conserved,?_⟩
  have hf : ops.toFinset = finite.toFinset := by
    ext e
    simpa using hp.2 e
  rw [run_value, ← List.sum_toFinset _ hp.1, hf] at bound
  exact bound

/-- The lower bound for the union of all issued events, including executions
with recursively reconstructed merge bases. No replica need hold this union. -/
theorem global_boundV {n : Nat} {K : Int} {C : Configuration (D n K)}
    (reach : MintCertifiedReachV (D n K) (canonicalVirtualMergeBase (D n K))
      (generation n K) C) :
    K ≤ globalValue K reach.events_finite.toFinset := by
  obtain ⟨_,_,_,_,_,_,bound⟩ :=
    all_events_safe (canonicalV reach) (honestV reach) reach.events_finite
  exact bound

theorem global_bound {n : Nat} {K : Int} {C : Configuration (D n K)}
    (reach : MintCertifiedReach (D n K) (generation n K) C) :
    K ≤ globalValue K (reach.toV (V := canonicalVirtualMergeBase (D n K))).events_finite.toFinset :=
  global_boundV reach.toV

end Sal.MRDTs.Paper1.BalegasBoundedCounterEvent
