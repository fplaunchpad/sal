import Sal.MRDTs.Paper1.FugueMaxClientRefinement

namespace Sal.MRDTs.Paper1.FugueMaxPhysicalClientRefinement
open Foundation
open Instances.SidedEmbedRGA
open Instances.SidedEmbedRGA.FugueMax
open FugueMaxClientCandidate
open FugueMaxSourceRepresentation

theorem insert_front {new : SRec} (s : SState)
    (before : ∀ r ∈ s, Sal.EmbedRGA.keyLt (Sal.EmbedRGA.sKey r.2.2)
      (Sal.EmbedRGA.sKey new.2.2) = true) : sInsert new s = new :: s := by
  cases s with
  | nil => rfl
  | cons head tail => simp [sInsert,before head (by simp)]

theorem insert_filter {new : SRec} (keep : SRec → Bool) (kept : keep new = true)
    (s : SState) (sorted : SSorted s) :
    sInsert new (s.filter keep) = (sInsert new s).filter keep := by
  induction s with
  | nil => simp [sInsert,kept]
  | cons head tail ih =>
    have ih := ih (List.pairwise_cons.mp sorted).2
    cases included : keep head <;>
      by_cases before : Sal.EmbedRGA.keyLt (Sal.EmbedRGA.sKey head.2.2)
        (Sal.EmbedRGA.sKey new.2.2) = true <;>
        simp [sInsert,included,before,kept,ih]
    rw [insert_front]
    · simp [kept]
    · intro r hr
      exact Sal.EmbedRGA.keyLt_trans ((List.pairwise_cons.mp sorted).1 r hr) before

theorem splice_ids (id left : Nat) (pairs : List (Nat × Nat)) :
    (sInsAfter left (id,id) pairs).map Prod.fst =
      FugueMaxNaturalSequence.insertAfter (pairs.map Prod.fst) id left := by
  induction pairs with
  | nil => rfl
  | cons head tail ih =>
    by_cases same : head.1 = left <;>
      simp [sInsAfter,FugueMaxNaturalSequence.insertAfter,same,ih]

theorem physical_insert_matches_abstract {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    {K D : KnowM} {g : MRec} {permanent live : SState}
    (oldInv : KInv Γ K) (augInv : KInv Γ (K ++ [g]))
    (slc : ∀ b ∈ K ++ [g], SLC Γ (K ++ [g]) b)
    (bk : ∀ b ∈ K ++ [g], RBk Γ (K ++ [g]) b)
    (inserted : mIsIns g = true)
    (leftKnown : g.lo = 0 ∨ g.lo ∈ mMintedIds K)
    (rightExact : g.ro = succOfM Γ K g.lo)
    (sorted : SSorted permanent)
    (shape : ∀ r ∈ permanent, r = node Γ K r.1 ∧ (r.1 = 0 ∨ r.1 ∈ mMintedIds K))
    (anchor : node Γ K g.lo ∈ permanent)
    (fresh : ∀ r ∈ permanent, r.1 ≠ g.ts)
    (undeleted : g.ts ∉ deletedTargets D)
    (liveEq : live = permanent.filter (fun r => decide (r.1 ≠ 0 ∧ r.1 ∉ deletedTargets D))) :
    sIds (mStep Γ live g) = visible
      (FugueMaxNaturalSequence.step ⟨sIds permanent,deletedTargets D⟩
        (FugueMaxNaturalSequence.ofMessage g)) := by
  let new : SRec := (g.ts,g.ts,Sal.EmbedRGA.fmCoordOf Γ g.chain)
  let keep : SRec → Bool := fun r => decide (r.1 ≠ 0 ∧ r.1 ∉ deletedTargets D)
  have nonzero : g.ts ≠ 0 := by
    have positive := augInv.pos g (by simp)
    omega
  have kept : keep new = true := by simp [keep,new,nonzero,undeleted]
  have missing : g.ts ∉ sIds live := by
    intro member
    obtain ⟨r,hr,same⟩ := List.mem_map.mp member
    rw [liveEq] at hr
    exact fresh r (List.mem_of_mem_filter hr) same
  obtain ⟨parent,side,operation⟩ := mIsIns_shape inserted
  have splice := issuer_origin_splice oldInv augInv slc bk inserted leftKnown rightExact
    sorted shape anchor fresh
  have idsSplice : sIds (sInsert new permanent) =
      FugueMaxNaturalSequence.insertAfter (sIds permanent) g.ts g.lo := by
    have ids := congrArg (List.map Prod.fst) splice
    rw [splice_ids] at ids
    simpa [sIds,List.map_map,sProj,new] using ids
  simp only [mStep,operation,if_neg missing]
  rw [liveEq,insert_filter keep kept permanent sorted]
  change (List.filter keep (sInsert new permanent)).map Prod.fst = _
  have filtered : (List.filter keep (sInsert new permanent)).map Prod.fst =
      (sIds (sInsert new permanent)).filter
        (fun id => decide (id ≠ 0 ∧ id ∉ deletedTargets D)) := by
    dsimp only [keep,sIds]
    exact (List.filter_map (f := fun r : SRec => r.1)
      (p := fun id => decide (id ≠ 0 ∧ id ∉ deletedTargets D))
      (l := sInsert new permanent)).symm
  rw [filtered,idsSplice]
  simp [FugueMaxNaturalSequence.ofMessage,operation,FugueMaxNaturalSequence.step,visible,visiblePart]

/-- Explicit physical-source conclusion: updating the unchanged issuer has
the positional client effect. The permanent representation is a proof relation;
the abstract contract contains no coordinates or structural parents. -/
theorem physical_insert_refines_positional {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    {K D : KnowM} {issuer : IssuerState} {permanent : SState}
    {rep stamp index id : Nat} {g : MRec}
    (generated : Generates Γ issuer rep stamp (.insert index id) g)
    (oldInv : KInv Γ K) (augInv : KInv Γ (K ++ [g]))
    (slc : ∀ b ∈ K ++ [g], SLC Γ (K ++ [g]) b)
    (bk : ∀ b ∈ K ++ [g], RBk Γ (K ++ [g]) b)
    (leftKnown : g.lo = 0 ∨ g.lo ∈ mMintedIds K)
    (rightExact : g.ro = succOfM Γ K g.lo)
    (sorted : SSorted permanent)
    (shape : ∀ r ∈ permanent, r = node Γ K r.1 ∧ (r.1 = 0 ∨ r.1 ∈ mMintedIds K))
    (anchor : node Γ K g.lo ∈ permanent)
    (fresh : ∀ r ∈ permanent, r.1 ≠ g.ts)
    (undeleted : g.ts ∉ deletedTargets D)
    (liveEq : issuer.live = permanent.filter (fun r => decide (r.1 ≠ 0 ∧ r.1 ∉ deletedTargets D)))
    (root : ∃ tail, sIds permanent = 0 :: tail)
    (unique : (sIds permanent).Nodup) :
    sIds (update Γ issuer g).live = clientStep (sIds issuer.live) (.insert index id) := by
  obtain ⟨inserted,same⟩ := FugueMaxClientRefinement.generated_insert_facts generated
  have physical := physical_insert_matches_abstract oldInv augInv slc bk inserted
    leftKnown rightExact sorted shape anchor fresh undeleted liveEq
  have view : visible ⟨sIds permanent,deletedTargets D⟩ = sIds issuer.live := by
    rw [liveEq]
    unfold visible visiblePart sIds
    exact List.filter_map ..
  obtain ⟨tail,root⟩ := root
  have nonzero : id ≠ 0 := by
    have positive := augInv.pos g (by simp)
    omega
  have abstract := FugueMaxNaturalSequence.generated_insert_refines_source generated
    view root unique nonzero (same ▸ undeleted)
  exact physical.trans abstract

theorem physical_delete_refines_positional {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    {issuer : IssuerState} {rep stamp index : Nat} {g : MRec}
    (generated : Generates Γ issuer rep stamp (.delete index) g)
    (unique : (sIds issuer.live).Nodup) (noRoot : 0 ∉ sIds issuer.live) :
    sIds (update Γ issuer g).live = clientStep (sIds issuer.live) (.delete index) := by
  let source : Buffer := ⟨sIds issuer.live,∅⟩
  have view : visible source = sIds issuer.live := by
    apply List.filter_eq_self.mpr
    intro id member
    have nonzero : id ≠ 0 := fun eq => noRoot (eq ▸ member)
    simp [source,nonzero]
  have bound : index < (visible source).length := by
    rw [view]
    simpa [sIds] using generated.1
  have abstract := FugueMaxNaturalSequence.positional_delete_refines
    (s := source) unique bound
  rw [view] at abstract
  have targetNonzero : (sIds issuer.live).getD index 0 ≠ 0 := by
    rw [List.getD_eq_getElem _ _ (by simpa [view] using bound)]
    exact fun eq => noRoot (eq ▸ List.getElem_mem (by simpa [view] using bound))
  have physical : sIds (update Γ issuer g).live =
      visible (FugueMaxNaturalSequence.step source
        (.deleteID ((sIds issuer.live).getD index 0))) := by
    rw [generated.2]
    simp only [update,prepareDelete,mStep,sIds]
    simp only [FugueMaxNaturalSequence.step]
    rw [visible_delete (s := source) (id := (issuer.live.map Prod.fst).getD index 0) targetNonzero,view]
    dsimp only [sIds]
    rw [List.filter_map]
    apply congrArg (List.map Prod.fst)
    apply List.filter_congr
    intro r hr
    apply Bool.eq_iff_iff.mpr
    simp [bne_iff_ne]
  exact physical.trans abstract

#print axioms insert_filter
#print axioms physical_insert_matches_abstract
#print axioms physical_insert_refines_positional
#print axioms physical_delete_refines_positional
end Sal.MRDTs.Paper1.FugueMaxPhysicalClientRefinement
