import Sal.MRDTs.Instances.FugueMaxOriginBounds
import Sal.MRDTs.Instances.FugueMaxListRefinement

/-! Proof-side key threshold for an origin-local immediate splice.
The abstract sequence machine itself does not use these coordinates. -/
namespace Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax
open Sal.EmbedRGA (keyLt keyLt_irrefl keyLt_trans keyLt_total keyLt_asymm)
open Foundation

/-- If the generated key lies between the anchor and its immediate successor,
then comparison with every old key selects exactly the prefix through the
anchor. `successorFirst` includes the end-of-list case without a fictitious
right identity. -/
theorem origin_splice_threshold {anchor fresh old : List Nat}
    (afterAnchor : keyLt fresh anchor = true)
    (distinct : old ≠ anchor)
    (successorFirst : keyLt old anchor = true → keyLt old fresh = true) :
    keyLt fresh old = true ↔ keyLt anchor old = true := by
  constructor
  · intro before
    rcases keyLt_total distinct with after | prior
    · have conflict := keyLt_asymm (successorFirst after)
      rw [before] at conflict
      contradiction
    · exact prior
  · intro prior
    exact keyLt_trans afterAnchor prior

/-- The successor's maximality and the right-origin bound exclude every old
key from the new gap. This is the substantive threshold step for a source
generated insert with a right origin. -/
theorem successor_gap_excludes {right fresh old : List Nat}
    (rightBound : keyLt right fresh = true)
    (maximal : keyLt right old = false) : keyLt old fresh = true := by
  by_cases equal : old = right
  · simpa [equal] using rightBound
  · rcases keyLt_total equal with lower | higher
    · exact keyLt_trans lower rightBound
    · rw [higher] at maximal
      contradiction

/-- Transport the issuer's immediate-successor fact into the augmented
history. Every old identity after the left origin lies after the new birth.
This closes the nonempty-right-bound half of the source splice proof. -/
theorem issuer_successor_excludes_old {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    {K : KnowM} {g : MRec} {right old : Nat}
    (oldInv : KInv Γ K) (augInv : KInv Γ (K ++ [g]))
    (slc : ∀ b ∈ K ++ [g], SLC Γ (K ++ [g]) b)
    (bk : ∀ b ∈ K ++ [g], RBk Γ (K ++ [g]) b)
    (inserted : mIsIns g = true) (origin : g.ro = some right)
    (successor : succOfM Γ K g.lo = some right)
    (candidate : (old,mKey Γ K old) ∈ succCandM Γ K g.lo) :
    keyLt (mKey Γ K old) (Sal.EmbedRGA.sKey (Sal.EmbedRGA.fmCoordOf Γ g.chain)) = true := by
  have member : g ∈ K ++ [g] := by simp
  have positive : ∀ b ∈ [g], 1 ≤ b.ts := by
    intro b hb
    simp only [List.mem_singleton] at hb
    subst b
    exact augInv.pos g member
  have rightMinted := succOfM_mem successor
  have stableRight : mKey Γ (K ++ [g]) right = mKey Γ K right := by
    unfold mKey
    rw [mChainOf_append_stable (Or.inr rightMinted) oldInv.pos positive]
  have bounds := record_origin_key_bounds augInv slc bk member inserted
  have rightBound := bounds.2 right origin
  rw [stableRight] at rightBound
  exact successor_gap_excludes rightBound (succOfM_max successor candidate)

theorem no_successor_no_candidate {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    {K : KnowM} {anchor old : Nat} (none : succOfM Γ K anchor = none) :
    (old,mKey Γ K old) ∉ succCandM Γ K anchor := by
  intro candidate
  obtain ⟨right,some⟩ := succOfM_isSome_of_cand candidate
  rw [none] at some
  contradiction

theorem issuer_old_key_threshold {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    {K : KnowM} {g : MRec} {old : Nat}
    (oldInv : KInv Γ K) (augInv : KInv Γ (K ++ [g]))
    (slc : ∀ b ∈ K ++ [g], SLC Γ (K ++ [g]) b)
    (bk : ∀ b ∈ K ++ [g], RBk Γ (K ++ [g]) b)
    (inserted : mIsIns g = true)
    (leftKnown : g.lo = 0 ∨ g.lo ∈ mMintedIds K)
    (rightExact : g.ro = succOfM Γ K g.lo)
    (oldMinted : old ∈ mMintedIds K) :
    keyLt (Sal.EmbedRGA.sKey (Sal.EmbedRGA.fmCoordOf Γ g.chain)) (mKey Γ K old) = true ↔
      old = g.lo ∨ keyLt (mKey Γ K g.lo) (mKey Γ K old) = true := by
  have member : g ∈ K ++ [g] := by simp
  have positive : ∀ b ∈ [g], 1 ≤ b.ts := by
    intro b hb
    simp only [List.mem_singleton] at hb
    subst b
    exact augInv.pos g member
  have stableLeft : mKey Γ (K ++ [g]) g.lo = mKey Γ K g.lo := by
    unfold mKey
    rw [mChainOf_append_stable leftKnown oldInv.pos positive]
  have afterAnchor := (record_origin_key_bounds augInv slc bk member inserted).1
  rw [stableLeft] at afterAnchor
  by_cases same : old = g.lo
  · simp only [same,true_or,iff_true]
    exact afterAnchor
  · have different : mKey Γ K old ≠ mKey Γ K g.lo := by
      intro eq
      exact same (mKey_inj oldInv (Or.inr oldMinted) leftKnown eq)
    rw [or_iff_right same]
    apply origin_splice_threshold afterAnchor different
    intro after
    have candidate := cand_of_after oldMinted (Or.inr after)
    cases successor : succOfM Γ K g.lo with
    | none => exact False.elim (no_successor_no_candidate successor candidate)
    | some right =>
      exact issuer_successor_excludes_old oldInv augInv slc bk inserted
        (rightExact.trans successor) successor candidate

theorem minted_after_root {Γ : Sal.EmbedRGA.OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) {id : Nat} (minted : id ∈ mMintedIds K) :
    keyLt (mKey Γ K id) (mKey Γ K 0) = true := by
  obtain ⟨g,hg,same⟩ := List.mem_map.mp minted
  obtain ⟨member,inserted⟩ := List.mem_filter.mp hg
  obtain ⟨tag,delta,tail,shape⟩ := chain_head_R inv g.chain.length g member inserted (by omega)
  apply mBefore_of_chainBefore inv (Or.inl rfl) (Or.inr minted)
  rw [mChainOf_zero inv.pos,← same,mChainOf_of_mem inv member inserted,shape]
  exact Sal.EmbedRGA.fmChainBefore.extR [] tag delta tail

theorem issuer_key_threshold {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    {K : KnowM} {g : MRec} {old : Nat}
    (oldInv : KInv Γ K) (augInv : KInv Γ (K ++ [g]))
    (slc : ∀ b ∈ K ++ [g], SLC Γ (K ++ [g]) b)
    (bk : ∀ b ∈ K ++ [g], RBk Γ (K ++ [g]) b)
    (inserted : mIsIns g = true)
    (leftKnown : g.lo = 0 ∨ g.lo ∈ mMintedIds K)
    (rightExact : g.ro = succOfM Γ K g.lo)
    (oldKnown : old = 0 ∨ old ∈ mMintedIds K) :
    keyLt (Sal.EmbedRGA.sKey (Sal.EmbedRGA.fmCoordOf Γ g.chain)) (mKey Γ K old) = true ↔
      old = g.lo ∨ keyLt (mKey Γ K g.lo) (mKey Γ K old) = true := by
  rcases oldKnown with rfl | minted
  · have member : g ∈ K ++ [g] := by simp
    have newMinted : g.ts ∈ mMintedIds (K ++ [g]) :=
      List.mem_map.mpr ⟨g,List.mem_filter.mpr ⟨member,inserted⟩,rfl⟩
    have afterRoot := minted_after_root augInv newMinted
    unfold mKey at afterRoot
    rw [mChainOf_of_mem augInv member inserted,mChainOf_zero augInv.pos] at afterRoot
    have rootEq : mKey Γ K 0 = Sal.EmbedRGA.sKey (Sal.EmbedRGA.fmCoordOf Γ []) := by
      simp [mKey,mChainOf_zero oldInv.pos]
    rw [← rootEq] at afterRoot
    apply iff_of_true afterRoot
    rcases leftKnown with zero | minted
    · exact Or.inl zero.symm
    · exact Or.inr (minted_after_root oldInv minted)
  · exact issuer_old_key_threshold oldInv augInv slc bk inserted leftKnown rightExact minted

theorem issuer_origin_splice {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    {K : KnowM} {g : MRec} {s : SState}
    (oldInv : KInv Γ K) (augInv : KInv Γ (K ++ [g]))
    (slc : ∀ b ∈ K ++ [g], SLC Γ (K ++ [g]) b)
    (bk : ∀ b ∈ K ++ [g], RBk Γ (K ++ [g]) b)
    (inserted : mIsIns g = true)
    (leftKnown : g.lo = 0 ∨ g.lo ∈ mMintedIds K)
    (rightExact : g.ro = succOfM Γ K g.lo)
    (sorted : SSorted s)
    (shape : ∀ r ∈ s, r = node Γ K r.1 ∧ (r.1 = 0 ∨ r.1 ∈ mMintedIds K))
    (anchor : node Γ K g.lo ∈ s)
    (fresh : ∀ r ∈ s, r.1 ≠ g.ts) :
    (sInsert (g.ts,g.ts,Sal.EmbedRGA.fmCoordOf Γ g.chain) s).map sProj =
      sInsAfter g.lo (g.ts,g.ts) (s.map sProj) := by
  apply sInsert_map_insAfter sorted anchor rfl
  · intro r hr r' hr' same
    rw [(shape r hr).1,(shape r' hr').1,same]
  · intro r hr eq
    apply fresh r hr
    have member : g ∈ K ++ [g] := by simp
    have positive : ∀ b ∈ [g], 1 ≤ b.ts := by
      intro b hb
      simp only [List.mem_singleton] at hb
      subst b
      exact augInv.pos g member
    have oldKnown := (shape r hr).2
    have augKnown : r.1 = 0 ∨ r.1 ∈ mMintedIds (K ++ [g]) := by
      rcases oldKnown with zero | minted
      · exact Or.inl zero
      · exact Or.inr (by simpa [mMintedIds,mMinted_append] using
          List.mem_append_left (mMintedIds [g]) minted)
    have newKnown : g.ts = 0 ∨ g.ts ∈ mMintedIds (K ++ [g]) :=
      Or.inr (List.mem_map.mpr ⟨g,List.mem_filter.mpr ⟨member,inserted⟩,rfl⟩)
    apply mKey_inj augInv augKnown newKnown
    unfold mKey
    rw [mChainOf_append_stable oldKnown oldInv.pos positive,
      mChainOf_of_mem augInv member inserted]
    have coordinates := congrArg (fun x : SRec => x.2.2) (shape r hr).1
    dsimp only at coordinates
    rw [coordinates] at eq
    exact eq
  · intro r hr
    have threshold := issuer_key_threshold oldInv augInv slc bk inserted leftKnown
      rightExact (shape r hr).2
    have same : r = node Γ K g.lo ↔ r.1 = g.lo := by
      constructor
      · intro eq
        exact congrArg Prod.fst eq
      · intro eq
        rw [(shape r hr).1,eq]
    rw [same,(shape r hr).1]
    exact threshold

#print axioms origin_splice_threshold
#print axioms successor_gap_excludes
#print axioms issuer_successor_excludes_old
#print axioms issuer_old_key_threshold
#print axioms issuer_key_threshold
#print axioms issuer_origin_splice
end Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax
