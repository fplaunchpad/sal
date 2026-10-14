import Sal.MRDTs.Instances.FugueMaxBackward
import Sal.MRDTs.Paper1.FugueMaxOriginTreeWitness
import Sal.MRDTs.Paper1.FugueMaxSourceRepresentation
import Sal.MRDTs.Paper1.OriginForestDecomposition

/-! Source left-origin ancestry derived from honest chain shape.
The source invariant, not forward first-child adjacency alone, supplies the
connection to an ordered origin forest. -/
namespace Sal.MRDTs.Paper1.FugueMaxOriginForest
open Sal.EmbedRGA
open Foundation
open Instances.SidedEmbedRGA
open Instances.SidedEmbedRGA.FugueMax
open FugueMaxSourceRepresentation
open FugueMaxClientCandidate

theorem rheaded_origin_ancestor {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) (inv2 : ∀ g ∈ K, SLC Γ K g) :
    ∀ (N c : ℕ), c ∈ mMintedIds K → (mChainOf K c).length ≤ N →
    ∀ A : ℕ, (A = 0 ∨ A ∈ mMintedIds K) →
    (∃ t d ext, mChainOf K c = mChainOf K A ++ FMEntry.R t d :: ext) →
    mLoDesc K c A := by
  intro N
  induction N with
  | zero =>
      intro c hc hlen A hA hext
      exfalso
      obtain ⟨t, d, ext, hext⟩ := hext
      have := congrArg List.length hext
      simp at this
      omega
  | succ N ih =>
      intro c hc hlen A hA hext
      obtain ⟨t, d, ext, hext⟩ := hext
      obtain ⟨hloOr, t', d', ls', hdec, hall⟩ := loShape_of_inv inv inv2 hc
      have p1 : mChainOf K A <+: mChainOf K c :=
        ⟨FMEntry.R t d :: ext, hext.symm⟩
      have p2 : mChainOf K (mLoOf K c) <+: mChainOf K c :=
        ⟨FMEntry.R t' d' :: ls', hdec.symm⟩
      rcases List.prefix_or_prefix_of_prefix p2 p1 with hpre | hpre
      · -- chain(lo c) a prefix of chain(A)
        obtain ⟨u, hu⟩ := hpre
        cases u with
        | nil =>
            -- equal chains: lo c = A, take D = c
            rw [List.append_nil] at hu
            have hAeq : mLoOf K c = A := by
              have s1 := mChainOf_sum inv hloOr
              have s2 := mChainOf_sum inv hA
              rw [hu] at s1
              omega
            exact ⟨1, by simpa using hAeq⟩
        | cons e u' =>
            -- misalignment: A's R entry lands inside the all-L tail
            exfalso
            have hcc : mChainOf K (mLoOf K c)
                ++ FMEntry.R t' d' :: ls'
                = mChainOf K (mLoOf K c)
                  ++ (e :: u') ++ FMEntry.R t d :: ext := by
              rw [← hdec, hext, ← hu]
            rw [List.append_assoc] at hcc
            have hcc' := List.append_cancel_left hcc
            rw [List.cons_append] at hcc'
            injection hcc' with h1 h2
            have hmem : FMEntry.R t d ∈ ls' := by
              rw [h2]
              exact List.mem_append_right _ List.mem_cons_self
            obtain ⟨dd, hL⟩ := hall _ hmem
            exact FMEntry.noConfusion hL
      · -- chain(A) a prefix of chain(lo c)
        obtain ⟨v, hv⟩ := hpre
        cases v with
        | nil =>
            rw [List.append_nil] at hv
            have hAeq : mLoOf K c = A := by
              have s1 := mChainOf_sum inv hloOr
              have s2 := mChainOf_sum inv hA
              rw [← hv] at s1
              omega
            exact ⟨1, by simpa using hAeq⟩
        | cons e v' =>
            -- chain(lo c) strictly extends chain(A), R-headedly: recurse
            have hcc : mChainOf K A ++ FMEntry.R t d :: ext
                = mChainOf K A
                  ++ (e :: v') ++ FMEntry.R t' d' :: ls' := by
              rw [← hext, hdec, ← hv]
            rw [List.append_assoc] at hcc
            have hcc' := List.append_cancel_left hcc
            rw [List.cons_append] at hcc'
            injection hcc' with h1 h2
            have hlomint : mLoOf K c ∈ mMintedIds K := by
              rcases hloOr with h0 | h
              · exfalso
                rw [h0, mChainOf_zero inv.pos] at hv
                have := congrArg List.length hv
                simp at this
              · exact h
            have hlolen : (mChainOf K (mLoOf K c)).length ≤ N := by
              have := congrArg List.length hdec
              simp at this
              omega
            obtain ⟨steps, reached⟩ := ih (mLoOf K c) hlomint hlolen
              A hA ⟨t, d, v', by rw [← hv, ← h1]⟩
            exact ⟨steps + 1, by rw [Function.iterate_succ_apply]; exact reached⟩

theorem loDesc_refl (K : KnowM) (id : Nat) : mLoDesc K id id := ⟨0,rfl⟩

theorem loDesc_parent (K : KnowM) (id : Nat) : mLoDesc K id (mLoOf K id) := ⟨1,rfl⟩

theorem loDesc_trans {K : KnowM} {x y z : Nat}
    (xy : mLoDesc K x y) (yz : mLoDesc K y z) : mLoDesc K x z := by
  obtain ⟨a,ha⟩ := xy
  obtain ⟨b,hb⟩ := yz
  exact ⟨b+a,by rw [Function.iterate_add_apply,ha,hb]⟩

theorem loDesc_parent_peel {K : KnowM} {x y : Nat}
    (xy : mLoDesc K x y) (different : x ≠ y) : mLoDesc K (mLoOf K x) y := by
  obtain ⟨n,reached⟩ := xy
  cases n with
  | zero => exact (different reached).elim
  | succ n => exact ⟨n,by simpa only [Function.iterate_succ_apply] using reached⟩

theorem parent_closed {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) (slc : ∀ g ∈ K, SLC Γ K g)
    {id : Nat} (minted : id ∈ mMintedIds K) :
    mLoOf K id = 0 ∨ mLoOf K id ∈ mMintedIds K :=
  (loShape_of_inv inv slc minted).1

theorem parent_before {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) (slc : ∀ g ∈ K, SLC Γ K g)
    {id : Nat} (minted : id ∈ mMintedIds K) :
    mBefore Γ K (mLoOf K id) id := by
  obtain ⟨closed,t,d,tail,chain,_⟩ := loShape_of_inv inv slc minted
  apply mBefore_of_chainBefore inv closed (Or.inr minted)
  rw [chain]
  exact fmChainBefore.extR _ _ _ _

theorem parent_lt {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) {id : Nat} (minted : id ∈ mMintedIds K) :
    mLoOf K id < id := by
  obtain ⟨g,found,member,inserted,same⟩ := mRecOfId_of_minted minted
  rw [mLoOf_eq found,← same]
  obtain ⟨parent,side,operation⟩ := mIsIns_shape inserted
  cases side with
  | R =>
    obtain ⟨sameParent,lt,_⟩ := inv.linkR g member parent operation
    simpa [sameParent] using lt
  | L =>
    obtain ⟨_,lt,parentMinted,_,loClosed,t,d,rest,chain⟩ :=
      inv.linkL g member parent operation
    have sumParent := mChainOf_sum inv (Or.inr parentMinted)
    have sumLo := mChainOf_sum inv loClosed
    rw [chain,List.map_append,List.sum_append,sumLo] at sumParent
    omega

theorem loDesc_before_or_eq {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) (slc : ∀ g ∈ K, SLC Γ K g)
    {descendant ancestor : Nat} (minted : descendant ∈ mMintedIds K)
    (desc : mLoDesc K descendant ancestor) :
    ancestor = descendant ∨ mBefore Γ K ancestor descendant := by
  obtain ⟨n,reached⟩ := desc
  induction n generalizing descendant with
  | zero => exact Or.inl reached.symm
  | succ n ih =>
    rw [Function.iterate_succ_apply] at reached
    rcases parent_closed inv slc minted with root | parentMinted
    · rw [root,mLoOf_iterate_zero inv.pos] at reached
      subst ancestor
      exact Or.inr (by simpa [root] using parent_before inv slc minted)
    · rcases ih parentMinted reached with same | before
      · exact Or.inr (by simpa [same] using parent_before inv slc minted)
      · exact Or.inr (mBefore_trans before (parent_before inv slc minted))

theorem parent_le {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) (id : Nat) : mLoOf K id ≤ id := by
  by_cases minted : id ∈ mMintedIds K
  · exact Nat.le_of_lt (parent_lt inv minted)
  · have absent : mRecOfId K id = none := by
      cases found : mRecOfId K id with
      | none => rfl
      | some g =>
        have member : g ∈ mMinted K := List.mem_of_find?_eq_some found
        have same : g.ts = id := by simpa using List.find?_some found
        exact (minted (List.mem_map.mpr ⟨g,member,same⟩)).elim
    simp [mLoOf,absent]

theorem loDesc_le {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) {x y : Nat} (desc : mLoDesc K x y) : y ≤ x := by
  obtain ⟨n,reached⟩ := desc
  induction n generalizing x with
  | zero => exact Nat.le_of_eq reached.symm
  | succ n ih =>
    rw [Function.iterate_succ_apply] at reached
    exact (ih reached).trans (parent_le inv x)

theorem loDesc_antisymm {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) {x y : Nat} (xy : mLoDesc K x y) (yx : mLoDesc K y x) : x = y :=
  Nat.le_antisymm (loDesc_le inv yx) (loDesc_le inv xy)

theorem source_order_pairwise {Γ : OrderedPrefixCode} {K : KnowM} {s : SState}
    (sorted : SSorted s) (shape : ∀ r ∈ s, r = node Γ K r.1) :
    (s.map Prod.fst).Pairwise (mBefore Γ K) := by
  rw [List.pairwise_map]
  apply sorted.imp_of_mem
  intro a b ha hb before
  have ashape := shape a ha
  have bshape := shape b hb
  have ac := congrArg (fun r : SRec => r.2.2) ashape
  have bc := congrArg (fun r : SRec => r.2.2) bshape
  dsimp only at ac bc
  rw [ac,bc] at before
  exact before

/-- Every source origin-descendant cone is convex in structural display
order. The proof uses genuine source chain shape, including tombstones. -/
theorem origin_interval_closed {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) (slc : ∀ g ∈ K, SLC Γ K g)
    {ancestor descendant between : Nat}
    (ancestorKnown : ancestor = 0 ∨ ancestor ∈ mMintedIds K)
    (descendantKnown : descendant ∈ mMintedIds K)
    (betweenKnown : between ∈ mMintedIds K)
    (desc : mLoDesc K descendant ancestor)
    (after : mBefore Γ K ancestor between)
    (before : mBefore Γ K between descendant) :
    mLoDesc K between ancestor := by
  obtain ⟨steps,reached⟩ := desc
  obtain ⟨extension,chain⟩ := loDesc_prefix inv slc steps descendant ancestor descendantKnown reached
  have afterChain := chainBefore_of_mBefore inv ancestorKnown (Or.inr betweenKnown) after
  have beforeChain := chainBefore_of_mBefore inv (Or.inr betweenKnown) (Or.inr descendantKnown) before
  obtain ⟨ext,betweenChain⟩ := fm_subtree_convex (mChainOf K ancestor)
    ⟨[],by simp⟩ ⟨extension,chain.symm⟩ afterChain beforeChain
  obtain ⟨t,d,rest,same⟩ := fm_ext_after_is_R (p := mChainOf K ancestor)
    (ext := ext) (by rw [← betweenChain]; exact afterChain)
  apply rheaded_origin_ancestor inv slc (mChainOf K between).length between betweenKnown
    (Nat.le_refl _) ancestor ancestorKnown
  exact ⟨t,d,rest,by rw [betweenChain,same]⟩

theorem source_noGaps {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) (slc : ∀ g ∈ K, SLC Γ K g) (ids : List Nat)
    (minted : ∀ id ∈ ids, id ∈ mMintedIds K)
    (sorted : ids.Pairwise (mBefore Γ K)) :
    OriginForestDecomposition.NoGaps (mLoDesc K) ids := by
  induction ids with
  | nil => trivial
  | cons head rest ih =>
    have pieces := List.pairwise_cons.mp sorted
    refine ⟨?_,ih (fun id member => minted id (by simp [member])) pieces.2⟩
    apply pieces.2.imp_of_mem
    intro b c hb hc before desc
    exact origin_interval_closed inv slc (Or.inr (minted head (by simp)))
      (minted c (by simp [hc])) (minted b (by simp [hb])) desc (pieces.1 b hb) before

/-- The actual source permanent display constructs an ordered left-origin
forest. Pair identities and origins agree with source record lookups. -/
theorem source_forest_exists {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) (slc : ∀ g ∈ K, SLC Γ K g) (ids : List Nat)
    (unique : (0 :: ids).Nodup)
    (enumerates : ∀ id, id ∈ 0 :: ids ↔ id = 0 ∨ id ∈ mMintedIds K)
    (sorted : ids.Pairwise (mBefore Γ K)) :
    ∃ pairs, FugueMaxOriginTreeWitness.OriginPlan 0 ids pairs ∧
      ∀ pair ∈ pairs, pair.2 = mLoOf K pair.1 := by
  have nonzero : ∀ id ∈ ids, id ≠ 0 := by
    intro id member same
    exact (List.nodup_cons.mp unique).1 (same ▸ member)
  have minted : ∀ id ∈ ids, id ∈ mMintedIds K := by
    intro id member
    exact ((enumerates id).mp (by simp [member])).resolve_left (nonzero id member)
  apply OriginForestDecomposition.forest_exists (mLoOf K) (mLoDesc K)
    (@loDesc_trans K) (loDesc_antisymm inv) (loDesc_parent K)
    (fun x y desc ne => loDesc_parent_peel desc ne) 0 ids unique
  · intro id member desc
    obtain ⟨steps,reached⟩ := desc
    rw [mLoOf_iterate_zero inv.pos] at reached
    exact nonzero id member reached.symm
  · intro id member
    exact Nat.ne_of_lt (parent_lt inv (minted id member))
  · intro id member
    rcases parent_closed inv slc (minted id member) with root | known
    · exact Or.inl root
    · rcases List.mem_cons.mp ((enumerates _).mpr (Or.inr known)) with root | inIds
      · exact Or.inl root
      · exact Or.inr inIds
  · apply sorted.imp_of_mem
    intro a b ha hb before same
    have reverse := parent_before inv slc (minted a ha)
    rw [same] at reverse
    exact mBefore_asymm before reverse
  · exact source_noGaps inv slc ids minted sorted

theorem honest_source_ordered_representation {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis)
    {ops : List (Op Payload)} {E : Set (Op Payload)}
    (enumerates : listPermOf ops E) (supported : ∀ e ∈ E, e ∈ C.events)
    (ordered : respects ops (@loOn (datatype Γ).toUpdateSig (replayOrder Γ) C.replayContext E))
    (inv : KInv Γ (ops.map recordOf)) :
    ∃ s : Buffer, (∃ tail, s.order = 0 :: tail) ∧ s.order.Nodup ∧
      visible s = sIds (summarize Γ (ops.map recordOf)).live ∧
      (∀ id, id ∈ s.order ↔ id = 0 ∨ id ∈ mMintedIds (ops.map recordOf)) ∧
      s.order.Pairwise (mBefore Γ (ops.map recordOf)) ∧
      s.deleted = deletedTargets ((ops.map recordOf).filter (fun g => !mIsIns g)) := by
  let K := ops.map recordOf
  let D := K.filter (fun g => !mIsIns g)
  have nodup : K.Nodup := enumerates.1.map_on (by
    intro a ha b hb same
    have eq := congrArg eventOf same
    simpa using eq)
  obtain ⟨L,births,construction⟩ := exists_chain_construction (mMinted K)
  have sub : ∀ g ∈ L, g ∈ K ∧ mIsIns g = true :=
    fun g member => List.mem_filter.mp (births.mem_iff.mpr member)
  have parents := birth_parents_of_construction inv births construction
  obtain ⟨sorted,_⟩ := births_refine inv sub (births.nodup (nodup.filter _)) construction parents
  have shape : ∀ r ∈ buildNodes Γ K L,
      r = node Γ K r.1 ∧ (r.1 = 0 ∨ r.1 ∈ mMintedIds K) := by
    intro r member
    rcases (buildNodes_mem Γ K L r).mp member with rfl | ⟨g,hg,rfl⟩
    · exact ⟨rfl,Or.inl rfl⟩
    · exact ⟨rfl,Or.inr (List.mem_map.mpr ⟨g,births.mem_iff.mpr hg,rfl⟩)⟩
  have root : node Γ K 0 ∈ buildNodes Γ K L :=
    (buildNodes_mem Γ K L _).mpr (Or.inl rfl)
  obtain ⟨tail,first⟩ := sorted_root_first inv sorted shape root
  refine ⟨sourceBuffer Γ K L D,⟨tail.map Prod.fst,?_,⟩,?_,?_,?_,?_,rfl⟩
  · change (buildNodes Γ K L).map Prod.fst = _
    rw [first]
    rfl
  · exact sourceBuffer_nodup sorted (fun r hr => (shape r hr).1)
  · exact sourceBuffer_matches_issuer C mint trans enumerates supported ordered inv births sorted
  · intro id
    change id ∈ (buildNodes Γ K L).map Prod.fst ↔ _
    constructor
    · intro member
      obtain ⟨r,hr,same⟩ := List.mem_map.mp member
      exact same ▸ (shape r hr).2
    · intro known
      apply List.mem_map.mpr
      refine ⟨node Γ K id,?_,rfl⟩
      apply (buildNodes_mem Γ K L _).mpr
      rcases known with zero | minted
      · exact Or.inl (by rw [zero])
      · obtain ⟨g,hg,same⟩ := List.mem_map.mp minted
        exact Or.inr ⟨g,births.mem_iff.mp hg,by rw [same]⟩

  · exact source_order_pairwise sorted (fun r hr => (shape r hr).1)

#print axioms honest_source_ordered_representation
#print axioms source_forest_exists
#print axioms rheaded_origin_ancestor
#print axioms parent_lt
#print axioms origin_interval_closed
end Sal.MRDTs.Paper1.FugueMaxOriginForest
