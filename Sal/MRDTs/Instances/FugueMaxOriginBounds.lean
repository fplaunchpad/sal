import Sal.MRDTs.Instances.FugueMaxHonesty

/-! Recorded origins delimit the strict structural display gap of a FugueMax
insertion. The bounds follow from the exact issuer's KInv/SLC/RBk facts;
structural parents and origins may be tombstones. No client specification or
merge equation is assumed by these geometry lemmas. -/
namespace Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax
open Foundation
open Sal.EmbedRGA (OrderedPrefixCode Side FMEntry fmChainBefore fmCoordOf sKey keyLt)

/-- A coherent insertion is strictly after its recorded left origin. -/
theorem record_after_left_origin {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) (slc : ∀ g ∈ K, SLC Γ K g)
    {g : MRec} (member : g ∈ K) (inserted : mIsIns g = true) :
    mBefore Γ K g.lo g.ts := by
  have minted : g.ts ∈ mMintedIds K :=
    List.mem_map.mpr ⟨g,List.mem_filter.mpr ⟨member,inserted⟩,rfl⟩
  obtain ⟨left,t,d,tail,chain,_⟩ := loShape_of_inv inv slc minted
  have lo := mLoOf_eq (mRecOfId_of_mem inv member inserted)
  rw [lo] at left chain
  apply mBefore_of_chainBefore inv left (Or.inr minted)
  rw [chain]
  exact fmChainBefore.extR _ _ _ _

/-- Both branches of the exact Fugue parent rule place the insertion strictly
before its recorded right origin, when that origin exists. -/
theorem record_before_right_origin {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) (bk : ∀ g ∈ K, RBk Γ K g)
    {g : MRec} (member : g ∈ K) (inserted : mIsIns g = true)
    {right : Nat} (origin : g.ro = some right) :
    mBefore Γ K g.ts right := by
  obtain ⟨parent,side,operation⟩ := mIsIns_shape inserted
  cases side with
  | R => exact (rmint_ro_after inv member (bk g member) operation origin).1
  | L =>
    obtain ⟨ro,_,parentMinted,chain,_,_⟩ := inv.linkL g member parent operation
    have same : parent = right := Option.some.inj (ro.symm.trans origin)
    subst right
    have minted : g.ts ∈ mMintedIds K :=
      List.mem_map.mpr ⟨g,List.mem_filter.mpr ⟨member,inserted⟩,rfl⟩
    apply mBefore_of_chainBefore inv (Or.inr minted) (Or.inr parentMinted)
    rw [mChainOf_of_mem inv member inserted,chain]
    exact fmChainBefore.extL _ _ _

theorem record_origin_bounds {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) (slc : ∀ g ∈ K, SLC Γ K g)
    (bk : ∀ g ∈ K, RBk Γ K g) {g : MRec}
    (member : g ∈ K) (inserted : mIsIns g = true) :
    mBefore Γ K g.lo g.ts ∧ ∀ right, g.ro = some right → mBefore Γ K g.ts right :=
  ⟨record_after_left_origin inv slc member inserted,
    fun _ origin => record_before_right_origin inv bk member inserted origin⟩

/-- The same bounds expressed directly at the immutable generated chain.
`keyLt` runs opposite to display order in the coordinate encoding. -/
theorem record_origin_key_bounds {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) (slc : ∀ g ∈ K, SLC Γ K g)
    (bk : ∀ g ∈ K, RBk Γ K g) {g : MRec}
    (member : g ∈ K) (inserted : mIsIns g = true) :
    keyLt (sKey (fmCoordOf Γ g.chain)) (mKey Γ K g.lo) = true ∧
      ∀ right, g.ro = some right →
        keyLt (mKey Γ K right) (sKey (fmCoordOf Γ g.chain)) = true := by
  have chain : mKey Γ K g.ts = sKey (fmCoordOf Γ g.chain) := by
    simp only [mKey,mChainOf_of_mem inv member inserted]
  have bounds := record_origin_bounds inv slc bk member inserted
  simpa only [mBefore,chain] using bounds

/-- Execution honesty transports issuer-local geometry into any supported,
causally closed version history. -/
theorem event_origin_bounds {Γ : OrderedPrefixCode}
    (C : Configuration (datatype Γ)) (mint : MintHonest (datatype Γ) (applicable Γ) C)
    (trans : Transitive C.vis) (irr : ∀ e, ¬ C.vis e e)
    (ops : List (Op Payload)) (nodup : ops.Nodup)
    (supported : ∀ e ∈ ops, e ∈ C.events)
    (closed : ∀ a b, C.vis a b → b ∈ ops → a ∈ ops)
    {e : Op Payload} (member : e ∈ ops) (inserted : mIsIns (recordOf e) = true) :
    mBefore Γ (ops.map recordOf) e.op.lo e.time ∧
      ∀ right, e.op.ro = some right → mBefore Γ (ops.map recordOf) e.time right := by
  obtain ⟨inv,slc,bk⟩ := invariants_of_mint C mint trans irr ops nodup supported closed
  exact record_origin_bounds inv slc bk (List.mem_map.mpr ⟨e,member,rfl⟩) inserted

#print axioms record_origin_bounds
#print axioms event_origin_bounds
end Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax
