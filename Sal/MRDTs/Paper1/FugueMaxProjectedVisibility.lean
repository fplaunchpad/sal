import Sal.MRDTs.Paper1.FugueMaxNaturalCommutation
import Sal.MRDTs.Paper1.FugueMaxHonestPhysicalRefinement
import Sal.MRDTs.Paper1.FugueMaxOriginForest

/-! Specification-conflict visibility for the origin-only guarded language.
These are language-level dependencies, independent of coordinate replay. -/
namespace Sal.MRDTs.Paper1.FugueMaxProjectedVisibility
open Foundation
open Instances.SidedEmbedRGA
open Instances.SidedEmbedRGA.FugueMax
open FugueMaxNaturalSequence

theorem generator_right_origin (Γ : Sal.EmbedRGA.OrderedPrefixCode) (K : KnowM)
    (rep stamp anchor : Nat) :
    (mGenInsAfter Γ K rep stamp anchor).ro =
      succOfM Γ K (mGenInsAfter Γ K rep stamp anchor).lo := by
  unfold mGenInsAfter
  split <;> simp_all

def MayConflict (a b : MRec) : Prop := match a.op,b.op with
  | .ins _ _,.ins _ _ => a.ts = b.ts ∨ a.lo = b.lo ∨ a.ts = b.lo ∨ b.ts = a.lo
  | .ins _ _,.del target => target = a.ts
  | .del target,.ins _ _ => target = b.ts
  | .del _,.del _ => False

theorem noncommuting_requires_dependency (a b : MRec)
    (conflict : ¬ spec.Commutes (ofMessage a) (ofMessage b)) : MayConflict a b := by
  cases ao : a.op <;> cases bo : b.op
  all_goals simp only [MayConflict,ao,bo]
  case ins.ins parent side parent' side' =>
    by_contra independent
    simp only [not_or] at independent
    apply conflict
    simpa [ofMessage,ao,bo] using
      FugueMaxNaturalControls.distinct_anchor_language_commutes a.ts a.lo b.ts b.lo
        independent.1 independent.2.1 independent.2.2.1 independent.2.2.2
  case ins.del parent side target =>
    by_contra different
    apply conflict
    simpa [ofMessage,ao,bo] using
      FugueMaxNaturalCommutation.insert_delete_commutes a.ts a.lo target different
  case del.ins target parent side =>
    by_contra different
    apply conflict
    simpa [ofMessage,ao,bo] using
      HistorySpec.commutes_symm
        (FugueMaxNaturalCommutation.insert_delete_commutes b.ts b.lo target different)
  case del.del target target' =>
    apply conflict
    simpa [ofMessage,ao,bo] using FugueMaxNaturalCommutation.deletes_commute target target'

theorem projected_visibility_requires_dependency {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    (C : ReplayContext (datatype Γ).toUpdateSig) {a b : Op Payload}
    (edge : projectedSpecVisibility (fun e => ofMessage (recordOf e)) spec C a b) :
    C.vis a b ∧ MayConflict (recordOf a) (recordOf b) :=
  ⟨edge.1,noncommuting_requires_dependency _ _ edge.2⟩

theorem issuer_same_anchor_reverse_display {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    {K : KnowM} {earlier later : MRec}
    (inv : KInv Γ K) (sourceSlc : ∀ b ∈ K, SLC Γ K b)
    (augInv : KInv Γ (K ++ [later]))
    (augSlc : ∀ b ∈ K ++ [later], SLC Γ (K ++ [later]) b)
    (augBk : ∀ b ∈ K ++ [later], RBk Γ (K ++ [later]) b)
    (earlierMember : earlier ∈ K) (earlierInsert : mIsIns earlier = true)
    (laterInsert : mIsIns later = true)
    (sameAnchor : earlier.lo = later.lo)
    (rightExact : later.ro = succOfM Γ K later.lo) :
    Sal.EmbedRGA.keyLt (Sal.EmbedRGA.sKey (Sal.EmbedRGA.fmCoordOf Γ earlier.chain))
      (Sal.EmbedRGA.sKey (Sal.EmbedRGA.fmCoordOf Γ later.chain)) = true := by
  have minted : earlier.ts ∈ mMintedIds K :=
    List.mem_map.mpr ⟨earlier,List.mem_filter.mpr ⟨earlierMember,earlierInsert⟩,rfl⟩
  have after := record_after_left_origin inv sourceSlc earlierMember earlierInsert
  rw [sameAnchor] at after
  have candidate := cand_of_after minted (Or.inr after)
  have comparison : Sal.EmbedRGA.keyLt (mKey Γ K earlier.ts)
      (Sal.EmbedRGA.sKey (Sal.EmbedRGA.fmCoordOf Γ later.chain)) = true := by
    cases successor : succOfM Γ K later.lo with
    | none => exact False.elim (no_successor_no_candidate successor candidate)
    | some right =>
      exact issuer_successor_excludes_old inv augInv augSlc augBk laterInsert
        (rightExact.trans successor) successor candidate
  simpa [mKey,mChainOf_of_mem inv earlierMember earlierInsert] using comparison

theorem honest_causal_same_anchor_reverse_display {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis)
    (irrefl : ∀ e, ¬ C.vis e e)
    {earlier later : Op Payload} (earlierPresent : earlier ∈ C.events)
    (laterPresent : later ∈ C.events) (causal : C.vis earlier later)
    (earlierInsert : mIsIns (recordOf earlier) = true)
    (laterInsert : mIsIns (recordOf later) = true)
    (sameAnchor : earlier.op.lo = later.op.lo) :
    Sal.EmbedRGA.keyLt (Sal.EmbedRGA.sKey (Sal.EmbedRGA.fmCoordOf Γ earlier.op.chain))
      (Sal.EmbedRGA.sKey (Sal.EmbedRGA.fmCoordOf Γ later.op.chain)) = true := by
  obtain ⟨past,enumerates,_,issued⟩ := mint later laterPresent
  change List (Op Payload) at past
  have supported : ∀ e ∈ past, e ∈ C.events := fun e he => ((enumerates.2 e).mp he).1
  have closed : ∀ a b, C.vis a b → b ∈ past → a ∈ past := by
    intro a b ab member
    exact (enumerates.2 a).mpr ⟨C.vis_src ab,trans ab ((enumerates.2 b).mp member).2⟩
  obtain ⟨inv,slc,_⟩ := invariants_of_mint C mint trans irrefl past enumerates.1 supported closed
  have notPast : later ∉ past := fun he => irrefl later ((enumerates.2 later).mp he).2
  have augNodup : (past ++ [later]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨enumerates.1,by simp,?_⟩
    intro a ha b hb equal
    have same := List.mem_singleton.mp hb
    subst b
    exact notPast (same ▸ ha)
  have augSupported : ∀ e ∈ past ++ [later], e ∈ C.events := by
    intro e he
    rcases List.mem_append.mp he with old | new
    · exact supported e old
    · exact (List.mem_singleton.mp new).symm ▸ laterPresent
  have augClosed : ∀ a b, C.vis a b → b ∈ past ++ [later] → a ∈ past ++ [later] := by
    intro a b ab hb
    apply List.mem_append_left
    rcases List.mem_append.mp hb with old | new
    · exact closed a b ab old
    · have same := List.mem_singleton.mp new
      subst b
      exact (enumerates.2 a).mpr ⟨C.vis_src ab,ab⟩
  obtain ⟨augInv,augSlc,augBk⟩ := invariants_of_mint C mint trans irrefl (past ++ [later])
    augNodup augSupported augClosed
  simp only [List.map_append,List.map_singleton] at augInv augSlc augBk
  rw [rawFold_records] at issued
  have canIssue := (applicable_exact inv (recordOf later)).mp (by simpa using issued)
  obtain ⟨_,_,index,generated⟩ := (canIssue_insert_exact Γ (past.map recordOf)
    (recordOf later) laterInsert).mp canIssue
  have rightExact : (recordOf later).ro =
      succOfM Γ (past.map recordOf) (recordOf later).lo := by
    conv_lhs => rw [generated]
    conv_rhs => arg 3; rw [generated]
    exact generator_right_origin _ _ _ _ _
  have earlierMember : recordOf earlier ∈ past.map recordOf :=
    List.mem_map.mpr ⟨earlier,(enumerates.2 earlier).mpr ⟨earlierPresent,causal⟩,rfl⟩
  exact issuer_same_anchor_reverse_display inv slc augInv augSlc augBk earlierMember
    earlierInsert laterInsert sameAnchor rightExact

theorem record_left_lt {Γ : Sal.EmbedRGA.OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) {g : MRec} (member : g ∈ K) (inserted : mIsIns g = true) : g.lo < g.ts := by
  have minted : g.ts ∈ mMintedIds K :=
    List.mem_map.mpr ⟨g,List.mem_filter.mpr ⟨member,inserted⟩,rfl⟩
  have lt := FugueMaxOriginForest.parent_lt inv minted
  rw [mLoOf_eq (mRecOfId_of_mem inv member inserted)] at lt
  exact lt

theorem delete_before_own_birth_impossible {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis)
    (irrefl : ∀ e, ¬ C.vis e e)
    {birth deletion : Op Payload} (birthPresent : birth ∈ C.events)
    (deletePresent : deletion ∈ C.events) (positive : 0 < birth.time)
    (target : (recordOf deletion).op = .del birth.time) : ¬ C.vis deletion birth := by
  intro reverse
  rcases delete_birth_of_mint C mint trans deletion deletePresent birth.time target with
    zero | ⟨original,present,causal,_,same⟩
  · exact (Nat.ne_of_gt positive) zero
  · have equal := C.replayContext.ts_unique present birthPresent same
    subst original
    exact irrefl birth (trans causal reverse)

def ParentsFirst (a b : Op Payload) : Prop :=
  mIsIns (recordOf a) = true → mIsIns (recordOf b) = true → a.op.lo ≠ b.time

def SiblingsReverse (Γ : Sal.EmbedRGA.OrderedPrefixCode) (a b : Op Payload) : Prop :=
  mIsIns (recordOf a) = true → mIsIns (recordOf b) = true → a.op.lo = b.op.lo →
    Sal.EmbedRGA.keyLt (Sal.EmbedRGA.sKey (Sal.EmbedRGA.fmCoordOf Γ a.op.chain))
      (Sal.EmbedRGA.sKey (Sal.EmbedRGA.fmCoordOf Γ b.op.chain)) = true

def BirthsFirst (a b : Op Payload) : Prop :=
  mIsIns (recordOf a) = false → mIsIns (recordOf b) = false

theorem respects_projected_visibility {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (mint : MintHonest (datatype Γ) (applicable Γ) C) (trans : Transitive C.vis)
    (irrefl : ∀ e, ¬ C.vis e e) (π : List (Op Payload))
    (supported : ∀ e ∈ π, e ∈ C.events)
    (inv : KInv Γ (π.map recordOf))
    (parents : π.Pairwise ParentsFirst) (siblings : π.Pairwise (SiblingsReverse Γ))
    (births : π.Pairwise BirthsFirst) :
    respects π (projectedSpecVisibility (fun e => ofMessage (recordOf e)) spec C.replayContext) := by
  have combined := parents.and (siblings.and births)
  apply combined.imp_of_mem
  intro a b ha hb properties edge
  obtain ⟨parent,sibling,birthFirst⟩ := properties
  obtain ⟨causal,dependency⟩ := projected_visibility_requires_dependency C.replayContext edge
  cases ao : (recordOf a).op <;> cases bo : (recordOf b).op
  all_goals simp only [MayConflict,ao,bo] at dependency
  case ins.ins p side p' side' =>
    have aInsert : mIsIns (recordOf a) = true := by simp [mIsIns,ao]
    have bInsert : mIsIns (recordOf b) = true := by simp [mIsIns,bo]
    rcases dependency with sameID | sameAnchor | bParent | aParent
    · have equal := C.replayContext.ts_unique (supported b hb) (supported a ha) sameID
      subst b
      exact irrefl a causal
    · have ordered := sibling aInsert bInsert sameAnchor.symm
      have reversed := honest_causal_same_anchor_reverse_display C mint trans irrefl
        (supported b hb) (supported a ha) causal bInsert aInsert sameAnchor
      have impossible := Sal.EmbedRGA.keyLt_asymm ordered
      rw [reversed] at impossible
      contradiction
    · exact parent aInsert bInsert bParent.symm
    · have anchorLt := record_left_lt inv (List.mem_map.mpr ⟨b,hb,rfl⟩) bInsert
      have causalLt := C.causal_mono causal
      change b.time < a.time at causalLt
      change a.time = b.op.lo at aParent
      change b.op.lo < b.time at anchorLt
      rw [aParent] at causalLt
      exact Nat.lt_irrefl _ (Nat.lt_trans anchorLt causalLt)
  case ins.del p side target =>
    have positive := inv.pos (recordOf a) (List.mem_map.mpr ⟨a,ha,rfl⟩)
    apply delete_before_own_birth_impossible C mint trans irrefl (supported a ha) (supported b hb)
      (Nat.lt_of_lt_of_le (by decide : 0 < 1) positive) ?_ causal
    simpa [dependency] using bo
  case del.ins target p side =>
    have afterBirth := birthFirst (by simp [mIsIns,ao])
    simp [mIsIns,bo] at afterBirth

#print axioms noncommuting_requires_dependency
#print axioms honest_causal_same_anchor_reverse_display
#print axioms respects_projected_visibility
end Sal.MRDTs.Paper1.FugueMaxProjectedVisibility
