import Sal.MRDTs.Paper1.Automation.ArchivedInputDerivation
import Sal.MRDTs.Paper1.Automation.ArchivedKitAutomation
import Sal.MRDTs.Paper1.Automation.GenericIssuanceAdapters
import Sal.MRDTs.Paper1.Automation.FiniteLookupAutomation
import Sal.MRDTs.Paper1.Automation.FugueCodePrimitives
import Sal.MRDTs.Paper1.Automation.OrderedRecordAutomation
import Sal.MRDTs.Paper1.CertifiedFugueVCReplay

namespace Sal.MRDTs.Paper1.Automation.AutomatedFugue
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1 Sal.EmbedRGA
open Instances.SidedEmbedRGA Instances.SidedEmbedRGA.FugueMax
open CertifiedFugueVCReplay
set_option maxHeartbeats 4000000

def insertion (e : Op Payload) := mIsIns (recordOf e)
def written (Γ : OrderedPrefixCode) (e : Op Payload) : SRec := (e.1,e.1,fmCoordOf Γ e.2.2.chain)
def target (e : Op Payload) (n : Nat) := e.2.2.op=.del n

theorem provenance_step (Γ : OrderedPrefixCode) (s : State) (e : Op Payload) (p : SRec) :
    p∈(rawUpdate Γ s e).live → (insertion e=true ∧ p=written Γ e) ∨ p∈s.live := by
  rcases e with ⟨t,r,⟨op,lo,ro,ch⟩⟩
  cases op <;> simp only [rawUpdate,mStep,recordOf]
  · split <;> simp_all [insertion,written,mIsIns,recordOf]
    all_goals (ordered_generic_simp; tauto)
  · simp only [List.mem_filter]; tauto

def description (Γ : OrderedPrefixCode) : ArchivedOrderedRecords.Description (datatype Γ) SRec MRec where
  live := State.live
  archive := State.births
  archive_written := recordOf
  insertion := insertion
  id := Prod.fst
  Key := List Nat
  key := fun p=>sKey p.2.2
  lt := fun p q=>keyLt (sKey p.2.2) (sKey q.2.2)
  written := written Γ
  target := target

def equations (Γ : OrderedPrefixCode) : ArchivedOrderedRecords.Equations (description Γ) where
  order := SidedPrimitives.order
  initial_live := rfl
  initial_archive := rfl
  update_live := by
    rintro s ⟨t,r,⟨op,lo,ro,ch⟩⟩
    cases op <;> simp [description,ArchivedOrderedRecords.updateList,datatype,rawUpdate,mStep,
      recordOf,insertion,written,target,mIsIns,SidedPrimitives.insertion,sIds,eq_comm]
  merge_live := by intros; simp [description,ArchivedOrderedRecords.mergeList,datatype,rawMerge,sMerge,
    SidedPrimitives.merging,sIds]
  update_archive := by intros; rfl
  merge_archive := by intros; rfl
  written_id := fun _=>rfl
  insertion_not_killed := by
    rintro ⟨t,r,⟨op,lo,ro,ch⟩⟩ ins n
    cases op <;> simp_all [description,insertion,target,mIsIns,recordOf]
  ext := by
    intro s t live archive
    cases s; cases t; cases live; cases archive; rfl

def kit (Γ : OrderedPrefixCode) : ArchivedOrderedRecords.Kit (datatype Γ) SRec MRec :=
  (equations Γ).kit (description Γ)

def ChainFacts (g : MRec) : Prop :=
  0<g.ts ∧ (mIsIns g=true → PosFMChain g.chain ∧ TagsOK g.chain ∧ (g.chain.map fmδ).sum=g.ts)

theorem lookup_chain (K : KnowM) (facts : ∀g∈K, ChainFacts g)
    (x : ℕ) (hx : x=0 ∨ x∈mMintedIds K) :
    PosFMChain (mChainOf K x) ∧ TagsOK (mChainOf K x) ∧
      ((mChainOf K x).map fmδ).sum = x := by
  rcases hx with rfl | hx
  · simp only [mChainOf,mRecOfId,mMinted]
    rw [FiniteLookup.zero_lookup K mIsIns MRec.ts MRec.chain [] (fun g hg=>(facts g hg).1)]
    exact ⟨by simp [PosFMChain],by simp [TagsOK],rfl⟩
  · obtain ⟨g,lookup,mem,ins,time⟩ := FiniteLookup.marked_lookup K mIsIns MRec.ts x hx
    simp only [mChainOf,mRecOfId,mMinted,lookup,Option.map_some,Option.getD_some]
    rw [←time]
    exact (facts g mem).2 ins

theorem generated_chain (Γ : OrderedPrefixCode) (K : KnowM)
    (facts : ∀g∈K, ChainFacts g) (rep t a : ℕ) (positive : 0<t)
    (newer : ∀g∈K,g.ts<t) (anchor : a=0 ∨ a∈mMintedIds K) :
    ChainFacts (mGenInsAfter Γ K rep t a) := by
  have late : ∀x∈mMintedIds K,x<t := by
    intro x hx
    obtain ⟨g,_,mem,_,time⟩ := FiniteLookup.marked_lookup K mIsIns MRec.ts x hx
    rw [←time]; exact newer g mem
  have alt : a<t := anchor.elim (fun h => h ▸ positive) (late a)
  have wa := lookup_chain K facts a anchor
  cases hs : succOfM Γ K a with
  | none =>
    simp only [mGenInsAfter,hs]
    refine ⟨positive,fun _ => ?_⟩
    exact append_delta_valid fmδ fmTagOK _ a t _ wa.1 wa.2.1 wa.2.2 alt rfl (Or.inl rfl)
  | some n =>
    have hn : n∈mMintedIds K := by
      obtain ⟨p,hp,id⟩ := FiniteLookup.selected_id maxKey
        (by intro acc p
            cases acc with
            | none => simp [maxKey]
            | some b => by_cases h:keyLt b.2 p.2=true <;> simp [maxKey,h]) _ Prod.fst n hs
      have mem : p∈mKeys Γ K := by
        unfold succCandM at hp
        split at hp
        · exact hp
        · exact List.mem_of_mem_filter hp
      obtain ⟨x,hx,eq⟩ := List.mem_map.mp mem
      subst p
      exact id ▸ hx
    have wn := lookup_chain K facts n (Or.inr hn)
    have nlt := late n hn
    have npos : 0<n := by
      obtain ⟨g,_,mem,_,time⟩ := FiniteLookup.marked_lookup K mIsIns MRec.ts n hn
      rw [←time]; exact (facts g mem).1
    cases hr : hasRChildM K a with
    | true =>
      simp only [mGenInsAfter,hs,hr]
      refine ⟨positive,fun _ => ?_⟩
      exact append_delta_valid fmδ fmTagOK _ n t _ wn.1 wn.2.1 wn.2.2 nlt rfl trivial
    | false =>
      simp only [mGenInsAfter,hs,hr]
      refine ⟨positive,fun _ => ?_⟩
      apply append_delta_valid fmδ fmTagOK _ a t _ wa.1 wa.2.1 wa.2.2 alt rfl
      apply FugueCodes.key_tag Γ wn.1 wn.2.1
      intro empty
      simp [empty] at wn
      omega

def issuanceModel (Γ : OrderedPrefixCode) : CertifiedIssuance.Model (datatype Γ) MRec SRec where
  archive := State.births
  live := fun s=>s.live.toFinset
  record := recordOf
  written := written Γ
  insertion := insertion
  marked := mIsIns
  stamp := MRec.ts
  id := Prod.fst
  valid := ChainFacts
  guard := applicable Γ
  target := target
  initial_archive := rfl
  initial_live := rfl
  archive_step := by
    intro s e g
    simp only [datatype,rawUpdate]
    cases hi : mIsIns (recordOf e) <;> simp [hi,insertion,eq_comm]
  live_step := (kit Γ).update_provenance
  record_stamp := fun _=>rfl
  record_marked := fun _=>rfl
  written_id := fun _=>rfl
  issue_valid := by
    intro s e issued facts linked
    obtain ⟨K,Kset,issued⟩ := issued
    have table : ∀g∈K,ChainFacts g := by
      intro g hg; apply facts g; rw [←Kset]; exact List.mem_toFinset.mpr hg
    have liveAnchor : ∀a∈sIds s.live,a∈mMintedIds K := by
      intro a ha
      obtain ⟨p,hp,id⟩ := List.mem_map.mp ha
      obtain ⟨g,hg,ins,stamp⟩ := linked p (List.mem_toFinset.mpr hp)
      have mem : g∈K := by apply List.mem_toFinset.mp; rw [Kset]; exact hg
      exact List.mem_map.mpr ⟨g,List.mem_filter.mpr ⟨mem,ins⟩,stamp.trans id⟩
    by_cases ins : mIsIns (recordOf e)=true
    · simp only [canIssue,ins,if_true,Bool.and_eq_true,decide_eq_true_eq,
        List.all_eq_true,List.any_eq_true,List.mem_range] at issued
      obtain ⟨positive,newer,i,_,shape⟩ := issued
      rw [shape]
      apply generated_chain Γ K table _ _ _ positive newer
      by_cases iz : i=0
      · simp [iz]
      · simp only [if_neg iz]
        by_cases bound : i-1<(sIds s.live).length
        · right; apply liveAnchor
          rw [List.getD_eq_getElem _ _ bound]; exact List.getElem_mem bound
        · left; exact List.getD_eq_default _ _ (Nat.le_of_not_lt bound)
    · have no : mIsIns (recordOf e)=false := by cases h:mIsIns (recordOf e) <;> simp_all
      simp only [canIssue,no,Bool.false_eq_true,if_false,Bool.and_eq_true,
        decide_eq_true_eq,List.any_eq_true,List.mem_range] at issued
      obtain ⟨positive,_,_,_⟩ := issued
      exact ⟨positive,fun h=>False.elim (ins h)⟩
  issue_target := by
    intro s e issued n shape
    obtain ⟨K,_,issued⟩ := issued
    by_cases zero:n=0
    · exact Or.inl zero
    right
    have no : mIsIns (recordOf e)=false := by simp [mIsIns,recordOf,target] at shape ⊢; rw [shape]
    simp only [canIssue,no,Bool.false_eq_true,if_false,Bool.and_eq_true,
      decide_eq_true_eq,List.any_eq_true,List.mem_range] at issued
    obtain ⟨_,i,_,eq⟩ := issued
    have index : n=(sIds s.live).getD i 0 := by
      have h := congrArg MRec.op eq
      change e.2.2.op=.del _ at h
      rw [shape] at h
      exact MOp.del.inj h
    have member : n∈sIds s.live := by
      by_cases bound:i<(sIds s.live).length
      · rw [List.getD_eq_getElem _ _ bound] at index
        rw [index]; exact List.getElem_mem bound
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt bound)] at index
        exact False.elim (zero index)
    obtain ⟨p,hp,id⟩ := List.mem_map.mp member
    exact ⟨p,List.mem_toFinset.mpr hp,id⟩

def issuer (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (honest : ∃K:Configuration (datatype Γ),MintHonest (datatype Γ) (applicable Γ) K ∧ K.replayContext=C) :
    ArchivedOrderedRecords.IssuerEvidence (kit Γ) C := by
  obtain ⟨K,mint,rfl⟩ := honest
  have valid := CertifiedIssuance.valid_of_mint (issuanceModel Γ) K mint
  refine ⟨?_,?_⟩
  · exact CertifiedIssuance.creator_of_mint (issuanceModel Γ) (fun _ h=>h.1) K mint
  · apply ArchivedOrderedRecords.ChainCertificate.key_unique (Chain:=List FMEntry)
    refine ⟨fun c=>PosFMChain c ∧ TagsOK c,fun c=>sKey (fmCoordOf Γ c),fun c=>(c.map fmδ).sum,?_,?_⟩
    · intro a b va vb eq
      exact FugueCodes.coordinate_injective Γ va.1 vb.1 va.2 vb.2 (List.append_inj_left' eq (by simp))
    · intro e he ins
      obtain ⟨positive,tags,sum⟩ := (valid e he).2 ins
      exact ⟨e.2.2.chain,⟨positive,tags⟩,rfl,sum⟩

def adapter (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (H : Set (Op Payload)) (s : State) (rep : representation Γ C H s) :
    ArchivedOrderedRecords.IssuerEvidence (kit Γ) C ∧ ArchivedOrderedRecords.ReplayEvidence C H s := by
  derive_archived_adapter rep with (issuer Γ C) unfolding [representation]

def input (Γ : OrderedPrefixCode) : CommonVerification.Input (datatype Γ)
    policy (representation Γ) (scheme Γ) := by
  derive_archived_input (kit Γ) with (issuer Γ) unfolding [representation]
register_mrdt_input input

theorem automated_vcs (Γ : OrderedPrefixCode) : ConcreteMRDT.Raw.MergeVCs
    policy (representation Γ) (scheme Γ) := by mrdt_verify
#print axioms automated_vcs
end Sal.MRDTs.Paper1.Automation.AutomatedFugue
