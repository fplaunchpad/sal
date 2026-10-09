import Sal.MRDTs.Paper1.Automation.CommonVerification
import Sal.MRDTs.Paper1.Automation.GenericArchivedOrderedRecords
import Sal.MRDTs.Paper1.Automation.GenericCertifiedIssuance
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
    all_goals (ordered_record_simp; tauto)
  · simp only [List.mem_filter]; tauto

def kit (Γ : OrderedPrefixCode) : ArchivedOrderedRecords.Kit (datatype Γ) SRec MRec where
  archive := State.births
  archive_written := recordOf
  archive_add := insertion
  archive_init := rfl
  archive_update := by intros; rfl
  archive_merge := by intros; rfl
  carrier := fun s=>s.live.toFinset
  id := Prod.fst
  Key := List Nat
  key := fun p=>sKey p.2.2
  insertion := insertion
  written := written Γ
  target := target
  ordered := fun s=>SSorted s.live
  init_carrier := rfl
  init_ordered := List.Pairwise.nil
  written_id := fun _=>rfl
  update_provenance := by
    intro s e p hp
    simpa only [List.mem_toFinset] using provenance_step Γ s e p (List.mem_toFinset.mp hp)
  update_mem := by
    intro s e fresh p
    have absent : e.1∉sIds s.live := by
      intro h; obtain ⟨q,hq,id⟩ := List.mem_map.mp h
      exact fresh q (List.mem_toFinset.mpr hq) id
    rcases e with ⟨t,r,⟨op,lo,ro,ch⟩⟩
    cases op <;> simp [datatype,rawUpdate,mStep,recordOf,absent,insertion,written,target,mIsIns]
    all_goals (ordered_record_simp; tauto)
  update_ordered := by
    intro s e hs keys
    rcases e with ⟨t,r,⟨op,lo,ro,ch⟩⟩
    cases op with
    | ins a sd =>
      change SSorted (if t∈sIds s.live then s.live else sInsert _ s.live)
      split
      · exact hs
      · ordered_record
    | del n => exact List.Pairwise.filter _ hs
  birth_not_killed := by
    rintro ⟨t,r,⟨op,lo,ro,ch⟩⟩ ins
    cases op <;> simp_all [insertion,target,mIsIns,recordOf,written]
  merge_mem := by
    intro l a b al bl ab ba p
    have coherent : ∀(s t:List SRec),
        (∀x∈s,∀y∈t,x.1=y.1→x=y) → ∀p∈s,p.1∈sIds t ↔ p∈t := by
      intro s t eq p hp
      constructor
      · intro h; obtain ⟨q,hq,id⟩ := List.mem_map.mp h
        exact eq p hp q hq id.symm ▸ hq
      · intro h; exact List.mem_map.mpr ⟨p,h,rfl⟩
    have al' := fun hp=>coherent a.live l.live (fun x hx y hy=>al x (List.mem_toFinset.mpr hx) y (List.mem_toFinset.mpr hy)) p hp
    have bl' := fun hp=>coherent b.live l.live (fun x hx y hy=>bl x (List.mem_toFinset.mpr hx) y (List.mem_toFinset.mpr hy)) p hp
    have ab' := fun hp=>coherent a.live b.live (fun x hx y hy=>ab x (List.mem_toFinset.mpr hx) y (List.mem_toFinset.mpr hy)) p hp
    have ba' := fun hp=>coherent b.live a.live (fun x hx y hy=>ba x (List.mem_toFinset.mpr hx) y (List.mem_toFinset.mpr hy)) p hp
    simp only [datatype,rawMerge,sMerge,Certified.cell,List.mem_toFinset]
    ordered_record_simp
    tauto
  merge_ordered := by
    intro l a b ha hb coherent
    change SSorted (sMerge l.live a.live b.live)
    ordered_record
  ext := by
    intro s t hs ht same archive
    have live : s.live=t.live := by ordered_record
    cases s; cases t; cases live; cases archive; rfl

def ChainFacts (g : MRec) : Prop :=
  0<g.ts ∧ (mIsIns g=true → PosFMChain g.chain ∧ TagsOK g.chain ∧ (g.chain.map fmδ).sum=g.ts)

theorem lookup_chain (K : KnowM) (facts : ∀g∈K, ChainFacts g)
    (x : ℕ) (hx : x=0 ∨ x∈mMintedIds K) :
    PosFMChain (mChainOf K x) ∧ TagsOK (mChainOf K x) ∧
      ((mChainOf K x).map fmδ).sum = x := by
  rcases hx with rfl | hx
  · rw [mChainOf_zero (fun g hg => Nat.succ_le_of_lt (facts g hg).1)]
    exact ⟨by simp [PosFMChain],by simp [TagsOK],rfl⟩
  · obtain ⟨g,lookup,mem,ins,time⟩ := mRecOfId_of_minted hx
    rw [mChainOf_eq_of_rec lookup,←time]
    exact (facts g mem).2 ins

theorem generated_chain (Γ : OrderedPrefixCode) (K : KnowM)
    (facts : ∀g∈K, ChainFacts g) (rep t a : ℕ) (positive : 0<t)
    (newer : ∀g∈K,g.ts<t) (anchor : a=0 ∨ a∈mMintedIds K) :
    ChainFacts (mGenInsAfter Γ K rep t a) := by
  have late : ∀x∈mMintedIds K,x<t := by
    intro x hx
    obtain ⟨g,_,mem,_,time⟩ := mRecOfId_of_minted hx
    rw [←time]; exact newer g mem
  have alt : a<t := anchor.elim (fun h => h ▸ positive) (late a)
  have wa := lookup_chain K facts a anchor
  cases hs : succOfM Γ K a with
  | none =>
    rw [mGenInsAfter_none hs]
    refine ⟨positive,fun _ => ⟨?_,?_,?_⟩⟩
    · intro ent he
      rcases List.mem_append.mp he with he | he
      · exact wa.1 ent he
      · simp only [List.mem_singleton] at he; subst ent
        change 1≤t-a; omega
    · intro ent he
      rcases List.mem_append.mp he with he | he
      · exact wa.2.1 ent he
      · simp only [List.mem_singleton] at he; subst ent
        exact Or.inl rfl
    · simp only [List.map_append,List.sum_append,wa.2.2,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      change a+(t-a+0)=t; omega
  | some n =>
    have hn := succOfM_mem hs
    have wn := lookup_chain K facts n (Or.inr hn)
    have nlt := late n hn
    have npos : 0<n := by
      obtain ⟨g,_,mem,_,time⟩ := mRecOfId_of_minted hn
      rw [←time]; exact (facts g mem).1
    cases hr : hasRChildM K a with
    | true =>
      rw [mGenInsAfter_someTrue hs hr]
      refine ⟨positive,fun _ => ⟨?_,?_,?_⟩⟩
      · intro ent he
        rcases List.mem_append.mp he with he | he
        · exact wn.1 ent he
        · simp only [List.mem_singleton] at he; subst ent
          change 1≤t-n; omega
      · intro ent he
        rcases List.mem_append.mp he with he | he
        · exact wn.2.1 ent he
        · simp only [List.mem_singleton] at he; subst ent; exact trivial
      · simp only [List.map_append,List.sum_append,wn.2.2,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
        change n+(t-n+0)=t; omega
    | false =>
      rw [mGenInsAfter_someFalse hs hr]
      refine ⟨positive,fun _ => ⟨?_,?_,?_⟩⟩
      · intro ent he
        rcases List.mem_append.mp he with he | he
        · exact wa.1 ent he
        · simp only [List.mem_singleton] at he; subst ent
          change 1≤t-a; omega
      · intro ent he
        rcases List.mem_append.mp he with he | he
        · exact wa.2.1 ent he
        · simp only [List.mem_singleton] at he; subst ent
          apply tagOK_key Γ wn.1 wn.2.1
          intro empty
          simp [empty] at wn
          omega
      · simp only [List.map_append,List.sum_append,wa.2.2,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
        change a+(t-a+0)=t; omega

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
  live_step := by
    intro s e p hp
    simpa only [List.mem_toFinset] using provenance_step Γ s e p (List.mem_toFinset.mp hp)
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
    · obtain ⟨positive,newer,i,shape⟩ := (canIssue_insert_iff Γ _ _ ins).mp issued
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
      obtain ⟨positive,_,_⟩ := (canIssue_delete_iff Γ _ _ no).mp issued
      exact ⟨positive,fun h=>False.elim (ins h)⟩
  issue_target := by
    intro s e issued n shape
    obtain ⟨K,_,issued⟩ := issued
    by_cases zero:n=0
    · exact Or.inl zero
    right
    have no : mIsIns (recordOf e)=false := by simp [mIsIns,recordOf,target] at shape ⊢; rw [shape]
    obtain ⟨_,i,eq⟩ := (canIssue_delete_iff Γ _ _ no).mp issued
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
  · intro d hd n born kill
    rcases CertifiedIssuance.target_of_mint (issuanceModel Γ) K mint d hd n kill with zero | creator
    · obtain ⟨e,he,ins,stamp⟩ := born
      have positive := (valid e he).1
      exact False.elim ((Nat.ne_of_gt positive) (stamp.trans zero))
    · exact creator
  · apply ArchivedOrderedRecords.ChainCertificate.key_unique (Chain:=List FMEntry)
    refine ⟨fun c=>PosFMChain c ∧ TagsOK c,fun c=>sKey (fmCoordOf Γ c),fun c=>(c.map fmδ).sum,?_,?_⟩
    · intro a b va vb eq
      exact fmCoordOf_inj Γ va.1 vb.1 va.2 vb.2 (sKey_inj eq)
    · intro e he ins
      obtain ⟨positive,tags,sum⟩ := (valid e he).2 ins
      exact ⟨e.2.2.chain,⟨positive,tags⟩,rfl,sum⟩

def adapter (Γ : OrderedPrefixCode) (C : ReplayContext (datatype Γ).toUpdateSig)
    (H : Set (Op Payload)) (s : State) (rep : representation Γ C H s) :
    ArchivedOrderedRecords.IssuerEvidence (kit Γ) C ∧ ArchivedOrderedRecords.ReplayEvidence C H s :=
  ⟨issuer Γ C rep.1,rep.2.2.2.1,rep.2.2.2.2⟩

def input (Γ : OrderedPrefixCode) : CommonVerification.Input (datatype Γ)
    policy (representation Γ) (scheme Γ) :=
  .archived (kit Γ) (fun _ _ _=>Iff.rfl) (adapter Γ)
register_mrdt_input input

theorem automated_vcs (Γ : OrderedPrefixCode) : ConcreteMRDT.Raw.MergeVCs
    policy (representation Γ) (scheme Γ) := by mrdt_verify
#print axioms automated_vcs
end Sal.MRDTs.Paper1.Automation.AutomatedFugue
