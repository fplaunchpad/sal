import CertifiedExpansion
import CertifiedReplayExpansion
import Sal.MRDTs.Paper1.CertifiedMVRVC

/-! Exact registered MVRLive route. The semantic representation and issuer
are unchanged. Generic finite record kernels consume overwrite coverage,
derived freshly from mint-time live-record provenance and the actual issuer's
image equality. No old datatype replay/VC/Join theorem is used. -/
namespace NeemExpansion.CertifiedMVR
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1
open Sal.MRDTs.Instances.MVRLive
open CertifiedQueueMVR.MVR.RawVC
open Classical
set_option maxHeartbeats 1500000

abbrev value := Sal.MRDTs.Instances.MVR.writeValue
abbrev targets := Sal.MRDTs.Instances.MVR.overwrites

def Born (e : Event) (p : Nat × Nat) : Prop := p = (e.1,value e)
def Killed (e : Event) (p : Nat × Nat) : Prop := p.1 ∈ targets e

theorem update_cell (s : State) (e : Event) (p : Nat × Nat) :
    p ∈ update s e ↔ Born e p ∨ (p ∈ s ∧ ¬Killed e p) := by
  simp [update,Sal.MRDTs.Instances.MVR.clientStep,Born,Killed]

theorem fold_provenance (xs : List Event) (p : Nat × Nat) :
    p ∈ xs.foldl update ∅ → ∃ e ∈ xs, Born e p := by
  apply CertifiedReplay.provenance update ∅ (fun p s => p ∈ s) Born (by simp)
  intro s e p hp
  exact ((update_cell s e p).mp hp).elim Or.inl (fun h => Or.inr h.1)

/-- Issuer overwrite targets are precisely current live identifiers. Each
such identifier has an actual birth in the enumerated mint-time causal past. -/
theorem issued_birth {C : Configuration D}
    (mint : MintHonest D issuance.CanIssue C) {e : Event} (eligible : e ∈ C.events)
    {n : Nat} (target : n ∈ targets e) :
    ∃ birth ∈ C.events, C.vis birth e ∧ birth.1 = n := by
  obtain ⟨xs,perm,_,guard⟩ := mint e eligible
  have ids := guard.2
  have member : n ∈ (targets e).toFinset := List.mem_toFinset.mpr target
  rw [ids] at member
  obtain ⟨p,hp,time⟩ := Finset.mem_image.mp member
  obtain ⟨birth,hbirth,record⟩ := fold_provenance xs p hp
  have past := (perm.2 birth).mp hbirth
  exact ⟨birth,past.1,past.2,(congrArg Prod.fst record).symm.trans time⟩

theorem overwrite_visible {C : Configuration D}
    (execution : CertifiedExecution D issuance C) {birth e : Event}
    (hb : birth ∈ C.events) (he : e ∈ C.events) (target : birth.1 ∈ targets e) :
    C.vis birth e := by
  obtain ⟨a,ha,vis,time⟩ := issued_birth execution.mintHonest he target
  have same := C.replayContext.ts_unique ha hb time
  exact same ▸ vis

theorem represented (C : ReplayContext D.toUpdateSig) (H : Set Event) (s : State)
    (rep : representation C H s) : Represents H s := by
  obtain ⟨_,_,_,_,_,semantic⟩ := rep
  exact semantic

theorem birth_fresh {C : Configuration D} {H : Set Event} {s : State} {e : Event}
    (support : H ⊆ C.events) (eligible : e ∈ C.events) (absent : e ∉ H)
    (rep : Represents H s) : ∀ p, Born e p → p ∉ s := by
  intro p birth mem
  obtain ⟨⟨a,ha,record⟩,_⟩ := (rep p).mp mem
  have stamp : a.1 = e.1 := congrArg (fun p : Nat × Nat => p.1) (record.trans birth)
  exact absent ((C.replayContext.ts_unique (support ha) eligible stamp) ▸ ha)

/-- Survival transfers to a smaller event history when its birth is present.
This unfolds the existing semantic representation, not a replay invariant. -/
theorem survive_subset {H K : Set Event} {s t : State}
    (sub : H ⊆ K) (hs : Represents H s) (ht : Represents K t)
    (p : Nat × Nat) (live : p ∈ t)
    (birth : ∃e∈H,(e.1,value e)=p) : p ∈ s := by
  apply (hs p).mpr
  refine ⟨birth,?_⟩
  rintro ⟨e,he,dead⟩
  exact ((ht p).mp live).2 ⟨e,sub he,dead⟩

theorem expanded_vcs : ConcreteMRDT.Raw.MergeVCs policy representation scheme := by
  constructor
  · intro C E₁ E₂ l a b _ _ _ _ _ _ _
    exact Certified.comm l a b
  · intro C H s _ _ _
    exact Certified.initial s
  · intro C U s B e trans irrefl supported closed member semantic metadata hs hB hD hu
    obtain ⟨K,execution,eq,support,_,_⟩ := hu
    subst C
    have pastSub := (scheme K.replayContext).past_subset U e closed member
    have repS := represented _ _ _ hs
    have repB := represented _ _ _ hB
    apply Certified.causal B s (update B e) (update s e) (Born e) (Killed e)
    · constructor
      · exact birth_fresh (fun x hx => support (pastSub hx.1)) (support member)
          (fun h => h.2 rfl) repB
      · intro p live killed
        obtain ⟨⟨birth,hbirth,record⟩,_⟩ := (repS p).mp live
        have target : birth.1 ∈ targets e := by
          rw [show birth.1 = p.1 from congrArg Prod.fst record]
          exact killed
        have vis := overwrite_visible execution (support hbirth.1) (support member) target
        have birthPast : birth ∈ (scheme K.replayContext).Past e \ {e} :=
          ⟨Or.inr (.single vis),hbirth.2⟩
        exact survive_subset (show (scheme K.replayContext).Past e \ {e} ⊆ U \ {e} from fun x hx => ⟨pastSub hx.1,hx.2⟩) repB repS p live
          ⟨birth,birthPast,record⟩
    · exact update_cell B e
    · exact update_cell s e
  · intro C E₁ E₂ l B t b e ctx member absent hl hB ht hb hD hi hm
    obtain ⟨K,execution,eq,_,_,_⟩ := hi
    subst C
    have support₁ : E₁ ⊆ K.events := by simpa using ctx.supported₁
    have support₂ : E₂ ⊆ K.events := by simpa using ctx.supported₂
    have pastSub := (scheme K.replayContext).past_subset E₁ e ctx.closed₁ member
    have repL := represented _ _ _ hl
    have repB := represented _ _ _ hB
    have repOther := represented _ _ _ hb
    apply Certified.local_redistribute l B t b (update B e)
    constructor
    · intro p inPast _ inOther
      obtain ⟨⟨a,ha,recordA⟩,_⟩ := (repB p).mp inPast
      obtain ⟨⟨c,hc,recordC⟩,_⟩ := (repOther p).mp inOther
      have same := K.replayContext.ts_unique (support₁ (pastSub ha.1)) (support₂ hc)
        (congrArg (fun p : Nat × Nat => p.1) (recordA.trans recordC.symm))
      have common : a ∈ E₁ ∩ E₂ := ⟨pastSub ha.1,same ▸ hc⟩
      exact survive_subset Set.inter_subset_right repL repOther p inOther ⟨a,common,recordA⟩
    · intro p notPast updated
      have birth := ((update_cell B e p).mp updated).resolve_right (fun h => notPast h.1)
      exact birth_fresh (fun x hx => support₁ hx.1) (support₁ member)
        (fun h => absent h.2) repL p birth
  · intro C E₁ E₂ t₀ t₁ t₂ B e ctx member₁ member₂ h₀ hB h₁ h₂ hD hi₀ hi₁ hi₂ hm
    exact Certified.shared t₀ t₁ t₂ B (update B e)

#print axioms expanded_vcs
end NeemExpansion.CertifiedMVR
