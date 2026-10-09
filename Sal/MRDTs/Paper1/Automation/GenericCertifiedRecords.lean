import Sal.MRDTs.Paper1.Automation.CertifiedExpansion
import Sal.MRDTs.Paper1.Automation.CertifiedReplayExpansion
import Sal.MRDTs.Paper1.ConcreteJoin

/-! A parametric immutable-record template. Its implementation interface has
only fixed one-state, one-event and one-merge obligations. History provenance,
issuer-to-causality reasoning, semantic representation transport and all five
VCs are internal checked template theorems. -/
namespace Sal.MRDTs.Paper1.Automation.GenericCertifiedRecords
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1
open Classical

structure Model (D : MRDTSig) (I : Issuance D) (Record : Type) [DecidableEq Record] where
  carrier : D.State → Finset Record
  written : Op D.AppOp → Record
  tag : Record → Nat
  target : Op D.AppOp → Nat → Prop
  carrier_injective : Function.Injective carrier
  empty : carrier D.init = ∅
  written_tag : ∀ e, tag (written e) = e.1
  update_cell : ∀ s e p, p ∈ carrier (D.update s e) ↔
    p = written e ∨ (p ∈ carrier s ∧ ¬target e (tag p))
  merge_cell : ∀ l a b, carrier (D.merge l a b) =
    Certified.merge (carrier l) (carrier a) (carrier b)
  issuer_cell : ∀ e s, I.CanIssue e s → ∀ n, target e n →
    ∃ p ∈ carrier s, tag p = n

variable {D : MRDTSig} {I : Issuance D} {Record : Type} [DecidableEq Record]

namespace Model

def Semantic (M : Model D I Record) (H : Set (Op D.AppOp)) (s : D.State) : Prop :=
  ∀ p, p ∈ M.carrier s ↔ (∃ e ∈ H, M.written e = p) ∧
    ¬∃ e ∈ H, M.target e (M.tag p)

def Representation (M : Model D I Record) : ConcreteMRDT.Representation D :=
  fun context H s => ∃ C : Configuration D, CertifiedExecution D I C ∧
    C.replayContext = context ∧ H ⊆ C.events ∧ H.Finite ∧ M.Semantic H s

theorem provenance (M : Model D I Record) (xs : List (Op D.AppOp)) (p : Record) :
    p ∈ M.carrier (xs.foldl D.update D.init) → ∃ e ∈ xs, p = M.written e := by
  apply CertifiedReplay.provenance D.update D.init (fun p s => p ∈ M.carrier s)
    (fun e p => p = M.written e) (by simp [M.empty])
  intro s e p hp
  exact ((M.update_cell s e p).mp hp).elim Or.inl (fun h => Or.inr h.1)

theorem issued_birth (M : Model D I Record) {C : Configuration D}
    (mint : MintHonest D I.CanIssue C) {e : Op D.AppOp} (eligible : e ∈ C.events)
    {n : Nat} (target : M.target e n) :
    ∃ birth ∈ C.events, C.vis birth e ∧ birth.1 = n := by
  obtain ⟨xs,perm,_,guard⟩ := mint e eligible
  obtain ⟨p,hp,time⟩ := M.issuer_cell e _ guard n target
  obtain ⟨birth,hbirth,record⟩ := M.provenance xs p hp
  have past := (perm.2 birth).mp hbirth
  refine ⟨birth,past.1,past.2,?_⟩
  rw [record,M.written_tag] at time
  exact time

theorem target_visible (M : Model D I Record) {C : Configuration D}
    (execution : CertifiedExecution D I C) {birth e : Op D.AppOp}
    (hb : birth ∈ C.events) (he : e ∈ C.events) (target : M.target e birth.1) :
    C.vis birth e := by
  obtain ⟨a,ha,vis,time⟩ := M.issued_birth execution.mintHonest he target
  have same := C.replayContext.ts_unique ha hb time
  exact same ▸ vis

theorem represented (M : Model D I Record) (C : ReplayContext D.toUpdateSig)
    (H : Set (Op D.AppOp)) (s : D.State) (rep : M.Representation C H s) : M.Semantic H s := by
  obtain ⟨_,_,_,_,_,semantic⟩ := rep
  exact semantic

theorem birth_fresh (M : Model D I Record) {C : Configuration D}
    {H : Set (Op D.AppOp)} {s : D.State} {e : Op D.AppOp}
    (support : H ⊆ C.events) (eligible : e ∈ C.events) (absent : e ∉ H)
    (rep : M.Semantic H s) : ∀ p, p = M.written e → p ∉ M.carrier s := by
  intro p birth mem
  obtain ⟨⟨a,ha,record⟩,_⟩ := (rep p).mp mem
  have stamp : a.1 = e.1 := by
    have tags := congrArg M.tag (record.trans birth)
    simpa only [M.written_tag] using tags
  exact absent ((C.replayContext.ts_unique (support ha) eligible stamp) ▸ ha)

theorem survive_subset (M : Model D I Record) {H K : Set (Op D.AppOp)} {s t : D.State}
    (sub : H ⊆ K) (hs : M.Semantic H s) (ht : M.Semantic K t)
    (p : Record) (live : p ∈ M.carrier t) (birth : ∃ e ∈ H, M.written e = p) :
    p ∈ M.carrier s := by
  apply (hs p).mpr
  refine ⟨birth,?_⟩
  rintro ⟨e,he,dead⟩
  exact ((ht p).mp live).2 ⟨e,sub he,dead⟩

/-- No state/history invariant or desired merge equation is an input. The
scheme uses visibility as its metadata dependency, checked definitionally by
an instance. The operation policy remains arbitrary and unchanged. -/
theorem five_vcs (M : Model D I Record) (policy : OperationPolicy D.AppOp)
    (scheme : ∀ C : ReplayContext D.toUpdateSig, ConcreteMRDT.MetadataDependencies C)
    (metadata_cell : ∀ C a b, (scheme C).before a b ↔ C.vis a b) :
    ConcreteMRDT.Raw.MergeVCs policy M.Representation scheme := by
  constructor
  · intro C E₁ E₂ l a b _ _ _ _ _ _ _
    apply M.carrier_injective
    rw [M.merge_cell,M.merge_cell]
    exact Certified.comm _ _ _
  · intro C H s _ _ _
    apply M.carrier_injective
    rw [M.merge_cell,M.empty]
    exact Certified.initial _
  · intro C U s B e trans irrefl supported closed member semantic metadata hs hB hD hu
    obtain ⟨K,execution,eq,support,_,_⟩ := hu
    subst C
    have pastSub := (scheme K.replayContext).past_subset U e closed member
    have repS := M.represented _ _ _ hs
    have repB := M.represented _ _ _ hB
    apply M.carrier_injective
    rw [M.merge_cell]
    apply Certified.causal (M.carrier B) (M.carrier s)
      (M.carrier (D.update B e)) (M.carrier (D.update s e))
      (fun p => p = M.written e) (fun p => M.target e (M.tag p))
    · constructor
      · exact M.birth_fresh (fun x hx => support (pastSub hx.1)) (support member)
          (fun h => h.2 rfl) repB
      · intro p live killed
        obtain ⟨⟨birth,hbirth,record⟩,_⟩ := (repS p).mp live
        have target : M.target e birth.1 := by
          rw [← M.written_tag birth,record]
          exact killed
        have vis := M.target_visible execution (support hbirth.1) (support member) target
        have birthPast : birth ∈ (scheme K.replayContext).Past e \ {e} :=
          ⟨Or.inr (.single ((metadata_cell _ _ _).mpr vis)),hbirth.2⟩
        exact M.survive_subset
          (show (scheme K.replayContext).Past e \ {e} ⊆ U \ {e} from
            fun x hx => ⟨pastSub hx.1,hx.2⟩) repB repS p live ⟨birth,birthPast,record⟩
    · exact M.update_cell B e
    · exact M.update_cell s e
  · intro C E₁ E₂ l B t b e ctx member absent hl hB ht hb hD hi hm
    obtain ⟨K,execution,eq,_,_,_⟩ := hi
    subst C
    have support₁ : E₁ ⊆ K.events := by simpa using ctx.supported₁
    have support₂ : E₂ ⊆ K.events := by simpa using ctx.supported₂
    have pastSub := (scheme K.replayContext).past_subset E₁ e ctx.closed₁ member
    have repL := M.represented _ _ _ hl
    have repB := M.represented _ _ _ hB
    have repOther := M.represented _ _ _ hb
    apply M.carrier_injective
    rw [M.merge_cell,M.merge_cell,M.merge_cell,M.merge_cell]
    apply Certified.local_redistribute
    constructor
    · intro p inPast _ inOther
      obtain ⟨⟨a,ha,recordA⟩,_⟩ := (repB p).mp inPast
      obtain ⟨⟨c,hc,recordC⟩,_⟩ := (repOther p).mp inOther
      have tags : a.1 = c.1 := by
        have h := congrArg M.tag (recordA.trans recordC.symm)
        simpa only [M.written_tag] using h
      have same := K.replayContext.ts_unique (support₁ (pastSub ha.1)) (support₂ hc) tags
      have common : a ∈ E₁ ∩ E₂ := ⟨pastSub ha.1,same ▸ hc⟩
      exact M.survive_subset Set.inter_subset_right repL repOther p inOther ⟨a,common,recordA⟩
    · intro p notPast updated
      have birth := ((M.update_cell B e p).mp updated).resolve_right (fun h => notPast h.1)
      exact M.birth_fresh (fun x hx => support₁ hx.1) (support₁ member)
        (fun h => absent h.2) repL p birth
  · intro C E₁ E₂ t₀ t₁ t₂ B e ctx member₁ member₂ h₀ hB h₁ h₂ hD hi₀ hi₁ hi₂ hm
    apply M.carrier_injective
    simp only [M.merge_cell]
    exact Certified.shared _ _ _ _ _

end Model
end Sal.MRDTs.Paper1.Automation.GenericCertifiedRecords
