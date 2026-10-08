import Sal.MRDTs.Paper1.CertifiedMVRReplay
import Sal.MRDTs.Paper1.ConcreteJoin

namespace Sal.MRDTs.Paper1.CertifiedQueueMVR.MVR.RawVC
open Foundation Classical ConcreteMRDT
set_option maxHeartbeats 1500000
open Instances.MVRLive

abbrev policy := emptyPolicy

def scheme (C : ReplayContext D.toUpdateSig) : MetadataDependencies C where
  before := C.vis
  causal _ _ h := h
  covers _ _ h _ := h

/-- Execution eligibility and finite represented history, without a closure
restriction: the generic induction supplies arbitrary finite supported subsets.
Closure remains an independent guard on each merge VC. -/
def representation : Representation D := fun context E s =>
  ∃ C : Configuration D, CertifiedExecution D issuance C ∧ C.replayContext = context ∧
    E ⊆ C.events ∧ E.Finite ∧ Represents E s

theorem unique : ConcreteMRDT.Raw.Unique representation := by
  intro context E a b ha hb
  obtain ⟨_,_,_,_,_,ha⟩ := ha
  obtain ⟨_,_,_,_,_,hb⟩ := hb
  apply Finset.ext
  intro p
  exact (ha p).trans (hb p).symm

theorem initial (context : ReplayContext D.toUpdateSig) (E : Set Event) (s : State)
    (h : representation context E s) : representation context ∅ D.init := by
  obtain ⟨C,exec,eq,_,_,_⟩ := h
  exact ⟨C,exec,eq,Set.empty_subset _,Set.finite_empty,represents_empty⟩

private theorem fresh_record {C : Configuration D} {E : Set Event} {s : State} {e : Event}
    (sup : E ⊆ C.events) (he : e ∈ C.events) (absent : e ∉ E)
    (rep : Represents E s) : (e.time,Instances.MVR.writeValue e) ∉ s := by
  intro member
  obtain ⟨⟨b,hb,pair⟩,_⟩ := (rep _).mp member
  have same : b = e := C.replayContext.ts_unique (sup hb) he (congrArg (fun p : Nat × Nat => p.1) pair)
  exact absent (same ▸ hb)

private theorem causal_eq (A B : State) (e : Event)
    (fresh : (e.time,Instances.MVR.writeValue e) ∉ B)
    (self : e.time ∉ Instances.MVR.overwrites e)
    (covered : ∀ p ∈ A, p.1 ∈ Instances.MVR.overwrites e → p ∈ B) :
    merge B A (update B e) = update A e := by
  ext p
  have coverage := covered p
  simp only [merge,Instances.MVRLive.update,Instances.MVR.clientStep,Finset.mem_union,Finset.mem_inter,
    Finset.mem_sdiff,Finset.mem_insert,Finset.mem_filter]
  change (e.1,Instances.MVR.writeValue e) ∉ B at fresh
  change e.1 ∉ Instances.MVR.overwrites e at self
  grind

private theorem local_eq (l B t b : State) (e : Event)
    (freshB : (e.time,Instances.MVR.writeValue e) ∉ B)
    (freshL : (e.time,Instances.MVR.writeValue e) ∉ l)
    (self : e.time ∉ Instances.MVR.overwrites e)
    (shared : ∀ p ∈ B, p ∈ b → p ∈ l) :
    merge l (merge B t (update B e)) b = merge B (merge l t b) (update B e) := by
  ext p
  have sharing := shared p
  simp only [merge,Instances.MVRLive.update,Instances.MVR.clientStep,Finset.mem_union,Finset.mem_inter,
    Finset.mem_sdiff,Finset.mem_insert,Finset.mem_filter]
  change (e.1,Instances.MVR.writeValue e) ∉ B at freshB
  change (e.1,Instances.MVR.writeValue e) ∉ l at freshL
  change e.1 ∉ Instances.MVR.overwrites e at self
  grind

private theorem shared_eq (t₀ t₁ t₂ B : State) (e : Event) :
    merge (merge B t₀ (update B e)) (merge B t₁ (update B e))
      (merge B t₂ (update B e)) = merge B (merge t₀ t₁ t₂) (update B e) := by
  ext p
  simp only [merge,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
  tauto

private theorem rep_of (C : ReplayContext D.toUpdateSig) (E : Set Event) (s : State)
    (h : representation C E s) : Represents E s := by
  obtain ⟨_,_,_,_,_,h⟩ := h; exact h

private theorem past_vis {C : ReplayContext D.toUpdateSig} (trans : Transitive C.vis)
    {a e : Event} (h : a ∈ (scheme C).Past e \ {e}) : C.vis a e := by
  rcases h.1 with rfl | path
  · exact False.elim (h.2 rfl)
  · have t : Transitive (scheme C).before := trans
    rw [Relation.transGen_eq_self t] at path
    exact path

private theorem live_subset {A B : Set Event} {a b : State}
    (sub : A ⊆ B) (ha : Represents A a) (hb : Represents B b)
    {p : Nat × Nat} (live : p ∈ b)
    (birth : ∃ e ∈ A, (e.time,Instances.MVR.writeValue e) = p) : p ∈ a := by
  apply (ha p).mpr
  refine ⟨birth,?_⟩
  rintro ⟨e,he,dead⟩
  exact ((hb p).mp live).2 ⟨e,sub he,dead⟩

theorem mergeVCs : ConcreteMRDT.Raw.MergeVCs policy representation scheme := by
  constructor
  · intro C E₁ E₂ l a b _ _ _ _ _ _ _
    exact Instances.MVRLive.merge_comm l a b
  · intro C E s _ _ h
    change merge ∅ ∅ s = s
    simp [merge]
  · intro C U s B e trans irrefl supported closed member semantic metadata hs hB hupdateB hupdateS
    obtain ⟨K,exec,eq,sup,finite,repUpdate⟩ := hupdateS
    subst C
    have pastSub := (scheme K.replayContext).past_subset U e closed member
    have sub : (scheme K.replayContext).Past e \ {e} ⊆ U \ {e} :=
      fun x hx => ⟨pastSub hx.1,hx.2⟩
    have repS := rep_of _ _ _ hs
    have repB := rep_of _ _ _ hB
    apply causal_eq s B e
    · exact fresh_record (fun x hx => sup (pastSub hx.1)) (sup member)
        (fun h => h.2 rfl) repB
    · intro target
      exact Nat.lt_irrefl _ (issued_overwrite_lt exec.mintHonest (sup member) target)
    · intro p live target
      obtain ⟨⟨b,hb,pair⟩,_⟩ := (repS p).mp live
      have targetB : b.time ∈ Instances.MVR.overwrites e := by
        have times := congrArg (fun p : Nat × Nat => p.1) pair
        change b.1 = p.1 at times
        change b.1 ∈ Instances.MVR.overwrites e
        rw [times]
        exact target
      have vis := overwrite_implies_visibility exec (sup hb.1) (sup member) targetB
      have birth : b ∈ (scheme K.replayContext).Past e \ {e} :=
        ⟨Or.inr (.single vis),hb.2⟩
      exact live_subset sub repB repS live ⟨b,birth,pair⟩
  · intro C E₁ E₂ l B t b e ctx member absent hl hB ht hb hu hd hm
    obtain ⟨K,exec,eq,_,_,_⟩ := hd
    subst C
    have sup₁ : E₁ ⊆ K.events := by simpa using ctx.supported₁
    have sup₂ : E₂ ⊆ K.events := by simpa using ctx.supported₂
    have pastSub := (scheme K.replayContext).past_subset E₁ e ctx.closed₁ member
    have repL := rep_of _ _ _ hl
    have repB := rep_of _ _ _ hB
    have repOther := rep_of _ _ _ hb
    apply local_eq l B t b e
    · exact fresh_record (fun x hx => sup₁ (pastSub hx.1)) (sup₁ member)
        (fun h => h.2 rfl) repB
    · exact fresh_record (fun x hx => sup₁ hx.1) (sup₁ member)
        (fun h => absent h.2) repL
    · intro target
      exact Nat.lt_irrefl _ (issued_overwrite_lt exec.mintHonest (sup₁ member) target)
    · intro p inB inOther
      obtain ⟨⟨a,ha,pairA⟩,_⟩ := (repB p).mp inB
      obtain ⟨⟨c,hc,pairC⟩,_⟩ := (repOther p).mp inOther
      have same : a = c := K.replayContext.ts_unique (sup₁ (pastSub ha.1)) (sup₂ hc)
        (congrArg (fun p : Nat × Nat => p.1) (pairA.trans pairC.symm))
      have aBase : a ∈ E₁ ∩ E₂ := ⟨pastSub ha.1,same ▸ hc⟩
      exact live_subset Set.inter_subset_right repL repOther inOther ⟨a,aBase,pairA⟩
  · intro C E₁ E₂ t₀ t₁ t₂ B e ctx member₁ member₂ ht₀ hB ht₁ ht₂ hu hd₀ hd₁ hd₂ hm
    exact shared_eq t₀ t₁ t₂ B e

theorem finite (context : ReplayContext D.toUpdateSig) (E : Set Event) (s : State)
    (h : representation context E s) : ∃ π, listPermOf π E := by
  obtain ⟨_,_,_,_,fin,_⟩ := h
  exact ⟨fin.toFinset.toList,fin.toFinset.nodup_toList,by simpa using fin.mem_toFinset⟩

private theorem chronological_represents (K : Configuration D)
    (exec : CertifiedExecution D issuance K) (E : Set Event) (sup : E ⊆ K.events)
    (π : List Event) (hp : listPermOf π E) :
    Represents E (applySeq D.toUpdateSig D.init (Instances.MVR.chronological π)) := by
  have hp' : listPermOf (Instances.MVR.chronological π) E :=
    ⟨(Instances.MVR.chronological_perm π).symm.nodup hp.1,
      fun e => (Instances.MVR.chronological_perm π).mem_iff.trans (hp.2 e)⟩
  rw [fold_live _ (Instances.MVR.chronological_sorted π)
    (fun e he n hn => issued_overwrite_lt exec.mintHonest (sup ((hp'.2 e).mp he)) hn)]
  intro p
  rw [mem_live]
  simp only [Born,Dead,List.mem_toFinset,hp'.2]

private theorem reattach (K : Configuration D) (exec : CertifiedExecution D issuance K)
    (U H : Set Event) (sup : U ⊆ K.events) (sub : H ⊆ U) (e : Event)
    (member : e ∈ U) (maximal : ∀ x ∈ U, x ≠ e → ¬ K.vis e x)
    (absent : e ∉ H) {s : State} (rep : Represents H s) :
    Represents (H ∪ {e}) (Instances.MVRLive.update s e) := by
  apply represents_update e rep
  · intro b hb target
    have vis := overwrite_implies_visibility exec (sup member) (sup (sub hb)) target
    exact maximal b (sub hb) (fun eq => absent (eq ▸ hb)) vis
  · intro target
    exact Nat.lt_irrefl _ (issued_overwrite_lt exec.mintHonest (sup member) target)

theorem replaySupply (K : Configuration D) (exec : CertifiedExecution D issuance K) :
    ConcreteMRDT.Raw.ReplaySupply policy representation scheme K.replayContext := by
  constructor
  · intro E π hp sup
    have supported : E ⊆ K.events := by simpa using sup
    have fin : E.Finite := by
      have equal : E = {e | e ∈ π} := by ext e; exact (hp.2 e).symm
      rw [equal]; exact List.finite_toSet π
    exact ⟨_,K,exec,rfl,supported,fin,chronological_represents K exec E supported π hp⟩
  · intro U s hU sup nonempty closed
    have supported : U ⊆ K.events := by simpa using sup
    obtain ⟨π,hp⟩ := finite K.replayContext U s hU
    have fin : U.Finite := by obtain ⟨_,_,_,_,h,_⟩ := hU; exact h
    have hp' : listPermOf (Instances.MVR.chronological π) U :=
      ⟨(Instances.MVR.chronological_perm π).symm.nodup hp.1,
        fun e => (Instances.MVR.chronological_perm π).mem_iff.trans (hp.2 e)⟩
    have causal : respects (Instances.MVR.chronological π) K.vis :=
      (Instances.MVR.chronological_sorted π).imp (fun {_ _} le vis =>
        (not_lt_of_ge le) (K.causal_mono vis))
    have paper : respects (Instances.MVR.chronological π) (paperOrder policy K.replayContext U) := by
      apply causal.imp
      intro a b h edge
      rcases edge with edge | edge
      · exact h edge.1
      · exact edge.2.2.1.elim
    obtain ⟨e,member,semantic,metadata⟩ := joint_maximal_of_enumeration _ hp' nonempty paper causal
    have pastSub := (scheme K.replayContext).past_subset U e closed member
    have finPast := fin.subset pastSub
    let remainder := applySeq D.toUpdateSig D.init
      (Instances.MVR.chronological ((fin.diff (t := {e})).toFinset.toList))
    let past := applySeq D.toUpdateSig D.init
      (Instances.MVR.chronological ((finPast.diff (t := {e})).toFinset.toList))
    have enumerate : ∀ (E : Set Event) (h : E.Finite), listPermOf h.toFinset.toList E := by
      intro E h; exact ⟨h.toFinset.nodup_toList,by simpa using h.mem_toFinset⟩
    have repRem : Represents (U \ {e}) remainder :=
      chronological_represents K exec _ (fun x h => supported h.1) _ (enumerate _ _)
    have repPast : Represents ((scheme K.replayContext).Past e \ {e}) past :=
      chronological_represents K exec _ (fun x h => supported (pastSub h.1)) _ (enumerate _ _)
    have updateRem := reattach K exec U (U \ {e}) supported (fun _ h => h.1)
      e member metadata (fun h => h.2 rfl) repRem
    have updatePast := reattach K exec U ((scheme K.replayContext).Past e \ {e})
      supported (fun _ h => pastSub h.1) e member metadata (fun h => h.2 rfl) repPast
    have unionRem : (U \ {e}) ∪ {e} = U := by ext x; simp only [Set.mem_union,Set.mem_diff,Set.mem_singleton_iff]; grind
    have unionPast : ((scheme K.replayContext).Past e \ {e}) ∪ {e} =
        (scheme K.replayContext).Past e := by
      ext x; simp only [Set.mem_union,Set.mem_diff,Set.mem_singleton_iff,MetadataDependencies.Past,Set.mem_setOf_eq]; tauto
    refine ⟨{ event := e
              member := member
              semantic_maximal := semantic
              metadata_maximal := metadata
              remainder := remainder
              past := past
              remainder_rep := ⟨K,exec,rfl,(fun x h => supported h.1),fin.diff (t := {e}),repRem⟩,
              past_rep := ⟨K,exec,rfl,(fun x h => supported (pastSub h.1)),finPast.diff (t := {e}),repPast⟩,
              reconstructed_past := ⟨K,exec,rfl,(fun x h => supported (pastSub h)),finPast,
        by simpa only [unionPast] using updatePast⟩,
              reconstructed_union := ⟨K,exec,rfl,supported,fin,
        by simpa only [unionRem] using updateRem⟩ }⟩

theorem representationJoin : RepresentationJoin representation := by
  apply ConcreteMRDT.Raw.representationJoin_of_vcs mergeVCs unique initial finite
  intro context E₁ E₂ a b trans irrefl sup₁ sup₂ ha hb
  obtain ⟨K,exec,eq,_,_,_⟩ := ha
  subst context
  exact replaySupply K exec

/-- The production compact MVR merge preserves represented histories, derived
from the five raw VCs and finite induction rather than the legacy Join proof. -/
theorem represents_merge (C : Configuration D) (execution : CertifiedExecution D issuance C)
    (trans : Transitive C.vis)
    (E₁ E₂ : Set Event) (sup₁ : E₁ ⊆ C.events) (sup₂ : E₂ ⊆ C.events)
    (closed₁ : ∀ a b, C.vis a b → b ∈ E₁ → a ∈ E₁)
    (closed₂ : ∀ a b, C.vis a b → b ∈ E₂ → a ∈ E₂)
    (finite₁ : E₁.Finite) (finite₂ : E₂.Finite) {l a b : State}
    (hl : Represents (E₁ ∩ E₂) l) (ha : Represents E₁ a) (hb : Represents E₂ b) :
    Represents (E₁ ∪ E₂) (merge l a b) := by
  have joined := representationJoin C.replayContext E₁ E₂ l a b
    trans
    (fun e h => Nat.lt_irrefl e.time (C.causal_mono h))
    (fun e he => by simpa only [Configuration.replayContext_events] using sup₁ he)
    (fun e he => by simpa only [Configuration.replayContext_events] using sup₂ he) closed₁ closed₂
    ⟨C,execution,rfl,(fun x h => sup₁ h.1),finite₁.inter_of_left E₂,hl⟩
    ⟨C,execution,rfl,sup₁,finite₁,ha⟩ ⟨C,execution,rfl,sup₂,finite₂,hb⟩
  exact rep_of _ _ _ joined

end Sal.MRDTs.Paper1.CertifiedQueueMVR.MVR.RawVC
