import Sal.MRDTs.Paper1.MetadataCausalFrame

/-! The local/shared induction steps keep observable redistribution and
directed representation preservation separate. Their smaller-history and side
decomposition premises are the recursive obligations, not global Join. -/
namespace Sal.MRDTs.Paper1.AbstractMRDT
open Foundation
variable {D : MRDTSig}

def MergeCommMetadata (R : Representation D) : Prop :=
  ∀ C E₁ E₂ l a b, R C (E₁ ∪ E₂) (D.merge l b a) →
    R C (E₁ ∪ E₂) (D.merge l a b)

theorem swap_step {A : Model D} {P : OperationPolicy D.AppOp}
    {R : Representation D} {past : ReplayContext D.toUpdateSig → Op D.AppOp → Set (Op D.AppOp)}
    (vcs : MergeVCs A P R past) (metadata : MergeCommMetadata R)
    (C : ReplayContext D.toUpdateSig) (E₁ E₂ : Set (Op D.AppOp)) (l a b : D.State)
    (swapped : Admissible A P R C (E₁ ∪ E₂) (D.merge l b a)) :
    Admissible A P R C (E₁ ∪ E₂) (D.merge l a b) :=
  ⟨canonical_congr swapped.1 (equivalent_symm (vcs.merge_comm l a b)),
    metadata C E₁ E₂ l a b swapped.2⟩

structure PeelContext (A : Model D) (P : OperationPolicy D.AppOp)
    (scheme : ∀ C, MetadataDependencies A C) (C : ReplayContext D.toUpdateSig)
    (E₁ E₂ : Set (Op D.AppOp)) (e : Op D.AppOp) : Prop where
  trans : Transitive C.vis
  irrefl : ∀ x, ¬ C.vis x x
  supported₁ : Supported C E₁
  supported₂ : Supported C E₂
  closed₁ : (scheme C).Closed E₁
  closed₂ : (scheme C).Closed E₂
  semantic : ∀ x ∈ E₁ ∪ E₂, x ≠ e → ¬ order A P C (E₁ ∪ E₂) e x
  metadata : ∀ x ∈ E₁ ∪ E₂, x ≠ e → ¬ (scheme C).before e x

def LocalMetadata (A : Model D) (P : OperationPolicy D.AppOp)
    (R : Representation D) (scheme : ∀ C, MetadataDependencies A C) : Prop :=
  ∀ C E₁ E₂ s₀ B t₁ s₂ e,
    PeelContext A P scheme C E₁ E₂ e → e ∈ E₁ → e ∉ E₂ →
    Admissible A P R C (E₁ ∩ E₂) s₀ →
    Admissible A P R C ((scheme C).Past e \ {e}) B →
    Admissible A P R C (E₁ \ {e}) t₁ → Admissible A P R C E₂ s₂ →
    R C (E₁ ∪ E₂) (D.merge B (D.merge s₀ t₁ s₂) (D.update B e)) →
    R C (E₁ ∪ E₂) (D.merge s₀ (D.merge B t₁ (D.update B e)) s₂)

def SharedMetadata (A : Model D) (P : OperationPolicy D.AppOp)
    (R : Representation D) (scheme : ∀ C, MetadataDependencies A C) : Prop :=
  ∀ C E₁ E₂ t₀ t₁ t₂ B e,
    PeelContext A P scheme C E₁ E₂ e → e ∈ E₁ → e ∈ E₂ →
    Admissible A P R C ((E₁ ∩ E₂) \ {e}) t₀ →
    Admissible A P R C ((scheme C).Past e \ {e}) B →
    Admissible A P R C (E₁ \ {e}) t₁ →
    Admissible A P R C (E₂ \ {e}) t₂ →
    R C (E₁ ∪ E₂) (D.merge B (D.merge t₀ t₁ t₂) (D.update B e)) →
    R C (E₁ ∪ E₂)
      (D.merge (D.merge B t₀ (D.update B e)) (D.merge B t₁ (D.update B e))
        (D.merge B t₂ (D.update B e)))

theorem local_step {A : Model D} {P : OperationPolicy D.AppOp}
    {R : Representation D} {scheme : ∀ C, MetadataDependencies A C}
    (laws : Laws A P) (vcs : DependencyMergeVCs A P R scheme)
    (causal : CausalMetadata A P R scheme) (localMetadata : LocalMetadata A P R scheme)
    (substitute : MetadataSubstitution A R)
    (C : ReplayContext D.toUpdateSig) (E₁ E₂ : Set (Op D.AppOp))
    (choice : DependencyPeelChoice A P R C (scheme C) (E₁ ∪ E₂))
    (ctx : PeelContext A P scheme C E₁ E₂ choice.event)
    (s₀ s₁ s₂ t₁ : D.State) (member : choice.event ∈ E₁) (absent : choice.event ∉ E₂)
    (base : Admissible A P R C (E₁ ∩ E₂) s₀) (side : R C E₁ s₁)
    (other : Admissible A P R C E₂ s₂) (pre : Admissible A P R C (E₁ \ {choice.event}) t₁)
    (decomposition : R C E₁ (D.merge choice.past t₁ (D.update choice.past choice.event)))
    (smaller : R C ((E₁ ∪ E₂) \ {choice.event}) (D.merge s₀ t₁ s₂)) :
    Admissible A P R C (E₁ ∪ E₂) (D.merge s₀ s₁ s₂) := by
  have supported : Supported C (E₁ ∪ E₂) :=
    fun x h => h.elim (ctx.supported₁ x) (ctx.supported₂ x)
  have closed : (scheme C).Closed (E₁ ∪ E₂) :=
    fun a b edge hb => hb.elim (fun h => Or.inl (ctx.closed₁ a b edge h))
      (fun h => Or.inr (ctx.closed₂ a b edge h))
  have target := causal_frame laws vcs causal substitute C (E₁ ∪ E₂) choice
    ctx.trans ctx.irrefl supported closed (D.merge s₀ t₁ s₂) smaller
  have observable := vcs.delta.local_redistribute C E₁ E₂ s₀ choice.past t₁ s₂ choice.event
    (fun {_ _ _} h k => ctx.trans h k) ctx.irrefl ctx.supported₁ ctx.supported₂
    ((scheme C).closed_implies_conflictClosed E₁ ctx.closed₁)
    ((scheme C).closed_implies_conflictClosed E₂ ctx.closed₂)
    member absent ctx.semantic base choice.past_admissible pre other
  have reconstructed : Admissible A P R C (E₁ ∪ E₂)
      (D.merge s₀ (D.merge choice.past t₁ (D.update choice.past choice.event)) s₂) :=
    ⟨canonical_congr target.1 (equivalent_symm observable),
      localMetadata C E₁ E₂ s₀ choice.past t₁ s₂ choice.event ctx member absent
        base choice.past_admissible pre other target.2⟩
  have frame := substitute C E₁ E₂ s₀ s₁ s₂ s₀
    (D.merge choice.past t₁ (D.update choice.past choice.event)) s₂
    ctx.supported₁ ctx.supported₂ base.2 side other.2 base.2 decomposition other.2
  exact ⟨canonical_congr reconstructed.1 (equivalent_symm frame.1),frame.2 reconstructed.2⟩

theorem shared_step {A : Model D} {P : OperationPolicy D.AppOp}
    {R : Representation D} {scheme : ∀ C, MetadataDependencies A C}
    (laws : Laws A P) (vcs : DependencyMergeVCs A P R scheme)
    (causal : CausalMetadata A P R scheme) (sharedMetadata : SharedMetadata A P R scheme)
    (substitute : MetadataSubstitution A R)
    (C : ReplayContext D.toUpdateSig) (E₁ E₂ : Set (Op D.AppOp))
    (choice : DependencyPeelChoice A P R C (scheme C) (E₁ ∪ E₂))
    (ctx : PeelContext A P scheme C E₁ E₂ choice.event)
    (s₀ s₁ s₂ t₀ t₁ t₂ : D.State) (member₁ : choice.event ∈ E₁) (member₂ : choice.event ∈ E₂)
    (base : R C (E₁ ∩ E₂) s₀) (side₁ : R C E₁ s₁) (side₂ : R C E₂ s₂)
    (pre₀ : Admissible A P R C ((E₁ ∩ E₂) \ {choice.event}) t₀)
    (pre₁ : Admissible A P R C (E₁ \ {choice.event}) t₁)
    (pre₂ : Admissible A P R C (E₂ \ {choice.event}) t₂)
    (decomposition₀ : R C (E₁ ∩ E₂) (D.merge choice.past t₀ (D.update choice.past choice.event)))
    (decomposition₁ : R C E₁ (D.merge choice.past t₁ (D.update choice.past choice.event)))
    (decomposition₂ : R C E₂ (D.merge choice.past t₂ (D.update choice.past choice.event)))
    (smaller : R C ((E₁ ∪ E₂) \ {choice.event}) (D.merge t₀ t₁ t₂)) :
    Admissible A P R C (E₁ ∪ E₂) (D.merge s₀ s₁ s₂) := by
  have supported : Supported C (E₁ ∪ E₂) :=
    fun x h => h.elim (ctx.supported₁ x) (ctx.supported₂ x)
  have closed : (scheme C).Closed (E₁ ∪ E₂) :=
    fun a b edge hb => hb.elim (fun h => Or.inl (ctx.closed₁ a b edge h))
      (fun h => Or.inr (ctx.closed₂ a b edge h))
  have target := causal_frame laws vcs causal substitute C (E₁ ∪ E₂) choice
    ctx.trans ctx.irrefl supported closed (D.merge t₀ t₁ t₂) smaller
  have observable := vcs.delta.redistribute C E₁ E₂ t₀ t₁ t₂ choice.past choice.event
    (fun {_ _ _} h k => ctx.trans h k) ctx.irrefl ctx.supported₁ ctx.supported₂
    ((scheme C).closed_implies_conflictClosed E₁ ctx.closed₁)
    ((scheme C).closed_implies_conflictClosed E₂ ctx.closed₂)
    member₁ member₂ ctx.semantic pre₀ choice.past_admissible pre₁ pre₂
  have reconstructed : Admissible A P R C (E₁ ∪ E₂)
      (D.merge (D.merge choice.past t₀ (D.update choice.past choice.event))
        (D.merge choice.past t₁ (D.update choice.past choice.event))
        (D.merge choice.past t₂ (D.update choice.past choice.event))) :=
    ⟨canonical_congr target.1 (equivalent_symm observable),
      sharedMetadata C E₁ E₂ t₀ t₁ t₂ choice.past choice.event ctx member₁ member₂
        pre₀ choice.past_admissible pre₁ pre₂ target.2⟩
  have frame := substitute C E₁ E₂ s₀ s₁ s₂
    (D.merge choice.past t₀ (D.update choice.past choice.event))
    (D.merge choice.past t₁ (D.update choice.past choice.event))
    (D.merge choice.past t₂ (D.update choice.past choice.event))
    ctx.supported₁ ctx.supported₂ base side₁ side₂ decomposition₀ decomposition₁ decomposition₂
  exact ⟨canonical_congr reconstructed.1 (equivalent_symm frame.1),frame.2 reconstructed.2⟩

end Sal.MRDTs.Paper1.AbstractMRDT
