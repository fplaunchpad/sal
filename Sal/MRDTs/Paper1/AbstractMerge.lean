import Sal.MRDTs.Paper1.AbstractFormalism

/-! Representation-sensitive merge contracts. Canonicality alone identifies
states by their abstraction; it does not establish that hidden metadata belongs
to the event history. All five merge VC conclusions are observational, while
representation evidence remains an explicit premise. The generic correctness
route consumes representation Join. `MetadataJoin.representationJoin_of_vcs`
derives it from these five VCs with explicit representation-preserving rewrites,
guarded substitution, and replay supplies; observational equations alone do
not imply metadata preservation.
-/
namespace Sal.MRDTs.Paper1.AbstractMRDT
open Foundation
variable {D : MRDTSig}

abbrev Representation (D : MRDTSig) :=
  ReplayContext D.toUpdateSig → Set (Op D.AppOp) → D.State → Prop

def Admissible (A : Model D) (P : OperationPolicy D.AppOp) (R : Representation D)
    (C : ReplayContext D.toUpdateSig) (E : Set (Op D.AppOp)) (s : D.State) : Prop :=
  Canonical A P C E s ∧ R C E s

def RepresentsCanonical (A : Model D) (P : OperationPolicy D.AppOp)
    (R : Representation D) : Prop :=
  ∀ C E s, R C E s → Canonical A P C E s

def RepresentationJoin (R : Representation D) : Prop :=
  ∀ (C : ReplayContext D.toUpdateSig) (E₁ E₂ : Set (Op D.AppOp)) (l a b : D.State),
    Transitive C.vis → (∀ e, ¬ C.vis e e) →
    (∀ e ∈ E₁, e ∈ C.events) → (∀ e ∈ E₂, e ∈ C.events) →
    (∀ e f, C.vis e f → f ∈ E₁ → e ∈ E₁) →
    (∀ e f, C.vis e f → f ∈ E₂ → e ∈ E₂) →
    R C (E₁ ∩ E₂) l → R C E₁ a → R C E₂ b →
    R C (E₁ ∪ E₂) (D.merge l a b)

theorem merge_canonical_of_representation {A : Model D} {P : OperationPolicy D.AppOp}
    {R : Representation D} (canonical : RepresentsCanonical A P R)
    (join : RepresentationJoin R) (C : ReplayContext D.toUpdateSig)
    (E₁ E₂ : Set (Op D.AppOp)) (l a b : D.State)
    (trans : Transitive C.vis) (irrefl : ∀ e, ¬ C.vis e e)
    (sup₁ : ∀ e ∈ E₁, e ∈ C.events) (sup₂ : ∀ e ∈ E₂, e ∈ C.events)
    (closed₁ : ∀ e f, C.vis e f → f ∈ E₁ → e ∈ E₁)
    (closed₂ : ∀ e f, C.vis e f → f ∈ E₂ → e ∈ E₂)
    (hl : R C (E₁ ∩ E₂) l) (ha : R C E₁ a) (hb : R C E₂ b) :
    Canonical A P C (E₁ ∪ E₂) (D.merge l a b) :=
  canonical _ _ _ (join C E₁ E₂ l a b trans irrefl sup₁ sup₂ closed₁ closed₂ hl ha hb)

/-- Substitution at merge is sound for states representing the same indexed
histories. No unrestricted quotient merge or raw-state equality is used. -/
theorem merge_equivalent_of_representation {A : Model D} {P : OperationPolicy D.AppOp}
    {R : Representation D} (laws : Laws A P)
    (canonical : RepresentsCanonical A P R) (join : RepresentationJoin R)
    (C : ReplayContext D.toUpdateSig) (E₁ E₂ : Set (Op D.AppOp))
    (l a b l' a' b' : D.State)
    (trans : Transitive C.vis) (irrefl : ∀ e, ¬ C.vis e e)
    (sup₁ : ∀ e ∈ E₁, e ∈ C.events) (sup₂ : ∀ e ∈ E₂, e ∈ C.events)
    (closed₁ : ∀ e f, C.vis e f → f ∈ E₁ → e ∈ E₁)
    (closed₂ : ∀ e f, C.vis e f → f ∈ E₂ → e ∈ E₂)
    (hl : R C (E₁ ∩ E₂) l) (ha : R C E₁ a) (hb : R C E₂ b)
    (hl' : R C (E₁ ∩ E₂) l') (ha' : R C E₁ a') (hb' : R C E₂ b') :
    Equivalent A (D.merge l a b) (D.merge l' a' b') := by
  apply canonical_equivalent laws C (E₁ ∪ E₂)
    (fun e he => he.elim (sup₁ e) (sup₂ e))
  · exact merge_canonical_of_representation canonical join C E₁ E₂ l a b
      trans irrefl sup₁ sup₂ closed₁ closed₂ hl ha hb
  · exact merge_canonical_of_representation canonical join C E₁ E₂ l' a' b'
      trans irrefl sup₁ sup₂ closed₁ closed₂ hl' ha' hb'

structure DeltaVCs (A : Model D) (P : OperationPolicy D.AppOp)
    (R : Representation D)
    (past : ReplayContext D.toUpdateSig → Op D.AppOp → Set (Op D.AppOp) := causalPast A) : Prop where
  init :
    ∀ (C : Sal.MRDTs.Foundation.ReplayContext D.toUpdateSig)
      (ev : Set (Op D.AppOp)) (s : D.State),
      (∀ a ∈ ev, a ∈ C.events) →
      Admissible A P R C ev s →
      Equivalent A (D.merge D.init D.init s) s
  local_redistribute :
    ∀ (C : Sal.MRDTs.Foundation.ReplayContext D.toUpdateSig)
      (ev₁ ev₂ : Set (Op D.AppOp)) (s₀ B t₁ s₂ : D.State) (e : Op D.AppOp),
      (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
      (∀ a : Op D.AppOp, ¬ C.vis a a) →
      (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
      (∀ a b, C.vis a b → ¬ Commutes A a b → b ∈ ev₁ → a ∈ ev₁) →
      (∀ a b, C.vis a b → ¬ Commutes A a b → b ∈ ev₂ → a ∈ ev₂) →
      e ∈ ev₁ → e ∉ ev₂ →
      (∀ x ∈ ev₁ ∪ ev₂, x ≠ e → ¬ order A P C (ev₁ ∪ ev₂) e x) →
      Admissible A P R C (ev₁ ∩ ev₂) s₀ →
      Admissible A P R C (past C e \ {e}) B →
      Admissible A P R C (ev₁ \ {e}) t₁ →
      Admissible A P R C ev₂ s₂ →
      Equivalent A (D.merge s₀ (D.merge B t₁ (D.update B e)) s₂)
        (D.merge B (D.merge s₀ t₁ s₂) (D.update B e))
  redistribute :
    ∀ (C : Sal.MRDTs.Foundation.ReplayContext D.toUpdateSig)
      (ev₁ ev₂ : Set (Op D.AppOp)) (t₀ t₁ t₂ B : D.State) (e : Op D.AppOp),
      (∀ {a b c : Op D.AppOp}, C.vis a b → C.vis b c → C.vis a c) →
      (∀ a : Op D.AppOp, ¬ C.vis a a) →
      (∀ a ∈ ev₁, a ∈ C.events) → (∀ a ∈ ev₂, a ∈ C.events) →
      (∀ a b, C.vis a b → ¬ Commutes A a b → b ∈ ev₁ → a ∈ ev₁) →
      (∀ a b, C.vis a b → ¬ Commutes A a b → b ∈ ev₂ → a ∈ ev₂) →
      e ∈ ev₁ → e ∈ ev₂ →
      (∀ x ∈ ev₁ ∪ ev₂, x ≠ e → ¬ order A P C (ev₁ ∪ ev₂) e x) →
      Admissible A P R C ((ev₁ ∩ ev₂) \ {e}) t₀ →
      Admissible A P R C (past C e \ {e}) B →
      Admissible A P R C (ev₁ \ {e}) t₁ →
      Admissible A P R C (ev₂ \ {e}) t₂ →
      Equivalent A (D.merge (D.merge B t₀ (D.update B e)) (D.merge B t₁ (D.update B e))
          (D.merge B t₂ (D.update B e)))
        (D.merge B (D.merge t₀ t₁ t₂) (D.update B e))


def CausalDeltaVC (A : Model D) (P : OperationPolicy D.AppOp)
    (R : Representation D)
    (past : ReplayContext D.toUpdateSig → Op D.AppOp → Set (Op D.AppOp) := causalPast A) : Prop :=
  ∀ (C : ReplayContext D.toUpdateSig) (U : Set (Op D.AppOp)) (s t : D.State) (e : Op D.AppOp),
    Transitive C.vis → (∀ a, ¬ C.vis a a) →
    (∀ a ∈ U, a ∈ C.events) →
    (∀ a b, C.vis a b → ¬ Commutes A a b → b ∈ U → a ∈ U) →
    e ∈ U → (∀ x ∈ U, x ≠ e → ¬ order A P C U e x) →
    Admissible A P R C (U \ {e}) s →
    Admissible A P R C (past C e \ {e}) t →
    Equivalent A (D.merge t s (D.update t e)) (D.update s e)

structure MergeVCs (A : Model D) (P : OperationPolicy D.AppOp)
    (R : Representation D)
    (past : ReplayContext D.toUpdateSig → Op D.AppOp → Set (Op D.AppOp) := causalPast A) : Prop where
  merge_comm : ∀ l a b, Equivalent A (D.merge l a b) (D.merge l b a)
  delta : DeltaVCs A P R past
  causal_delta : CausalDeltaVC A P R past

/-- Metadata adequacy and sequential adequacy are distinct obligations. -/
theorem of_representation {A : Model D} {P : OperationPolicy D.AppOp}
    {R : Representation D} {S : HistorySpec (Op D.AppOp) D.Query D.Value}
    {C : Configuration D} (laws : Laws A P)
    (represented : ∀ v s E, C.ver v = some (s,E) → R C.replayContext E s)
    (canonical : RepresentsCanonical A P R)
    (compatible : SpecificationCompatibility A S) (sound : EventFoldHistorySound D S) :
    VersionsRALinearizable A P S C :=
  of_canonical laws (fun v s E hv => canonical _ _ _ (represented v s E hv)) compatible sound

end Sal.MRDTs.Paper1.AbstractMRDT
