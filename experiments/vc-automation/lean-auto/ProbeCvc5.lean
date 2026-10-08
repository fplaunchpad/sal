import Auto.Tactic
import Sal.MRDTs.Paper1.GuardedRawORSetReplay
import Sal.MRDTs.Paper1.CertifiedRGAVCReplay
set_option auto.native false
set_option auto.smt true
set_option auto.smt.trust true
set_option auto.smt.solver.name "cvc5"
set_option auto.smt.dumpHints.limitedRws false
set_option auto.smt.timeout 20
set_option trace.auto.smt.result true
set_option maxHeartbeats 2000000

/-! Faithful, proof-free copies of the five Raw.MergeVCs field propositions.
No bundle value or VC theorem is referenced by these definitions. -/
namespace VCAutomation
open Sal.MRDTs Sal.MRDTs.Foundation Sal.MRDTs.Paper1
open Sal.MRDTs.Paper1.ConcreteMRDT Sal.MRDTs.Paper1.ConcreteMRDT.Raw

def merge_comm_goal {D : MRDTSig} (P : OperationPolicy D.AppOp) (R : Representation D) (scheme : ∀ C : ReplayContext D.toUpdateSig, MetadataDependencies C) : Prop := ∀ C E₁ E₂ l a b,
    Supported C E₁ → Supported C E₂ → (scheme C).Closed E₁ → (scheme C).Closed E₂ →
    R C (E₁ ∩ E₂) l → R C E₁ a → R C E₂ b → D.merge l a b = D.merge l b a

def init_goal {D : MRDTSig} (P : OperationPolicy D.AppOp) (R : Representation D) (scheme : ∀ C : ReplayContext D.toUpdateSig, MetadataDependencies C) : Prop := ∀ C E s, Supported C E → (scheme C).Closed E → R C E s →
    D.merge D.init D.init s = s

def causal_delta_goal {D : MRDTSig} (P : OperationPolicy D.AppOp) (R : Representation D) (scheme : ∀ C : ReplayContext D.toUpdateSig, MetadataDependencies C) : Prop := ∀ C U s B e,
    Transitive C.vis → (∀ x, ¬ C.vis x x) → Supported C U → (scheme C).Closed U → e ∈ U →
    (∀ x ∈ U, x ≠ e → ¬ paperOrder P C U e x) →
    (∀ x ∈ U, x ≠ e → ¬ (scheme C).before e x) →
    R C (U \ {e}) s → R C ((scheme C).Past e \ {e}) B →
    R C ((scheme C).Past e) (D.update B e) → R C U (D.update s e) →
    D.merge B s (D.update B e) = D.update s e

def local_redistribute_goal {D : MRDTSig} (P : OperationPolicy D.AppOp) (R : Representation D) (scheme : ∀ C : ReplayContext D.toUpdateSig, MetadataDependencies C) : Prop := ∀ C E₁ E₂ l B t b e, Context P scheme C E₁ E₂ e → e ∈ E₁ → e ∉ E₂ →
    R C (E₁ ∩ E₂) l → R C ((scheme C).Past e \ {e}) B →
    R C (E₁ \ {e}) t → R C E₂ b → R C ((scheme C).Past e) (D.update B e) →
    R C E₁ (D.merge B t (D.update B e)) →
    R C ((E₁ ∪ E₂) \ {e}) (D.merge l t b) →
    D.merge l (D.merge B t (D.update B e)) b =
      D.merge B (D.merge l t b) (D.update B e)

def shared_goal {D : MRDTSig} (P : OperationPolicy D.AppOp) (R : Representation D) (scheme : ∀ C : ReplayContext D.toUpdateSig, MetadataDependencies C) : Prop := ∀ C E₁ E₂ t₀ t₁ t₂ B e, Context P scheme C E₁ E₂ e → e ∈ E₁ → e ∈ E₂ →
    R C ((E₁ ∩ E₂) \ {e}) t₀ → R C ((scheme C).Past e \ {e}) B →
    R C (E₁ \ {e}) t₁ → R C (E₂ \ {e}) t₂ → R C ((scheme C).Past e) (D.update B e) →
    R C (E₁ ∩ E₂) (D.merge B t₀ (D.update B e)) →
    R C E₁ (D.merge B t₁ (D.update B e)) → R C E₂ (D.merge B t₂ (D.update B e)) →
    R C ((E₁ ∪ E₂) \ {e}) (D.merge t₀ t₁ t₂) →
    D.merge (D.merge B t₀ (D.update B e)) (D.merge B t₁ (D.update B e))
      (D.merge B t₂ (D.update B e)) = D.merge B (D.merge t₀ t₁ t₂) (D.update B e)

section TypeAudit
variable {D : MRDTSig} (P : OperationPolicy D.AppOp) (R : Representation D)
    (scheme : ∀ C : ReplayContext D.toUpdateSig, MetadataDependencies C)
#check (fun (v : MergeVCs P R scheme) => (show merge_comm_goal P R scheme from v.merge_comm))
#check (fun (v : MergeVCs P R scheme) => (show init_goal P R scheme from v.init))
#check (fun (v : MergeVCs P R scheme) => (show causal_delta_goal P R scheme from v.causal_delta))
#check (fun (v : MergeVCs P R scheme) => (show local_redistribute_goal P R scheme from v.local_redistribute))
#check (fun (v : MergeVCs P R scheme) => (show shared_goal P R scheme from v.shared))
end TypeAudit

namespace Exact
variable {α : Type} [DecidableEq α]
def merge_comm : Prop := merge_comm_goal (ORSet.conflict α) (ORSet.RawReplay.representation (α := α)) (ORSet.RawReplay.scheme (α := α))
def init : Prop := init_goal (ORSet.conflict α) (ORSet.RawReplay.representation (α := α)) (ORSet.RawReplay.scheme (α := α))
def causal_delta : Prop := causal_delta_goal (ORSet.conflict α) (ORSet.RawReplay.representation (α := α)) (ORSet.RawReplay.scheme (α := α))
def local_redistribute : Prop := local_redistribute_goal (ORSet.conflict α) (ORSet.RawReplay.representation (α := α)) (ORSet.RawReplay.scheme (α := α))
def shared : Prop := shared_goal (ORSet.conflict α) (ORSet.RawReplay.representation (α := α)) (ORSet.RawReplay.scheme (α := α))
end Exact

namespace Efficient
variable {α : Type} [DecidableEq α]
def merge_comm : Prop := merge_comm_goal (EfficientORSet.EventSpec.conflict α) (EfficientORSet.RawReplay.representation (α := α)) (EfficientORSet.RawReplay.scheme (α := α))
def init : Prop := init_goal (EfficientORSet.EventSpec.conflict α) (EfficientORSet.RawReplay.representation (α := α)) (EfficientORSet.RawReplay.scheme (α := α))
def causal_delta : Prop := causal_delta_goal (EfficientORSet.EventSpec.conflict α) (EfficientORSet.RawReplay.representation (α := α)) (EfficientORSet.RawReplay.scheme (α := α))
def local_redistribute : Prop := local_redistribute_goal (EfficientORSet.EventSpec.conflict α) (EfficientORSet.RawReplay.representation (α := α)) (EfficientORSet.RawReplay.scheme (α := α))
def shared : Prop := shared_goal (EfficientORSet.EventSpec.conflict α) (EfficientORSet.RawReplay.representation (α := α)) (EfficientORSet.RawReplay.scheme (α := α))
end Efficient

namespace Embedded
variable {α : Type} [DecidableEq α] [Inhabited α]
open Sal.EmbedRGA
def merge_comm (Γ : OrderedPrefixCode) : Prop := merge_comm_goal (CertifiedRGAVCReplay.Embedded.policy (α := α)) (CertifiedRGAVCReplay.Embedded.representation (α := α) Γ) (CertifiedRGAVCReplay.Embedded.scheme (α := α) Γ)
def init (Γ : OrderedPrefixCode) : Prop := init_goal (CertifiedRGAVCReplay.Embedded.policy (α := α)) (CertifiedRGAVCReplay.Embedded.representation (α := α) Γ) (CertifiedRGAVCReplay.Embedded.scheme (α := α) Γ)
def causal_delta (Γ : OrderedPrefixCode) : Prop := causal_delta_goal (CertifiedRGAVCReplay.Embedded.policy (α := α)) (CertifiedRGAVCReplay.Embedded.representation (α := α) Γ) (CertifiedRGAVCReplay.Embedded.scheme (α := α) Γ)
def local_redistribute (Γ : OrderedPrefixCode) : Prop := local_redistribute_goal (CertifiedRGAVCReplay.Embedded.policy (α := α)) (CertifiedRGAVCReplay.Embedded.representation (α := α) Γ) (CertifiedRGAVCReplay.Embedded.scheme (α := α) Γ)
def shared (Γ : OrderedPrefixCode) : Prop := shared_goal (CertifiedRGAVCReplay.Embedded.policy (α := α)) (CertifiedRGAVCReplay.Embedded.representation (α := α) Γ) (CertifiedRGAVCReplay.Embedded.scheme (α := α) Γ)
end Embedded

end VCAutomation
theorem probe {α : Type} [DecidableEq α] : VCAutomation.Exact.merge_comm (α := α) := by
  unfold VCAutomation.Exact.merge_comm VCAutomation.merge_comm_goal
  intro C E₁ E₂ l a b h₁ h₂ h₃ h₄ h₅ h₆ h₇
  clear h₁ h₂ h₃ h₄ h₅ h₆ h₇ C E₁ E₂
  dsimp only [Sal.MRDTs.Paper1.ORSet.D, Sal.MRDTs.Paper1.ORSet.merge]
  apply Finset.ext
  intro x
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  auto
#print axioms probe
