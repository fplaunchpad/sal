import Sal.ConditionedMRDTs.MRDT_Instances.SidedRGA.SidedRGA
import Sal.ConditionedMRDTs.MRDT_Instances.ORSetCore.ORSetCore
import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_Embed.PeritextEmbed_MarkIntent
import Sal.ConditionedMRDTs.Metatheory.Product
import Sal.ConditionedMRDTs.MRDT_Instances.ProductionGenerationContracts

/-!
# Sided Peritext core

This is the first checked link for the shipped architecture: sided text and a
separate OR-set mark store. It proves the product Join obligation without
claiming the still-missing rendered sequential or mark-aware state-GC results.
-/

namespace Sal.ConditionedMRDTs.PeritextSided

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode)
open Sal.ConditionedMRDTs
open Sal.ConditionedMRDTs.PeritextEmbed.MarkDoc

deriving instance DecidableEq for MarkD

/-- Runtime deletes form a grow-only set. `OSCore` supplies the same union
algebra; the generation guard below admits only `add target` operations. -/
def DeleteStore : ConditionedMRDTSig :=
  OSCore ℕ id Unit (OSState ℕ) (fun s _ => s)

/-- Runtime marks form a grow-only map keyed by globally fresh `mid`. A
remove-mark is another immutable `MarkD` with `op = remove`; the guard admits
only OR-set adds, so the reachable representation is a unique-key grow map. -/
def RuntimeMarkStore : ConditionedMRDTSig :=
  OSCore MarkD MarkD.mid Unit (OSState MarkD) (fun s _ => s)

def Stores : ConditionedMRDTSig := prodSig DeleteStore RuntimeMarkStore

/-- The mathematical state shape corresponding to the runtime's separation of
sided text from marks. The exact operation-codec correspondence remains a
separate validation obligation. -/
def Core (Γ : OrderedPrefixCode) : ConditionedMRDTSig :=
  prodSig (S Γ) Stores

/-- Product history honesty: sided text needs its causal generation history;
the OR-set mark algebra has an unconditional Join theorem. -/
def CoreHonest (Γ : OrderedPrefixCode)
    (C : Sal.Emulation.Configuration (Core Γ).toCRDTSig) : Prop :=
  SHonestCore Γ (projCore₁ (D₂ := Stores) C)

/-- The shipped architecture's algebraic Join layer composes. This theorem is
strictly weaker than the desired Peritext flagship: it says nothing yet about
rendered rich-text intent or mark-aware state collection. -/
theorem core_join_at {Γ : OrderedPrefixCode}
    {C : Sal.Emulation.Configuration (Core Γ).toCRDTSig}
    (h : CoreHonest Γ C) : JoinLemma3At (Core Γ) C := by
  apply joinLemma3At_prod
  · exact s_join_at h
  · apply joinLemma3At_prod
    · exact OSCore_joinLemma3 _
    · exact OSCore_joinLemma3 _

/-- Issuer policy for the shipped product shape. Text operations retain the
sided kernel's anchor/freshness guard. Mark adds must use their event timestamp
as mark id and name two live text endpoints; mark removals must name a live
mark. These cross-component checks cannot be expressed by `prodPred`. -/
def coreGuard (Γ : OrderedPrefixCode)
    (e : Op (Core Γ).AppOp) (s : (Core Γ).State) : Prop :=
  match e.2.2 with
  | Sum.inl (.ins el π a sd) =>
      sApplicable (e.1, e.2.1, .ins el π a sd) s.1
  | Sum.inl (.del _) => False
  | Sum.inr (Sum.inl (OSOp.add x)) =>
      x ∈ sIds s.1 ∧ ∀ q : OSElem ℕ,
        q ∈ (show OSState ℕ from s.2.1) → q.2.2 ≠ x
  | Sum.inr (Sum.inl (OSOp.rem _)) => False
  | Sum.inr (Sum.inr (OSOp.add m)) =>
      m.mid = e.1 ∧ m.start_id ∈ sIds s.1 ∧ m.end_id ∈ sIds s.1 ∧
      (∀ q : OSElem ℕ, q ∈ (show OSState ℕ from s.2.1) →
        q.2.2 ≠ m.start_id ∧ q.2.2 ≠ m.end_id) ∧
      ∀ q : OSElem MarkD,
        q ∈ (show OSState MarkD from s.2.2) → q.2.2.mid ≠ m.mid
  | Sum.inr (Sum.inr (OSOp.rem _)) => False

/-- Visibility-respecting lists remain visibility-respecting after projecting
away mark events. -/
private theorem respects_vis_proj₁ {Γ : OrderedPrefixCode}
    {C : Sal.Emulation.Configuration (Core Γ).toCRDTSig}
    {ρ : List (Op (Core Γ).AppOp)} (h : respects ρ C.vis) :
    respects (projList₁ ρ) (projCore₁ (D₂ := Stores) C).vis := by
  unfold respects at h ⊢
  unfold projList₁
  rw [List.pairwise_filterMap]
  refine h.imp ?_
  intro x y hxy a hxa b hyb
  rw [oplOp_eq_some] at hxa hyb
  subst hxa
  subst hyb
  exact fun hv => hxy hv

/-- Product mint evidence projects to the exact sided mint evidence consumed
by `sidedGeneration`. -/
theorem mintHonest_text {Γ : OrderedPrefixCode} {C : Configuration (Core Γ)}
    (h : MintHonest (Core Γ) (coreGuard Γ) (Configuration.core C)) :
    MintHonest (S Γ) sApplicable
      (Configuration.core (projConf₁ (D₂ := Stores) C)) := by
  intro e he
  have he' : e ∈ (projCore₁ (D₂ := Stores) (Configuration.core C)).events := he
  obtain ⟨π, hp, hr, hg⟩ := h (inlOp e) (mem_projCore₁_events.mp he')
  refine ⟨projList₁ π, ?_, respects_vis_proj₁ hr, ?_⟩
  · have hp' := listPermOf_projList₁ hp
    have hset : evRes₁ {e' ∈ (Configuration.core C).events |
        (Configuration.core C).vis e' (inlOp e)} =
        {e' ∈ (Configuration.core (projConf₁ (D₂ := Stores) C)).events |
          (Configuration.core (projConf₁ (D₂ := Stores) C)).vis e' e} :=
      Set.ext fun x => and_congr mem_projConf₁_events.symm Iff.rfl
    exact hset ▸ hp'
  · rcases e with ⟨t, r, o⟩
    cases o with
    | ins el p a sd =>
        simpa [Core, Stores, coreGuard, applySeq_prod] using hg
    | del x =>
        exact False.elim (by simpa [coreGuard] using hg)

/-- The product generation contract exposes cross-component mark validity but
uses only the text projection to discharge the current Join premise. -/
def coreGeneration (Γ : OrderedPrefixCode) : GenerationContract (Core Γ) where
  Guard := coreGuard Γ
  History := fun C => CoreHonest Γ (Configuration.core C)
  history_of_mint := by
    intro C h
    exact sHonest_core ((sidedGeneration Γ).history_of_mint _ (mintHonest_text h))

-- PASS: both projections are the intended runtime components.
example (Γ : OrderedPrefixCode) :
    (Core Γ).State = (SState × (OSState ℕ × OSState MarkD)) := rfl

def guardMark : MarkD :=
  { mid := 2, mtype := .bold, start_id := 1, end_id := 1 }

-- PASS: a fresh mark over a live endpoint is admitted.
example :
    coreGuard Sal.EmbedRGA.unaryCode
      (2, 0, Sum.inr (Sum.inr (OSOp.add guardMark)))
      ([(1, 65, [])], ((∅ : OSState ℕ), (∅ : OSState MarkD))) := by
  simp [coreGuard, guardMark, sIds]

-- FAIL: the same mark cannot be generated before its endpoint exists.
example :
    ¬ coreGuard Sal.EmbedRGA.unaryCode
      (2, 0, Sum.inr (Sum.inr (OSOp.add guardMark)))
      ([], ((∅ : OSState ℕ), (∅ : OSState MarkD))) := by
  simp [coreGuard, guardMark, sIds]

#print axioms core_join_at
#print axioms mintHonest_text
#print axioms coreGeneration

end Sal.ConditionedMRDTs.PeritextSided
