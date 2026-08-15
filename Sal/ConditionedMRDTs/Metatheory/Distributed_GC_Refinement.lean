import Sal.ConditionedMRDTs.Metatheory.Distributed_GC
import Sal.ConditionedMRDTs.Metatheory.UnifiedVerifiedMRDT

/-!
# End-to-end distributed commit-GC refinement

This file connects the storage protocol in `Distributed_GC.lean` to the full
datatype-rich `Step3` semantics. A state contains:

* one semantic `Configuration D`, which is the source of materialized states,
  events, parents, and observable queries; and
* one physical commit holding per replica.

Fetch and local GC are silent. A visible conditioned-MRDT step must satisfy
`StepAvailable`: the acting replica physically holds every version that the
step may read. The semantic step is an actual `Step3`, not a reconstructed or
postulated label. Erasure therefore produces a genuine `Steps D` execution.

The runtime is the reality oracle: `sync.js` fetches immutable commits and
`ingest` recomputes their states, while `replica.js` prunes only the physical
DAG. This theorem validates the model relative to those trusted definitions;
it does not verify the JavaScript implementation.
-/

namespace Sal.ConditionedMRDTs

open Classical
open Sal.Emulation

variable {D : ConditionedMRDTSig}

/-- A datatype-rich semantic configuration plus separate physical holdings. -/
structure DistributedConfig (D : ConditionedMRDTSig) where
  core : Configuration D
  stores : DistributedWorld

/-- Every physically held version has a materialization in the semantic core,
and every registered semantic head is the corresponding local physical head. -/
def DistributedConfig.WellFormed (S : DistributedConfig D) : Prop :=
  (∀ r v, v ∈ (S.stores r).commits → (S.core.ver v).isSome) ∧
  (∀ r v, S.core.head r = some v →
    (S.stores r).head = v ∧ v ∈ (S.stores r).commits)

/-- Versions required by a visible `Step3` action are physically available at
the acting replica. Merge requires both heads and one materialized LCA. -/
def StepAvailable (S : DistributedConfig D) : Label3 D → Prop
  | .createReplica r => (0 : Version) ∈ (S.stores r).commits
  | .apply _ r _ => ∀ v, S.core.head r = some v → v ∈ (S.stores r).commits
  | .merge r₁ r₂ =>
      ∀ v₁ v₂, S.core.head r₁ = some v₁ → S.core.head r₂ = some v₂ →
        v₁ ∈ (S.stores r₁).commits ∧ v₂ ∈ (S.stores r₁).commits ∧
        ∃ vT, IsLCA S.core.parents v₁ v₂ vT ∧
          vT ∈ (S.stores r₁).commits
  | .query r _ _ => ∀ v, S.core.head r = some v → v ∈ (S.stores r).commits

/-- Install a newly authored head and record its immutable provenance. -/
def installAuthoredHead (L : DistributedLocal) (author : Replica) (v : Version) :
    DistributedLocal where
  self := L.self
  head := v
  commits := insert v L.commits
  roster := L.roster
  authors := insert author L.authors
  authored := fun r => if r = author then insert v (L.authored r) else L.authored r
  head_present := Set.mem_insert v L.commits
  self_registered := L.self_registered
  authored_present := by
    intro r w hw
    by_cases hr : r = author
    · subst r
      simp only [if_pos] at hw
      rcases hw with rfl | hw
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (L.authored_present author hw)
    · simp only [if_neg hr] at hw
      exact Set.mem_insert_of_mem _ (L.authored_present r hw)

/-- Physical-store effect of a visible semantic step. A visible transition may
add only the actor's new head; it cannot fabricate arbitrary allocated commits.
Fetch remains the only rule that imports remote history. -/
def VisibleStoreEvolution (S S' : DistributedConfig D) : Label3 D → Prop
  | .createReplica r =>
      S'.core.head r = some 0 ∧
      S'.stores = Function.update S.stores r (installHead (S.stores r) 0)
  | .apply _ r _ =>
      ∃ v, S'.core.head r = some v ∧
        S'.stores = Function.update S.stores r
          (installAuthoredHead (S.stores r) r v)
  | .merge r₁ _ =>
      ∃ v, S'.core.head r₁ = some v ∧
        S'.stores = Function.update S.stores r₁ (installHead (S.stores r₁) v)
  | .query _ _ _ => S'.stores = S.stores

/-- Distributed operational semantics. Storage steps are silent (`none`). A
visible step carries an actual conditioned `Step3` derivation. `WellFormed` is
required on both sides so a trace cannot manufacture an unmaterialized local
commit merely to satisfy availability. -/
inductive DistributedConfigStep (D : ConditionedMRDTSig) :
    DistributedConfig D → Option (Label3 D) → DistributedConfig D → Prop where
  | fetch (S : DistributedConfig D) (src dst : Replica)
      (hWF : S.WellFormed)
      (hWF' : (DistributedConfig.mk S.core
        (Function.update S.stores dst
          (receive (S.stores dst) (advertise (S.stores src))))).WellFormed) :
      DistributedConfigStep D S none
        ⟨S.core, Function.update S.stores dst
          (receive (S.stores dst) (advertise (S.stores src)))⟩
  | gc (S : DistributedConfig D) (r : Replica)
      (cert : LocalGCCertificate S.core.parents (S.stores r))
      (hWF : S.WellFormed)
      (hWF' : (DistributedConfig.mk S.core
        (Function.update S.stores r
          (collect S.core.parents (S.stores r) cert))).WellFormed) :
      DistributedConfigStep D S none
        ⟨S.core, Function.update S.stores r
          (collect S.core.parents (S.stores r) cert)⟩
  | visible {S S' : DistributedConfig D} {ℓ : Label3 D}
      (hWF : S.WellFormed) (hAvail : StepAvailable S ℓ)
      (hCore : Step3 D S.core ℓ S'.core)
      (hStores : VisibleStoreEvolution S S' ℓ) (hWF' : S'.WellFormed) :
      DistributedConfigStep D S (some ℓ) S'

/-- Finite traces of the distributed semantics. -/
inductive DistributedConfigSteps (D : ConditionedMRDTSig) :
    DistributedConfig D → List (Option (Label3 D)) → DistributedConfig D → Prop where
  | nil (S : DistributedConfig D) : DistributedConfigSteps D S [] S
  | cons {S S' S'' : DistributedConfig D} {ℓ : Option (Label3 D)}
      {ℓs : List (Option (Label3 D))} :
      DistributedConfigStep D S ℓ S' →
      DistributedConfigSteps D S' ℓs S'' →
      DistributedConfigSteps D S (ℓ :: ℓs) S''

/-- Remove silent fetch/GC labels. -/
def eraseDistributedLabels : List (Option (Label3 D)) → List (Label3 D) :=
  List.filterMap id

/-- Main end-to-end refinement: every finite execution of the distributed
storage protocol erases to a genuine execution of the full conditioned MRDT
semantics. Fetch and GC stutter; visible apply/merge/query/create steps are
preserved label for label. -/
theorem distributedConfig_refines_Step3
    {S₀ S₁ : DistributedConfig D} {ℓs : List (Option (Label3 D))}
    (hRun : DistributedConfigSteps D S₀ ℓs S₁) :
    Steps D S₀.core (eraseDistributedLabels ℓs) S₁.core := by
  induction hRun with
  | nil => exact Steps.nil _
  | cons hStep _ ih =>
      cases hStep with
      | fetch => simpa [eraseDistributedLabels] using ih
      | gc => simpa [eraseDistributedLabels] using ih
      | visible _ _ hCore _ _ =>
          simpa [eraseDistributedLabels] using Steps.cons hCore ih

/-- Queries are never available merely because the semantic head exists: the
physical replica must hold that head. This is the load-bearing negative gate. -/
theorem query_unavailable_without_head (S : DistributedConfig D)
    (r : Replica) (q : D.Query) (value : D.Value) (v : Version)
    (hHead : S.core.head r = some v) (hMissing : v ∉ (S.stores r).commits) :
    ¬ StepAvailable S (.query r q value) := by
  intro h
  exact hMissing (h v hHead)

/-- PASS control: well-formedness supplies query availability at every
registered head. -/
theorem query_available_of_wellFormed (S : DistributedConfig D)
    (hWF : S.WellFormed) (r : Replica) (q : D.Query) (value : D.Value) :
    StepAvailable S (.query r q value) := by
  intro v hv
  exact (hWF.2 r v hv).2

/-! ## Generation-certified distributed execution -/

/-- A distributed step with exactly the provenance required by
`MintCertifiedReach3`. Silent fetch/GC steps owe no generation premise because
they leave the semantic `Configuration` unchanged. -/
inductive MintCertifiedDistributedConfigStep (D : ConditionedMRDTSig)
    (G : GenerationContract D) :
    DistributedConfig D → Option (Label3 D) → DistributedConfig D → Prop where
  | silent {S S' : DistributedConfig D} :
      DistributedConfigStep D S none S' →
      MintCertifiedDistributedConfigStep D G S none S'
  | visible {S S' : DistributedConfig D} {ℓ : Label3 D} :
      DistributedConfigStep D S (some ℓ) S' →
      MintHonest D G.Guard (Configuration.core S.core) →
      GuardedStep3 D G S.core ℓ S'.core →
      MintHonest D G.Guard (Configuration.core S'.core) →
      MintCertifiedDistributedConfigStep D G S (some ℓ) S'

inductive MintCertifiedDistributedConfigSteps (D : ConditionedMRDTSig)
    (G : GenerationContract D) : DistributedConfig D →
    List (Option (Label3 D)) → DistributedConfig D → Prop where
  | nil (S : DistributedConfig D) : MintCertifiedDistributedConfigSteps D G S [] S
  | cons {S S' S'' : DistributedConfig D} {ℓ : Option (Label3 D)}
      {ℓs : List (Option (Label3 D))} :
      MintCertifiedDistributedConfigStep D G S ℓ S' →
      MintCertifiedDistributedConfigSteps D G S' ℓs S'' →
      MintCertifiedDistributedConfigSteps D G S (ℓ :: ℓs) S''

theorem MintCertifiedDistributedConfigStep.toRaw
    {G : GenerationContract D} {S S' : DistributedConfig D}
    {ℓ : Option (Label3 D)}
    (h : MintCertifiedDistributedConfigStep D G S ℓ S') :
    DistributedConfigStep D S ℓ S' := by
  cases h with
  | silent hs => exact hs
  | visible hs => exact hs

theorem MintCertifiedDistributedConfigSteps.toRaw
    {G : GenerationContract D} {S S' : DistributedConfig D}
    {ℓs : List (Option (Label3 D))}
    (h : MintCertifiedDistributedConfigSteps D G S ℓs S') :
    DistributedConfigSteps D S ℓs S' := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons hs.toRaw ih

private theorem mintCertifiedReach_follow_distributed
    {G : GenerationContract D} {hInit : D.Inv D.init}
    {S₀ S₁ : DistributedConfig D} {ℓs : List (Option (Label3 D))}
    (hStart : MintCertifiedReach3 D G hInit S₀.core)
    (hRun : MintCertifiedDistributedConfigSteps D G S₀ ℓs S₁) :
    MintCertifiedReach3 D G hInit S₁.core := by
  induction hRun with
  | nil => exact hStart
  | cons hs _ ih =>
      cases hs with
      | silent hSilent =>
          cases hSilent with
          | fetch => exact ih hStart
          | gc => exact ih hStart
      | visible _ hPre hGuard hPost =>
          exact ih (.step hStart hPre hGuard hPost)

/-- Generic generation lift. Starting at `initConfig`, a certified distributed
execution produces the repository's existing `MintCertifiedReach3`; no second
honesty or reachability predicate is introduced. -/
theorem mintCertifiedReach_of_distributed
    {G : GenerationContract D} {hInit : D.Inv D.init}
    {S₀ S₁ : DistributedConfig D} {ℓs : List (Option (Label3 D))}
    (hCore : S₀.core = initConfig D hInit)
    (hRun : MintCertifiedDistributedConfigSteps D G S₀ ℓs S₁) :
    MintCertifiedReach3 D G hInit S₁.core := by
  apply mintCertifiedReach_follow_distributed (hRun := hRun)
  rw [hCore]
  exact .init

/-- The generic distributed result exported to clients of a unified
certificate. -/
structure DistributedVerifiedResult (V : UnifiedVerifiedMRDT D)
    (C : Configuration D) : Prop where
  mintCertified : MintCertifiedReach3 D V.generation V.verified.initInv C
  raLinearizable : IsRALinearizable3 C
  safe : VersionsSafe V.safety C
  observable : VersionsObservable V.safety C

theorem UnifiedVerifiedMRDT.distributed
    (V : UnifiedVerifiedMRDT D) {S₀ S₁ : DistributedConfig D}
    {ℓs : List (Option (Label3 D))}
    (hCore : S₀.core = initConfig D V.verified.initInv)
    (hRun : MintCertifiedDistributedConfigSteps D V.generation S₀ ℓs S₁) :
    DistributedVerifiedResult V S₁.core := by
  have hMint := mintCertifiedReach_of_distributed hCore hRun
  exact ⟨hMint, V.ra_linearizable hMint, V.safe hMint, V.observable hMint⟩

/-- The reusable theorem shape instantiated by production datatypes. -/
def DistributedCorrectness (V : UnifiedVerifiedMRDT D) : Prop :=
  ∀ {S₀ S₁ : DistributedConfig D} {ℓs : List (Option (Label3 D))},
    S₀.core = initConfig D V.verified.initInv →
    MintCertifiedDistributedConfigSteps D V.generation S₀ ℓs S₁ →
    DistributedVerifiedResult V S₁.core

theorem UnifiedVerifiedMRDT.distributedCorrectness
    (V : UnifiedVerifiedMRDT D) : DistributedCorrectness V :=
  fun hCore hRun => V.distributed hCore hRun

/-- Sequential intent remains the certificate's history theorem. The
distributed package reuses it unchanged rather than claiming that one global
sequential order represents every concurrent execution. -/
theorem UnifiedVerifiedMRDT.distributedSequential
    (V : UnifiedVerifiedMRDT D) (ops : List (Op D.AppOp))
    (hHonest : V.verified.seq.Honest ops) :
    V.verified.seq.Rel (applySeq D.toCRDTSig D.init ops)
      (V.verified.Spec.run ops) :=
  V.verified.sequential ops hHonest

end Sal.ConditionedMRDTs

#print axioms Sal.ConditionedMRDTs.distributedConfig_refines_Step3
#print axioms Sal.ConditionedMRDTs.query_unavailable_without_head
#print axioms Sal.ConditionedMRDTs.mintCertifiedReach_of_distributed
#print axioms Sal.ConditionedMRDTs.UnifiedVerifiedMRDT.distributed
