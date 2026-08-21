import Sal.MRDTs.Instances.FinsetStore
import Sal.MRDTs.Instances.ProductionRGA
import Sal.MRDTs.Instances.PeritextRender

/-!
# Runtime-shaped Sided Peritext core

The logical state has three components: sided text, a grow-only set of
character deletions, and a grow-only set of immutable mark events.  Compact
Fugue gap evidence belongs to the optional state-GC representation, not to the
raw MRDT signature.
-/

namespace Sal.MRDTs.Instances.SidedPeritext

open Sal.MRDTs.Foundation
open Sal.EmbedRGA (OrderedPrefixCode)
open Sal.MRDTs.Instances.SidedEmbedRGA
open Classical

noncomputable section

abbrev MarkEvent := PeritextRender.MarkD

abbrev DeleteStore := FinsetStore.D Nat
abbrev MarkStore := FinsetStore.D MarkEvent
abbrev Stores := prodSig DeleteStore MarkStore
abbrev Core (Γ : OrderedPrefixCode) := prodSig (S Γ) Stores

/-- Rich client read over the three internal components.  The semantic MRDT
used by the state-GC theorem exposes this view, never the raw insertion shadow
or the grow-only evidence stores. -/
def documentOf (s : (Core Γ).State) : PeritextRender.DocD where
  shadow := s.1.map fun r => (r.1, r.2.1, ([] : List Bool))
  deleted := s.2.1.toList

def renderState (s : (Core Γ).State) (kind : PeritextRender.MType) :
    List (Nat × Bool) :=
  PeritextRender.renderMarksDoc (documentOf s) s.2.2.toList kind

/-- Production-facing signature.  Its operational carrier is exactly
`Core`; only the query boundary is narrowed to the rich document read. -/
def RichCore (Γ : OrderedPrefixCode) : MRDTSig where
  State := (Core Γ).State
  dec_state := (Core Γ).dec_state
  init := (Core Γ).init
  AppOp := (Core Γ).AppOp
  dec_op := (Core Γ).dec_op
  Query := PeritextRender.MType
  Value := List (Nat × Bool)
  update := (Core Γ).update
  merge := (Core Γ).merge
  query := renderState
  rc := (Core Γ).rc
  mergeL := (Core Γ).mergeL
  merge_init_slice := (Core Γ).merge_init_slice

/-- Cross-component issuer guard. Native text deletion is disabled: logical
deletion is an addition to `DeleteStore`, preserving the insertion shadow
needed by the Fugue policy and state collector. -/
def coreGuard (Γ : OrderedPrefixCode)
    (e : Op (Core Γ).AppOp) (s : (Core Γ).State) : Prop := by
  change Op (SOp ⊕ (Nat ⊕ MarkEvent)) at e
  change SState × (Finset Nat × Finset MarkEvent) at s
  exact match e.2.2 with
    | .inl (.ins el pref anchor side) =>
        sApplicable (e.1, e.2.1, .ins el pref anchor side) s.1
    | .inl (.del _) => False
    | .inr (.inl deleted) =>
        deleted ∈ sIds s.1 ∧ deleted ∉ s.2.1
    | .inr (.inr mark) =>
        mark.mid = e.1 ∧
        mark.start_id ∈ sIds s.1 ∧ mark.end_id ∈ sIds s.1 ∧
        mark.start_id ∉ s.2.1 ∧ mark.end_id ∉ s.2.1 ∧
        ∀ old ∈ s.2.2, old.mid ≠ mark.mid

def CoreHonest (Γ : OrderedPrefixCode) (C : Configuration (Core Γ)) : Prop :=
  SHonest Γ (projConf₁ C)

theorem coreHonest_of_mint {Γ : OrderedPrefixCode}
    (C : Configuration (Core Γ))
    (h : MintHonest (Core Γ) (coreGuard Γ) C) : CoreHonest Γ C := by
  apply sHonest_of_applicable
  intro e he
  have heC : inlOp e ∈ C.events := mem_projConf₁_events.mp he
  obtain ⟨π, hp, _hr, hg⟩ := h (inlOp e) heC
  refine ⟨projList₁ π, ?_, ?_⟩
  · constructor
    · exact nodup_projList₁ hp.1
    · intro a
      rw [mem_projList₁, hp.2]
      constructor
      · rintro ⟨ha, hv⟩
        exact ⟨mem_projConf₁_events.mpr ha, hv⟩
      · rintro ⟨ha, hv⟩
        exact ⟨mem_projConf₁_events.mp ha, hv⟩
  · rw [applySeq_prod] at hg
    rcases e with ⟨t, r, op⟩
    cases op with
    | ins el pref anchor side =>
        simpa [coreGuard, inlOp, Core, Stores, DeleteStore, MarkStore, sFold]
          using hg
    | del x =>
        exact False.elim (by simpa [coreGuard, inlOp] using hg)

def generation (Γ : OrderedPrefixCode) : GenerationContract (Core Γ) where
  Guard := coreGuard Γ
  History := CoreHonest Γ
  history_of_mint := coreHonest_of_mint

theorem core_join_at {Γ : OrderedPrefixCode}
    {C : Sal.MRDTs.Foundation.Configuration (Core Γ).toCRDTSig}
    (h : SHonestCore Γ (projCore₁ C)) : JoinLemma3At (Core Γ) C := by
  apply joinLemma3At_prod
  · exact s_join_at h
  · apply joinLemma3At_prod
    · exact FinsetStore.join.at _
    · exact FinsetStore.join.at _

def convergence (Γ : OrderedPrefixCode) :
    ConvergenceCertificate (Core Γ) (generation Γ) where
  sound := fun h => (isRALinearizable_iff_join _ _).mpr
    (ra_of_mintCertified
      (fun C hH => core_join_at (sHonest_core hH)) h)
  soundV := fun h => (isRALinearizable_iff_join _ _).mpr
    (ra_of_mintCertifiedV
      (fun C hH => core_join_at (sHonest_core hH)) h)

/-! ## Independent sequential editor machine -/

abbrev RichState := List (Nat × Nat) × (Finset Nat × Finset MarkEvent)

def richSpec : SequentialSpec (Op (SOp ⊕ (Nat ⊕ MarkEvent))) where
  State := RichState
  init := ([(0, 0)], (∅, ∅))
  step q e :=
    match e.2.2 with
    | .inl text => (sSpecStep q.1 (e.1, e.2.1, text), q.2)
    | .inr (.inl deleted) => (q.1, (insert deleted q.2.1, q.2.2))
    | .inr (.inr mark) => (q.1, (q.2.1, insert mark q.2.2))

private theorem richRun_eq (ops : List (Op (SOp ⊕ (Nat ⊕ MarkEvent)))) :
    richSpec.run ops =
      (ProductionRGA.sidedSpec.run (projList₁ ops),
        (FinsetStore.spec.run (projList₁ (projList₂ ops)),
         FinsetStore.spec.run (projList₂ (projList₂ ops)))) := by
  induction ops using List.reverseRecOn with
  | nil => rfl
  | append_singleton ops e ih =>
      rw [SequentialSpec.run_append_single, ih]
      rcases e with ⟨t, r, e | e⟩
      · simp [richSpec, projList₁, projList₂, oplOp, oprOp,
          SequentialSpec.run_append_single, ProductionRGA.sidedSpec]
      · rcases e with e | e
        · simp [richSpec, projList₁, projList₂, oplOp, oprOp,
            SequentialSpec.run_append_single, FinsetStore.spec]
        · simp [richSpec, projList₁, projList₂, oplOp, oprOp,
            SequentialSpec.run_append_single, FinsetStore.spec]

private theorem split_projList₁ {A₁ A₂ : Type}
    {ops : List (Op (A₁ ⊕ A₂))} {pre : List (Op A₁)}
    {e : Op A₁} {post : List (Op A₁)}
    (h : projList₁ ops = pre ++ e :: post) :
    ∃ pre' post', ops = pre' ++ inlOp e :: post' ∧ projList₁ pre' = pre := by
  change List.filterMap oplOp ops = pre ++ e :: post at h
  obtain ⟨l₁, rest, hops, hl₁, hrest⟩ :=
    List.filterMap_eq_append_iff.mp h
  obtain ⟨skip, a, tail, hr, hskip, ha, _⟩ :=
    List.filterMap_eq_cons_iff.mp hrest
  have hae : a = inlOp e := oplOp_eq_some.mp ha
  subst a
  refine ⟨l₁ ++ skip, tail, ?_, ?_⟩
  · rw [hops, hr, List.append_assoc]
  · change List.filterMap oplOp (l₁ ++ skip) = pre
    rw [List.filterMap_append, hl₁]
    have hempty : List.filterMap oplOp skip = [] := by
      simpa only [List.filterMap_eq_nil_iff] using hskip
    rw [hempty, List.append_nil]

theorem linearMint_text {Γ : OrderedPrefixCode}
    {ops : List (Op (Core Γ).AppOp)}
    (h : LinearMintHistory (Core Γ) (coreGuard Γ) ops) :
    LinearMintHistory (S Γ) sApplicable (projList₁ ops) := by
  constructor
  · intro pre e post heq
    obtain ⟨pre', post', hops, hpre⟩ := split_projList₁ heq
    have hg := h.guarded pre' (inlOp e) post' hops
    rw [applySeq_prod, hpre] at hg
    rcases e with ⟨t, r, op⟩
    cases op with
    | ins el pref anchor side =>
        simpa [coreGuard, inlOp, Core, Stores, DeleteStore, MarkStore, sFold]
          using hg
    | del x => exact False.elim (by simpa [coreGuard, inlOp] using hg)
  · intro pre e post heq old hold
    obtain ⟨pre', post', hops, hpre⟩ := split_projList₁ heq
    apply h.clocked pre' (inlOp e) post' hops (inlOp old)
    exact mem_projList₁.mp (hpre ▸ hold)

def sequential (Γ : OrderedPrefixCode) :
    SequentialRefinement (Core Γ) richSpec where
  Honest := fun ops => sSeqOK Γ (projList₁ ops)
  Rel s q :=
    s.1.map sProj = q.1.filter (fun p => decide (p.1 ≠ 0)) ∧ s.2 = q.2
  init := by
    constructor
    · rfl
    · rfl
  sound := by
    intro ops htext
    rw [richRun_eq, applySeq_prod, applySeq_prod]
    constructor
    · simpa [ProductionRGA.sidedSpec, SequentialSpec.run,
        sSpecFold, sFold] using sided_seq_read (Γ := Γ) htext
    · rfl

noncomputable def verified (Γ : OrderedPrefixCode) : VerifiedMRDT (Core Γ) where
  generation := generation Γ
  convergence := convergence Γ
  Spec := richSpec
  sequential := sequential Γ
  sequential_of_mint := fun _ h =>
    ProductionRGA.sidedSequential_of_mint (linearMint_text h)
  safety := SafetyCertificate.trivial (generation Γ)

theorem sequentially_correct {Γ : OrderedPrefixCode}
    (ops : List (Op (Core Γ).AppOp))
    (h : LinearMintHistory (Core Γ) (coreGuard Γ) ops) :
    (sequential Γ).Rel
      (applySeq (Core Γ).toCRDTSig (Core Γ).init ops)
      (richSpec.run ops) :=
  (verified Γ).sequentially_correct ops h

/-! ## Production-facing rich signature

The following package transfers the operational proofs to `RichCore`.  The
state, operations, update, merge, conflict relation, and ternary merge are
definitionally the same; only client queries differ.
-/

def asCoreConfig {Γ : OrderedPrefixCode}
    (C : Configuration (RichCore Γ)) : Configuration (Core Γ) where
  N := C.N
  L := C.L
  vis := C.vis
  dom_eq := C.dom_eq
  vis_src := C.vis_src
  vis_tgt := C.vis_tgt
  vis_causal := C.vis_causal
  timestamps_distinct := C.timestamps_distinct
  causal_mono := C.causal_mono
  vis_total_same_replica := C.vis_total_same_replica
  ver := C.ver
  head := C.head
  parents := C.parents
  parents_lt := C.parents_lt
  ver_init := by simpa [RichCore] using C.ver_init
  head_coherent := C.head_coherent
  lca_events := C.lca_events

def RichCoreHonest (Γ : OrderedPrefixCode)
    (C : Configuration (RichCore Γ)) : Prop := CoreHonest Γ (asCoreConfig C)

theorem mintHonest_to_core {Γ : OrderedPrefixCode}
    {C : Configuration (RichCore Γ)}
    (h : MintHonest (RichCore Γ) (coreGuard Γ) C) :
    MintHonest (Core Γ) (coreGuard Γ) (asCoreConfig C) := by
  intro e he
  obtain ⟨π, hp, hr, hg⟩ := h e (by simpa [asCoreConfig] using he)
  exact ⟨π, by simpa [asCoreConfig] using hp,
    by simpa [asCoreConfig] using hr, by simpa [RichCore] using hg⟩

def richGeneration (Γ : OrderedPrefixCode) : GenerationContract (RichCore Γ) where
  Guard := coreGuard Γ
  History := RichCoreHonest Γ
  history_of_mint := fun _ h => coreHonest_of_mint _ (mintHonest_to_core h)

def asCoreFoundation {Γ : OrderedPrefixCode}
    (C : Sal.MRDTs.Foundation.Configuration (RichCore Γ).toCRDTSig) :
    Sal.MRDTs.Foundation.Configuration (Core Γ).toCRDTSig where
  N := C.N
  L := C.L
  vis := C.vis
  dom_eq := C.dom_eq
  vis_src := C.vis_src
  vis_tgt := C.vis_tgt
  vis_causal := C.vis_causal
  timestamps_distinct := C.timestamps_distinct
  vis_total_same_replica := C.vis_total_same_replica

theorem rich_join_at {Γ : OrderedPrefixCode}
    {C : Sal.MRDTs.Foundation.Configuration (RichCore Γ).toCRDTSig}
    (h : SHonestCore Γ (projCore₁ (asCoreFoundation C))) :
    JoinLemma3At (RichCore Γ) C := by
  have hc := core_join_at (Γ := Γ) h
  simpa [RichCore, asCoreFoundation] using hc

def richConvergence (Γ : OrderedPrefixCode) :
    ConvergenceCertificate (RichCore Γ) (richGeneration Γ) where
  sound := fun h => (isRALinearizable_iff_join _ _).mpr
    (ra_of_mintCertified
      (fun C hH => rich_join_at (by
        simpa [RichCoreHonest, asCoreConfig, asCoreFoundation]
          using sHonest_core hH)) h)
  soundV := fun h => (isRALinearizable_iff_join _ _).mpr
    (ra_of_mintCertifiedV
      (fun C hH => rich_join_at (by
        simpa [RichCoreHonest, asCoreConfig, asCoreFoundation]
          using sHonest_core hH)) h)

def richSequential (Γ : OrderedPrefixCode) :
    SequentialRefinement (RichCore Γ) richSpec where
  Honest := fun ops => sSeqOK Γ (projList₁ ops)
  Rel := (sequential Γ).Rel
  init := (sequential Γ).init
  sound := by
    intro ops h
    simpa [RichCore] using (sequential Γ).sound ops h

theorem linearMint_to_core {Γ : OrderedPrefixCode}
    {ops : List (Op (RichCore Γ).AppOp)}
    (h : LinearMintHistory (RichCore Γ) (coreGuard Γ) ops) :
    LinearMintHistory (Core Γ) (coreGuard Γ) ops := by
  constructor
  · intro pre e post heq
    simpa [RichCore] using h.guarded pre e post heq
  · exact h.clocked

noncomputable def richVerified (Γ : OrderedPrefixCode) : VerifiedMRDT (RichCore Γ) where
  generation := richGeneration Γ
  convergence := richConvergence Γ
  Spec := richSpec
  sequential := richSequential Γ
  sequential_of_mint := fun _ h =>
    ProductionRGA.sidedSequential_of_mint (linearMint_text (linearMint_to_core h))
  safety := SafetyCertificate.trivial (richGeneration Γ)

theorem rich_sequentially_correct {Γ : OrderedPrefixCode}
    (ops : List (Op (RichCore Γ).AppOp))
    (h : LinearMintHistory (RichCore Γ) (coreGuard Γ) ops) :
    (richSequential Γ).Rel
      (applySeq (RichCore Γ).toCRDTSig (RichCore Γ).init ops)
      (richSpec.run ops) :=
  (richVerified Γ).sequentially_correct ops h

#print axioms coreHonest_of_mint
#print axioms core_join_at
#print axioms convergence
#print axioms verified
#print axioms sequentially_correct
#print axioms richVerified
#print axioms rich_sequentially_correct

end
end Sal.MRDTs.Instances.SidedPeritext
