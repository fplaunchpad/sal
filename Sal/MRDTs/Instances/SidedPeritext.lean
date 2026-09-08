import Sal.MRDTs.Instances.FinsetStore
import Sal.MRDTs.Instances.ProductionRGA
import Sal.MRDTs.Instances.PeritextRender

/-!
# Runtime-shaped Sided Peritext core

The logical state has three components: sided text, a grow-only set of
character deletions, and a grow-only set of immutable mark events. The sole
public resolve-conflict relation lifts the sided-RGA conflicts on text events;
the evidence-store and cross-component pairs commute and therefore receive
\`Either\`.
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
  query := renderState
  merge := (Core Γ).merge

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

/-- Issuance provenance for the mixed rich-text datatype projects to genuine
SidedEmbedRGA issuance provenance.  This is stronger than the honesty-only
projection above and lets the public legalization proof reuse the component
certificate. -/
theorem mintHonest_text {Γ : OrderedPrefixCode}
    {C : Configuration (Core Γ)}
    (h : MintHonest (Core Γ) (coreGuard Γ) C) :
    MintHonest (S Γ) sApplicable (projConf₁ C) := by
  intro e he
  have heC : inlOp e ∈ C.events := mem_projConf₁_events.mp he
  obtain ⟨π, hp, hr, hg⟩ := h (inlOp e) heC
  refine ⟨projList₁ π, ?_, ?_, ?_⟩
  · constructor
    · exact nodup_projList₁ hp.1
    · intro a
      rw [mem_projList₁, hp.2]
      constructor
      · rintro ⟨ha, hvis⟩
        exact ⟨mem_projConf₁_events.mpr ha, hvis⟩
      · rintro ⟨ha, hvis⟩
        exact ⟨mem_projConf₁_events.mp ha, hvis⟩
  · exact respects_projList₁_of (fun _ _ hvis => hvis) hr
  · rw [applySeq_prod] at hg
    rcases e with ⟨t, r, op⟩
    cases op with
    | ins el pref anchor side =>
        simpa [coreGuard, inlOp, Core, Stores, DeleteStore, MarkStore, sFold]
          using hg
    | del target =>
        exact False.elim (by simpa [coreGuard, inlOp] using hg)

def generation (Γ : OrderedPrefixCode) : Issuance (Core Γ) where
  CanIssue := coreGuard Γ

/-! ## Independent sequential editor machine -/

abbrev RichState := List (Nat × Nat) × (Finset Nat × Finset MarkEvent)

def richSpec : SequentialMachine (Op (SOp ⊕ (Nat ⊕ MarkEvent))) where
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
      rw [SequentialMachine.run_append_single, ih]
      rcases e with ⟨t, r, e | e⟩
      · simp [richSpec, projList₁, projList₂, oplOp, oprOp,
          SequentialMachine.run_append_single, ProductionRGA.sidedSpec]
      · rcases e with e | e
        · simp [richSpec, projList₁, projList₂, oplOp, oprOp,
            SequentialMachine.run_append_single, FinsetStore.spec]
        · simp [richSpec, projList₁, projList₂, oplOp, oprOp,
            SequentialMachine.run_append_single, FinsetStore.spec]

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
    · simpa [ProductionRGA.sidedSpec, SequentialMachine.run,
        sSpecFold, sFold] using sided_seq_read (Γ := Γ) htext
    · rfl

/-! ## Public merged-history specification -/

/-- The mixed witness first legalizes the text projection, then replays the
two grow-only evidence stores.  All three cross-component classes commute. -/
def coreCanonical
    (ops : List (Op (SOp ⊕ (Nat ⊕ MarkEvent)))) :
    List (Op (SOp ⊕ (Nat ⊕ MarkEvent))) :=
  (ProductionRGA.SidedWitness.canonical (projList₁ ops)).map inlOp ++
    (projList₂ ops).map inrOp

@[simp] theorem projList₁_coreCanonical
    (ops : List (Op (SOp ⊕ (Nat ⊕ MarkEvent)))) :
    projList₁ (coreCanonical ops) =
      ProductionRGA.SidedWitness.canonical (projList₁ ops) := by
  simp [coreCanonical]

@[simp] theorem projList₂_coreCanonical
    (ops : List (Op (SOp ⊕ (Nat ⊕ MarkEvent)))) :
    projList₂ (coreCanonical ops) = projList₂ ops := by
  simp [coreCanonical]

def coreSemanticCommutes
    (a b : Op (SOp ⊕ (Nat ⊕ MarkEvent))) : Prop :=
  match a.2.2, b.2.2 with
  | .inl x, .inl y =>
      ProductionRGA.sidedSemanticCommutes
        (a.1, a.2.1, x) (b.1, b.2.1, y)
  | _, _ => True

@[simp] theorem coreSemanticCommutes_inl_inr
    (a : Op SOp) (b : Op (Nat ⊕ MarkEvent)) :
    coreSemanticCommutes (inlOp (A₂ := Nat ⊕ MarkEvent) a)
      (inrOp (A₁ := SOp) b) := by
  rcases a with ⟨ta, ra, a⟩
  rcases b with ⟨tb, rb, b⟩
  simp [coreSemanticCommutes, inlOp, inrOp]

@[simp] theorem coreSemanticCommutes_inr_inl
    (a : Op (Nat ⊕ MarkEvent)) (b : Op SOp) :
    coreSemanticCommutes (inrOp (A₁ := SOp) a)
      (inlOp (A₂ := Nat ⊕ MarkEvent) b) := by
  rcases a with ⟨ta, ra, a⟩
  rcases b with ⟨tb, rb, b⟩
  simp [coreSemanticCommutes, inlOp, inrOp]

@[simp] theorem coreSemanticCommutes_inr_inr
    (a b : Op (Nat ⊕ MarkEvent)) :
    coreSemanticCommutes (inrOp (A₁ := SOp) a)
      (inrOp (A₁ := SOp) b) := by
  rcases a with ⟨ta, ra, a⟩
  rcases b with ⟨tb, rb, b⟩
  simp [coreSemanticCommutes, inlOp, inrOp]

theorem coreSemanticCommutes_symm
    (a b : Op (SOp ⊕ (Nat ⊕ MarkEvent))) :
    coreSemanticCommutes a b ↔ coreSemanticCommutes b a := by
  obtain ⟨ats₀, ar, aop⟩ := a
  obtain ⟨bt, br, bop⟩ := b
  cases aop <;> cases bop <;>
    simp [coreSemanticCommutes,
      ProductionRGA.sidedSemanticCommutes_symm]

def coreRcOrder
    (a b : Op (SOp ⊕ (Nat ⊕ MarkEvent))) : RcRes :=
  match a.2.2, b.2.2 with
  | .inl x, .inl y =>
      ProductionRGA.sidedRcOrder
        (a.1, a.2.1, x) (b.1, b.2.1, y)
  | _, _ => .Either

noncomputable def coreRc (Γ : OrderedPrefixCode) :
    ReplayPolicy (Core Γ).toUpdateSig where
  order := coreRcOrder

@[simp] theorem coreRc_order_inl (Γ : OrderedPrefixCode)
    (a b : Op SOp) :
    (coreRc Γ).order
        (inlOp (A₂ := Nat ⊕ MarkEvent) a)
        (inlOp (A₂ := Nat ⊕ MarkEvent) b) =
      (ProductionRGA.sidedRc Γ).order a b := by
  rcases a with ⟨ta, ra, a⟩
  rcases b with ⟨tb, rb, b⟩
  rfl

@[simp] theorem coreRc_conflict_inl (Γ : OrderedPrefixCode)
    (a b : Op SOp) :
    ((coreRc Γ).Before (inlOp (A₂ := Nat ⊕ MarkEvent) a)
        (inlOp (A₂ := Nat ⊕ MarkEvent) b) ∨
      (coreRc Γ).Before (inlOp (A₂ := Nat ⊕ MarkEvent) b)
        (inlOp (A₂ := Nat ⊕ MarkEvent) a)) ↔
      ((ProductionRGA.sidedRc Γ).Before a b ∨
        (ProductionRGA.sidedRc Γ).Before b a) := by
  simp

@[simp] theorem coreRc_conflicts_inl_inr (Γ : OrderedPrefixCode)
    (a : Op SOp) (b : Op (Nat ⊕ MarkEvent)) :
    ¬ ((coreRc Γ).Before (inlOp (A₂ := Nat ⊕ MarkEvent) a)
        (inrOp (A₁ := SOp) b) ∨
      (coreRc Γ).Before (inrOp (A₁ := SOp) b)
        (inlOp (A₂ := Nat ⊕ MarkEvent) a)) := by
  rcases a with ⟨ta, ra, a⟩
  rcases b with ⟨tb, rb, b⟩
  simp [coreRc, coreRcOrder, inlOp, inrOp, ReplayPolicy.Before]

@[simp] theorem coreRc_conflicts_inr_inl (Γ : OrderedPrefixCode)
    (a : Op (Nat ⊕ MarkEvent)) (b : Op SOp) :
    ¬ ((coreRc Γ).Before (inrOp (A₁ := SOp) a)
        (inlOp (A₂ := Nat ⊕ MarkEvent) b) ∨
      (coreRc Γ).Before (inlOp (A₂ := Nat ⊕ MarkEvent) b)
        (inrOp (A₁ := SOp) a)) := by
  rcases a with ⟨ta, ra, a⟩
  rcases b with ⟨tb, rb, b⟩
  simp [coreRc, coreRcOrder, inlOp, inrOp, ReplayPolicy.Before]

@[simp] theorem coreRc_conflicts_inr_inr (Γ : OrderedPrefixCode)
    (a b : Op (Nat ⊕ MarkEvent)) :
    ¬ ((coreRc Γ).Before (inrOp (A₁ := SOp) a)
        (inrOp (A₁ := SOp) b) ∨
      (coreRc Γ).Before (inrOp (A₁ := SOp) b)
        (inrOp (A₁ := SOp) a)) := by
  rcases a with ⟨ta, ra, a⟩
  rcases b with ⟨tb, rb, b⟩
  simp [coreRc, coreRcOrder, inrOp, ReplayPolicy.Before]

theorem coreRc_inl_iff {Γ : OrderedPrefixCode}
    {C : Sal.MRDTs.Foundation.ReplayContext (Core Γ).toUpdateSig}
    (E : Set (Op (SOp ⊕ (Nat ⊕ MarkEvent))))
    (a b : Op SOp) :
    @loOn _ (coreRc Γ) C E (inlOp a) (inlOp b) ↔
      @loOn _ (ProductionRGA.sidedRc Γ) (projReplayContext₁ C)
        (evRes₁ E) a b := by
  constructor
  · rintro (⟨hvis, hconf⟩ | ⟨hnv, hnv', hrc, habs⟩)
    · exact Or.inl ⟨hvis, (coreRc_conflict_inl Γ _ _).mp hconf⟩
    · refine Or.inr ⟨hnv, hnv', by simpa using hrc, ?_⟩
      rintro ⟨e₃, he₃, hvis₃, hconf₃⟩
      exact habs ⟨inlOp e₃, he₃, hvis₃,
        (coreRc_conflict_inl Γ _ _).mpr hconf₃⟩
  · rintro (⟨hvis, hconf⟩ | ⟨hnv, hnv', hrc, habs⟩)
    · exact Or.inl ⟨hvis, (coreRc_conflict_inl Γ _ _).mpr hconf⟩
    · refine Or.inr ⟨hnv, hnv', by simpa using hrc, ?_⟩
      rintro ⟨e₃, he₃, hvis₃, hconf₃⟩
      rcases op_sum_cases e₃ with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · exact habs ⟨c, he₃, hvis₃,
          (coreRc_conflict_inl Γ _ _).mp hconf₃⟩
      · exact (coreRc_conflicts_inl_inr Γ b c) hconf₃

theorem coreRc_inr_false {Γ : OrderedPrefixCode}
    {C : Sal.MRDTs.Foundation.ReplayContext (Core Γ).toUpdateSig}
    (E : Set (Op (SOp ⊕ (Nat ⊕ MarkEvent))))
    (a b : Op (Nat ⊕ MarkEvent)) :
    ¬ @loOn _ (coreRc Γ) C E (inrOp a) (inrOp b) := by
  rintro (⟨_, hconf⟩ | ⟨_, _, hrc, _⟩)
  · exact (coreRc_conflicts_inr_inr Γ a b) hconf
  · rcases a with ⟨ta, ra, a⟩
    rcases b with ⟨tb, rb, b⟩
    simpa [coreRc, coreRcOrder, inrOp] using hrc

theorem coreRc_cross_rl_false {Γ : OrderedPrefixCode}
    {C : Sal.MRDTs.Foundation.ReplayContext (Core Γ).toUpdateSig}
    (E : Set (Op (SOp ⊕ (Nat ⊕ MarkEvent))))
    (b : Op (Nat ⊕ MarkEvent)) (a : Op SOp) :
    ¬ @loOn _ (coreRc Γ) C E (inrOp b) (inlOp a) := by
  rintro (⟨_, hconf⟩ | ⟨_, _, hrc, _⟩)
  · exact (coreRc_conflicts_inr_inl Γ b a) hconf
  · rcases a with ⟨ta, ra, a⟩
    rcases b with ⟨tb, rb, b⟩
    simpa [coreRc, coreRcOrder, inlOp, inrOp] using hrc

theorem coreRespects_projList₁ {Γ : OrderedPrefixCode}
    {C : Sal.MRDTs.Foundation.ReplayContext (Core Γ).toUpdateSig}
    {E : Set (Op (Core Γ).AppOp)} {ops : List (Op (Core Γ).AppOp)}
    (h : respects ops (@loOn _ (coreRc Γ) C E)) :
    respects (projList₁ ops)
      (@loOn _ (ProductionRGA.sidedRc Γ) (projReplayContext₁ C) (evRes₁ E)) := by
  unfold respects at h ⊢
  unfold projList₁
  rw [List.pairwise_filterMap]
  refine h.imp ?_
  intro x y hxy a hxa b hyb
  rw [oplOp_eq_some] at hxa hyb
  subst x
  subst y
  exact fun hlo => hxy ((coreRc_inl_iff E b a).mpr hlo)

theorem coreIsCanonicalState_proj₁ {Γ : OrderedPrefixCode}
    {C : Sal.MRDTs.Foundation.ReplayContext (Core Γ).toUpdateSig}
    {E : Set (Op (Core Γ).AppOp)} {s : (Core Γ).State}
    (h : @IsCanonicalState _ (coreRc Γ) C E s) :
    @IsCanonicalState _ (ProductionRGA.sidedRc Γ)
      (projReplayContext₁ C) (evRes₁ E) s.1 := by
  obtain ⟨ops, hp, hr, hf⟩ := h
  exact ⟨projList₁ ops, listPermOf_projList₁ hp,
    coreRespects_projList₁ hr,
    congrArg Prod.fst ((applySeq_prod (Core Γ).init ops).symm.trans hf)⟩

theorem coreIsCanonicalState_proj₂ {Γ : OrderedPrefixCode}
    {C : Sal.MRDTs.Foundation.ReplayContext (Core Γ).toUpdateSig}
    {E : Set (Op (Core Γ).AppOp)} {s : (Core Γ).State}
    (h : @IsCanonicalState _ (coreRc Γ) C E s) :
    IsCanonicalState (projReplayContext₂ C) (evRes₂ E) s.2 := by
  obtain ⟨ops, hp, _, hf⟩ := h
  refine ⟨projList₂ ops, listPermOf_projList₂ hp, ?_,
    congrArg Prod.snd ((applySeq_prod (Core Γ).init ops).symm.trans hf)⟩
  unfold respects
  exact List.pairwise_of_forall fun _ _ => by
    simp [loOn, UpdateSig.rc, ReplayPolicy.Before,
      ReplayPolicy.default, ReplayPolicy.unconstrained]

theorem coreCanonical_glue {Γ : OrderedPrefixCode}
    {C : Sal.MRDTs.Foundation.ReplayContext (Core Γ).toUpdateSig}
    {E : Set (Op (Core Γ).AppOp)}
    {s₁ : (S Γ).State} {s₂ : Stores.State}
    (h₁ : @IsCanonicalState _ (ProductionRGA.sidedRc Γ)
      (projReplayContext₁ C) (evRes₁ E) s₁)
    (h₂ : IsCanonicalState (projReplayContext₂ C) (evRes₂ E) s₂) :
    @IsCanonicalState _ (coreRc Γ) C E (s₁, s₂) := by
  obtain ⟨ops₁, hp₁, hr₁, hf₁⟩ := h₁
  obtain ⟨ops₂, hp₂, _, hf₂⟩ := h₂
  refine ⟨ops₁.map inlOp ++ ops₂.map inrOp, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hp₁.1.map inlOp_injective, hp₂.1.map inrOp_injective, ?_⟩
    intro x hx y hy
    rw [List.mem_map] at hx hy
    obtain ⟨a, _, rfl⟩ := hx
    obtain ⟨b, _, rfl⟩ := hy
    exact inlOp_ne_inrOp a b
  · intro x
    rw [List.mem_append, List.mem_map, List.mem_map]
    constructor
    · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
      · exact (hp₁.2 a).mp ha
      · exact (hp₂.2 b).mp hb
    · intro hx
      rcases op_sum_cases x with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · exact Or.inl ⟨a, (hp₁.2 a).mpr hx, rfl⟩
      · exact Or.inr ⟨b, (hp₂.2 b).mpr hx, rfl⟩
  · unfold respects
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_map]
      exact hr₁.imp fun {x y} h hlo => h ((coreRc_inl_iff E y x).mp hlo)
    · rw [List.pairwise_map]
      exact List.pairwise_of_forall fun x y => coreRc_inr_false E y x
    · intro x hx y hy
      rw [List.mem_map] at hx hy
      obtain ⟨a, _, rfl⟩ := hx
      obtain ⟨b, _, rfl⟩ := hy
      exact coreRc_cross_rl_false E b a
  · rw [applySeq_prod, projList₁_append, projList₂_append,
      projList₁_map_inlOp, projList₁_map_inrOp,
      projList₂_map_inlOp, projList₂_map_inrOp, List.append_nil]
    show (applySeq (S Γ).toUpdateSig (S Γ).init ops₁,
      applySeq Stores.toUpdateSig Stores.init ops₂) = (s₁, s₂)
    rw [hf₁, hf₂]

theorem core_join_at {Γ : OrderedPrefixCode}
    {C : Sal.MRDTs.Foundation.ReplayContext (Core Γ).toUpdateSig}
    (h : SHonestCore Γ (projReplayContext₁ C)) :
    @JoinAt (Core Γ) (coreRc Γ) C := by
  intro ev₁ ev₂ s₀ s₁ s₂ htr hir hin₁ hin₂ hcl₁ hcl₂ h₀ hc₁ hc₂
  have hJ₁ := (@s_join_at Γ _ h) (evRes₁ ev₁) (evRes₁ ev₂)
    s₀.1 s₁.1 s₂.1
    (fun {a b c} hab hbc => htr hab hbc)
    (fun a hv => hir (inlOp a) hv)
    (fun a ha => mem_projReplayContext₁_events.mpr (hin₁ _ ha))
    (fun a ha => mem_projReplayContext₁_events.mpr (hin₂ _ ha))
    (fun a b hv hnc hb => hcl₁ (inlOp a) (inlOp b) hv
      (fun hc => hnc ((commutes_prod_inl_iff a b).mp hc)) hb)
    (fun a b hv hnc hb => hcl₂ (inlOp a) (inlOp b) hv
      (fun hc => hnc ((commutes_prod_inl_iff a b).mp hc)) hb)
    (coreIsCanonicalState_proj₁ h₀)
    (coreIsCanonicalState_proj₁ hc₁)
    (coreIsCanonicalState_proj₁ hc₂)
  have hJ₂ := (joinAt_prod (FinsetStore.join.at _)
      (FinsetStore.join.at _)) (evRes₂ ev₁) (evRes₂ ev₂)
    s₀.2 s₁.2 s₂.2
    (fun {a b c} hab hbc => htr hab hbc)
    (fun a hv => hir (inrOp a) hv)
    (fun a ha => mem_projReplayContext₂_events.mpr (hin₁ _ ha))
    (fun a ha => mem_projReplayContext₂_events.mpr (hin₂ _ ha))
    (fun a b hv hnc hb => hcl₁ (inrOp a) (inrOp b) hv
      (fun hc => hnc ((commutes_prod_inr_iff a b).mp hc)) hb)
    (fun a b hv hnc hb => hcl₂ (inrOp a) (inrOp b) hv
      (fun hc => hnc ((commutes_prod_inr_iff a b).mp hc)) hb)
    (coreIsCanonicalState_proj₂ h₀)
    (coreIsCanonicalState_proj₂ hc₁)
    (coreIsCanonicalState_proj₂ hc₂)
  exact coreCanonical_glue hJ₁ hJ₂

def replayAdequacy (Γ : OrderedPrefixCode) :
    @ReplayAdequacyCertificate (Core Γ) (generation Γ) (coreRc Γ) :=
  ReplayAdequacyCertificate.ofJoinOn
    (fun _ hGood => core_join_at hGood)
    (fun C hMint => by
      simpa only [projConf₁_core] using
        (sHonest_core (coreHonest_of_mint C hMint)))

theorem coreCanonicalConfig_proj₁ {Γ : OrderedPrefixCode}
    {C : Configuration (Core Γ)}
    (h : @CanonicalConfig _ (coreRc Γ) C) :
    @CanonicalConfig _ (ProductionRGA.sidedRc Γ) (projConf₁ C) where
  canonical := by
    intro v s E hv
    change (C.ver v).map (fun p => (p.1.1, evRes₁ p.2)) = some (s, E) at hv
    obtain ⟨p, hp, hpeq⟩ := Option.map_eq_some_iff.mp hv
    have hs : p.1.1 = s := congrArg Prod.fst hpeq
    have hE : evRes₁ p.2 = E := congrArg Prod.snd hpeq
    subst s
    subst E
    exact coreIsCanonicalState_proj₁ (C := C.replayContext)
      ((@CanonicalConfig.canonical _ (coreRc Γ) C h) v p.1 p.2 hp)
  vis_trans := fun hab hbc =>
    (@CanonicalConfig.vis_trans _ (coreRc Γ) C h) hab hbc
  vis_irrefl := fun a =>
    (@CanonicalConfig.vis_irrefl _ (coreRc Γ) C h) (inlOp a)
  version_events_supported := by
    intro v s E hv a ha
    rw [mem_projConf₁_events]
    change (C.ver v).map (fun p => (p.1.1, evRes₁ p.2)) = some (s, E) at hv
    obtain ⟨p, hp, hpeq⟩ := Option.map_eq_some_iff.mp hv
    have hE : evRes₁ p.2 = E := congrArg Prod.snd hpeq
    subst E
    exact (@CanonicalConfig.version_events_supported _ (coreRc Γ) C h)
      v p.1 p.2 hp (inlOp a) ha
  version_events_causal := by
    intro v s E hv a b hab hb
    change (C.ver v).map (fun p => (p.1.1, evRes₁ p.2)) = some (s, E) at hv
    obtain ⟨p, hp, hpeq⟩ := Option.map_eq_some_iff.mp hv
    have hE : evRes₁ p.2 = E := congrArg Prod.snd hpeq
    subst E
    exact (@CanonicalConfig.version_events_causal _ (coreRc Γ) C h)
      v p.1 p.2 hp
      (inlOp a) (inlOp b) hab hb

/-- The independent editor state and its legal histories.  Store additions
are total; the nontrivial legality is exactly the SidedEmbedRGA text
projection. Cross-component issuance still enforces valid deletion and mark
references at the replica API. -/
noncomputable def clientSpec (Γ : OrderedPrefixCode) : SequentialSpec (Core Γ) where
  toSequentialMachine := richSpec
  Legal := fun ops => ProductionRGA.sidedLegal Γ (projList₁ ops)
  query := fun q query => match query with
    | .inl _ => .inl ((q.1.filter (fun p => decide (p.1 ≠ 0))).map Prod.snd)
    | .inr storeQuery => .inr ((Stores).query q.2 storeQuery)

def coreRel (s : (Core Γ).State) (q : RichState) : Prop :=
  s.1.map sProj = q.1.filter (fun p => decide (p.1 ≠ 0)) ∧ s.2 = q.2

theorem coreCanonical_respects_of {Γ : OrderedPrefixCode}
    {C : Configuration (Core Γ)}
    (hgood : @CanonicalConfig _ (coreRc Γ) C)
    (hmintText : MintHonest (S Γ) sApplicable (projConf₁ C))
    {v : Version} {s : (Core Γ).State}
    {E : Set (Op (Core Γ).AppOp)}
    (hver : C.ver v = some (s, E))
    {ops : List (Op (Core Γ).AppOp)}
    (hperm : listPermOf ops E) :
    respects (coreCanonical ops)
      (@loOn _ (coreRc Γ) C.replayContext E) := by
  have hpver : (projConf₁ C).ver v = some (s.1, evRes₁ E) := by
    simp [projConf₁, hver]
  have htext := ProductionRGA.sidedCanonical_respects_of
    (coreCanonicalConfig_proj₁ hgood)
    (sHonest_core (sHonest_of_mint hmintText))
    hpver (listPermOf_projList₁ hperm)
  unfold respects at htext ⊢
  unfold coreCanonical
  rw [List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.pairwise_map]
    exact htext.imp fun {a b} hab hba =>
      hab (by
        simpa only [projConf₁_core] using
          ((coreRc_inl_iff (C := C.replayContext) E b a).mp hba))
  · induction projList₂ ops with
    | nil => exact List.Pairwise.nil
    | cons a rest ih =>
        rw [List.pairwise_map, List.pairwise_cons]
        refine ⟨?_, ?_⟩
        · intro b hb
          exact coreRc_inr_false E b a
        · simpa [List.pairwise_map] using ih
  · intro x hx y hy
    rw [List.mem_map] at hx hy
    obtain ⟨a, _, rfl⟩ := hx
    obtain ⟨b, _, rfl⟩ := hy
    exact coreRc_cross_rl_false E b a

theorem coreCanonical_respects {Γ : OrderedPrefixCode}
    {C : Configuration (Core Γ)}
    (exec : CertifiedExecution (Core Γ) (generation Γ) C)
    {v : Version} {s : (Core Γ).State}
    {E : Set (Op (Core Γ).AppOp)}
    (hver : C.ver v = some (s, E))
    {ops : List (Op (Core Γ).AppOp)}
    (hperm : listPermOf ops E) :
    respects (coreCanonical ops)
      (@loOn _ (coreRc Γ) C.replayContext E) := by
  apply coreCanonical_respects_of
    (exec.canonicalConfig (fun _ hmint =>
      core_join_at (by simpa only [projConf₁_core] using
        (sHonest_core (coreHonest_of_mint _ hmint)))))
    (mintHonest_text exec.mintHonest) hver hperm

theorem coreLegalizationSound (Γ : OrderedPrefixCode)
    {C : Configuration (Core Γ)}
    (hgood : @CanonicalConfig _ (coreRc Γ) C)
    (hmint : MintHonest (Core Γ) (coreGuard Γ) C)
    (replay : @HasReplayWitness _ (coreRc Γ) C) :
    IsSpecLinearizable (Core Γ) (coreRc Γ)
      (clientSpec Γ) coreRel C := by
    intro v s E hver
    obtain ⟨ops, hperm, hresp, hfold⟩ := replay v s E hver
    have hpver : (projConf₁ C).ver v = some (s.1, evRes₁ E) := by
      simp [projConf₁, hver]
    have hmintText := mintHonest_text hmint
    have hseq : sSeqOK Γ
        (ProductionRGA.SidedWitness.canonical (projList₁ ops)) :=
      ProductionRGA.sidedCanonical_seqOK_of
        (coreCanonicalConfig_proj₁ hgood) hmintText hpver
        (listPermOf_projList₁ hperm)
    have hlegal : (clientSpec Γ).Legal (coreCanonical ops) := by
      change ProductionRGA.sidedLegal Γ (projList₁ (coreCanonical ops))
      rw [projList₁_coreCanonical]
      exact ProductionRGA.sidedLegal_of_seqOK hseq
    have htextPerm := ProductionRGA.SidedWitness.canonical_listPermOf
      (listPermOf_projList₁ hperm)
    have hwholePerm : listPermOf (coreCanonical ops) E := by
      apply listPermOf_glue htextPerm (listPermOf_projList₂ hperm)
    have hrespText : respects (projList₁ ops)
        (@loOn _ (ProductionRGA.sidedRc Γ)
          (projReplayContext₁ C.replayContext) (evRes₁ E)) :=
      coreRespects_projList₁ hresp
    have hgoodText := coreCanonicalConfig_proj₁ hgood
    have hsub := hgoodText.version_events_supported v s.1 (evRes₁ E) hpver
    have hclosed := hgoodText.version_events_causal v s.1 (evRes₁ E) hpver
    have hhon : SHonestCore Γ (projConf₁ C).replayContext :=
      sHonest_core (sHonest_of_mint hmintText)
    have hwfReplay : SWf Γ (projList₁ ops) :=
      s_wf_of_enum hhon hsub
        (fun a b hvis _ hb => hclosed a b hvis hb)
        (listPermOf_projList₁ hperm) hrespText
    have hwfCanonical : SWf Γ
        (ProductionRGA.SidedWitness.canonical (projList₁ ops)) :=
      sWf_of_seqOK hseq
    have htextFold :
        sFold Γ (ProductionRGA.SidedWitness.canonical (projList₁ ops)) =
          sFold Γ (projList₁ ops) :=
      s_fold_canon Γ hwfCanonical hwfReplay
        (fun e => (htextPerm.2 e).trans
          ((listPermOf_projList₁ hperm).2 e).symm)
    have hfold' := hfold
    rw [applySeq_prod] at hfold'
    have hstateText :
        sFold Γ (ProductionRGA.SidedWitness.canonical (projList₁ ops)) =
          s.1 := by
      rw [htextFold]
      exact congrArg Prod.fst hfold'
    have hstateStores :
        applySeq Stores.toUpdateSig Stores.init (projList₂ ops) = s.2 :=
      congrArg Prod.snd hfold'
    have hstate : applySeq (Core Γ).toUpdateSig (Core Γ).init
        (coreCanonical ops) = s := by
      rw [applySeq_prod, projList₁_coreCanonical,
        projList₂_coreCanonical]
      apply Prod.ext
      · simpa [Core, sFold] using hstateText
      · simpa [Core, Stores] using hstateStores
    have hcanonHonest : (sequential Γ).Honest (coreCanonical ops) := by
      change sSeqOK Γ (projList₁ (coreCanonical ops))
      rw [projList₁_coreCanonical]
      exact hseq
    have hrel0 := (sequential Γ).sound (coreCanonical ops) hcanonHonest
    change coreRel
      (applySeq (Core Γ).toUpdateSig (Core Γ).init (coreCanonical ops))
      (richSpec.run (coreCanonical ops)) at hrel0
    have hrel : coreRel s ((clientSpec Γ).run (coreCanonical ops)) := by
      simpa [clientSpec, SequentialSpec.run] using hstate ▸ hrel0
    refine ⟨coreCanonical ops, hwholePerm,
      coreCanonical_respects_of hgood hmintText hver hperm,
      hlegal, hrel, ?_⟩
    intro query
    rcases query with textQuery | storeQuery
    · change Sum.inl (s.1.map (fun r => r.2.1)) =
        Sum.inl
          (((((clientSpec Γ).run (coreCanonical ops)).1).filter
            (fun p => decide (p.1 ≠ 0))).map Prod.snd)
      apply congrArg Sum.inl
      simpa [sProj, List.map_map, Function.comp_def] using
        congrArg (List.map Prod.snd) hrel.1
    · change Sum.inr (Stores.query s.2 storeQuery) =
        Sum.inr (Stores.query ((clientSpec Γ).run (coreCanonical ops)).2
          storeQuery)
      rw [hrel.2]

noncomputable def coreSequentialCorrectness (Γ : OrderedPrefixCode) :
    SequentialCorrectnessCertificate (Core Γ) (generation Γ)
      (coreRc Γ) (clientSpec Γ) coreRel where
  sound C exec replay :=
    coreLegalizationSound Γ
      (exec.canonicalConfig (fun _ hmint =>
        core_join_at (by simpa only [projConf₁_core] using
          (sHonest_core (coreHonest_of_mint _ hmint)))))
      exec.mintHonest replay

noncomputable def verified (Γ : OrderedPrefixCode) : VerifiedMRDT (Core Γ) where
  issuance := generation Γ
  rc := coreRc Γ
  replayAdequacy := replayAdequacy Γ
  Spec := clientSpec Γ
  Rel := coreRel
  sequentialCorrectness := coreSequentialCorrectness Γ

noncomputable def replayAdequate (Γ : OrderedPrefixCode) : ReplayAdequateMRDT (Core Γ) where
  issuance := generation Γ
  rc := coreRc Γ
  replayAdequacy := replayAdequacy Γ
  Machine := richSpec
  sequential := sequential Γ
  sequential_of_mint := fun _ h =>
    ProductionRGA.sidedSequential_of_mint (linearMint_text h)

theorem sequentially_correct {Γ : OrderedPrefixCode}
    (ops : List (Op (Core Γ).AppOp))
    (h : LinearMintHistory (Core Γ) (coreGuard Γ) ops) :
    (sequential Γ).Rel
      (applySeq (Core Γ).toUpdateSig (Core Γ).init ops)
      (richSpec.run ops) :=
  (replayAdequate Γ).sequentially_correct ops h

/-! ## Production-facing rich signature

The following package transfers the operational proofs to `RichCore`.  The
state, operations, update, merge, conflict relation, and ternary merge are
definitionally the same; only client queries differ.
-/

def asCoreConfig {Γ : OrderedPrefixCode}
    (C : Configuration (RichCore Γ)) : Configuration (Core Γ) where
  vis := C.vis
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
  head_alloc := C.head_alloc
  gca_events := C.gca_events

def RichCoreHonest (Γ : OrderedPrefixCode)
    (C : Configuration (RichCore Γ)) : Prop := CoreHonest Γ (asCoreConfig C)

/-- The abstract rich document contains only the text sequence exposed by the
sequential machine.  It does not depend on the implementation's path field. -/
def richDocumentOf (q : RichState) : PeritextRender.DocD where
  shadow :=
    (q.1.filter (fun p => decide (p.1 ≠ 0))).map
      (fun p => (p.1, p.2, ([] : List Bool)))
  deleted := q.2.1.toList

/-- Client specification for the production query boundary.  It shares the
independent editor transition system with `clientSpec`, but observes rendered
rich text rather than exposing the three component stores. -/
noncomputable def richClientSpec (Γ : OrderedPrefixCode) :
    SequentialSpec (RichCore Γ) where
  toSequentialMachine := richSpec
  Legal := fun ops => ProductionRGA.sidedLegal Γ (projList₁ ops)
  query := fun q kind =>
    PeritextRender.renderMarksDoc (richDocumentOf q) q.2.2.toList kind

def richRel (s : (RichCore Γ).State) (q : RichState) : Prop :=
  coreRel s q

noncomputable def richRc (Γ : OrderedPrefixCode) :
    ReplayPolicy (RichCore Γ).toUpdateSig :=
  coreRc Γ

theorem documentOf_eq_richDocumentOf {Γ : OrderedPrefixCode}
    {s : (Core Γ).State} {q : RichState} (h : coreRel s q) :
    documentOf s = richDocumentOf q := by
  apply congrArg₂ PeritextRender.DocD.mk
  · rw [← h.1]
    simp [documentOf, richDocumentOf, sProj, List.map_map,
      Function.comp_def]
  · exact congrArg (fun x : Finset Nat => x.toList)
      (congrArg Prod.fst h.2)

theorem mintHonest_to_core {Γ : OrderedPrefixCode}
    {C : Configuration (RichCore Γ)}
    (h : MintHonest (RichCore Γ) (coreGuard Γ) C) :
    MintHonest (Core Γ) (coreGuard Γ) (asCoreConfig C) := by
  intro e he
  obtain ⟨π, hp, hr, hg⟩ := h e (by simpa [asCoreConfig] using he)
  exact ⟨π, by simpa [asCoreConfig] using hp,
    by simpa [asCoreConfig] using hr, by simpa [RichCore] using hg⟩

theorem canonicalConfig_to_core {Γ : OrderedPrefixCode}
    {C : Configuration (RichCore Γ)}
    (h : @CanonicalConfig _ (richRc Γ) C) :
    @CanonicalConfig _ (coreRc Γ) (asCoreConfig C) := by
  letI : ReplayPolicy (Core Γ).toUpdateSig := coreRc Γ
  refine {
    canonical := ?_
    vis_trans := (@CanonicalConfig.vis_trans _ (richRc Γ) C h)
    vis_irrefl := (@CanonicalConfig.vis_irrefl _ (richRc Γ) C h)
    version_events_supported := ?_
    version_events_causal := ?_ }
  ·
    intro v s E hver
    simpa [richRc, RichCore, asCoreConfig] using
      ((@CanonicalConfig.canonical _ (richRc Γ) C h)
        v s E (by simpa [asCoreConfig] using hver))
  ·
    intro v s E hver
    exact (@CanonicalConfig.version_events_supported _ (richRc Γ) C h)
      v s E (by simpa [asCoreConfig] using hver)
  ·
    intro v s E hver
    exact (@CanonicalConfig.version_events_causal _ (richRc Γ) C h)
      v s E (by simpa [asCoreConfig] using hver)

def richGeneration (Γ : OrderedPrefixCode) : Issuance (RichCore Γ) where
  CanIssue := coreGuard Γ

def asCoreFoundation {Γ : OrderedPrefixCode}
    (C : Sal.MRDTs.Foundation.ReplayContext (RichCore Γ).toUpdateSig) :
    Sal.MRDTs.Foundation.ReplayContext (Core Γ).toUpdateSig where
  L := C.L
  vis := C.vis
  timestamps_distinct := C.timestamps_distinct
  vis_total_same_replica := C.vis_total_same_replica

theorem rich_join_at {Γ : OrderedPrefixCode}
    {C : Sal.MRDTs.Foundation.ReplayContext (RichCore Γ).toUpdateSig}
    (h : SHonestCore Γ (projReplayContext₁ (asCoreFoundation C))) :
    @JoinAt (RichCore Γ) (richRc Γ) C := by
  have hc := core_join_at (Γ := Γ) h
  simpa [RichCore, asCoreFoundation] using hc

def richReplayAdequacy (Γ : OrderedPrefixCode) :
    @ReplayAdequacyCertificate (RichCore Γ) (richGeneration Γ)
      (richRc Γ) :=
  ReplayAdequacyCertificate.ofJoinOn
    (fun _ hGood => rich_join_at hGood)
    (fun C hMint => by
      simpa [RichCoreHonest, asCoreConfig, asCoreFoundation]
        using sHonest_core
          (coreHonest_of_mint (asCoreConfig C) (mintHonest_to_core hMint)))

def richSequential (Γ : OrderedPrefixCode) :
    SequentialRefinement (RichCore Γ) richSpec where
  Honest := fun ops => sSeqOK Γ (projList₁ ops)
  Rel := (sequential Γ).Rel
  init := (sequential Γ).init
  sound := by
    intro ops h
    simpa [RichCore] using (sequential Γ).sound ops h

theorem richLegalizationSound (Γ : OrderedPrefixCode)
    {C : Configuration (RichCore Γ)}
    (hgood : @CanonicalConfig _ (richRc Γ) C)
    (hmint : MintHonest (RichCore Γ) (coreGuard Γ) C)
    (replay : @HasReplayWitness _ (richRc Γ) C) :
    IsSpecLinearizable (RichCore Γ) (richRc Γ)
      (richClientSpec Γ) richRel C := by
  have replayCore : @HasReplayWitness _ (coreRc Γ) (asCoreConfig C) := by
    simpa [richRc, RichCore, asCoreConfig] using replay
  have certifiedCore := coreLegalizationSound Γ
    (canonicalConfig_to_core hgood) (mintHonest_to_core hmint) replayCore
  intro v s E hver
  have hverCore : (asCoreConfig C).ver v = some (s, E) := by
    simpa [asCoreConfig] using hver
  obtain ⟨ops, hperm, hresp, hlegal, hrel, _⟩ :=
    certifiedCore v s E hverCore
  refine ⟨ops, hperm, ?_, ?_, hrel, ?_⟩
  · simpa [richRc, asCoreConfig, RichCore] using hresp
  · simpa [richClientSpec, clientSpec] using hlegal
  · intro kind
    change renderState s kind =
      PeritextRender.renderMarksDoc
        (richDocumentOf ((richClientSpec Γ).run ops))
        ((richClientSpec Γ).run ops).2.2.toList kind
    have hdoc := documentOf_eq_richDocumentOf hrel
    rw [renderState, hdoc, hrel.2]
    simp [richClientSpec, clientSpec, SequentialSpec.run]

noncomputable def richSequentialCorrectness (Γ : OrderedPrefixCode) :
    SequentialCorrectnessCertificate (RichCore Γ) (richGeneration Γ)
      (richRc Γ) (richClientSpec Γ) richRel where
  sound C exec replay :=
    richLegalizationSound Γ
      (exec.canonicalConfig (fun C' hmint => rich_join_at (by
        simpa [RichCoreHonest, asCoreConfig, asCoreFoundation]
          using sHonest_core
            (coreHonest_of_mint (asCoreConfig C')
              (mintHonest_to_core (by
                simpa [richGeneration] using hmint))))))
      exec.mintHonest replay

noncomputable def richVerified (Γ : OrderedPrefixCode) :
    VerifiedMRDT (RichCore Γ) where
  issuance := richGeneration Γ
  rc := richRc Γ
  replayAdequacy := richReplayAdequacy Γ
  Spec := richClientSpec Γ
  Rel := richRel
  sequentialCorrectness := richSequentialCorrectness Γ

theorem linearMint_to_core {Γ : OrderedPrefixCode}
    {ops : List (Op (RichCore Γ).AppOp)}
    (h : LinearMintHistory (RichCore Γ) (coreGuard Γ) ops) :
    LinearMintHistory (Core Γ) (coreGuard Γ) ops := by
  constructor
  · intro pre e post heq
    simpa [RichCore] using h.guarded pre e post heq
  · exact h.clocked

noncomputable def richReplayAdequate (Γ : OrderedPrefixCode) : ReplayAdequateMRDT (RichCore Γ) where
  issuance := richGeneration Γ
  rc := richRc Γ
  replayAdequacy := richReplayAdequacy Γ
  Machine := richSpec
  sequential := richSequential Γ
  sequential_of_mint := fun _ h =>
    ProductionRGA.sidedSequential_of_mint (linearMint_text (linearMint_to_core h))

theorem rich_sequentially_correct {Γ : OrderedPrefixCode}
    (ops : List (Op (RichCore Γ).AppOp))
    (h : LinearMintHistory (RichCore Γ) (coreGuard Γ) ops) :
    (richSequential Γ).Rel
      (applySeq (RichCore Γ).toUpdateSig (RichCore Γ).init ops)
      (richSpec.run ops) :=
  (richReplayAdequate Γ).sequentially_correct ops h

#print axioms coreHonest_of_mint
#print axioms core_join_at
#print axioms replayAdequacy
#print axioms replayAdequate
#print axioms sequentially_correct
#print axioms richVerified
#print axioms richReplayAdequate
#print axioms rich_sequentially_correct

end
end Sal.MRDTs.Instances.SidedPeritext
