import Sal.MRDTs.Paper1.EventBridge

/-!
# Operation labels and pointwise `ops`

The paper's operation label may contain identifiers as well as an application
payload. This module moves the arguments previously supplied by an event-label
translation into the operation itself. Issued events carry those arguments;
`ops` only reads the operation field. The implementation and policy inspect
the original payload, and the independent specification reads its arguments.

The encoding is injective even when the specification ignores some arguments.
The configuration and history transport below therefore preserves event
identity, visibility, the concrete paper order, and query answers.
-/
namespace Sal.MRDTs.Paper1.OperationLabels
open Foundation

variable {D : MRDTSig} {U : Type}

/-- The complete operation label: application payload and specification inputs. -/
abbrev Operation (D : MRDTSig) (U : Type) := D.AppOp × U

def erase (e : Op (Operation D U)) : Op D.AppOp := (e.time, e.rep, e.op.1)

/-- Constructed when the original event is issued, not chosen during replay. -/
def issue (args : Op D.AppOp → U) (e : Op D.AppOp) : Op (Operation D U) :=
  (e.time, e.rep, (e.op, args e))

@[simp] theorem erase_issue (args : Op D.AppOp → U) (e : Op D.AppOp) :
    erase (issue args e) = e := rfl

theorem issue_injective (args : Op D.AppOp → U) : Function.Injective (issue args) :=
  fun _ _ h => by simpa using congrArg erase h

/-- Literal pointwise operation projection, as in the manuscript. -/
def ops {A : Type} (events : List (Op A)) : List A := events.map Op.op

def datatype (D : MRDTSig) (U : Type) [DecidableEq U] : MRDTSig where
  State := D.State
  dec_state := D.dec_state
  init := D.init
  AppOp := Operation D U
  dec_op := inferInstance
  Query := D.Query
  Value := D.Value
  update s e := D.update s (erase e)
  merge := D.merge
  query := D.query

def policy (P : OperationPolicy D.AppOp) : OperationPolicy (Operation D U) :=
  ⟨fun a b => P.before a.1 b.1⟩

def specification (S : HistorySpec U D.Query D.Value) :
    HistorySpec (Operation D U) D.Query D.Value := S.withInputs Prod.snd

variable [DecidableEq U]

@[simp] theorem update_issue (args : Op D.AppOp → U) (s : D.State) (e : Op D.AppOp) :
    (datatype D U).update s (issue args e) = D.update s e := rfl

@[simp] theorem commutes_issue (args : Op D.AppOp → U) (a b : Op D.AppOp) :
    (datatype D U).toUpdateSig.commutes (issue args a) (issue args b) ↔
      D.toUpdateSig.commutes a b := Iff.rfl

theorem fold_issue (args : Op D.AppOp → U) (s : D.State) (π : List (Op D.AppOp)) :
    applySeq (datatype D U).toUpdateSig s (π.map (issue args)) =
      applySeq D.toUpdateSig s π := by
  induction π generalizing s with
  | nil => rfl
  | cons e es ih => exact ih (D.update s e)

/-- Issuance checks that the carried arguments were computed from this event,
in addition to the datatype's original guard. -/
def issuance (args : Op D.AppOp → U) (I : Issuance D) : Issuance (datatype D U) :=
  ⟨fun e s => e.op.2 = args (erase e) ∧ I.CanIssue (erase e) s⟩

@[simp] theorem issuance_issue (args : Op D.AppOp → U) (I : Issuance D)
    (e : Op D.AppOp) (s : D.State) :
    (issuance args I).CanIssue (issue args e) s ↔ I.CanIssue e s := by
  simp [issuance, issue, erase, Op.op, Op.time, Op.rep]

/-- The consistency check excludes arguments invented independently of issuance. -/
theorem issuance_rejects_mismatch (args : Op D.AppOp → U) (I : Issuance D)
    (e : Op (Operation D U)) (s : D.State) (bad : e.op.2 ≠ args (erase e)) :
    ¬ (issuance args I).CanIssue e s := fun h => bad h.1

omit [DecidableEq U] in
/-- Adding arguments does not create application-policy edges. -/
@[simp] theorem policy_issue (args : Op D.AppOp → U) (P : OperationPolicy D.AppOp)
    (a b : Op D.AppOp) :
    (policy P).before (issue args a).op (issue args b).op ↔ P.before a.op b.op := Iff.rfl

/-- Query values are unchanged for every stored state. -/
@[simp] theorem query_same (s : D.State) (q : D.Query) :
    (datatype D U).query s q = D.query s q := rfl

private def versions (args : Op D.AppOp → U) (C : Configuration D) :=
  fun v => (C.ver v).map (fun x => (x.1, issue args '' x.2))

private theorem heads (args : Op D.AppOp → U) (C : Configuration D) (r : Replica) :
    headEventsFrom (D := datatype D U) (versions args C) C.head r =
      (C.headEvents r).map (Set.image (issue args)) := by
  cases hh : C.head r with
  | none => simp [headEventsFrom, Configuration.headEvents, versions, hh]
  | some v =>
    cases hv : C.ver v <;> simp [headEventsFrom, Configuration.headEvents, versions, hh, hv]

private theorem head_origin (args : Op D.AppOp → U) (C : Configuration D)
    {r : Replica} {E : Set (Op (Operation D U))}
    (h : headEventsFrom (D := datatype D U) (versions args C) C.head r = some E) :
    ∃ F, C.headEvents r = some F ∧ E = issue args '' F := by
  rw [heads] at h
  cases he : C.headEvents r with
  | none => simp [he] at h
  | some F => exact ⟨F, rfl, (Option.some.inj (by simpa [he] using h)).symm⟩

/-- Same stored states, version graph and replicas; each event now carries its
complete operation label. No new execution or issuance assumption is added. -/
def configuration (args : Op D.AppOp → U) (C : Configuration D) :
    Configuration (datatype D U) where
  vis a b := ∃ x y, a = issue args x ∧ b = issue args y ∧ C.vis x y
  ver := versions args C
  head := C.head
  parents := C.parents
  parents_lt := C.parents_lt
  ver_init := by simp [versions, C.ver_init, datatype]
  head_alloc := by
    intro r v h
    simpa [versions] using C.head_alloc r v h
  vis_src := by
    rintro a b ⟨x,y,rfl,rfl,h⟩
    obtain ⟨r,F,hr,hx⟩ := C.vis_src h
    exact ⟨r,issue args '' F,by
      rw [heads]
      exact congrArg (Option.map (Set.image (issue args))) hr, ⟨x,hx,rfl⟩⟩
  vis_tgt := by
    rintro a b ⟨x,y,rfl,rfl,h⟩
    obtain ⟨r,F,hr,hy⟩ := C.vis_tgt h
    exact ⟨r,issue args '' F,by
      rw [heads]
      exact congrArg (Option.map (Set.image (issue args))) hr, ⟨y,hy,rfl⟩⟩
  vis_causal := by
    rintro a b r E ⟨x,y,rfl,rfl,h⟩ hr hb
    obtain ⟨F,hF,rfl⟩ := head_origin args C hr
    rcases hb with ⟨y',hy',eq⟩
    have : y' = y := issue_injective args eq
    subst y'
    exact ⟨x,C.vis_causal h hF hy',rfl⟩
  timestamps_distinct := by
    intro a b r E r' E' hr ha hr' hb ne
    obtain ⟨F,hF,rfl⟩ := head_origin args C hr
    obtain ⟨F',hF',rfl⟩ := head_origin args C hr'
    obtain ⟨x,hx,rfl⟩ := ha
    obtain ⟨y,hy,rfl⟩ := hb
    exact C.timestamps_distinct hF hx hF' hy (fun h => ne (congrArg (issue args) h))
  causal_mono := by
    rintro a b ⟨x,y,rfl,rfl,h⟩
    exact C.causal_mono h
  vis_total_same_replica := by
    intro a b r E r' E' hr ha hr' hb ne same
    obtain ⟨F,hF,rfl⟩ := head_origin args C hr
    obtain ⟨F',hF',rfl⟩ := head_origin args C hr'
    obtain ⟨x,hx,rfl⟩ := ha
    obtain ⟨y,hy,rfl⟩ := hb
    rcases C.vis_total_same_replica hF hx hF' hy
      (fun h => ne (congrArg (issue args) h)) same with h | h
    · exact Or.inl ⟨x,y,rfl,rfl,h⟩
    · exact Or.inr ⟨y,x,rfl,rfl,h⟩
  gca_events := by
    intro v₁ v₂ vT s₁ E₁ s₂ E₂ sT ET hg h₁ h₂ hT
    rcases Option.map_eq_some_iff.mp h₁ with ⟨⟨s₁',F₁⟩,hv₁,eq₁⟩
    rcases Option.map_eq_some_iff.mp h₂ with ⟨⟨s₂',F₂⟩,hv₂,eq₂⟩
    rcases Option.map_eq_some_iff.mp hT with ⟨⟨sT',FT⟩,hvT,eqT⟩
    cases eq₁; cases eq₂; cases eqT
    rw [C.gca_events hg hv₁ hv₂ hvT, Set.image_inter (issue_injective args)]

@[simp] theorem visibility_issue (args : Op D.AppOp → U) (C : Configuration D)
    (a b : Op D.AppOp) :
    (configuration args C).vis (issue args a) (issue args b) ↔ C.vis a b := by
  change (∃ x y, issue args a = issue args x ∧ issue args b = issue args y ∧ C.vis x y) ↔ _
  simp only [(issue_injective args).eq_iff]
  constructor
  · rintro ⟨x,y,rfl,rfl,h⟩; exact h
  · exact fun h => ⟨a,b,rfl,rfl,h⟩

theorem order_issue (args : Op D.AppOp → U) (P : OperationPolicy D.AppOp)
    (C : Configuration D) (E : Set (Op D.AppOp)) (a b : Op D.AppOp) :
    paperOrder (policy P) (configuration args C).replayContext
      (issue args '' E) (issue args a) (issue args b) ↔
    paperOrder P C.replayContext E a b := by
  simp only [paperOrder, Configuration.replayContext, visibility_issue, commutes_issue]
  have absorb : (∃ c ∈ issue args '' E, (configuration args C).vis (issue args b) c ∧
      ¬ (datatype D U).toUpdateSig.commutes (issue args b) c) ↔
      ∃ c ∈ E, C.vis b c ∧ ¬ D.toUpdateSig.commutes b c := by
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, hv, hn⟩
      exact ⟨c, hc, (visibility_issue args C b c).mp hv, hn⟩
    · rintro ⟨c, hc, hv, hn⟩
      exact ⟨issue args c, ⟨c, hc, rfl⟩, (visibility_issue args C b c).mpr hv, hn⟩
  constructor
  · rintro (h | ⟨ha,hb,hp,hn⟩)
    · exact Or.inl h
    · exact Or.inr ⟨ha,hb,hp,fun hc => hn (absorb.mpr hc)⟩
  · rintro (h | ⟨ha,hb,hp,hn⟩)
    · exact Or.inl h
    · exact Or.inr ⟨ha,hb,hp,fun hc => hn (absorb.mp hc)⟩

theorem labels_issue (args : Op D.AppOp → U) (S : HistorySpec U D.Query D.Value)
    (π : List (Op D.AppOp)) (q : D.Query) (v : D.Value) :
    (specification S).admits
      (projectedUpdates (D := datatype D U) (π.map (issue args)) ++ [.query q v]) ↔
    S.admits (projectedLabels args π ++ [.query q v]) := by
  simp [specification, HistorySpec.withInputs, projectedUpdates, projectedLabels,
    List.map_map, SeqLabel.mapUpdate, issue, Op.op, Function.comp_def]

omit [DecidableEq U] in
/-- `ops` reads the carried label; interpreting its second component gives the
same update history as the previous translation. -/
theorem ops_issue (args : Op D.AppOp → U) (π : List (Op D.AppOp)) :
    ops (π.map (issue args)) = π.map (fun e => (e.op, args e)) := by
  simp [ops, List.map_map, Function.comp_def, issue, Op.op]

omit [DecidableEq U] in
theorem permutation_issue (args : Op D.AppOp → U)
    {π : List (Op D.AppOp)} {E : Set (Op D.AppOp)} (h : listPermOf π E) :
    listPermOf (π.map (issue args)) (issue args '' E) := by
  refine ⟨h.1.map (issue_injective args), ?_⟩
  intro e
  simp only [List.mem_map, Set.mem_image]
  exact exists_congr (fun a => and_congr (h.2 a) Iff.rfl)

private theorem respects_order_issue (args : Op D.AppOp → U)
    (P : OperationPolicy D.AppOp) (C : Configuration D)
    {π : List (Op D.AppOp)} {E : Set (Op D.AppOp)}
    (h : respects π (paperOrder P C.replayContext E)) :
    respects (π.map (issue args))
      (paperOrder (policy P) (configuration args C).replayContext (issue args '' E)) := by
  rw [respects, List.pairwise_map]
  exact h.imp (fun {a b} hab hnew => hab ((order_issue args P C E b a).mp hnew))

theorem respects_specification_issue (args : Op D.AppOp → U)
    (S : HistorySpec U D.Query D.Value) (C : Configuration D)
    {π : List (Op D.AppOp)}
    (h : respects π (projectedSpecVisibility args S C.replayContext)) :
    respects (π.map (issue args))
      (specVisibility (specification S) (configuration args C).replayContext) := by
  rw [respects, List.pairwise_map]
  apply h.imp
  intro a b hab hnew
  apply hab
  exact ⟨(visibility_issue args C b a).mp hnew.1,
    fun hc => hnew.2 (S.withInputs_commutes Prod.snd hc)⟩

/-- Every existing projected-label correctness proof yields the standard
criterion whose `ops` projects the complete operation field pointwise. -/
theorem specificationRA (args : Op D.AppOp → U)
    {P : OperationPolicy D.AppOp} {S : HistorySpec U D.Query D.Value}
    {C : Configuration D}
    (h : ProjectedSpecificationRALinearizable D P args S C) :
    SpecificationRALinearizable (datatype D U) (policy P) (specification S)
      (configuration args C) := by
  intro r v s E hh hv q
  obtain ⟨⟨s',F⟩,hF,eq⟩ := Option.map_eq_some_iff.mp hv
  cases eq
  obtain ⟨π,hπ,ho,hs,ha⟩ := h r v s' F hh hF q
  exact ⟨π.map (issue args), permutation_issue args hπ,
    respects_order_issue args P C ho, respects_specification_issue args S C hs,
    (labels_issue args S π q (D.query s' q)).mpr ha⟩

/-- In particular, the paper's literal pointwise-`ops` criterion holds. -/
theorem ra (args : Op D.AppOp → U)
    {P : OperationPolicy D.AppOp} {S : HistorySpec U D.Query D.Value}
    {C : Configuration D}
    (h : ProjectedSpecificationRALinearizable D P args S C) :
    RALinearizable (datatype D U) (policy P) (specification S)
      (configuration args C) :=
  (specificationRA args h).active

/-- The same conversion retains the all-allocated-versions guarantee used by
full-event case studies, not just the replica-head guarantee. -/
theorem eventVersionsRA {P : OperationPolicy D.AppOp}
    {S : HistorySpec (Op D.AppOp) D.Query D.Value} {C : Configuration D}
    (h : EventVersionsSpecificationRA D P S C) :
    VersionsRALinearizable (datatype D (Op D.AppOp)) (policy P) (specification S)
      (configuration id C) := by
  intro v s E hv q
  obtain ⟨⟨s',F⟩,hF,eq⟩ := Option.map_eq_some_iff.mp hv
  cases eq
  obtain ⟨π,hπ,ho,_,ha⟩ := h v s' F hF q
  exact ⟨π.map (issue id), permutation_issue id hπ,
    respects_order_issue id P C ho, (labels_issue id S π q (D.query s' q)).mpr ha⟩

omit [DecidableEq U] in
/-- The existing history constructor is exactly pointwise `ops`, followed by
wrapping each operation as an update label. -/
theorem projectedUpdates_eq_ops (π : List (Op D.AppOp)) :
    projectedUpdates π = (ops π).map (SeqLabel.update (Query := D.Query) (Value := D.Value)) := by
  simp [projectedUpdates, ops, List.map_map, Function.comp_def]

omit [DecidableEq U] in
/-- PASS+FAIL control: metadata appears in the operation field, and two births
with the same application payload are not collapsed into one label. -/
theorem identified_labels_control (p : D.AppOp) :
    ops [issue id (1, 0, p)] = [(p, (1, 0, p))] ∧
    ops [issue id (1, 0, p)] ≠ ops [issue id (2, 0, p)] := by
  simp [ops, issue, Op.op, Op.time, Op.rep]

#print axioms specificationRA
#print axioms eventVersionsRA

end Sal.MRDTs.Paper1.OperationLabels
