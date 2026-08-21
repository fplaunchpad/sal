import Sal.ConditionedMRDTs.Metatheory.GC_CompressedDAG

/-!
# Distributed commit GC protocol

Unlike `Configuration`, this operational model has a separate commit holding,
head, closed roster, and author provenance at every replica. Fetch/receive is
set union. Frontier evidence is derived locally from received commit ancestry;
the wire never carries an independently trusted evidence assertion. Local GC
is partial: it refuses unless the derived frontier covers every roster member.

The simulation relation is intentionally datatype-parametric.  Reads depend on
the materialized state of the current head; merge/LCA preservation is supplied
by `compressed_isLCA_iff` from `GC_CompressedDAG`.
-/

namespace Sal.ConditionedMRDTs

open Classical
open Sal.Emulation

section Distributed

variable {State : Type} (parents : Version → List Version)

/-- A local replica store. `authored r` records the immutable commits minted by
`r` that this store currently holds. It is provenance, not a wire assertion
about stability. -/
structure DistributedLocal where
  self : Replica
  head : Version
  commits : Set Version
  roster : Set Replica
  authors : Set Replica
  authored : Replica → Set Version
  head_present : head ∈ commits
  self_registered : self ∈ roster
  authored_present : ∀ r, authored r ⊆ commits

/-- A fetch response carries immutable commits and their author provenance.
The receiver derives frontier evidence after ingest. -/
structure GCEnvelope where
  commits : Set Version
  authors : Set Replica
  authored : Replica → Set Version
  authored_present : ∀ r, authored r ⊆ commits

/-- Receive is union for both monotone components. -/
def receive (L : DistributedLocal) (m : GCEnvelope) : DistributedLocal where
  self := L.self
  head := L.head
  commits := L.commits ∪ m.commits
  roster := L.roster
  authors := L.authors ∪ m.authors
  authored := fun r => L.authored r ∪ m.authored r
  head_present := Or.inl L.head_present
  self_registered := L.self_registered
  authored_present := by
    intro r v hv
    rcases hv with hv | hv
    · exact Or.inl (L.authored_present r hv)
    · exact Or.inr (m.authored_present r hv)

theorem receive_commits_mono (L : DistributedLocal) (m : GCEnvelope) :
    L.commits ⊆ (receive L m).commits := Set.subset_union_left

theorem receive_authored_mono (L : DistributedLocal) (m : GCEnvelope) (r : Replica) :
    L.authored r ⊆ (receive L m).authored r := Set.subset_union_left

/-- Commit-shaped frontier evidence derived from the authenticated local DAG. -/
def DerivedEvidence (L : DistributedLocal) (r : Replica) : Set Version :=
  {v | v ∈ L.authored r ∧ v ∈ L.commits ∧ Reaches parents v L.head}

/-- Complete evidence: every closed-roster member has advertised an extant
commit that is an ancestor of the local head. -/
def EvidenceComplete (L : DistributedLocal) : Prop :=
  ∀ r ∈ L.roster, r = L.self ∨
    ∃ v, v ∈ DerivedEvidence parents L r

/-- A certificate chooses the bounded retained set and records exactly the
closure facts consumed by future head-sync LCA queries. -/
structure LocalGCCertificate (L : DistributedLocal) where
  keep : Set Version
  parents_lt : ∀ v p, p ∈ parents v → p < v
  complete : EvidenceComplete parents L
  head_kept : L.head ∈ keep
  evidence_kept : ∀ r ∈ L.roster, r = L.self ∨
    ∃ v, v ∈ DerivedEvidence parents L r ∧ v ∈ keep
  support : keep ⊆ L.commits
  mca_closed : ∀ v₁ ∈ keep, ∀ v₂ ∈ keep, ∀ m,
    IsMCA parents {v₁} v₂ m → m ∈ keep

/-- Successful local GC.  Notice that the old root is absent whenever it is
not in the certificate's keep set. -/
def collect (L : DistributedLocal) (cert : LocalGCCertificate parents L) :
    DistributedLocal where
  self := L.self
  head := L.head
  commits := cert.keep
  roster := L.roster
  authors := L.authors
  authored := fun r => L.authored r ∩ cert.keep
  head_present := cert.head_kept
  self_registered := L.self_registered
  authored_present := by
    intro r v hv
    exact hv.2

/-- Executable/specification-level refusal: `none` is returned when complete
frontier evidence is unavailable. -/
noncomputable def localGC (L : DistributedLocal) : Option DistributedLocal :=
  if h : ∃ cert : LocalGCCertificate parents L, True
  then some (collect parents L h.choose)
  else none

theorem localGC_refuses_without_evidence (L : DistributedLocal)
    (hmissing : ¬ EvidenceComplete parents L) : localGC parents L = none := by
  simp only [localGC]
  split
  · rename_i h
    exact absurd h.choose.complete hmissing
  · rfl

theorem localGC_succeeds_with_certificate (L : DistributedLocal)
    (cert : LocalGCCertificate parents L) : ∃ L', localGC parents L = some L' := by
  simp only [localGC]
  split
  · exact ⟨_, rfl⟩
  · rename_i h
    exact absurd ⟨cert, trivial⟩ h

/-- Forward-simulation relation from a compact local holding to its no-GC
counterpart. -/
def StoreSim (full compact : DistributedLocal) : Prop :=
  full.self = compact.self ∧ full.head = compact.head ∧
  compact.commits ⊆ full.commits ∧ compact.head ∈ compact.commits ∧
  full.roster = compact.roster ∧ compact.authors ⊆ full.authors ∧
  ∀ r, compact.authored r ⊆ full.authored r

theorem collect_simulates (L : DistributedLocal) (cert : LocalGCCertificate parents L) :
    StoreSim L (collect parents L cert) :=
  ⟨rfl, rfl, cert.support, cert.head_kept, rfl, Set.Subset.rfl,
    fun _ _ hv => hv.1⟩

/-- Future asynchronous receives preserve the simulation when both executions
receive the same immutable batch. -/
theorem receive_preserves_sim {F C : DistributedLocal} (h : StoreSim F C)
    (m : GCEnvelope) : StoreSim (receive F m) (receive C m) := by
  refine ⟨h.1, h.2.1, ?_, Or.inl h.2.2.2.1, h.2.2.2.2.1, ?_, ?_⟩
  intro v hv
  rcases hv with hv | hv
  · exact Or.inl (h.2.2.1 hv)
  · exact Or.inr hv
  · intro r hr
    rcases hr with hr | hr
    · exact Or.inl (h.2.2.2.2.2.1 hr)
    · exact Or.inr hr
  · intro r v hv
    rcases hv with hv | hv
    · exact Or.inl (h.2.2.2.2.2.2 r hv)
    · exact Or.inr hv

/-- Head-state reads are identical across the simulation. -/
theorem read_preserved (stateAt : Version → State) {F C : DistributedLocal}
    (h : StoreSim F C) : stateAt F.head = stateAt C.head := by rw [h.2.1]

/-- A head-sync merge that materializes the same fresh result version in both
stores preserves the simulation.  The datatype-specific equality of the
materialized merge state is discharged by retained LCA preservation below. -/
def installHead (L : DistributedLocal) (v : Version) : DistributedLocal where
  self := L.self
  head := v
  commits := insert v L.commits
  roster := L.roster
  authors := L.authors
  authored := L.authored
  head_present := Set.mem_insert v L.commits
  self_registered := L.self_registered
  authored_present := by
    intro r w hw
    exact Set.mem_insert_of_mem v (L.authored_present r hw)

theorem installHead_preserves_sim {F C : DistributedLocal} (h : StoreSim F C)
    (v : Version) : StoreSim (installHead F v) (installHead C v) := by
  refine ⟨h.1, rfl, ?_, Set.mem_insert v C.commits, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  intro w hw
  rcases hw with rfl | hw
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (h.2.2.1 hw)

/-- Own-head discipline: once an evidence commit is below an author's head,
advancing that head along ancestry cannot invalidate the evidence. -/
theorem evidence_ancestor_of_later_head {e old new : Version}
    (he : Reaches parents e old) (hadvance : Reaches parents old new) :
    Reaches parents e new := he.trans hadvance

/-- The graph fact used by a future merge: within a certified retained store,
the compressed DAG supplies exactly the old LCA. -/
theorem collect_lca_preserved (L : DistributedLocal)
    (cert : LocalGCCertificate parents L) {v₁ v₂ vT : Version}
    (h₁ : v₁ ∈ cert.keep) (h₂ : v₂ ∈ cert.keep) (hT : vT ∈ cert.keep) :
    IsLCARel (CompressedReaches parents cert.keep) v₁ v₂ vT ↔
      IsLCA parents v₁ v₂ vT :=
  compressed_isLCA_iff_of_mcaClosed parents cert.keep cert.parents_lt
    h₁ h₂ hT cert.mca_closed

/-- Membership reconfiguration is safe only for a non-author with no evidence;
an author/offline member remains in the roster until an explicit epoch-base
rebootstrap decision is made. -/
def CanRemoveMember (L : DistributedLocal) (r : Replica) : Prop :=
  r ≠ L.self ∧ r ∉ L.authors ∧ L.authored r = ∅

def removeMember (L : DistributedLocal) (r : Replica)
    (h : CanRemoveMember L r) : DistributedLocal where
  self := L.self
  head := L.head
  commits := L.commits
  roster := L.roster \ {r}
  authors := L.authors
  authored := L.authored
  head_present := L.head_present
  self_registered := by
    exact ⟨L.self_registered, fun hs => h.1 hs.symm⟩
  authored_present := L.authored_present

/-- A parent-free epoch base is admissible only as a complete snapshot: the
base is installed as both present head and sole retained commit. -/
def ingestEpochBase (L : DistributedLocal) (base : Version) : DistributedLocal where
  self := L.self
  head := base
  commits := {base}
  roster := L.roster
  authors := L.authors
  authored := fun _ => ∅
  head_present := Set.mem_singleton base
  self_registered := L.self_registered
  authored_present := by simp

/-! ### Multiple-local-state asynchronous semantics -/

/-- An operational world contains one independent local state per replica. -/
abbrev DistributedWorld := Replica → DistributedLocal

/-- A sender answers a fetch with immutable holdings and author provenance.
Sending the whole holding abstracts the runtime's ancestry-set difference:
union at the receiver gives the same resulting holding. -/
def advertise (L : DistributedLocal) : GCEnvelope :=
  ⟨L.commits, L.authors, L.authored, L.authored_present⟩

/-- Asynchronous protocol steps. `fetch` updates only the receiver by union.
`headSync` is separate because ingesting remote history does not itself change
the local head. Collection is a local step carrying its checked certificate. -/
inductive DistributedStep : DistributedWorld → DistributedWorld → Prop where
  | fetch (W : DistributedWorld) (src dst : Replica) :
      DistributedStep W (Function.update W dst (receive (W dst) (advertise (W src))))
  | headSync (W : DistributedWorld) (r : Replica) (v : Version)
      (present : v ∈ (W r).commits) :
      DistributedStep W (Function.update W r (installHead (W r) v))
  | gc (W : DistributedWorld) (r : Replica)
      (cert : LocalGCCertificate parents (W r)) :
      DistributedStep W (Function.update W r (collect parents (W r) cert))

theorem fetch_is_union (W : DistributedWorld) (src dst : Replica) :
    (receive (W dst) (advertise (W src))).commits =
      (W dst).commits ∪ (W src).commits := rfl

/-- The no-GC world has the same fetch and head-sync behavior but no collection
transition. -/
inductive NoGCStep : DistributedWorld → DistributedWorld → Prop where
  | fetch (W : DistributedWorld) (src dst : Replica) :
      NoGCStep W (Function.update W dst (receive (W dst) (advertise (W src))))
  | headSync (W : DistributedWorld) (r : Replica) (v : Version)
      (present : v ∈ (W r).commits) :
      NoGCStep W (Function.update W r (installHead (W r) v))

/-- One distributed step is matched by zero or one no-GC steps. Collection
stutters in the no-GC world. -/
inductive NoGCMatch : DistributedWorld → DistributedWorld → Prop where
  | refl (W : DistributedWorld) : NoGCMatch W W
  | step {W W' : DistributedWorld} (h : NoGCStep W W') : NoGCMatch W W'

/-- Pointwise simulation from a no-GC world to a compact distributed world. -/
def WorldSim (full compact : DistributedWorld) : Prop :=
  ∀ r, StoreSim (full r) (compact r)

theorem receive_advertise_preserves_sim {Fdst Cdst Fsrc Csrc : DistributedLocal}
    (hdst : StoreSim Fdst Cdst) (hsrc : StoreSim Fsrc Csrc) :
    StoreSim (receive Fdst (advertise Fsrc))
      (receive Cdst (advertise Csrc)) := by
  refine ⟨hdst.1, hdst.2.1, ?_, Or.inl hdst.2.2.2.1,
    hdst.2.2.2.2.1, ?_, ?_⟩
  · intro v hv
    rcases hv with hv | hv
    · exact Or.inl (hdst.2.2.1 hv)
    · exact Or.inr (hsrc.2.2.1 hv)
  · intro r hr
    rcases hr with hr | hr
    · exact Or.inl (hdst.2.2.2.2.2.1 hr)
    · exact Or.inr (hsrc.2.2.2.2.2.1 hr)
  · intro r v hv
    rcases hv with hv | hv
    · exact Or.inl (hdst.2.2.2.2.2.2 r hv)
    · exact Or.inr (hsrc.2.2.2.2.2.2 r hv)

theorem world_fetch_preserves_sim {F C : DistributedWorld} (h : WorldSim F C)
    (src dst : Replica) :
    WorldSim
      (Function.update F dst (receive (F dst) (advertise (F src))))
      (Function.update C dst (receive (C dst) (advertise (C src)))) := by
  intro r
  by_cases hr : r = dst
  · subst r
    simp [Function.update]
    exact receive_advertise_preserves_sim (h dst) (h src)
  · simp [Function.update, hr]
    exact h r

theorem world_headSync_preserves_sim {F C : DistributedWorld} (h : WorldSim F C)
    (r : Replica) (v : Version) :
    WorldSim (Function.update F r (installHead (F r) v))
      (Function.update C r (installHead (C r) v)) := by
  intro x
  by_cases hx : x = r
  · subst x
    simp [Function.update]
    exact installHead_preserves_sim (h r) v
  · simp [Function.update, hx]
    exact h x

theorem world_collect_preserves_sim {F C : DistributedWorld} (h : WorldSim F C)
    (r : Replica) (cert : LocalGCCertificate parents (C r)) :
    WorldSim F (Function.update C r (collect parents (C r) cert)) := by
  intro x
  by_cases hx : x = r
  · subst x
    simp [Function.update]
    exact ⟨(h r).1, (h r).2.1,
      fun _ hv => (h r).2.2.1 (cert.support hv), cert.head_kept,
      (h r).2.2.2.2.1,
      fun _ hv => (h r).2.2.2.2.2.1 hv,
      fun a _ hv => (h r).2.2.2.2.2.2 a hv.1⟩
  · simp [Function.update, hx]
    exact h x

/-- Headline world-level forward simulation. Fetch and head synchronization
take the corresponding no-GC step. Local collection is silent. -/
theorem distributed_refines_noGC {F C C' : DistributedWorld}
    (hSim : WorldSim F C) (hStep : DistributedStep parents C C') :
    ∃ F', NoGCMatch F F' ∧ WorldSim F' C' := by
  cases hStep with
  | fetch src dst =>
      refine ⟨Function.update F dst (receive (F dst) (advertise (F src))),
        NoGCMatch.step (NoGCStep.fetch F src dst), ?_⟩
      exact world_fetch_preserves_sim hSim src dst
  | headSync r v present =>
      have hPresent : v ∈ (F r).commits := (hSim r).2.2.1 present
      refine ⟨Function.update F r (installHead (F r) v),
        NoGCMatch.step (NoGCStep.headSync F r v hPresent), ?_⟩
      exact world_headSync_preserves_sim hSim r v
  | gc r cert =>
      exact ⟨F, NoGCMatch.refl F, world_collect_preserves_sim parents hSim r cert⟩

inductive DistributedSteps : DistributedWorld → DistributedWorld → Prop where
  | refl (W : DistributedWorld) : DistributedSteps W W
  | tail {W₀ W₁ W₂ : DistributedWorld}
      (run : DistributedSteps W₀ W₁)
      (last : DistributedStep parents W₁ W₂) : DistributedSteps W₀ W₂

inductive NoGCSteps : DistributedWorld → DistributedWorld → Prop where
  | refl (W : DistributedWorld) : NoGCSteps W W
  | tail {W₀ W₁ W₂ : DistributedWorld}
      (run : NoGCSteps W₀ W₁)
      (last : NoGCStep W₁ W₂) : NoGCSteps W₀ W₂

theorem NoGCSteps.append_match {F₀ F₁ F₂ : DistributedWorld}
    (hSteps : NoGCSteps F₀ F₁) (hMatch : NoGCMatch F₁ F₂) :
    NoGCSteps F₀ F₂ := by
  cases hMatch with
  | refl => exact hSteps
  | step h => exact NoGCSteps.tail hSteps h

/-- Execution-level refinement. Every finite asynchronous execution with
arbitrarily many local collections has a no-GC execution with the same fetch
and head-sync actions. The final worlds remain pointwise related. -/
theorem distributed_execution_refines_noGC {F₀ C₀ C₁ : DistributedWorld}
    (hSim : WorldSim F₀ C₀) (hRun : DistributedSteps parents C₀ C₁) :
    ∃ F₁, NoGCSteps F₀ F₁ ∧ WorldSim F₁ C₁ := by
  induction hRun with
  | refl => exact ⟨F₀, NoGCSteps.refl F₀, hSim⟩
  | tail run last ih =>
      rcases ih with ⟨Fmid, hFRun, hMid⟩
      rcases distributed_refines_noGC parents hMid last with ⟨F₁, hMatch, hFinal⟩
      exact ⟨F₁, hFRun.append_match hMatch, hFinal⟩

theorem world_read_preserved (stateAt : Version → State) {F C : DistributedWorld}
    (h : WorldSim F C) (r : Replica) :
    stateAt (F r).head = stateAt (C r).head :=
  read_preserved stateAt (h r)

/-- A single shared global commit store can project exactly to a world only
when every local holding is identical. Local collection does not preserve this
relation; this is why the sound refinement target above is behavioral no-GC,
not an exact one-global-store state after every asynchronous step. -/
def UniformHolding (W : DistributedWorld) : Prop :=
  ∀ r₁ r₂, (W r₁).commits = (W r₂).commits

/-- Exact projection to the carrier of one centralized commit store. This is a
quiescent-boundary relation, not an invariant of intermediate local-GC steps. -/
def ProjectsGlobalHolding (global : Set Version) (W : DistributedWorld) : Prop :=
  ∀ r, (W r).commits = global

/-- A coordinated collection applies one checked local certificate at every
replica. It is a specification boundary; the asynchronous protocol reaches it
through individual `DistributedStep.gc` transitions. -/
def collectEverywhere (W : DistributedWorld)
    (cert : ∀ r, LocalGCCertificate parents (W r)) : DistributedWorld :=
  fun r => collect parents (W r) (cert r)

/-- At a coordinated cut, equal certified keep sets give exactly the carrier
of one global collection. Intermediate asynchronous states need not project to
one global store, as the FAIL control below demonstrates. -/
theorem coordinated_collect_projects_global (W : DistributedWorld)
    (cert : ∀ r, LocalGCCertificate parents (W r)) (Keep : Set Version)
    (hKeep : ∀ r, (cert r).keep = Keep) :
    ProjectsGlobalHolding Keep (collectEverywhere parents W cert) := by
  intro r
  simp [collectEverywhere, collect, hKeep r]

theorem projectsGlobal_implies_uniform {global : Set Version} {W : DistributedWorld}
    (h : ProjectsGlobalHolding global W) : UniformHolding W := by
  intro r₁ r₂
  rw [h r₁, h r₂]

end Distributed

/-! ## Refusal control -/

namespace DistributedGCSpot

theorem reaches_nil_eq {a b : Version} (h : Reaches (fun _ => []) a b) : a = b := by
  induction h with
  | refl => rfl
  | tail _ hstep _ => simp at hstep

def lone : DistributedLocal where
  self := 0
  head := 4
  commits := {4}
  roster := {0, 1}
  authors := {0}
  authored := fun _ => ∅
  head_present := by simp
  self_registered := by simp
  authored_present := by simp

example : ¬ EvidenceComplete (fun _ => []) lone := by
  intro h
  rcases h 1 (by simp [lone]) with hself | ⟨v, hv⟩
  · simp [lone] at hself
  simpa [DerivedEvidence, lone] using hv

example : localGC (fun _ => []) lone = none :=
  localGC_refuses_without_evidence (fun _ => []) lone (by
    intro h
    rcases h 1 (by simp [lone]) with hself | ⟨v, hv⟩
    · simp [lone] at hself
    simpa [DerivedEvidence, lone] using hv)

/-- PASS: fetching an authored commit makes its evidence derivable from the
received ancestry; no evidence assertion is present on the wire. -/
def source : DistributedLocal where
  self := 1
  head := 4
  commits := {4}
  roster := {0, 1}
  authors := {1}
  authored := fun r => if r = 1 then {4} else ∅
  head_present := by simp
  self_registered := by simp
  authored_present := by
    intro r v hv
    split at hv
    · simpa using hv
    · simp at hv

def sink : DistributedLocal where
  self := 0
  head := 4
  commits := {4}
  roster := {0, 1}
  authors := {0}
  authored := fun _ => ∅
  head_present := by simp
  self_registered := by simp
  authored_present := by simp

example : 4 ∈ DerivedEvidence (fun _ => [])
    (receive sink (advertise source)) 1 := by
  refine ⟨?_, by simp [sink, source, receive, advertise], Relation.ReflTransGen.refl⟩
  simp [sink, source, receive, advertise]

/-- FAIL: commit presence alone does not fabricate author provenance. -/
example : 4 ∉ DerivedEvidence (fun _ => []) sink 1 := by
  simp [DerivedEvidence, sink]

def fullNode (r : Replica) : DistributedLocal where
  self := r
  head := 5
  commits := {4, 5}
  roster := {r}
  authors := ∅
  authored := fun _ => ∅
  head_present := by simp
  self_registered := by simp
  authored_present := by simp

def keepHead : LocalGCCertificate (fun _ => []) (fullNode 0) where
  keep := {5}
  parents_lt := by simp
  complete := by
    intro r hr
    exact Or.inl (by simpa [fullNode] using hr)
  head_kept := by simp [fullNode]
  evidence_kept := by
    intro r hr
    exact Or.inl (by simpa [fullNode] using hr)
  support := by simp [fullNode]
  mca_closed := by
    intro v₁ h₁ v₂ h₂ w hw
    have hv₁ : v₁ = 5 := by simpa using h₁
    subst v₁
    have hv₂ : v₂ = 5 := by simpa using h₂
    subst v₂
    have hw5 : w = 5 := reaches_nil_eq hw.1.2
    simpa [hw5]

/-- PASS: the weakened MCA-closure certificate is realizably root-free. -/
example : (0 : Version) ∉ (collect (fun _ => []) (fullNode 0) keepHead).commits := by
  simp [collect, keepHead]

def uniformWorld : DistributedWorld := fun r => fullNode r

example : UniformHolding uniformWorld := by
  intro r₁ r₂
  rfl

/-- Checked obstruction to exact per-step refinement into one shared global
holding: collecting at replica 0 leaves replica 1 uncollected. -/
example : ¬ UniformHolding
    (Function.update uniformWorld 0 (collect (fun _ => []) (fullNode 0) keepHead)) := by
  intro h
  have heq := h 0 1
  have h0 : (0 : Replica) ≠ 1 := by decide
  simp [Function.update, h0, uniformWorld, fullNode, collect, keepHead] at heq
  have hfour : (4 : Version) ∈ ({5} : Set Version) := by
    rw [heq]
    simp
  simp at hfour

end DistributedGCSpot

end Sal.ConditionedMRDTs

#print axioms Sal.ConditionedMRDTs.collect_lca_preserved
#print axioms Sal.ConditionedMRDTs.receive_preserves_sim
#print axioms Sal.ConditionedMRDTs.distributed_refines_noGC
#print axioms Sal.ConditionedMRDTs.distributed_execution_refines_noGC
#print axioms Sal.ConditionedMRDTs.coordinated_collect_projects_global
#print axioms Sal.ConditionedMRDTs.DistributedGCSpot.reaches_nil_eq
