import Sal.MRDTs.Framework.Signature
import Sal.MRDTs.Framework.Base.ReplayContext
import Sal.MRDTs.Framework.Base.LabeledTS
import Mathlib.Data.Set.Basic

/-!
# Unconditioned ternary execution

The ranked configuration records only operational coherence.  In particular,
it carries no proof that stored states satisfy a client invariant.
-/

namespace Sal.MRDTs

open Sal.MRDTs.Foundation

abbrev Version : Type := Nat

/-- Point update of a replica-indexed partial map. -/
def updateRep {α} (f : Replica → Option α) (r : Replica) (x : α) :
    Replica → Option α :=
  fun r' => if r' = r then some x else f r'

def Reaches (parents : Version → List Version) : Version → Version → Prop :=
  Relation.ReflTransGen (fun a b => a ∈ parents b)

/-- A greatest common ancestor: `vT` is common to both inputs and every other
common ancestor reaches it. This is stronger than being one of several
incomparable maximal merge bases. -/
def IsGCA (parents : Version → List Version) (v₁ v₂ vT : Version) : Prop :=
  Reaches parents vT v₁ ∧ Reaches parents vT v₂ ∧
    ∀ w, Reaches parents w v₁ → Reaches parents w v₂ → Reaches parents w vT

/-- The common ancestors of a pair of versions. -/
def CommonAncestors (parents : Version → List Version) (a b : Version) : Set Version :=
  {x | Reaches parents x a ∧ Reaches parents x b}

/-- A maximal common ancestor of two versions. Unlike a GCA, it need not be
unique: another maximal common ancestor may be incomparable with `m`. -/
def IsMaximalCommonAncestor (parents : Version → List Version)
    (a b m : Version) : Prop :=
  m ∈ CommonAncestors parents a b ∧
    ∀ x ∈ CommonAncestors parents a b, Reaches parents m x → x = m

/-- Common ancestors of `w` and at least one member of `S`. This support-set
generalization is used by the recursive virtual-merge-base construction. -/
def CommonAncestorsWithAny (parents : Version → List Version)
    (S : Set Version) (w : Version) : Set Version :=
  {x | (∃ u ∈ S, Reaches parents x u) ∧ Reaches parents x w}

/-- A maximal element among the common ancestors of `w` and any member of
`S`. This is the support-set generalization of `IsMaximalCommonAncestor`. -/
def IsMaximalCommonAncestorWithAny (parents : Version → List Version)
    (S : Set Version) (w m : Version) : Prop :=
  m ∈ CommonAncestorsWithAny parents S w ∧
    ∀ x ∈ CommonAncestorsWithAny parents S w, Reaches parents m x → x = m

@[simp] theorem commonAncestorsWithAny_singleton
    (parents : Version → List Version) (a b : Version) :
    CommonAncestorsWithAny parents {a} b = CommonAncestors parents a b := by
  ext x
  constructor
  · rintro ⟨⟨u, hu, hxu⟩, hxb⟩
    have hua : u = a := by simpa using hu
    subst u
    exact ⟨hxu, hxb⟩
  · rintro ⟨hxa, hxb⟩
    exact ⟨⟨a, rfl, hxa⟩, hxb⟩

@[simp] theorem isMaximalCommonAncestorWithAny_singleton
    (parents : Version → List Version) (a b m : Version) :
    IsMaximalCommonAncestorWithAny parents {a} b m ↔
      IsMaximalCommonAncestor parents a b m := by
  simp [IsMaximalCommonAncestorWithAny, IsMaximalCommonAncestor,
    commonAncestorsWithAny_singleton]

theorem parentStep_wf {parents : Version → List Version}
    (h : ∀ v p, p ∈ parents v → p < v) :
    WellFounded (fun a b : Version => a ∈ parents b) := by
  have hsub : Subrelation (fun a b : Version => a ∈ parents b)
      (fun a b : Version => a < b) := by
    intro a b hab
    exact h b a hab
  exact hsub.wf Nat.lt_wfRel.wf

theorem reaches_le {parents : Version → List Version}
    (h : ∀ v p, p ∈ parents v → p < v)
    {a b : Version} (r : Reaches parents a b) : a ≤ b := by
  induction r with
  | refl => exact Nat.le_refl _
  | tail _ edge ih => exact ih.trans (Nat.le_of_lt (h _ _ edge))

def headStateFrom {D : MRDTSig}
    (ver : Version → Option (D.State × Set (Op D.AppOp)))
    (head : Replica → Option Version) (r : Replica) : Option D.State :=
  head r >>= fun v => (ver v).map Prod.fst

def headEventsFrom {D : MRDTSig}
    (ver : Version → Option (D.State × Set (Op D.AppOp)))
    (head : Replica → Option Version) (r : Replica) :
    Option (Set (Op D.AppOp)) :=
  head r >>= fun v => (ver v).map Prod.snd

/-- Operational state of the version-DAG semantics.  All fields describe the
shape and coherence of the execution itself; client safety is external. -/
structure Configuration (D : MRDTSig) where
  vis : Op D.AppOp → Op D.AppOp → Prop
  ver : Version → Option (D.State × Set (Op D.AppOp))
  head : Replica → Option Version
  parents : Version → List Version
  parents_lt : ∀ v p, p ∈ parents v → p < v
  ver_init : ver 0 = some (D.init, ∅)
  head_alloc : ∀ r v, head r = some v → (ver v).isSome
  vis_src : ∀ {a b}, vis a b →
    ∃ r s, headEventsFrom ver head r = some s ∧ s a
  vis_tgt : ∀ {a b}, vis a b →
    ∃ r s, headEventsFrom ver head r = some s ∧ s b
  vis_causal : ∀ {a b r s}, vis a b →
    headEventsFrom ver head r = some s → s b → s a
  timestamps_distinct :
    ∀ {a b : Op D.AppOp} {r s r' s'},
      headEventsFrom ver head r = some s → s a →
      headEventsFrom ver head r' = some s' → s' b →
      a ≠ b → a.1 ≠ b.1
  causal_mono : ∀ {a b : Op D.AppOp}, vis a b → a.1 < b.1
  vis_total_same_replica :
    ∀ {a b : Op D.AppOp} {r s r' s'},
      headEventsFrom ver head r = some s → s a →
      headEventsFrom ver head r' = some s' → s' b →
      a ≠ b → a.2.1 = b.2.1 → vis a b ∨ vis b a
  gca_events : ∀ {v₁ v₂ vT s₁ e₁ s₂ e₂ sT eT},
    IsGCA parents v₁ v₂ vT →
    ver v₁ = some (s₁, e₁) → ver v₂ = some (s₂, e₂) →
    ver vT = some (sT, eT) → eT = e₁ ∩ e₂

namespace Configuration

variable {D : MRDTSig}

def headState (C : Configuration D) (r : Replica) : Option D.State :=
  headStateFrom C.ver C.head r

def headEvents (C : Configuration D) (r : Replica) :
    Option (Set (Op D.AppOp)) :=
  headEventsFrom C.ver C.head r

theorem headState_eq_of_head_ver (C : Configuration D) {r : Replica}
    {v : Version} {s : D.State} {E : Set (Op D.AppOp)}
    (hhead : C.head r = some v) (hver : C.ver v = some (s, E)) :
    C.headState r = some s := by
  simp [headState, headStateFrom, hhead, hver]

theorem headEvents_eq_of_head_ver (C : Configuration D) {r : Replica}
    {v : Version} {s : D.State} {E : Set (Op D.AppOp)}
    (hhead : C.head r = some v) (hver : C.ver v = some (s, E)) :
    C.headEvents r = some E := by
  simp [headEvents, headEventsFrom, hhead, hver]

theorem headState_none_iff_headEvents_none (C : Configuration D) (r : Replica) :
    C.headState r = none ↔ C.headEvents r = none := by
  simp only [headState, headEvents, headStateFrom, headEventsFrom]
  cases hhead : C.head r with
  | none => simp
  | some v =>
      cases hver : C.ver v with
      | none => simp
      | some pair => simp

theorem headEvents_update_of_store_head_update
    (C C' : Configuration D) {r : Replica} {vnew : Version}
    {snew : D.State} {Enew : Set (Op D.AppOp)}
    (hfresh : C.ver vnew = none)
    (hver : C'.ver = fun v => if v = vnew then some (snew, Enew) else C.ver v)
    (hhead : C'.head = fun r' => if r' = r then some vnew else C.head r') :
    C'.headEvents = updateRep C.headEvents r Enew := by
  funext r'
  by_cases hrr : r' = r
  · subst r'
    simp [headEvents, headEventsFrom, hhead, hver, updateRep]
  · simp only [headEvents, headEventsFrom]
    rw [show C'.head r' = C.head r' by simp [hhead, hrr]]
    rw [updateRep]
    simp only [if_neg hrr]
    cases h : C.head r' with
    | none => simp [Configuration.headEvents, headEventsFrom, h]
    | some v =>
        have hvne : v ≠ vnew := by
          intro hv
          subst v
          have := C.head_alloc r' vnew h
          rw [hfresh] at this
          simp at this
        simp [Configuration.headEvents, headEventsFrom, h, hver, hvne]

theorem headState_update_of_store_head_update
    (C C' : Configuration D) {r : Replica} {vnew : Version}
    {snew : D.State} {Enew : Set (Op D.AppOp)}
    (hfresh : C.ver vnew = none)
    (hver : C'.ver = fun v => if v = vnew then some (snew, Enew) else C.ver v)
    (hhead : C'.head = fun r' => if r' = r then some vnew else C.head r') :
    C'.headState = updateRep C.headState r snew := by
  funext r'
  by_cases hrr : r' = r
  · subst r'
    simp [headState, headStateFrom, hhead, hver, updateRep]
  · simp only [headState, headStateFrom]
    rw [show C'.head r' = C.head r' by simp [hhead, hrr]]
    rw [updateRep]
    simp only [if_neg hrr]
    cases h : C.head r' with
    | none => simp [Configuration.headState, headStateFrom, h]
    | some v =>
        have hvne : v ≠ vnew := by
          intro hv
          subst v
          have := C.head_alloc r' vnew h
          rw [hfresh] at this
          simp at this
        simp [Configuration.headState, headStateFrom, h, hver, hvne]

def events (C : Configuration D) : Set (Op D.AppOp) :=
  fun e => ∃ r s, C.headEvents r = some s ∧ s e

def verState (C : Configuration D) (v : Version) : Option D.State :=
  (C.ver v).map Prod.fst

def verEvents (C : Configuration D) (v : Version) : Option (Set (Op D.AppOp)) :=
  (C.ver v).map Prod.snd

/-- Projection consumed by replay-order and canonical-state proofs. -/
def replayContext (C : Configuration D) :
    Sal.MRDTs.Foundation.ReplayContext D.toUpdateSig where
  L := C.headEvents
  vis := C.vis
  timestamps_distinct := C.timestamps_distinct
  vis_total_same_replica := C.vis_total_same_replica

@[simp] theorem replayContext_events (C : Configuration D) :
    C.replayContext.events = C.events := rfl

@[simp] theorem replayContext_vis (C : Configuration D) :
    C.replayContext.vis = C.vis := rfl

theorem parents_wf (C : Configuration D) :
    WellFounded (fun a b : Version => a ∈ C.parents b) :=
  parentStep_wf C.parents_lt

end Configuration

private theorem initVer_decompose {D : MRDTSig}
    {v : Version} {s : D.State} {e : Set (Op D.AppOp)}
    (hv : (if v = 0 then some (D.init, (∅ : Set (Op D.AppOp))) else none) =
      some (s, e)) :
    v = 0 ∧ s = D.init ∧ e = ∅ := by
  by_cases h : v = 0
  · rw [if_pos h, Option.some.injEq, Prod.mk.injEq] at hv
    exact ⟨h, hv.1.symm, hv.2.symm⟩
  · rw [if_neg h] at hv
    simp at hv

/-- Initial configuration.  No invariant witness is required. -/
def initConfig (D : MRDTSig) : Configuration D where
  vis := fun _ _ => False
  ver := fun v => if v = 0 then some (D.init, ∅) else none
  head := fun r => if r = 0 then some 0 else none
  parents := fun _ => []
  parents_lt := by simp
  ver_init := by simp
  head_alloc := by
    intro r v hr
    by_cases hr0 : r = 0
    · subst r
      simp at hr
      subst v
      simp
    · simp [hr0] at hr
  vis_src := fun h => absurd h id
  vis_tgt := fun h => absurd h id
  vis_causal := fun h _ _ => absurd h id
  timestamps_distinct := by
    intro a b r s r' s' hLr hsa _ _ _
    by_cases hr : r = 0
    · subst hr
      simp [headEventsFrom] at hLr
      subst hLr
      exact hsa.elim
    · simp [headEventsFrom, hr] at hLr
  causal_mono := fun h => absurd h id
  vis_total_same_replica := by
    intro a b r s r' s' hLr hsa _ _ _ _
    by_cases hr : r = 0
    · subst hr
      simp [headEventsFrom] at hLr
      subst hLr
      exact hsa.elim
    · simp [headEventsFrom, hr] at hLr
  gca_events := by
    intro v₁ v₂ vT s₁ e₁ s₂ e₂ sT eT _ hv₁ hv₂ hvT
    have h1 := (initVer_decompose hv₁).2.2
    have h2 := (initVer_decompose hv₂).2.2
    have h3 := (initVer_decompose hvT).2.2
    subst e₁
    subst e₂
    subst eT
    rw [Set.empty_inter]

inductive Label (D : MRDTSig) where
  | fork (dst src : Replica)
  | apply (t : Timestamp) (r : Replica) (o : D.AppOp)
  | merge (r₁ r₂ : Replica)
  | query (r : Replica) (q : D.Query) (v : D.Value)

/-- Raw execution.  Apply deliberately has no client guard. -/
inductive Step (D : MRDTSig) :
    Configuration D → Label D → Configuration D → Prop where
  | fork {C : Configuration D} {dst src : Replica}
      {v vnew : Version} {s : D.State} {ev : Set (Op D.AppOp)}
      (freshReplica : C.head dst = none)
      (sourceHead : C.head src = some v)
      (sourceVersion : C.ver v = some (s, ev))
      (freshVersion : C.ver vnew = none) (rank : v < vnew)
      (C' : Configuration D)
      (vis : C'.vis = C.vis)
      (ver : C'.ver = fun w => if w = vnew then some (s, ev) else C.ver w)
      (head : C'.head = fun r' => if r' = dst then some vnew else C.head r')
      (parents : C'.parents = fun w => if w = vnew then [v] else C.parents w) :
      Step D C (.fork dst src) C'
  | apply {C : Configuration D} {t : Timestamp} {r : Replica} {o : D.AppOp}
      {v : Version} {s : D.State} {ev : Set (Op D.AppOp)} {vnew : Version}
      (headAt : C.head r = some v) (versionAt : C.ver v = some (s, ev))
      (freshTime : ∀ e', e' ∈ C.events → Op.time e' ≠ t)
      (freshStore : ∀ w sw Ew, C.ver w = some (sw, Ew) →
        ∀ e' ∈ Ew, Op.time e' ≠ t)
      (freshVersion : C.ver vnew = none) (rank : v < vnew)
      (C' : Configuration D)
      (vis : C'.vis = fun a b => C.vis a b ∨ (ev a ∧ b = (t, r, o)))
      (ver : C'.ver = fun w => if w = vnew
        then some (D.update s (t, r, o), ev ∪ {(t, r, o)}) else C.ver w)
      (head : C'.head = fun r' => if r' = r then some vnew else C.head r')
      (parents : C'.parents = fun w => if w = vnew then [v] else C.parents w) :
      Step D C (.apply t r o) C'
  | merge {C : Configuration D} {r₁ r₂ : Replica}
      {v₁ v₂ vT vm : Version} {s₁ s₂ sT : D.State}
      {ev₁ ev₂ evT : Set (Op D.AppOp)}
      (head₁ : C.head r₁ = some v₁) (head₂ : C.head r₂ = some v₂)
      (version₁ : C.ver v₁ = some (s₁, ev₁))
      (version₂ : C.ver v₂ = some (s₂, ev₂))
      (gca : IsGCA C.parents v₁ v₂ vT)
      (versionGCA : C.ver vT = some (sT, evT))
      (freshVersion : C.ver vm = none) (rank₁ : v₁ < vm) (rank₂ : v₂ < vm)
      (C' : Configuration D)
      (vis : C'.vis = C.vis)
      (ver : C'.ver = fun w => if w = vm
        then some (D.merge sT s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
      (head : C'.head = fun r' => if r' = r₁ then some vm else C.head r')
      (parents : C'.parents = fun w => if w = vm then [v₁, v₂] else C.parents w) :
      Step D C (.merge r₁ r₂) C'
  | query {C : Configuration D} {r : Replica} {q : D.Query}
      {v : D.Value} {s : D.State}
      (stateAt : C.headState r = some s) (value : v = D.query s q) :
      Step D C (.query r q v) C

namespace Step

/-- Positive control for fork: the destination receives the source snapshot at
a fresh child version whose sole parent is the source head. -/
theorem fork_copies_source {D : MRDTSig} {C C' : Configuration D}
    {dst src : Replica} (h : Step D C (.fork dst src) C') :
    ∃ v vnew s ev,
      C.head src = some v ∧ C.ver v = some (s, ev) ∧
      C'.headState dst = some s ∧ C'.headEvents dst = some ev ∧
      C'.head dst = some vnew ∧ C'.ver vnew = some (s, ev) ∧
      C'.parents vnew = [v] := by
  cases h
  case fork v vnew s ev sourceVersion freshVersion rank freshReplica sourceHead
      vis ver parents head =>
    refine ⟨v, vnew, s, ev, sourceHead, sourceVersion, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Configuration.headState, headStateFrom, head, ver]
    · simp [Configuration.headEvents, headEventsFrom, head, ver]
    · rw [head]
      simp
    · rw [ver]
      simp
    · rw [parents]
      simp

/-- Negative control for the rejected root-reset semantics: every fork head is
a strictly newer version and therefore cannot be the initial version. -/
theorem fork_head_ne_root {D : MRDTSig} {C C' : Configuration D}
    {dst src : Replica} (h : Step D C (.fork dst src) C') :
    C'.head dst ≠ some 0 := by
  cases h
  case fork v vnew s ev sourceVersion freshVersion rank freshReplica sourceHead
      vis ver parents head =>
    rw [head]
    simp only [if_pos]
    intro hz
    have hvnew : vnew = 0 := Option.some.inj hz
    exact (Nat.ne_of_gt (Nat.zero_lt_of_lt rank)) hvnew

end Step

def labeledTS (D : MRDTSig) : LabeledTS where
  State := Configuration D
  Label := Label D
  step := Step D
  silent := fun _ => False

/-! ## Virtual merge-base execution -/

/-- Framework-supplied resolution of the synthetic base used when two heads
have no registered GCA. The production resolver is the canonical
recursive maximal-common-ancestor fold; this interface keeps the raw execution and GC layers
independent of its executable DAG representation. -/
structure VirtualMergeBaseResolver (D : MRDTSig) where
  state : Configuration D → Version → Version → D.State

/-- Raw execution widened by a virtual-merge-base merge.  Ordinary execution embeds
conservatively through `base`; a virtual merge allocates only its final node. -/
inductive StepV (D : MRDTSig) (V : VirtualMergeBaseResolver D) :
    Configuration D → Label D → Configuration D → Prop where
  | base {C C' : Configuration D} {l : Label D} :
      Step D C l C' → StepV D V C l C'
  | mergeVirtual {C : Configuration D} {r₁ r₂ : Replica}
      {v₁ v₂ vm : Version} {s₁ s₂ : D.State}
      {ev₁ ev₂ : Set (Op D.AppOp)}
      (head₁ : C.head r₁ = some v₁) (head₂ : C.head r₂ = some v₂)
      (version₁ : C.ver v₁ = some (s₁, ev₁))
      (version₂ : C.ver v₂ = some (s₂, ev₂))
      (freshVersion : C.ver vm = none) (rank₁ : v₁ < vm) (rank₂ : v₂ < vm)
      (C' : Configuration D)
      (vis : C'.vis = C.vis)
      (ver : C'.ver = fun w => if w = vm then
        some (D.merge (V.state C v₁ v₂) s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
      (head : C'.head = fun r' => if r' = r₁ then some vm else C.head r')
      (parents : C'.parents = fun w => if w = vm then [v₁, v₂] else C.parents w) :
      StepV D V C (.merge r₁ r₂) C'

def labeledTSV (D : MRDTSig) (V : VirtualMergeBaseResolver D) : LabeledTS where
  State := Configuration D
  Label := Label D
  step := StepV D V
  silent := fun _ => False

end Sal.MRDTs
