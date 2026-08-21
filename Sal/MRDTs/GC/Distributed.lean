import Sal.MRDTs.GC.CompressedDAG

/-!
# Distributed commit-history garbage collection

This is the runtime GC layer.  Each replica owns a local immutable commit
holding. Fetch is union; frontier evidence is derived from received authored
commits; collection is local and refuses without complete roster evidence.
The theorem in this file refines the asynchronous collecting protocol directly
to the same protocol with collection erased.  There is no global/STW GC
semantics in the public framework.
-/

namespace Sal.MRDTs.GC

open Classical Sal.Emulation Sal.MRDTs

variable (parents : Version → List Version)

structure Local where
  self : Replica
  head : Version
  commits : Set Version
  roster : Set Replica
  authors : Set Replica
  authored : Replica → Set Version
  head_present : head ∈ commits
  self_registered : self ∈ roster
  authored_present : ∀ r, authored r ⊆ commits

structure Envelope where
  commits : Set Version
  authors : Set Replica
  authored : Replica → Set Version
  authored_present : ∀ r, authored r ⊆ commits

def advertise (L : Local) : Envelope :=
  ⟨L.commits, L.authors, L.authored, L.authored_present⟩

def receive (L : Local) (m : Envelope) : Local where
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
    exact hv.elim (fun h => Or.inl (L.authored_present r h))
      (fun h => Or.inr (m.authored_present r h))

theorem receive_commits_mono (L : Local) (m : Envelope) :
    L.commits ⊆ (receive L m).commits := Set.subset_union_left

def DerivedEvidence (L : Local) (r : Replica) : Set Version :=
  {v | v ∈ L.authored r ∧ v ∈ L.commits ∧ Reaches parents v L.head}

def EvidenceComplete (L : Local) : Prop :=
  ∀ r ∈ L.roster, r = L.self ∨ ∃ v, v ∈ DerivedEvidence parents L r

/-- A successful local collection certificate. `lca_preserved` is the exact
runtime obligation: every future retained-head LCA query has the same answer
in the compressed carrier.  The canonical MCA-closed keep-set construction
discharges it in the graph metatheory. -/
structure Certificate (L : Local) where
  keep : Set Version
  complete : EvidenceComplete parents L
  head_kept : L.head ∈ keep
  evidence_kept : ∀ r ∈ L.roster, r = L.self ∨
    ∃ v, v ∈ DerivedEvidence parents L r ∧ v ∈ keep
  support : keep ⊆ L.commits
  compressedReaches : Version → Version → Prop
  reaches_exact : ∀ {a b}, a ∈ keep → b ∈ keep →
    (compressedReaches a b ↔ Reaches parents a b)
  lca_preserved : ∀ {v₁ v₂ vT}, v₁ ∈ keep → v₂ ∈ keep → vT ∈ keep →
    (IsLCARel compressedReaches v₁ v₂ vT ↔ IsLCA parents v₁ v₂ vT)

/-- The canonical root-free certificate constructor. Closure under maximal
common ancestors is sufficient; paths and the old root need not be retained. -/
noncomputable def Certificate.ofMCAClosed (L : Local)
    (keep : Set Version)
    (complete : EvidenceComplete parents L)
    (head_kept : L.head ∈ keep)
    (evidence_kept : ∀ r ∈ L.roster, r = L.self ∨
      ∃ v, v ∈ DerivedEvidence parents L r ∧ v ∈ keep)
    (support : keep ⊆ L.commits)
    (parents_lt : ∀ v p, p ∈ parents v → p < v)
    (mca_closed : ∀ a ∈ keep, ∀ b ∈ keep, ∀ m,
      IsMCA parents {a} b m → m ∈ keep) : Certificate parents L where
  keep := keep
  complete := complete
  head_kept := head_kept
  evidence_kept := evidence_kept
  support := support
  compressedReaches := CompressedReaches parents keep
  reaches_exact := fun ha hb => compressedReaches_iff parents keep ha hb
  lca_preserved := fun h₁ h₂ hT =>
    compressed_isLCA_iff_of_mcaClosed parents keep parents_lt h₁ h₂ hT mca_closed

def collect (L : Local) (cert : Certificate parents L) : Local where
  self := L.self
  head := L.head
  commits := cert.keep
  roster := L.roster
  authors := L.authors
  authored := fun r => L.authored r ∩ cert.keep
  head_present := cert.head_kept
  self_registered := L.self_registered
  authored_present := fun _ _ h => h.2

noncomputable def localGC (L : Local) : Option Local :=
  if h : Nonempty (Certificate parents L) then some (collect parents L h.some) else none

theorem localGC_refuses_without_evidence (L : Local)
    (h : ¬ EvidenceComplete parents L) : localGC parents L = none := by
  simp only [localGC]
  split
  · rename_i hex
    exact absurd hex.some.complete h
  · rfl

def StoreSim (full compact : Local) : Prop :=
  full.self = compact.self ∧ full.head = compact.head ∧
  compact.commits ⊆ full.commits ∧ compact.head ∈ compact.commits ∧
  full.roster = compact.roster ∧ compact.authors ⊆ full.authors ∧
  ∀ r, compact.authored r ⊆ full.authored r

theorem collect_simulates (L : Local) (cert : Certificate parents L) :
    StoreSim L (collect parents L cert) :=
  ⟨rfl, rfl, cert.support, cert.head_kept, rfl, Set.Subset.rfl,
    fun _ _ h => h.1⟩

theorem receive_preserves_sim {F C : Local} (h : StoreSim F C) (m : Envelope) :
    StoreSim (receive F m) (receive C m) := by
  refine ⟨h.1, h.2.1, ?_, Or.inl h.2.2.2.1, h.2.2.2.2.1, ?_, ?_⟩
  · intro v hv
    exact hv.elim (fun x => Or.inl (h.2.2.1 x)) Or.inr
  · intro v hv
    exact hv.elim (fun x => Or.inl (h.2.2.2.2.2.1 x)) Or.inr
  · intro r v hv
    exact hv.elim (fun x => Or.inl (h.2.2.2.2.2.2 r x)) Or.inr

def installHead (L : Local) (v : Version) : Local where
  self := L.self
  head := v
  commits := insert v L.commits
  roster := L.roster
  authors := L.authors
  authored := L.authored
  head_present := by
    change v = v ∨ v ∈ L.commits
    exact Or.inl rfl
  self_registered := L.self_registered
  authored_present := by
    intro r w h
    change w = v ∨ w ∈ L.commits
    exact Or.inr (L.authored_present r h)

theorem installHead_preserves_sim {F C : Local} (h : StoreSim F C) (v : Version) :
    StoreSim (installHead F v) (installHead C v) := by
  refine ⟨h.1, rfl, ?_, (by
      change v = v ∨ v ∈ C.commits
      exact Or.inl rfl), h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  intro w hw
  rcases hw with rfl | hw
  · change w = w ∨ w ∈ F.commits
    exact Or.inl rfl
  · change w = v ∨ w ∈ F.commits
    exact Or.inr (h.2.2.1 hw)

abbrev World := Replica → Local

/-- The asynchronous implementation: fetch, explicit head synchronization,
and local collection. -/
inductive Step : World → World → Prop where
  | fetch (W : World) (src dst : Replica) :
      Step W (Function.update W dst (receive (W dst) (advertise (W src))))
  | headSync (W : World) (r : Replica) (v : Version)
      (present : v ∈ (W r).commits) :
      Step W (Function.update W r (installHead (W r) v))
  | gc (W : World) (r : Replica) (cert : Certificate parents (W r)) :
      Step W (Function.update W r (collect parents (W r) cert))

/-- The specification protocol has the same network behavior but no
collection transition. -/
inductive NoGCStep : World → World → Prop where
  | fetch (W : World) (src dst : Replica) :
      NoGCStep W (Function.update W dst (receive (W dst) (advertise (W src))))
  | headSync (W : World) (r : Replica) (v : Version)
      (present : v ∈ (W r).commits) :
      NoGCStep W (Function.update W r (installHead (W r) v))

inductive NoGCMatch : World → World → Prop where
  | silent (W : World) : NoGCMatch W W
  | visible {W W'} : NoGCStep W W' → NoGCMatch W W'

def WorldSim (full compact : World) : Prop := ∀ r, StoreSim (full r) (compact r)

theorem fetch_preserves {F C : World} (h : WorldSim F C) (src dst : Replica) :
    WorldSim
      (Function.update F dst (receive (F dst) (advertise (F src))))
      (Function.update C dst (receive (C dst) (advertise (C src)))) := by
  intro r
  by_cases hr : r = dst
  · subst r
    simp only [Function.update_self]
    have hs := h src
    have hd := h dst
    -- Both sides receive corresponding (possibly compact) advertisements.
    refine ⟨hd.1, hd.2.1, ?_, Or.inl hd.2.2.2.1, hd.2.2.2.2.1, ?_, ?_⟩
    · intro v hv
      exact hv.elim (fun x => Or.inl (hd.2.2.1 x))
        (fun x => Or.inr (hs.2.2.1 x))
    · intro v hv
      exact hv.elim (fun x => Or.inl (hd.2.2.2.2.2.1 x))
        (fun x => Or.inr (hs.2.2.2.2.2.1 x))
    · intro a v hv
      exact hv.elim (fun x => Or.inl (hd.2.2.2.2.2.2 a x))
        (fun x => Or.inr (hs.2.2.2.2.2.2 a x))
  · simp [Function.update, hr]
    exact h r

theorem headSync_preserves {F C : World} (h : WorldSim F C)
    (r : Replica) (v : Version) :
    WorldSim (Function.update F r (installHead (F r) v))
      (Function.update C r (installHead (C r) v)) := by
  intro x
  by_cases hx : x = r
  · subst x
    simp [installHead_preserves_sim (h r) v]
  · simp [Function.update, hx, h x]

theorem collect_preserves {F C : World} (h : WorldSim F C)
    (r : Replica) (cert : Certificate parents (C r)) :
    WorldSim F (Function.update C r (collect parents (C r) cert)) := by
  intro x
  by_cases hx : x = r
  · subst x
    simp only [Function.update_self]
    exact ⟨(h r).1, (h r).2.1, fun _ hv => (h r).2.2.1 (cert.support hv),
      cert.head_kept, (h r).2.2.2.2.1,
      fun _ hv => (h r).2.2.2.2.2.1 hv,
      fun a _ hv => (h r).2.2.2.2.2.2 a hv.1⟩
  · simp [Function.update, hx, h x]

/-- One collecting step is matched by either the corresponding no-GC network
step or stuttering. -/
theorem refines_noGC {F C C' : World} (h : WorldSim F C)
    (hs : Step parents C C') :
    ∃ F', NoGCMatch F F' ∧ WorldSim F' C' := by
  cases hs with
  | fetch src dst =>
      refine ⟨_, .visible (.fetch F src dst), fetch_preserves h src dst⟩
  | headSync r v present =>
      have presentF : v ∈ (F r).commits := (h r).2.2.1 present
      refine ⟨_, .visible (.headSync F r v presentF), headSync_preserves h r v⟩
  | gc r cert =>
      exact ⟨F, .silent F, collect_preserves parents h r cert⟩

inductive Steps : World → World → Prop where
  | refl (W) : Steps W W
  | tail {A B C} : Steps A B → Step parents B C → Steps A C

inductive NoGCSteps : World → World → Prop where
  | refl (W) : NoGCSteps W W
  | tail {A B C} : NoGCSteps A B → NoGCStep B C → NoGCSteps A C

/-- Full trace refinement: local distributed GC is observationally a
stuttering optimization of the asynchronous no-GC protocol. -/
theorem execution_refines_noGC {F₀ C₀ C₁ : World}
    (h₀ : WorldSim F₀ C₀) (hs : Steps parents C₀ C₁) :
    ∃ F₁, NoGCSteps F₀ F₁ ∧ WorldSim F₁ C₁ := by
  induction hs with
  | refl => exact ⟨F₀, .refl _, h₀⟩
  | tail pre one ih =>
      obtain ⟨F, htrace, hsim⟩ := ih
      obtain ⟨F', hmatch, hsim'⟩ := refines_noGC parents hsim one
      cases hmatch with
      | silent => exact ⟨F, htrace, hsim'⟩
      | visible hvis => exact ⟨_, .tail htrace hvis, hsim'⟩

theorem read_preserved (stateAt : Version → α) {F C : World}
    (h : WorldSim F C) (r : Replica) :
    stateAt (F r).head = stateAt (C r).head := by rw [(h r).2.1]

end Sal.MRDTs.GC
