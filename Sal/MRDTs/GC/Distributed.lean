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

open Classical Sal.MRDTs.Foundation Sal.MRDTs

variable (parents : Version → List Version)

/-- Immutable metadata carried by a commit record. The protocol does not store
or synchronize a second authorship index in its logical state. -/
abbrev Author := Version → Option Replica

structure Local where
  head : Version
  commits : Set Version
  head_present : head ∈ commits

structure Envelope where
  commits : Set Version

def advertise (L : Local) : Envelope :=
  ⟨L.commits⟩

def receive (L : Local) (m : Envelope) : Local where
  head := L.head
  commits := L.commits ∪ m.commits
  head_present := Or.inl L.head_present

theorem receive_commits_mono (L : Local) (m : Envelope) :
    L.commits ⊆ (receive L m).commits := Set.subset_union_left

def DerivedEvidence (author : Author) (L : Local) (r : Replica) : Set Version :=
  {v | v ∈ L.commits ∧ author v = some r ∧ Reaches parents v L.head}

def EvidenceComplete (author : Author) (roster : Set Replica)
    (self : Replica) (L : Local) : Prop :=
  ∀ r ∈ roster, r = self ∨ ∃ v, v ∈ DerivedEvidence parents author L r

/-- A successful local collection certificate. `lca_preserved` is the exact
runtime obligation: every future retained-head LCA query has the same answer
in the compressed carrier.  The canonical MCA-closed keep-set construction
discharges it in the graph metatheory. -/
structure Certificate (author : Author) (roster : Set Replica)
    {self : Replica} (L : Local) where
  keep : Set Version
  complete : EvidenceComplete parents author roster self L
  head_kept : L.head ∈ keep
  evidence_kept : ∀ r ∈ roster, r = self ∨
    ∃ v, v ∈ DerivedEvidence parents author L r ∧ v ∈ keep
  support : keep ⊆ L.commits
  compressedReaches : Version → Version → Prop
  reaches_exact : ∀ {a b}, a ∈ keep → b ∈ keep →
    (compressedReaches a b ↔ Reaches parents a b)
  lca_preserved : ∀ {v₁ v₂ vT}, v₁ ∈ keep → v₂ ∈ keep → vT ∈ keep →
    (IsLCARel compressedReaches v₁ v₂ vT ↔ IsLCA parents v₁ v₂ vT)

/-- The canonical root-free certificate constructor. Closure under maximal
common ancestors is sufficient; paths and the old root need not be retained. -/
noncomputable def Certificate.ofMCAClosed (author : Author)
    (roster : Set Replica) (self : Replica) (L : Local)
    (keep : Set Version)
    (complete : EvidenceComplete parents author roster self L)
    (head_kept : L.head ∈ keep)
    (evidence_kept : ∀ r ∈ roster, r = self ∨
      ∃ v, v ∈ DerivedEvidence parents author L r ∧ v ∈ keep)
    (support : keep ⊆ L.commits)
    (parents_lt : ∀ v p, p ∈ parents v → p < v)
    (mca_closed : ∀ a ∈ keep, ∀ b ∈ keep, ∀ m,
      IsMCA parents {a} b m → m ∈ keep) :
      Certificate parents author roster (self := self) L where
  keep := keep
  complete := complete
  head_kept := head_kept
  evidence_kept := evidence_kept
  support := support
  compressedReaches := CompressedReaches parents keep
  reaches_exact := fun ha hb => compressedReaches_iff parents keep ha hb
  lca_preserved := fun h₁ h₂ hT =>
    compressed_isLCA_iff_of_mcaClosed parents keep parents_lt h₁ h₂ hT mca_closed

def collect (L : Local)
    (cert : Certificate parents author roster (self := self) L) : Local where
  head := L.head
  commits := Certificate.keep cert
  head_present := Certificate.head_kept cert

noncomputable def localGC (author : Author) (roster : Set Replica)
    (self : Replica) (L : Local) : Option Local :=
  if h : Nonempty (Certificate parents author roster (self := self) L) then
    some (collect parents L h.some) else none

theorem localGC_refuses_without_evidence (L : Local)
    (h : ¬ EvidenceComplete parents author roster self L) :
    localGC parents author roster self L = none := by
  simp only [localGC]
  split
  · rename_i hex
    exact absurd (Certificate.complete hex.some) h
  · rfl

def StoreSim (full compact : Local) : Prop :=
  full.head = compact.head ∧ compact.commits ⊆ full.commits ∧
  compact.head ∈ compact.commits

theorem collect_simulates (L : Local)
    (cert : Certificate parents author roster (self := self) L) :
    StoreSim L (collect parents L cert) :=
  ⟨rfl, Certificate.support cert, Certificate.head_kept cert⟩

theorem receive_preserves_sim {F C : Local} (h : StoreSim F C) (m : Envelope) :
    StoreSim (receive F m) (receive C m) := by
  refine ⟨h.1, ?_, Or.inl h.2.2⟩
  · intro v hv
    exact hv.elim (fun x => Or.inl (h.2.1 x)) Or.inr

def installHead (L : Local) (v : Version) : Local where
  head := v
  commits := insert v L.commits
  head_present := by
    change v = v ∨ v ∈ L.commits
    exact Or.inl rfl

theorem installHead_preserves_sim {F C : Local} (h : StoreSim F C) (v : Version) :
    StoreSim (installHead F v) (installHead C v) := by
  refine ⟨rfl, ?_, (by
      change v = v ∨ v ∈ C.commits
      exact Or.inl rfl)⟩
  intro w hw
  rcases hw with rfl | hw
  · change w = w ∨ w ∈ F.commits
    exact Or.inl rfl
  · change w = v ∨ w ∈ F.commits
    exact Or.inr (h.2.1 hw)

abbrev World := Replica → Local

/-- The asynchronous implementation: fetch, explicit head synchronization,
and local collection. -/
inductive Step (author : Author) (roster : Set Replica) : World → World → Prop where
  | fetch (W : World) (src dst : Replica) :
      Step author roster W (Function.update W dst (receive (W dst) (advertise (W src))))
  | headSync (W : World) (r : Replica) (v : Version)
      (present : v ∈ (W r).commits) :
      Step author roster W (Function.update W r (installHead (W r) v))
  | gc (W : World) (r : Replica)
      (cert : Certificate parents author roster (self := r) (W r)) :
      Step author roster W (Function.update W r (collect parents (W r) cert))

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
    refine ⟨hd.1, ?_, Or.inl hd.2.2⟩
    · intro v hv
      exact hv.elim (fun x => Or.inl (hd.2.1 x))
        (fun x => Or.inr (hs.2.1 x))
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
    (r : Replica)
    (cert : Certificate parents author roster (self := r) (C r)) :
    WorldSim F (Function.update C r (collect parents (C r) cert)) := by
  intro x
  by_cases hx : x = r
  · subst x
    simp only [Function.update_self]
    exact ⟨(h r).1,
      fun _ hv => (h r).2.1 (Certificate.support cert hv),
      Certificate.head_kept cert⟩
  · simp [Function.update, hx, h x]

/-- One collecting step is matched by either the corresponding no-GC network
step or stuttering. -/
theorem refines_noGC {F C C' : World} (h : WorldSim F C)
    (hs : Step parents author roster C C') :
    ∃ F', NoGCMatch F F' ∧ WorldSim F' C' := by
  cases hs with
  | fetch src dst =>
      refine ⟨_, .visible (.fetch F src dst), fetch_preserves h src dst⟩
  | headSync r v present =>
      have presentF : v ∈ (F r).commits := (h r).2.1 present
      refine ⟨_, .visible (.headSync F r v presentF), headSync_preserves h r v⟩
  | gc r cert =>
      exact ⟨F, .silent F, collect_preserves parents h r cert⟩

inductive Steps (author : Author) (roster : Set Replica) : World → World → Prop where
  | refl (W) : Steps author roster W W
  | tail {A B C} : Steps author roster A B →
      Step parents author roster B C → Steps author roster A C

inductive NoGCSteps : World → World → Prop where
  | refl (W) : NoGCSteps W W
  | tail {A B C} : NoGCSteps A B → NoGCStep B C → NoGCSteps A C

/-- Full trace refinement: local distributed GC is observationally a
stuttering optimization of the asynchronous no-GC protocol. -/
theorem execution_refines_noGC {F₀ C₀ C₁ : World}
    (h₀ : WorldSim F₀ C₀) (hs : Steps parents author roster C₀ C₁) :
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
    stateAt (F r).head = stateAt (C r).head := by rw [(h r).1]

namespace EvidenceSPOT

def spotParents : Version → List Version
  | 1 => [0]
  | 2 => [1]
  | _ => []

def spotAuthor : Author
  | 1 => some 1
  | 2 => none -- the merge/head commit is deliberately unauthored
  | _ => some 0

def completeLocal : Local where
  head := 2
  commits := fun v => v = 0 ∨ v = 1 ∨ v = 2
  head_present := Or.inr (Or.inr rfl)

def missingAuthorLocal : Local where
  head := 2
  commits := fun v => v = 0 ∨ v = 2
  head_present := Or.inr rfl

/-- PASS: a retained commit authored by replica 1 and reaching the head is
enough; no stored per-author index is needed. -/
theorem complete : EvidenceComplete spotParents spotAuthor
    (fun r => r = 0 ∨ r = 1) 0 completeLocal := by
  intro r hr
  rcases hr with rfl | rfl
  · exact Or.inl rfl
  · refine Or.inr ⟨1, ?_⟩
    refine ⟨Or.inr (Or.inl rfl), rfl, ?_⟩
    exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl
      (by change 1 ∈ spotParents 2; simp [spotParents])

/-- FAIL control: merely retaining the head does not fabricate evidence from
replica 1 when no retained commit has that immutable author. -/
theorem missing_author :
    ¬ EvidenceComplete spotParents spotAuthor
      (fun r => r = 0 ∨ r = 1) 0 missingAuthorLocal := by
  intro h
  have h1 := h 1 (Or.inr rfl)
  rcases h1 with impossible | ⟨v, hv⟩
  · exact Nat.noConfusion impossible
  · rcases hv with ⟨hmem, hauthor, _⟩
    change v = 0 ∨ v = 2 at hmem
    rcases hmem with rfl | rfl <;> simp [spotAuthor] at hauthor

end EvidenceSPOT

#print axioms EvidenceSPOT.complete
#print axioms EvidenceSPOT.missing_author
#print axioms execution_refines_noGC

end Sal.MRDTs.GC
