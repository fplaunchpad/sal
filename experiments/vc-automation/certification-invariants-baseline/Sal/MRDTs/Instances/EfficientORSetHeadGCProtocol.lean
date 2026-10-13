import Sal.MRDTs.Instances.EfficientORSetRetirement

/-! # Repeated head-only GC over a supplied causal semantic execution

The semantic heads and uncollected intersection bases are supplied with the
existing history interpretation. GC correctness is proved from the actual
compact operations and the current-head guard, not assumed in transitions.
The fixed finite roster may have any size. Ghost retirement evidence is not
runtime storage and does not change the head representation.
-/

namespace Sal.MRDTs.Instances.EfficientORSet.HeadGC.Protocol
open Sal.MRDTs.Foundation
open Retirement
open Classical

variable {n : Nat}
abbrev Heads (n : Nat) := Fin n → Finset Ev

def global (h : Heads n) : Finset Ev := Finset.univ.biUnion h

theorem mem_global (h : Heads n) (e : Ev) :
    e ∈ global h ↔ ∃ r, e ∈ h r := by simp [global]

/-- A causal execution grows each head's history. An event newly introduced
to the whole system observes every event already known at all replicas. -/
structure Advance (vis : Ev → Ev → Prop) (h h' : Heads n) : Prop where
  grow : ∀ r, h r ⊆ h' r
  sees : ∀ a, (∀ r, a ∈ h r) → ∀ r e, e ∈ h' r → e ∉ global h → vis a e

structure GlobalCut (vis : Ev → Ev → Prop) (h : Heads n)
    (earlier : Finset (Record Nat)) (d : Record Nat) where
  witness : Record Nat
  cut : Finset Ev
  different : witness ≠ d
  same : witness.2.2 = d.2.2
  witnessHere : ∀ r, birth witness ∈ h r
  discardedHere : ∀ r, birth d ∈ h r
  witnessLive : live vis (↑cut) witness
  witnessNotRetired : witness ∉ earlier
  discardedAtCut : birth d ∈ cut
  earlierAtCut : ∀ p ∈ earlier, birth p ∈ cut
  post : ∀ r e, e ∈ h r → e ∉ cut → vis (birth witness) e ∧ vis (birth d) e

def GlobalCut.at {vis h earlier d} (c : @GlobalCut n vis h earlier d) (r : Fin n) :
    CutEvidence vis (h r) earlier d := {
  witness := c.witness, cut := c.cut, different := c.different, same := c.same
  witnessHere := c.witnessHere r, witnessLive := c.witnessLive
  witnessNotRetired := c.witnessNotRetired, discardedAtCut := c.discardedAtCut
  earlierAtCut := c.earlierAtCut, post := c.post r }

def GlobalCut.advance {vis h h' earlier d} (c : @GlobalCut n vis h earlier d)
    (adv : Advance vis h h') : GlobalCut vis h' earlier d := {
  c with
  witnessHere := fun r => adv.grow r (c.witnessHere r)
  discardedHere := fun r => adv.grow r (c.discardedHere r)
  post := by
    intro r e he hk
    by_cases hold : e ∈ global h
    · obtain ⟨s, hs⟩ := (mem_global h e).mp hold
      exact c.post s e hs hk
    · exact ⟨adv.sees _ c.witnessHere r e he hold,
        adv.sees _ c.discardedHere r e he hold⟩ }

inductive GlobalLog (vis : Ev → Ev → Prop) (h : Heads n) :
    Finset (Record Nat) → Prop where
  | empty : GlobalLog vis h ∅
  | retire {earlier d} : GlobalLog vis h earlier → GlobalCut vis h earlier d →
      GlobalLog vis h (insert d earlier)

theorem GlobalLog.at {vis h retired} (log : @GlobalLog n vis h retired) (r : Fin n) :
    Log vis (h r) retired := by
  induction log with
  | empty => exact .empty
  | retire _ cut ih => exact .retire ih (cut.at r)

theorem GlobalLog.seen {vis h retired} (log : @GlobalLog n vis h retired) :
    ∀ d ∈ retired, ∀ r, birth d ∈ h r := by
  induction log with
  | empty => simp
  | @retire earlier d _ cut ih =>
      intro p hp r
      rcases Finset.mem_insert.mp hp with heq | hp
      · subst p; exact cut.discardedHere r
      · exact ih p hp r

theorem GlobalLog.advance {vis h h' retired} (log : @GlobalLog n vis h retired)
    (adv : Advance vis h h') : GlobalLog vis h' retired := by
  induction log with
  | empty => exact .empty
  | retire _ cut ih => exact .retire ih (cut.advance adv)

/-- Reference semantics only: no compact state or GC condition occurs here.
The existing EfficientORSet execution certificate supplies this interpretation. -/
structure Semantic (vis : Ev → Ev → Prop) (n : Nat) where
  events : Heads n
  full : Fin n → State Nat
  represented : ∀ r, Represents vis (↑(events r)) (full r)

structure World (vis : Ev → Ev → Prop) (n : Nat) where
  semantic : Semantic vis n
  compact : Fin n → State Nat
  retired : Finset (Record Nat)

structure Invariant {vis} (w : World vis n) : Prop where
  log : GlobalLog vis w.semantic.events w.retired
  lower : ∀ r, w.semantic.full r \ w.retired ⊆ w.compact r
  upper : ∀ r, w.compact r ⊆ w.semantic.full r
  missing : ∀ d ∈ w.retired, ∃ r, d ∉ w.compact r

def initial (s : Semantic vis n) : World vis n := ⟨s, s.full, ∅⟩

theorem initial_valid (s : Semantic vis n) : Invariant (initial s) :=
  ⟨.empty, by simp [initial], by simp [initial], by simp [initial]⟩

theorem queries_equal {vis} (trans : Transitive vis)
    (clock : ∀ a b, vis a b → a.1 < b.1)
    {w : World vis n} (inv : Invariant w) (r : Fin n) :
    elements (w.compact r) = elements (w.semantic.full r) :=
  compact_query_correct vis trans clock _ _ _ (w.semantic.represented r)
    (inv.log.at r) (inv.lower r) (inv.upper r)

theorem update_mono (e : Ev) {a b : State Nat} (h : a ⊆ b) :
    update a e ⊆ update b e := by
  intro p hp
  rw [mem_update_iff] at hp ⊢
  exact hp.elim Or.inl (fun hh => Or.inr ⟨h hh.1, hh.2⟩)

theorem update_lower (e : Ev) (retired : Finset (Record Nat))
    {a b : State Nat} (h : a \ retired ⊆ b) :
    update a e \ retired ⊆ update b e := by
  intro p hp
  obtain ⟨hp, hn⟩ := Finset.mem_sdiff.mp hp
  rw [mem_update_iff] at hp ⊢
  exact hp.elim Or.inl (fun hh => Or.inr ⟨h (Finset.mem_sdiff.mpr ⟨hh.1, hn⟩), hh.2⟩)

theorem merge_mono (l : State Nat) {a b a' b' : State Nat}
    (ha : a ⊆ a') (hb : b ⊆ b') : merge l a b ⊆ merge l a' b' := by
  intro p hp
  simp only [merge, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at hp ⊢
  rcases hp with (⟨⟨hl, hap⟩, hbp⟩ | ⟨hap, hn⟩) | ⟨hbp, hn⟩
  · exact Or.inl (Or.inl ⟨⟨hl, ha hap⟩, hb hbp⟩)
  · exact Or.inl (Or.inr ⟨ha hap, hn⟩)
  · exact Or.inr ⟨hb hbp, hn⟩

theorem merge_lower (l : State Nat) (retired : Finset (Record Nat))
    {a b a' b' : State Nat} (ha : a \ retired ⊆ a') (hb : b \ retired ⊆ b') :
    merge l a b \ retired ⊆ merge l a' b' := by
  intro p hp
  obtain ⟨hp, hn⟩ := Finset.mem_sdiff.mp hp
  have hpa : p ∈ a → p ∈ a' := fun h => ha (Finset.mem_sdiff.mpr ⟨h, hn⟩)
  have hpb : p ∈ b → p ∈ b' := fun h => hb (Finset.mem_sdiff.mpr ⟨h, hn⟩)
  simp only [merge, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at hp ⊢
  tauto

/-- A known record missing at the collecting replica cannot reappear there.
This uses the original semantic base and the source's full interpretation. -/
theorem missing_merge {vis} (E F : Finset Ev) (l b cb ca : State Nat)
    (base : Represents vis (↑(E ∩ F)) l) (source : Represents vis (↑F) b)
    (upper : cb ⊆ b) (d : Record Nat) (known : birth d ∈ E)
    (absent : d ∉ ca) : d ∉ merge l ca cb := by
  intro hm
  have fromB : d ∈ cb ∧ d ∉ l := by
    simpa [merge, absent] using hm
  have liveB := (source d).mp (upper fromB.1)
  apply fromB.2
  apply (base d).mpr
  refine ⟨?_, ?_⟩
  · exact Finset.mem_inter.mpr ⟨known, liveB.1⟩
  · rintro ⟨e, he, hv, hk⟩
    exact liveB.2 ⟨e, (Finset.mem_inter.mp he).2, hv, hk⟩

/-- The new ghost cut is constructed FROM the actual global-presence guard.
It does not ask the caller for a query-preservation proof. -/
def makeCut {vis} {w : World vis n} (inv : Invariant w) (r : Fin n)
    (a d : Record Nat) (different : a ≠ d) (same : a.2.2 = d.2.2)
    (allA : ∀ j, a ∈ w.compact j) (allD : ∀ j, d ∈ w.compact j) :
    GlobalCut vis w.semantic.events w.retired d := {
  witness := a
  cut := global w.semantic.events
  different := different
  same := same
  witnessHere := fun j => ((w.semantic.represented j a).mp (inv.upper j (allA j))).1
  discardedHere := fun j => ((w.semantic.represented j d).mp (inv.upper j (allD j))).1
  witnessLive := by
    refine ⟨?_, ?_⟩
    · exact (mem_global _ _).mpr ⟨r,
        ((w.semantic.represented r a).mp (inv.upper r (allA r))).1⟩
    · rintro ⟨e, he, hv, hk⟩
      obtain ⟨j, hj⟩ := (mem_global _ _).mp he
      exact ((w.semantic.represented j a).mp (inv.upper j (allA j))).2 ⟨e, hj, hv, hk⟩
  witnessNotRetired := by
    intro h
    obtain ⟨j, hj⟩ := inv.missing a h
    exact hj (allA j)
  discardedAtCut := (mem_global _ _).mpr ⟨r,
    ((w.semantic.represented r d).mp (inv.upper r (allD r))).1⟩
  earlierAtCut := fun p hp => (mem_global _ _).mpr ⟨r, inv.log.seen p hp r⟩
  post := by
    intro j e he hn
    exact False.elim (hn ((mem_global _ _).mpr ⟨j, he⟩)) }

def collect (w : World vis n) (r : Fin n) (d : Record Nat) : World vis n :=
  ⟨w.semantic, Function.update w.compact r ((w.compact r).erase d), insert d w.retired⟩

theorem collect_valid {vis} {w : World vis n} (inv : Invariant w) (r : Fin n)
    (a d : Record Nat) (different : a ≠ d) (same : a.2.2 = d.2.2)
    (allA : ∀ j, a ∈ w.compact j) (allD : ∀ j, d ∈ w.compact j) :
    Invariant (collect w r d) := by
  refine ⟨.retire inv.log (makeCut inv r a d different same allA allD), ?_, ?_, ?_⟩
  · intro j p hp
    obtain ⟨hp, hn⟩ := Finset.mem_sdiff.mp hp
    have hnd : p ≠ d := fun h => hn (Finset.mem_insert.mpr (Or.inl h))
    have hnr : p ∉ w.retired := fun h => hn (Finset.mem_insert.mpr (Or.inr h))
    have hc := inv.lower j (Finset.mem_sdiff.mpr ⟨hp, hnr⟩)
    by_cases hj : j = r
    · subst j
      simpa [collect] using Finset.mem_erase.mpr ⟨hnd, hc⟩
    · simpa [collect, Function.update, hj] using hc
  · intro j p hp
    by_cases hj : j = r
    · subst j
      exact inv.upper r (Finset.mem_erase.mp (by simpa [collect] using hp)).2
    · exact inv.upper j (by simpa [collect, Function.update, hj] using hp)
  · intro p hp
    rcases Finset.mem_insert.mp hp with h | h
    · subst p
      exact ⟨r, by simp [collect]⟩
    · obtain ⟨j, hj⟩ := inv.missing p h
      refine ⟨j, ?_⟩
      by_cases heq : j = r
      · subst j
        simp [collect, hj]
      · simpa [collect, Function.update, heq] using hj

def applyHead (w : World vis n) (s' : Semantic vis n) (r : Fin n) (e : Ev) : World vis n :=
  ⟨s', Function.update w.compact r (update (w.compact r) e), w.retired⟩

/-- A replica may apply an already certified retirement later. It need not
re-establish simultaneous physical presence, which the first collection has
already destroyed. The retirement log is unchanged. -/
theorem collect_retired_valid {vis} {w : World vis n} (inv : Invariant w)
    (r : Fin n) (d : Record Nat) (retired : d ∈ w.retired) :
    Invariant (collect w r d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [collect, Finset.insert_eq_of_mem retired] using inv.log
  · intro j p hp
    obtain ⟨hp, hn⟩ := Finset.mem_sdiff.mp hp
    have hnd : p ≠ d := fun h => hn (Finset.mem_insert.mpr (Or.inl h))
    have hnr : p ∉ w.retired := fun h => hn (Finset.mem_insert.mpr (Or.inr h))
    have hc := inv.lower j (Finset.mem_sdiff.mpr ⟨hp, hnr⟩)
    by_cases hj : j = r
    · subst j
      simpa [collect] using Finset.mem_erase.mpr ⟨hnd, hc⟩
    · simpa [collect, Function.update, hj] using hc
  · intro j p hp
    by_cases hj : j = r
    · subst j
      exact inv.upper r (Finset.mem_erase.mp (by simpa [collect] using hp)).2
    · exact inv.upper j (by simpa [collect, Function.update, hj] using hp)
  · intro p hp
    have hp' : p ∈ w.retired := by simpa [collect, Finset.insert_eq_of_mem retired] using hp
    obtain ⟨j, hj⟩ := inv.missing p hp'
    refine ⟨j, ?_⟩
    by_cases heq : j = r
    · subst j
      simp [collect, hj]
    · simpa [collect, Function.update, heq] using hj

theorem apply_valid {vis} {w : World vis n} (inv : Invariant w)
    (s' : Semantic vis n) (r : Fin n) (e : Ev)
    (adv : Advance vis w.semantic.events s'.events)
    (full : s'.full = Function.update w.semantic.full r (update (w.semantic.full r) e))
    (fresh : ∀ j p, birth p ∈ w.semantic.events j → e.1 ≠ p.2.1) :
    Invariant (applyHead w s' r e) := by
  refine ⟨inv.log.advance adv, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j = r
    · subst j
      simpa [applyHead, full] using update_lower e w.retired (inv.lower r)
    · simpa [applyHead, full, Function.update, hj] using inv.lower j
  · intro j
    by_cases hj : j = r
    · subst j
      simpa [applyHead, full] using update_mono e (inv.upper r)
    · simpa [applyHead, full, Function.update, hj] using inv.upper j
  · intro d hd
    obtain ⟨j, hj⟩ := inv.missing d hd
    refine ⟨j, ?_⟩
    by_cases h : j = r
    · subst j
      change d ∉ Function.update w.compact r (update (w.compact r) e) r
      simp only [Function.update_self]
      intro hmem
      rw [mem_update_iff] at hmem
      rcases hmem with heq | hmem
      · exact fresh r d (inv.log.seen d hd r) (congrArg Prod.fst heq)
      · exact hj hmem.1
    · simpa [applyHead, Function.update, h] using hj

def mergeHeads (w : World vis n) (s' : Semantic vis n)
    (r peer : Fin n) (l : State Nat) : World vis n :=
  ⟨s', Function.update w.compact r (merge l (w.compact r) (w.compact peer)), w.retired⟩

theorem merge_valid {vis} {w : World vis n} (inv : Invariant w)
    (s' : Semantic vis n) (r peer : Fin n) (l : State Nat)
    (adv : Advance vis w.semantic.events s'.events)
    (full : s'.full = Function.update w.semantic.full r
      (merge l (w.semantic.full r) (w.semantic.full peer)))
    (base : Represents vis (↑(w.semantic.events r ∩ w.semantic.events peer)) l) :
    Invariant (mergeHeads w s' r peer l) := by
  refine ⟨inv.log.advance adv, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j = r
    · subst j
      simpa [mergeHeads, full] using merge_lower l w.retired (inv.lower r) (inv.lower peer)
    · simpa [mergeHeads, full, Function.update, hj] using inv.lower j
  · intro j
    by_cases hj : j = r
    · subst j
      simpa [mergeHeads, full] using merge_mono l (inv.upper r) (inv.upper peer)
    · simpa [mergeHeads, full, Function.update, hj] using inv.upper j
  · intro d hd
    obtain ⟨j, hj⟩ := inv.missing d hd
    refine ⟨j, ?_⟩
    by_cases h : j = r
    · subst j
      simpa [mergeHeads] using missing_merge _ _ l _ _ _ base
        (w.semantic.represented peer) (inv.upper peer) d (inv.log.seen d hd r) hj
    · simpa [mergeHeads, Function.update, h] using hj

/-- The causal-advance obligation follows directly from ordinary update
history growth and the issuer observing its own head. -/
theorem advance_apply {vis} (h : Heads n) (r : Fin n) (e : Ev)
    (sees : ∀ a ∈ h r, vis a e) :
    Advance vis h (Function.update h r (insert e (h r))) := by
  constructor
  · intro j a ha
    by_cases hj : j = r
    · subst j; simpa using Finset.mem_insert_of_mem ha
    · simpa [Function.update, hj] using ha
  · intro a allA j z hz hn
    by_cases hj : j = r
    · subst j
      have hz' : z ∈ insert e (h r) := by simpa using hz
      rcases Finset.mem_insert.mp hz' with heq | hold
      · subst z; exact sees a (allA r)
      · exact False.elim (hn ((mem_global _ _).mpr ⟨r, hold⟩))
    · have hold : z ∈ h j := by simpa [Function.update, hj] using hz
      exact False.elim (hn ((mem_global _ _).mpr ⟨j, hold⟩))

theorem advance_merge {vis} (h : Heads n) (r peer : Fin n) :
    Advance vis h (Function.update h r (h r ∪ h peer)) := by
  constructor
  · intro j a ha
    by_cases hj : j = r
    · subst j; simpa using Finset.mem_union_left (h peer) ha
    · simpa [Function.update, hj] using ha
  · intro a _ j e he hn
    apply False.elim
    apply hn
    apply (mem_global _ _).mpr
    by_cases hj : j = r
    · subst j
      have he' : e ∈ h r ∪ h peer := by simpa using he
      exact (Finset.mem_union.mp he').elim (fun hh => ⟨r, hh⟩) (fun hh => ⟨peer, hh⟩)
    · exact ⟨j, by simpa [Function.update, hj] using he⟩

/-- Reference states evolve by the ordinary datatype equations. Collection
is the local erase operation guarded by actual global presence and timestamp
order. No transition premise mentions compact query correctness. -/
inductive Step (vis : Ev → Ev → Prop) : World vis n → World vis n → Prop where
  | apply {w : World vis n} (s' : Semantic vis n) (r : Fin n) (e : Ev)
      (events : s'.events = Function.update w.semantic.events r (insert e (w.semantic.events r)))
      (full : s'.full = Function.update w.semantic.full r (update (w.semantic.full r) e))
      (sees : ∀ a ∈ w.semantic.events r, vis a e)
      (fresh : ∀ j p, birth p ∈ w.semantic.events j → e.1 ≠ p.2.1) :
      Step vis w (applyHead w s' r e)
  | merge {w : World vis n} (s' : Semantic vis n) (r peer : Fin n) (l : State Nat)
      (events : s'.events = Function.update w.semantic.events r
        (w.semantic.events r ∪ w.semantic.events peer))
      (full : s'.full = Function.update w.semantic.full r
        (merge l (w.semantic.full r) (w.semantic.full peer)))
      (base : Represents vis (↑(w.semantic.events r ∩ w.semantic.events peer)) l) :
      Step vis w (mergeHeads w s' r peer l)
  | collect {w : World vis n} (r : Fin n) (a d : Record Nat)
      (ordered : a.2.1 < d.2.1) (same : a.2.2 = d.2.2)
      (allA : ∀ j, a ∈ w.compact j) (allD : ∀ j, d ∈ w.compact j) :
      Step vis w (collect w r d)
  | collectKnown {w : World vis n} (r : Fin n) (d : Record Nat)
      (certified : d ∈ w.retired) : Step vis w (collect w r d)

theorem Step.preserves {vis} {w w' : World vis n}
    (step : Step vis w w') (inv : Invariant w) : Invariant w' := by
  cases step with
  | apply s' r e events full sees fresh =>
      apply apply_valid inv s' r e _ full fresh
      rw [events]
      exact advance_apply _ r e sees
  | merge s' r peer l events full base =>
      apply merge_valid inv s' r peer l _ full base
      rw [events]
      exact advance_merge _ r peer
  | collect r a d ordered same allA allD =>
      apply collect_valid inv r a d _ same allA allD
      intro heq
      exact Nat.ne_of_lt ordered (congrArg (fun p : Record Nat => p.2.1) heq)
  | collectKnown r d certified => exact collect_retired_valid inv r d certified

inductive Steps (vis : Ev → Ev → Prop) : World vis n → World vis n → Prop where
  | refl (w) : Steps vis w w
  | tail {w w' w''} : Steps vis w w' → Step vis w' w'' → Steps vis w w''

theorem Steps.preserves {vis} {w w' : World vis n}
    (run : Steps vis w w') (inv : Invariant w) : Invariant w' := by
  induction run with
  | refl => exact inv
  | tail _ step ih => exact step.preserves ih

/-- Arbitrarily many updates, merges and head-only retirements preserve every
head query. The roster is fixed and all bases carry the uncollected semantic
interpretation. The reference execution may have arbitrary causal branching. -/
theorem repeated_gc_correct {vis} (trans : Transitive vis)
    (clock : ∀ a b, vis a b → a.1 < b.1)
    (start : Semantic vis n) {finish : World vis n}
    (run : Steps vis (initial start) finish) (r : Fin n) :
    elements (finish.compact r) = elements (finish.semantic.full r) :=
  queries_equal trans clock (run.preserves (initial_valid start)) r

#print axioms makeCut
#print axioms Step.preserves
#print axioms repeated_gc_correct

end Sal.MRDTs.Instances.EfficientORSet.HeadGC.Protocol
