import Sal.ConditionedMRDTs.Metatheory.GenericSafety

/-!
# Generation contracts and guarded execution

`Step3` remains the untrusted environment semantics.  This file layers a
client generation contract over it: only `apply` steps are additionally
checked, against the state stored at the issuing replica's current head.

The history component is deliberately abstract.  In particular it can be the
existential mint-time causal-fold judgment used by the queue; the interface
does not demand that a guard hold for every enumeration of a causal past.

The safety invariant below is also deliberately separate from `D.Inv` and
from `Configuration`.  Its preservation is a conclusion of guarded
reachability, avoiding the circular construction in which a configuration can
only be formed after supplying the invariant one intends to prove.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Classical

/-- A guard holds at one causal enumeration of every event's mint-time past.
This is the weakest common provenance shape needed by order-sensitive guards.
-/
def MintHonest (D : ConditionedMRDTSig)
    (Guard : Op D.AppOp → D.State → Prop)
    (C : Sal.Emulation.Configuration D.toCRDTSig) : Prop :=
  ∀ e, e ∈ C.events →
    ∃ π : List (Op D.AppOp),
      listPermOf π {e' ∈ C.events | C.vis e' e} ∧
      respects π C.vis ∧
      Guard e (applySeq D.toCRDTSig D.init π)

/-- The public generation contract.  `history_of_mint` is the explicit bridge
from a local issuer check to the configuration-history premise consumed by a
datatype's Join theorem. -/
structure GenerationContract (D : ConditionedMRDTSig) where
  Guard : Op D.AppOp → D.State → Prop
  History : Configuration D → Prop
  history_of_mint : ∀ C, MintHonest D Guard (Configuration.core C) → History C

/-- A raw step together with precisely the additional premise owed by an
`apply`: the guard is checked at the issuing replica's materialized head. -/
inductive GuardedStep3 (D : ConditionedMRDTSig) (G : GenerationContract D) :
    Configuration D → Label3 D → Configuration D → Prop where
  | nonApply {C C' : Configuration D} {l : Label3 D} :
      Step3 D C l C' →
      (∀ t r o, l ≠ .apply t r o) →
      GuardedStep3 D G C l C'
  | apply {C C' : Configuration D} {t : Timestamp} {r : Replica}
      {o : D.AppOp} {v : Version} {s : D.State}
      (hhead : C.head r = some v)
      (hver : (C.ver v).map Prod.fst = some s)
      (hguard : G.Guard (t, r, o) s)
      (hstep : Step3 D C (.apply t r o) C') :
      GuardedStep3 D G C (.apply t r o) C'

/-- Widened guarded semantics.  Virtual merges are administrative and owe no
new client premise; base applies must pass `GuardedStep3`. -/
inductive GuardedStep3V (D : ConditionedMRDTSig) (G : GenerationContract D) :
    Configuration D → Label3 D → Configuration D → Prop where
  | base {C C' : Configuration D} {l : Label3 D} :
      GuardedStep3 D G C l C' → GuardedStep3V D G C l C'
  | virtual {C C' : Configuration D} {l : Label3 D} :
      Step3V D C l C' →
      (∀ s : Step3 D C l C', False) →
      GuardedStep3V D G C l C'

theorem GuardedStep3.toRaw {D : ConditionedMRDTSig}
    {G : GenerationContract D} {C C' : Configuration D} {l : Label3 D}
    (h : GuardedStep3 D G C l C') : Step3 D C l C' := by
  cases h with
  | nonApply h _ => exact h
  | apply _ _ _ h => exact h

theorem GuardedStep3V.toRaw {D : ConditionedMRDTSig}
    {G : GenerationContract D} {C C' : Configuration D} {l : Label3 D}
    (h : GuardedStep3V D G C l C') : Step3V D C l C' := by
  cases h with
  | base h => exact .base h.toRaw
  | virtual h _ => exact h

/-- Guarded reachability for ordinary execution. -/
inductive GuardedReach3 (D : ConditionedMRDTSig) (G : GenerationContract D)
    (hInit : D.Inv D.init) : Configuration D → Prop where
  | init : GuardedReach3 D G hInit (initConfig D hInit)
  | step {C C' l} : GuardedReach3 D G hInit C →
      GuardedStep3 D G C l C' → GuardedReach3 D G hInit C'

/-- Guarded reachability for virtual-LCA execution. -/
inductive GuardedReach3V (D : ConditionedMRDTSig) (G : GenerationContract D)
    (hInit : D.Inv D.init) : Configuration D → Prop where
  | init : GuardedReach3V D G hInit (initConfig D hInit)
  | step {C C' l} : GuardedReach3V D G hInit C →
      GuardedStep3V D G C l C' → GuardedReach3V D G hInit C'

/-- Every guarded execution is a raw execution. -/
theorem rawReach_of_guardedReach {D : ConditionedMRDTSig}
    {G : GenerationContract D} {hInit : D.Inv D.init}
    {C : Configuration D} (h : GuardedReach3 D G hInit C) :
    (labeledTS3 D).ReachableFrom (initConfig D hInit) C := by
  induction h with
  | init => exact .refl
  | step _ hs ih => exact ih.tail ⟨_, hs.toRaw⟩

theorem rawReachV_of_guardedReachV {D : ConditionedMRDTSig}
    {G : GenerationContract D} {hInit : D.Inv D.init}
    {C : Configuration D} (h : GuardedReach3V D G hInit C) :
    (labeledTS3V D).ReachableFrom (initConfig D hInit) C := by
  induction h with
  | init => exact .refl
  | step _ hs ih => exact ih.tail ⟨_, hs.toRaw⟩

/-- The initial configuration has vacuous mint provenance. -/
theorem mintHonest_init {D : ConditionedMRDTSig}
    (Guard : Op D.AppOp → D.State → Prop) (hInit : D.Inv D.init) :
    MintHonest D Guard (Configuration.core (initConfig D hInit)) := by
  intro e he
  obtain ⟨r, E, hL, heE⟩ := he
  by_cases hr : r = 0
  · subst r
    simp only [Configuration.core, initConfig, if_pos, Option.some.injEq] at hL
    subst E
    exact absurd heE (Set.notMem_empty e)
  · simp [Configuration.core, initConfig, hr] at hL

/-- Guarded execution with the missing historical evidence made explicit.
Every node, including the post-state, records a causal enumeration witnessing
the local guard at mint time.  This is the smallest sound auxiliary witness:
raw `Configuration` does not retain old issuer heads, so the evidence cannot
in general be reconstructed later.
-/
inductive MintCertifiedReach3 (D : ConditionedMRDTSig)
    (G : GenerationContract D) (hInit : D.Inv D.init) : Configuration D → Prop where
  | init : MintCertifiedReach3 D G hInit (initConfig D hInit)
  | step {C C' l} : MintCertifiedReach3 D G hInit C →
      MintHonest D G.Guard (Configuration.core C) →
      GuardedStep3 D G C l C' →
      MintHonest D G.Guard (Configuration.core C') →
      MintCertifiedReach3 D G hInit C'

inductive MintCertifiedReach3V (D : ConditionedMRDTSig)
    (G : GenerationContract D) (hInit : D.Inv D.init) : Configuration D → Prop where
  | init : MintCertifiedReach3V D G hInit (initConfig D hInit)
  | step {C C' l} : MintCertifiedReach3V D G hInit C →
      MintHonest D G.Guard (Configuration.core C) →
      GuardedStep3V D G C l C' →
      MintHonest D G.Guard (Configuration.core C') →
      MintCertifiedReach3V D G hInit C'

theorem guardedReach_of_mintCertified {D : ConditionedMRDTSig}
    {G : GenerationContract D} {hInit : D.Inv D.init} {C : Configuration D}
    (h : MintCertifiedReach3 D G hInit C) : GuardedReach3 D G hInit C := by
  induction h with
  | init => exact .init
  | step _ _ hs _ ih => exact .step ih hs

theorem mintHonest_of_mintCertified {D : ConditionedMRDTSig}
    {G : GenerationContract D} {hInit : D.Inv D.init} {C : Configuration D}
    (h : MintCertifiedReach3 D G hInit C) :
    MintHonest D G.Guard (Configuration.core C) := by
  cases h with
  | init => exact mintHonest_init G.Guard hInit
  | step _ _ _ hpost => exact hpost

theorem guardedReachV_of_mintCertified {D : ConditionedMRDTSig}
    {G : GenerationContract D} {hInit : D.Inv D.init} {C : Configuration D}
    (h : MintCertifiedReach3V D G hInit C) : GuardedReach3V D G hInit C := by
  induction h with
  | init => exact .init
  | step _ _ hs _ ih => exact .step ih hs

theorem honestReachV_of_mintCertified {D : ConditionedMRDTSig}
    {G : GenerationContract D} {hInit : D.Inv D.init} {C : Configuration D}
    (h : MintCertifiedReach3V D G hInit C) : HonestReachV D G.History hInit C := by
  induction h with
  | init => exact .init
  | step _ hmint hs _ ih =>
      exact ih.step (G.history_of_mint _ hmint) hs.toRaw

/-- A certified guarded execution is contract reachability under the history
predicate generated by the local guard. -/
theorem honestReach_of_mintCertified {D : ConditionedMRDTSig}
    {G : GenerationContract D} {hInit : D.Inv D.init} {C : Configuration D}
    (h : MintCertifiedReach3 D G hInit C) : HonestReach D G.History hInit C := by
  induction h with
  | init => exact .init
  | step _ hmint hs _ ih =>
      exact ih.step (G.history_of_mint _ hmint) hs.toRaw

/-- The checked state and guard are recoverable from every guarded apply. -/
theorem guardedApply_provenance {D : ConditionedMRDTSig}
    {G : GenerationContract D} {C C' : Configuration D}
    {t : Timestamp} {r : Replica} {o : D.AppOp}
    (h : GuardedStep3 D G C (.apply t r o) C') :
    ∃ v s, C.head r = some v ∧ (C.ver v).map Prod.fst = some s ∧
      G.Guard (t, r, o) s := by
  cases h with
  | nonApply _ hne => exact absurd rfl (hne t r o)
  | apply hhead hver hguard _ => exact ⟨_, _, hhead, hver, hguard⟩

def VersionsSatisfy {D : ConditionedMRDTSig}
    (Safe : D.State → Prop) (C : Configuration D) : Prop :=
  ∀ v s E, C.ver v = some (s, E) → Safe s

/-- A safety certificate independent of the signature's structural `Inv`.
Its primitive obligation is deliberately global/history-sensitive: some
valid invariants (notably escrow) are not preserved by an arbitrary ternary
merge of three invariant states, but are preserved for causally related
versions in a certified execution. -/
structure SafetyCertificate (D : ConditionedMRDTSig)
    (G : GenerationContract D) where
  Safe : D.State → Prop
  /-- The client-facing fact extracted from the inductive safety invariant. -/
  Observable : D.State → Prop
  preservation : ∀ {hInit : D.Inv D.init} {C},
    MintCertifiedReach3 D G hInit C → VersionsSatisfy Safe C
  preservationV : ∀ {hInit : D.Inv D.init} {C},
    MintCertifiedReach3V D G hInit C → VersionsSatisfy Safe C
  consequence : ∀ s, Safe s → Observable s

/-- Stronger, local sufficient laws. This optional constructor is convenient
for ordinary inductive invariants, but is not imposed on history-sensitive
certificates. -/
structure LocalSafetyLaws (D : ConditionedMRDTSig)
    (G : GenerationContract D) where
  Safe : D.State → Prop
  Observable : D.State → Prop
  init : Safe D.init
  update : ∀ s e, Safe s → G.Guard e s → Safe (D.update s e)
  merge : ∀ l a b, Safe l → Safe a → Safe b → Safe (D.mergeL l a b)
  version_preservation : ∀ {C C' l}, VersionsSatisfy Safe C →
    GuardedStep3 D G C l C' → VersionsSatisfy Safe C'
  version_preservationV : ∀ {C C' l}, VersionsSatisfy Safe C →
    GuardedStep3V D G C l C' → VersionsSatisfy Safe C'
  consequence : ∀ s, Safe s → Observable s

abbrev VersionsSafe {D : ConditionedMRDTSig} {G : GenerationContract D}
    (S : SafetyCertificate D G) (C : Configuration D) : Prop :=
  VersionsSatisfy S.Safe C

abbrev VersionsObservable {D : ConditionedMRDTSig}
    {G : GenerationContract D} (S : SafetyCertificate D G)
    (C : Configuration D) : Prop :=
  VersionsSatisfy S.Observable C

theorem versionsObservable_of_safe {D : ConditionedMRDTSig}
    {G : GenerationContract D} (S : SafetyCertificate D G)
    {C : Configuration D} (h : VersionsSafe S C) :
    VersionsObservable S C := by
  intro v s E hv
  exact S.consequence s (h v s E hv)

theorem versionsSafe_init {D : ConditionedMRDTSig} {G : GenerationContract D}
    (S : LocalSafetyLaws D G) (hInit : D.Inv D.init) :
    VersionsSatisfy S.Safe (initConfig D hInit) := by
  intro v s E hv
  by_cases h : v = 0
  · subst v
    simp only [initConfig, if_pos, Option.some.injEq, Prod.mk.injEq] at hv
    simpa [hv.1] using S.init
  · simp [initConfig, h] at hv

theorem versionsSafe_of_guardedReach {D : ConditionedMRDTSig}
    {G : GenerationContract D} (S : LocalSafetyLaws D G)
    {hInit : D.Inv D.init} {C : Configuration D}
    (h : GuardedReach3 D G hInit C) : VersionsSatisfy S.Safe C := by
  induction h with
  | init => exact versionsSafe_init S hInit
  | step _ hstep ih => exact S.version_preservation ih hstep

def LocalSafetyLaws.toCertificate {D : ConditionedMRDTSig}
    {G : GenerationContract D} (S : LocalSafetyLaws D G) :
    SafetyCertificate D G where
  Safe := S.Safe
  Observable := S.Observable
  preservation := fun h =>
    versionsSafe_of_guardedReach S (guardedReach_of_mintCertified h)
  preservationV := by
    intro hInit C h
    induction h with
    | init => exact versionsSafe_init S hInit
    | step _ _ hs _ ih => exact S.version_preservationV ih hs
  consequence := S.consequence

/-! PASS/FAIL controls: a guarded apply exposes a witness; it cannot be
mistaken for a non-apply administrative step. -/
example {D : ConditionedMRDTSig} {G : GenerationContract D}
    {C C' : Configuration D} {t r o}
    (h : GuardedStep3 D G C (.apply t r o) C') :
    ∃ v s, C.head r = some v ∧ (C.ver v).map Prod.fst = some s ∧
      G.Guard (t, r, o) s := guardedApply_provenance h

example {D : ConditionedMRDTSig} {G : GenerationContract D}
    {C C' : Configuration D} {t r o}
    (h : GuardedStep3 D G C (.apply t r o) C') :
    ¬ (∀ t' r' o', Label3.apply t r o ≠ Label3.apply t' r' o') := by
  intro hall
  exact hall t r o rfl

#print axioms guardedApply_provenance
#print axioms versionsSafe_of_guardedReach

end Sal.ConditionedMRDTs
