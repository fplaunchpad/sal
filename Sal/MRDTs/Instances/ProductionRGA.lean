import Sal.MRDTs.Instances.EmbedRGASequential
import Sal.MRDTs.Instances.SidedEmbedRGASequential

/-! Complete paper-facing certificates for the one- and two-sided embedded
RGAs. -/

namespace Sal.MRDTs.Instances.ProductionRGA

open Sal.MRDTs.Foundation
open Sal.EmbedRGA (OrderedPrefixCode)

variable {α : Type} [DecidableEq α] [Inhabited α]

namespace EmbedWitness

open Sal.MRDTs.Instances.EmbedRGA

def isInsert (e : Op (EOp α)) : Bool := eIsIns e

def leBool (a b : Op (EOp α)) : Bool :=
  match a.2.2, b.2.2 with
  | .ins _ _ _, .ins _ _ _ => decide (a.1 ≤ b.1)
  | .ins _ _ _, .del _ => true
  | .del _, .ins _ _ _ => false
  | .del _, .del _ => true

def LE (a b : Op (EOp α)) : Prop := leBool a b = true

def canonical (ops : List (Op (EOp α))) : List (Op (EOp α)) :=
  ops.mergeSort leBool

theorem canonical_perm (ops : List (Op (EOp α))) :
    ops.Perm (canonical ops) :=
  (List.mergeSort_perm ops leBool).symm

theorem canonical_listPermOf {ops : List (Op (EOp α))}
    {E : Set (Op (EOp α))} (h : listPermOf ops E) :
    listPermOf (canonical ops) E := by
  have hp := canonical_perm ops
  exact ⟨hp.nodup h.1, fun e => (hp.mem_iff (a := e)).symm.trans (h.2 e)⟩

theorem canonical_ordered (ops : List (Op (EOp α))) :
    (canonical ops).Pairwise LE := by
  unfold canonical LE
  apply List.pairwise_mergeSort
  · rintro ⟨ta, ra, oa⟩ ⟨tb, rb, ob⟩ ⟨tc, rc, oc⟩ hab hbc
    cases oa <;> cases ob <;> cases oc <;> simp [leBool] at *
    exact Nat.le_trans hab hbc
  · rintro ⟨ta, ra, oa⟩ ⟨tb, rb, ob⟩
    cases oa <;> cases ob <;> simp [leBool]
    exact Nat.le_total ta tb

theorem prefix_wf {Γ : OrderedPrefixCode} {whole pre suffix : List (Op (EOp α))}
    (h : EWf Γ whole) (split : whole = pre ++ suffix) : EWf Γ pre := by
  subst whole
  induction suffix using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton suffix e ih =>
      apply ih
      have hh : EWf Γ ((pre ++ suffix) ++ [e]) := by
        simpa [List.append_assoc] using h
      exact hh.prefix

theorem dels_nil_of_insert_only {ops : List (Op (EOp α))}
    (h : ∀ e ∈ ops, eIsIns e = true) : eDels ops = [] := by
  induction ops with
  | nil => rfl
  | cons e rest ih =>
      obtain ⟨ts, replica, op⟩ := e
      cases op with
      | del x =>
          have bad := h (ts, replica, .del x) List.mem_cons_self
          simp [eIsIns] at bad
      | ins el pref anchor =>
          change eDels rest = []
          exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem wf_of_insert_only {Γ : OrderedPrefixCode}
    {C : Configuration (E Γ α)} {ops : List (Op (EOp α))}
    (hnd : ops.Nodup)
    (hsub : ∀ e ∈ ops, e ∈ C.events)
    (hhon : EHonestCore Γ C.core)
    (hins : ∀ e ∈ ops, eIsIns e = true) : EWf Γ ops where
  ins_nodup := by
    apply List.Nodup.map_on ?_ (hnd.filter _)
    intro a ha b hb htime
    exact C.core.ts_unique (hsub a (List.mem_of_mem_filter ha))
      (hsub b (List.mem_of_mem_filter hb)) htime
  del_late := by
    intro pre e post split he hdel
    rw [dels_nil_of_insert_only (fun x hx => hins x (by rw [split]; simp [hx]))]
      at hdel
    simp at hdel
  keys_inj := by
    obtain ⟨chainOf, hchain⟩ := hhon.chain_gen
    intro o₁ h₁ o₂ h₂ hi₁ hi₂ hne hkey
    obtain ⟨hp₁, hc₁, hs₁⟩ := hchain o₁ (hsub o₁ h₁) hi₁
    obtain ⟨hp₂, hc₂, hs₂⟩ := hchain o₂ (hsub o₂ h₂) hi₂
    apply hne
    have hc : Sal.EmbedRGA.coordOf Γ (chainOf o₁.1) =
        Sal.EmbedRGA.coordOf Γ (chainOf o₂.1) := by
      rw [← hc₁, ← hc₂]
      exact Sal.EmbedRGA.key_inj hkey
    have hsame := Sal.EmbedRGA.coordOf_inj Γ hp₁ hp₂ hc
    calc o₁.1 = (chainOf o₁.1).sum := hs₁.symm
      _ = (chainOf o₂.1).sum := by rw [hsame]
      _ = o₂.1 := hs₂

theorem earlier_insert_mem_prefix {whole pre suffix : List (Op (EOp α))}
    {current parent : Op (EOp α)}
    (ordered : whole.Pairwise LE)
    (split : whole = pre ++ current :: suffix)
    (parentMem : parent ∈ whole)
    (currentIns : eIsIns current = true)
    (parentIns : eIsIns parent = true)
    (earlier : parent.1 < current.1) : parent ∈ pre := by
  subst whole
  rw [List.mem_append] at parentMem
  rcases parentMem with hp | hp
  · exact hp
  · simp only [List.mem_cons] at hp
    rcases hp with rfl | hs
    · exact (Nat.lt_irrefl _ earlier).elim
    · have cross := (List.pairwise_append.mp ordered).2.1
      have rel := (List.pairwise_cons.mp cross).1 parent hs
      obtain ⟨ct, cr, cop⟩ := current
      obtain ⟨pt, pr, pop⟩ := parent
      cases cop with
      | del x => simp [eIsIns] at currentIns
      | ins cel cpref canchor =>
          cases pop with
          | del x => simp [eIsIns] at parentIns
          | ins pel ppref panchor =>
              simp [LE, leBool] at rel
              exact (Nat.not_le_of_lt earlier rel).elim

theorem insert_mem_prefix_of_delete {whole pre suffix : List (Op (EOp α))}
    {current parent : Op (EOp α)}
    (ordered : whole.Pairwise LE)
    (split : whole = pre ++ current :: suffix)
    (parentMem : parent ∈ whole)
    (currentDel : eIsIns current = false)
    (parentIns : eIsIns parent = true) : parent ∈ pre := by
  subst whole
  rw [List.mem_append] at parentMem
  rcases parentMem with hp | hp
  · exact hp
  · simp only [List.mem_cons] at hp
    rcases hp with rfl | hs
    · rw [parentIns] at currentDel
      simp at currentDel
    · have cross := (List.pairwise_append.mp ordered).2.1
      have rel := (List.pairwise_cons.mp cross).1 parent hs
      obtain ⟨ct, cr, cop⟩ := current
      obtain ⟨pt, pr, pop⟩ := parent
      cases cop <;> cases pop <;> simp [eIsIns, LE, leBool] at *

theorem prefix_insert_only {whole pre suffix : List (Op (EOp α))}
    {current : Op (EOp α)} (ordered : whole.Pairwise LE)
    (split : whole = pre ++ current :: suffix)
    (currentIns : eIsIns current = true) :
    ∀ e ∈ pre, eIsIns e = true := by
  intro e he
  subst whole
  have cross := (List.pairwise_append.mp ordered).2.2
  have rel := cross e he current List.mem_cons_self
  obtain ⟨et, er, eop⟩ := e
  obtain ⟨ct, cr, cop⟩ := current
  cases eop <;> cases cop <;> simp [eIsIns, LE, leBool] at *

end EmbedWitness

def embedSpec : SequentialMachine (Op (Sal.MRDTs.Instances.EmbedRGA.EOp α)) where
  State := List (ℕ × α)
  init := []
  step := Sal.MRDTs.Instances.EmbedRGA.eSpecStep

/-- Implementation-independent client legality. The carried prefix must name
the coordinate of an earlier allocated anchor; deletion only requires earlier
allocation, so repeated concurrent deletion remains legal. -/
def embedLegal (Γ : OrderedPrefixCode)
    (ops : List (Op (Sal.MRDTs.Instances.EmbedRGA.EOp α))) : Prop :=
  ∀ pre current post, ops = pre ++ current :: post →
    match current.2.2 with
    | .ins _ pref anchor =>
        (∀ x ∈ Sal.MRDTs.Instances.EmbedRGA.eInsIds pre, x < current.1) ∧
        ((anchor = 0 ∧ pref = []) ∨
          ∃ parent ∈ pre,
            Sal.MRDTs.Instances.EmbedRGA.eIsIns parent = true ∧
            parent.1 = anchor ∧
            Sal.MRDTs.Instances.EmbedRGA.eCoord Γ parent = pref)
    | .del target =>
        ∃ parent ∈ pre,
          Sal.MRDTs.Instances.EmbedRGA.eIsIns parent = true ∧
          parent.1 = target

theorem embedLegal_of_seqOK {Γ : OrderedPrefixCode}
    {ops : List (Op (Sal.MRDTs.Instances.EmbedRGA.EOp α))}
    (h : Sal.MRDTs.Instances.EmbedRGA.eSeqOK Γ ops) :
    embedLegal Γ ops := by
  open Sal.MRDTs.Instances.EmbedRGA in
    intro pre current post split
    have hc := h pre current post split
    obtain ⟨ts, replica, action⟩ := current
    cases action with
    | del target => exact hc
    | ins el pref anchor =>
        refine ⟨hc.1, ?_⟩
        rcases hc.2.2 with hroot | ⟨anchorEl, hanchor⟩
        · exact Or.inl hroot
        · obtain ⟨parent, hparent, hpins, hrec⟩ :=
            e_fold_rec_sub Γ pre (anchor, anchorEl, pref) hanchor
          refine Or.inr ⟨parent, hparent, hpins, ?_, ?_⟩
          · have hfirst := congrArg (fun r : ERec α => r.1) hrec
            simpa [eRecOf] using hfirst.symm
          · have hcoord := congrArg (fun r : ERec α => r.2.2) hrec
            simpa [eRecOf] using hcoord.symm

noncomputable def embedClientSpec (Γ : OrderedPrefixCode) :
    SequentialSpec (Sal.MRDTs.Instances.EmbedRGA.E Γ α) where
  toSequentialMachine := embedSpec
  Legal := embedLegal Γ
  query := fun q _ => q.map Prod.snd

def embedRel (s : Sal.MRDTs.Instances.EmbedRGA.EState α)
    (q : List (ℕ × α)) : Prop :=
  s.map Sal.MRDTs.Instances.EmbedRGA.eProj = q

theorem embed_respects_loOn_of_lo {Γ : OrderedPrefixCode}
    {C : Sal.MRDTs.Foundation.Configuration
      (Sal.MRDTs.Instances.EmbedRGA.E Γ α).toCRDTSig}
    {E : Set (Op (Sal.MRDTs.Instances.EmbedRGA.EOp α))}
    {ops : List (Op (Sal.MRDTs.Instances.EmbedRGA.EOp α))}
    (h : respects ops (Sal.MRDTs.Foundation.lo C)) :
    respects ops (loOn C E) := by
  open Sal.MRDTs.Instances.EmbedRGA in
    unfold respects at h ⊢
    apply h.imp
    intro a b hab hOn
    apply hab
    rw [loOn_iff_of_rc_either (E_rc_either Γ)] at hOn
    exact Or.inl hOn

def embedSequential (Γ : OrderedPrefixCode) :
    SequentialRefinement (Sal.MRDTs.Instances.EmbedRGA.E Γ α) embedSpec where
  Honest := Sal.MRDTs.Instances.EmbedRGA.eSeqOK Γ
  Rel s q := s.map Sal.MRDTs.Instances.EmbedRGA.eProj = q
  init := rfl
  sound := by
    intro ops h
    simpa [embedSpec, SequentialMachine.run, Sal.MRDTs.Instances.EmbedRGA.eSpecFold, Sal.MRDTs.Instances.EmbedRGA.eFold] using
      (Sal.MRDTs.Instances.EmbedRGA.embed_seq_sound (Γ := Γ) h)

theorem embedSequential_of_mint {Γ : OrderedPrefixCode}
    {ops : List (Op (Sal.MRDTs.Instances.EmbedRGA.EOp α))}
    (h : LinearMintHistory (Sal.MRDTs.Instances.EmbedRGA.E Γ α) Sal.MRDTs.Instances.EmbedRGA.eApplicable ops) : Sal.MRDTs.Instances.EmbedRGA.eSeqOK Γ ops := by
  intro pre e post heq
  obtain ⟨ts, replica, op⟩ := e
  cases op with
  | ins el pref anchor =>
      refine ⟨?_, h.guarded pre _ post heq⟩
      intro x hx
      obtain ⟨old, hold, _hins, htime⟩ :=
        Sal.MRDTs.Instances.EmbedRGA.mem_eInsIds.mp hx
      rw [← htime]
      exact h.clocked pre _ post heq old hold
  | del x =>
      have hg := h.guarded pre (ts, replica, .del x) post heq
      simp only [Sal.MRDTs.Instances.EmbedRGA.eApplicable] at hg
      obtain ⟨rec, hrec, hidx⟩ := List.mem_map.mp hg
      obtain ⟨iop, hiop, hins, hieq⟩ :=
        Sal.MRDTs.Instances.EmbedRGA.e_fold_rec_sub Γ pre rec hrec
      refine ⟨iop, hiop, hins, ?_⟩
      rw [hieq] at hidx
      exact hidx

theorem embedCanonical_seqOK {Γ : OrderedPrefixCode}
    {C : Configuration (Sal.MRDTs.Instances.EmbedRGA.E Γ α)}
    (exec : CertifiedExecution (Sal.MRDTs.Instances.EmbedRGA.E Γ α)
      (Sal.MRDTs.Instances.EmbedRGA.generation Γ) C)
    {v : Version} {s : (Sal.MRDTs.Instances.EmbedRGA.E Γ α).State}
    {E : Set (Op (Sal.MRDTs.Instances.EmbedRGA.EOp α))}
    (hver : C.ver v = some (s, E))
    {ops : List (Op (Sal.MRDTs.Instances.EmbedRGA.EOp α))}
    (hperm : listPermOf ops E) :
    Sal.MRDTs.Instances.EmbedRGA.eSeqOK Γ
      (EmbedWitness.canonical ops) := by
  open Sal.MRDTs.Instances.EmbedRGA in
    have hgood : GoodConfig3 C := exec.goodConfig (fun _ hmint =>
      e_join_at (eHonest_core (eHonest_of_mint hmint)))
    have hsub := hgood.ver_events_sub v s E hver
    have hclosed := hgood.ver_causal v s E hver
    have hmint := exec.mintHonest
    have hhon : EHonestCore Γ C.core :=
      eHonest_core (eHonest_of_mint hmint)
    have hcan := EmbedWitness.canonical_listPermOf hperm
    have hord := EmbedWitness.canonical_ordered ops
    intro pre current post split
    have hordSplit :
        (pre ++ current :: post).Pairwise EmbedWitness.LE := by
      simpa [split] using hord
    have hcurrentList : current ∈ EmbedWitness.canonical ops := by
      rw [split]
      simp
    have hcurrentE : current ∈ E := (hcan.2 current).mp hcurrentList
    have hcurrentC : current ∈ C.events := hsub current hcurrentE
    obtain ⟨ts, replica, action⟩ := current
    cases action with
    | ins el pref anchor =>
        have hpreIns : ∀ e ∈ pre, eIsIns e = true :=
          EmbedWitness.prefix_insert_only hord split (by simp [eIsIns])
        have hclock : ∀ x ∈ eInsIds pre, x < ts := by
          intro x hx
          obtain ⟨old, hold, holdIns, holdTime⟩ := mem_eInsIds.mp hx
          have holdList : old ∈ EmbedWitness.canonical ops := by
            rw [split]
            exact List.mem_append_left _ hold
          have holdE : old ∈ E := (hcan.2 old).mp holdList
          have cross := (List.pairwise_append.mp hordSplit).2.2
          have hleRaw := cross old hold (ts, replica, .ins el pref anchor)
            List.mem_cons_self
          have hle : old.1 ≤ ts := by
            obtain ⟨ot, orp, oop⟩ := old
            cases oop <;> simp [eIsIns] at holdIns
            simpa [EmbedWitness.LE, EmbedWitness.leBool] using hleRaw
          have hne : old.1 ≠ ts := by
            intro heq
            have hop : old = (ts, replica, .ins el pref anchor) :=
              C.core.ts_unique (hsub old holdE) hcurrentC heq
            subst old
            have hnd := hcan.1
            rw [split, List.nodup_append] at hnd
            exact hnd.2.2 _ hold _ List.mem_cons_self rfl
          rw [← holdTime]
          exact Nat.lt_of_le_of_ne hle hne
        obtain ⟨origin, horigin, _, hguard⟩ := hmint _ hcurrentC
        change eApplicable (ts, replica, .ins el pref anchor) (eFold Γ origin) at hguard
        simp only [eApplicable] at hguard
        refine ⟨hclock, hguard.1, ?_⟩
        rcases hguard.2 with hroot | ⟨anchorEl, hanchorOrigin⟩
        · exact Or.inl hroot
        · obtain ⟨parent, hparentOrigin, hparentIns, hparentRec⟩ :=
            e_fold_rec_sub Γ origin (anchor, anchorEl, pref) hanchorOrigin
          have hparentPast := (horigin.2 parent).mp hparentOrigin
          have hparentE : parent ∈ E :=
            hclosed parent (ts, replica, .ins el pref anchor)
              hparentPast.2 hcurrentE
          have hparentAll : parent ∈ EmbedWitness.canonical ops :=
            (hcan.2 parent).mpr hparentE
          have hparentTime : parent.1 = anchor := by
            have hfirst := congrArg (fun r : ERec α => r.1) hparentRec
            simpa [eRecOf] using hfirst.symm
          have hparentPre : parent ∈ pre :=
            EmbedWitness.earlier_insert_mem_prefix hord split hparentAll
              (by simp [eIsIns]) hparentIns (by rw [hparentTime]; exact hguard.1)
          have hpreNodup : pre.Nodup := by
            have hnd := hcan.1
            rw [split, List.nodup_append] at hnd
            exact hnd.1
          have hpreSub : ∀ e ∈ pre, e ∈ C.events := by
            intro e he
            apply hsub e
            apply (hcan.2 e).mp
            rw [split]
            exact List.mem_append_left _ he
          have hwf := EmbedWitness.wf_of_insert_only hpreNodup hpreSub hhon hpreIns
          have hnoDels : anchor ∉ eDels pre := by
            rw [EmbedWitness.dels_nil_of_insert_only hpreIns]
            simp
          have hrecPre : (anchor, anchorEl, pref) ∈ eFold Γ pre :=
            (e_fold_mem Γ hwf (anchor, anchorEl, pref)).mpr
              ⟨⟨parent, hparentPre, hparentIns, hparentRec⟩, hnoDels⟩
          exact Or.inr ⟨anchorEl, hrecPre⟩
    | del target =>
        obtain ⟨origin, horigin, _, hguard⟩ := hmint _ hcurrentC
        change eApplicable (ts, replica, .del target) (eFold Γ origin) at hguard
        simp only [eApplicable] at hguard
        obtain ⟨rec, hrecOrigin, htarget⟩ := List.mem_map.mp hguard
        obtain ⟨parent, hparentOrigin, hparentIns, hparentRec⟩ :=
          e_fold_rec_sub Γ origin rec hrecOrigin
        have hparentPast := (horigin.2 parent).mp hparentOrigin
        have hparentE : parent ∈ E :=
          hclosed parent (ts, replica, .del target) hparentPast.2 hcurrentE
        have hparentAll : parent ∈ EmbedWitness.canonical ops :=
          (hcan.2 parent).mpr hparentE
        have hparentPre : parent ∈ pre :=
          EmbedWitness.insert_mem_prefix_of_delete hord split hparentAll
            (by simp [eIsIns]) hparentIns
        refine ⟨parent, hparentPre, hparentIns, ?_⟩
        rw [hparentRec] at htarget
        exact htarget

/-! The raw conflict relation is intentionally stronger than the relation
seen on reachable, sorted states.  This checked control prevents the public
legalization proof from silently treating raw universal commutation as
reachable-state commutation. -/

def rawCommuteCounterState :
    Sal.MRDTs.Instances.EmbedRGA.EState ℕ :=
  [(99, 9, [false]), (100, 10, [])]

def rawCommuteCounterInsert :
    Op (Sal.MRDTs.Instances.EmbedRGA.EOp ℕ) :=
  (1, 0, .ins 1 [] 0)

def rawCommuteCounterDelete :
    Op (Sal.MRDTs.Instances.EmbedRGA.EOp ℕ) :=
  (2, 0, .del 99)

/-- An insert and a deletion of an unrelated identifier fail the raw
`CRDTSig.commutes` test only because that test ranges over malformed,
unsorted representation states. -/
theorem unrelated_insert_delete_not_raw_comm :
    ¬ (Sal.MRDTs.Instances.EmbedRGA.E Sal.EmbedRGA.unaryCode ℕ).toCRDTSig.commutes
      rawCommuteCounterInsert rawCommuteCounterDelete := by
  intro h
  have bad := h rawCommuteCounterState
  have unequal :
      (Sal.MRDTs.Instances.EmbedRGA.E Sal.EmbedRGA.unaryCode ℕ).update
          ((Sal.MRDTs.Instances.EmbedRGA.E Sal.EmbedRGA.unaryCode ℕ).update
            rawCommuteCounterState rawCommuteCounterInsert)
          rawCommuteCounterDelete ≠
      (Sal.MRDTs.Instances.EmbedRGA.E Sal.EmbedRGA.unaryCode ℕ).update
          ((Sal.MRDTs.Instances.EmbedRGA.E Sal.EmbedRGA.unaryCode ℕ).update
            rawCommuteCounterState rawCommuteCounterDelete)
          rawCommuteCounterInsert := by
    native_decide
  exact unequal bad

/-- Semantic operation independence for the embedded sequence. Inserts only
conflict with deletion of the identifier that they allocate; two inserts and
two idempotent deletes are freely arbitrated. This relation deliberately
ignores malformed concrete list states. -/
def embedSemanticCommutes
    (a b : Op (Sal.MRDTs.Instances.EmbedRGA.EOp α)) : Prop :=
  match a.2.2, b.2.2 with
  | .ins _ _ _, .ins _ _ _ => True
  | .ins _ _ _, .del target => a.1 ≠ target
  | .del target, .ins _ _ _ => b.1 ≠ target
  | .del _, .del _ => True

theorem embedSemanticCommutes_symm
    (a b : Op (Sal.MRDTs.Instances.EmbedRGA.EOp α)) :
    embedSemanticCommutes a b ↔ embedSemanticCommutes b a := by
  obtain ⟨ats₀, ar, aop⟩ := a
  obtain ⟨bt, br, bop⟩ := b
  cases aop <;> cases bop <;> simp [embedSemanticCommutes, ne_comm]

noncomputable def embedInteraction (Γ : OrderedPrefixCode) :
    InteractionSpec (Sal.MRDTs.Instances.EmbedRGA.E Γ α) :=
  InteractionSpec.ofIndependence embedSemanticCommutes
    embedSemanticCommutes_symm

@[simp] theorem embedInteraction_conflicts (Γ : OrderedPrefixCode)
    (a b : Op (Sal.MRDTs.Instances.EmbedRGA.EOp α)) :
    ((embedInteraction Γ).interaction a b).Conflicts ↔
      ¬ embedSemanticCommutes a b := by
  exact InteractionSpec.ofIndependence_conflicts
    (D := Sal.MRDTs.Instances.EmbedRGA.E Γ α)
    embedSemanticCommutes embedSemanticCommutes_symm a b

@[simp] theorem embedInteraction_not_before (Γ : OrderedPrefixCode)
    (a b : Op (Sal.MRDTs.Instances.EmbedRGA.EOp α)) :
    ¬ ((embedInteraction Γ).interaction a b).FstBeforeSnd := by
  exact InteractionSpec.ofIndependence_not_before
    (D := Sal.MRDTs.Instances.EmbedRGA.E Γ α)
    embedSemanticCommutes embedSemanticCommutes_symm a b

theorem embedCanonical_respects {Γ : OrderedPrefixCode}
    {C : Configuration (Sal.MRDTs.Instances.EmbedRGA.E Γ α)}
    (exec : CertifiedExecution (Sal.MRDTs.Instances.EmbedRGA.E Γ α)
      (Sal.MRDTs.Instances.EmbedRGA.generation Γ) C)
    {v : Version} {s : (Sal.MRDTs.Instances.EmbedRGA.E Γ α).State}
    {E : Set (Op (Sal.MRDTs.Instances.EmbedRGA.EOp α))}
    (hver : C.ver v = some (s, E))
    {ops : List (Op (Sal.MRDTs.Instances.EmbedRGA.EOp α))}
    (hperm : listPermOf ops E) :
    respects (EmbedWitness.canonical ops)
      (interactionLoOn (embedInteraction Γ) C.core E) := by
  open Sal.MRDTs.Instances.EmbedRGA in
    have hgood : GoodConfig3 C := exec.goodConfig (fun _ hmint =>
      e_join_at (eHonest_core (eHonest_of_mint hmint)))
    have hsub := hgood.ver_events_sub v s E hver
    have hhon : EHonestCore Γ C.core :=
      eHonest_core (eHonest_of_mint exec.mintHonest)
    have hcan := EmbedWitness.canonical_listPermOf hperm
    have hordered := EmbedWitness.canonical_ordered ops
    have hall : ∀ e ∈ EmbedWitness.canonical ops, e ∈ C.events := by
      intro e he
      exact hsub e ((hcan.2 e).mp he)
    unfold respects
    generalize hwhole : EmbedWitness.canonical ops = whole at hall hordered
    clear hwhole
    induction whole with
    | nil => exact List.Pairwise.nil
    | cons a rest ih =>
        rw [List.pairwise_cons] at hordered ⊢
        refine ⟨?_, ih (fun e he => hall e (List.mem_cons_of_mem _ he))
          hordered.2⟩
        intro b hb hlo
        have hab := hordered.1 b hb
        rcases hlo with hvisConflict | hrc
        · rcases hvisConflict with ⟨hvba, hconflict⟩
          have haC := hall a List.mem_cons_self
          have hbC := hall b (List.mem_cons_of_mem _ hb)
          obtain ⟨ats, ar, aop⟩ := a
          obtain ⟨bt, br, bop⟩ := b
          cases aop with
          | del ax =>
              cases bop with
              | ins bel bpref banchor =>
                  simp [EmbedWitness.LE, EmbedWitness.leBool] at hab
              | del target =>
                  simpa [embedInteraction, InteractionSpec.ofIndependence,
                    embedSemanticCommutes, Interaction.Conflicts] using
                    hconflict
          | ins ael apref aanchor =>
              cases bop with
              | ins bel bpref banchor =>
                  simpa [embedInteraction, InteractionSpec.ofIndependence,
                    embedSemanticCommutes, Interaction.Conflicts] using
                    hconflict
              | del target =>
                  have hat : ats = target := by
                    have hncBA : ¬ embedSemanticCommutes
                        (bt, br, .del target)
                        (ats, ar, .ins ael apref aanchor) := by
                      exact (embedInteraction_conflicts Γ _ _).mp hconflict
                    have hnc : ¬ embedSemanticCommutes
                        (ats, ar, .ins ael apref aanchor)
                        (bt, br, .del target) := fun hcomm =>
                      hncBA ((embedSemanticCommutes_symm _ _).mp hcomm)
                    simpa [embedSemanticCommutes] using not_ne_iff.mp hnc
                  obtain ⟨creator, hcreatorC, hcreatorVis, hcreatorTime,
                    _⟩ := hhon.del_has_ins (bt, br, .del target) hbC target rfl
                  have hcreatorEq :
                      creator = (ats, ar, .ins ael apref aanchor) :=
                    C.core.ts_unique hcreatorC haC
                      (hcreatorTime.trans hat.symm)
                  subst creator
                  exact hgood.vis_irrefl _
                    (hgood.vis_trans hcreatorVis hvba)
        · exact (embedInteraction_not_before Γ _ _) hrc.2.2.1

noncomputable def embedSequentialCorrectness (Γ : OrderedPrefixCode) :
    SequentialCorrectnessCertificate (Sal.MRDTs.Instances.EmbedRGA.E Γ α)
      (Sal.MRDTs.Instances.EmbedRGA.generation Γ)
      (embedInteraction Γ) (embedClientSpec Γ) embedRel where
  sound C exec replay := by
    open Sal.MRDTs.Instances.EmbedRGA in
      intro v s E hver
      obtain ⟨ops, hperm, hresp, hfold⟩ := replay v s E hver
      have hseq := embedCanonical_seqOK exec hver hperm
      have hlegal := embedLegal_of_seqOK hseq
      have hcan := EmbedWitness.canonical_listPermOf hperm
      have hgood : GoodConfig3 C := exec.goodConfig (fun _ hmint =>
        e_join_at (eHonest_core (eHonest_of_mint hmint)))
      have hsub := hgood.ver_events_sub v s E hver
      have hclosed := hgood.ver_causal v s E hver
      have hhon : EHonestCore Γ C.core :=
        eHonest_core (eHonest_of_mint exec.mintHonest)
      have hwfReplay : EWf Γ ops :=
        e_wf_of_enum hhon hsub
          (fun a b hvis _ hb => hclosed a b hvis hb)
          hperm (embed_respects_loOn_of_lo hresp)
      have hwfCanonical : EWf Γ (EmbedWitness.canonical ops) :=
        eWf_of_seqOK hseq
      have hcanonFold :
          eFold Γ (EmbedWitness.canonical ops) = eFold Γ ops :=
        e_fold_canon Γ hwfCanonical hwfReplay
          (fun e => (hcan.2 e).trans (hperm.2 e).symm)
      have hstate : eFold Γ (EmbedWitness.canonical ops) = s := by
        rw [hcanonFold]
        exact hfold
      have hsound := embed_seq_sound hseq
      have hrel : embedRel s ((embedClientSpec Γ).run
          (EmbedWitness.canonical ops)) := by
        unfold embedRel
        change s.map eProj = eSpecFold (EmbedWitness.canonical ops)
        rw [← hstate]
        exact hsound
      refine ⟨EmbedWitness.canonical ops, hcan,
        embedCanonical_respects exec hver hperm, hlegal, hrel, ?_⟩
      intro query
      cases query
      change s.map (fun r => r.2.1) =
        ((embedClientSpec Γ).run (EmbedWitness.canonical ops)).map Prod.snd
      simpa [eProj, List.map_map, Function.comp_def] using
        congrArg (List.map Prod.snd) hrel

noncomputable def replayEmbed (Γ : OrderedPrefixCode) : ReplayVerifiedMRDT (Sal.MRDTs.Instances.EmbedRGA.E Γ α) where
  issuance := Sal.MRDTs.Instances.EmbedRGA.generation Γ
  convergence := Sal.MRDTs.Instances.EmbedRGA.convergence Γ
  Machine := embedSpec
  sequential := embedSequential Γ
  sequential_of_mint := fun _ h => embedSequential_of_mint h

noncomputable def embed (Γ : OrderedPrefixCode) :
    VerifiedMRDT (Sal.MRDTs.Instances.EmbedRGA.E Γ α) where
  issuance := Sal.MRDTs.Instances.EmbedRGA.generation Γ
  interaction := embedInteraction Γ
  convergence := Sal.MRDTs.Instances.EmbedRGA.convergence Γ
  Spec := embedClientSpec Γ
  Rel := embedRel
  sequentialCorrectness := embedSequentialCorrectness Γ

namespace SidedWitness

open Sal.MRDTs.Instances.SidedEmbedRGA

def leBool (a b : Op SOp) : Bool :=
  match a.2.2, b.2.2 with
  | .ins _ _ _ _, .ins _ _ _ _ => decide (a.1 ≤ b.1)
  | .ins _ _ _ _, .del _ => true
  | .del _, .ins _ _ _ _ => false
  | .del _, .del _ => true

def LE (a b : Op SOp) : Prop := leBool a b = true

def canonical (ops : List (Op SOp)) : List (Op SOp) :=
  ops.mergeSort leBool

theorem canonical_perm (ops : List (Op SOp)) : ops.Perm (canonical ops) :=
  (List.mergeSort_perm ops leBool).symm

theorem canonical_listPermOf {ops : List (Op SOp)} {E : Set (Op SOp)}
    (h : listPermOf ops E) : listPermOf (canonical ops) E := by
  have hp := canonical_perm ops
  exact ⟨hp.nodup h.1, fun e => (hp.mem_iff (a := e)).symm.trans (h.2 e)⟩

theorem canonical_ordered (ops : List (Op SOp)) :
    (canonical ops).Pairwise LE := by
  unfold canonical LE
  apply List.pairwise_mergeSort
  · rintro ⟨ta, ra, oa⟩ ⟨tb, rb, ob⟩ ⟨tc, rc, oc⟩ hab hbc
    cases oa <;> cases ob <;> cases oc <;> simp [leBool] at *
    exact Nat.le_trans hab hbc
  · rintro ⟨ta, ra, oa⟩ ⟨tb, rb, ob⟩
    cases oa <;> cases ob <;> simp [leBool]
    exact Nat.le_total ta tb

theorem dels_nil_of_insert_only {ops : List (Op SOp)}
    (h : ∀ e ∈ ops, sIsIns e = true) : sDels ops = [] := by
  induction ops with
  | nil => rfl
  | cons e rest ih =>
      obtain ⟨ts, replica, op⟩ := e
      cases op with
      | del x =>
          have bad := h (ts, replica, .del x) List.mem_cons_self
          simp [sIsIns] at bad
      | ins el pref anchor side =>
          change sDels rest = []
          exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem wf_of_insert_only {Γ : OrderedPrefixCode}
    {C : Configuration (S Γ)} {ops : List (Op SOp)}
    (hnd : ops.Nodup) (hsub : ∀ e ∈ ops, e ∈ C.events)
    (hhon : SHonestCore Γ C.core)
    (hins : ∀ e ∈ ops, sIsIns e = true) : SWf Γ ops where
  ins_nodup := by
    apply List.Nodup.map_on ?_ (hnd.filter _)
    intro a ha b hb htime
    exact C.core.ts_unique (hsub a (List.mem_of_mem_filter ha))
      (hsub b (List.mem_of_mem_filter hb)) htime
  del_late := by
    intro pre e post split he hdel
    rw [dels_nil_of_insert_only (fun x hx => hins x (by rw [split]; simp [hx]))]
      at hdel
    simp at hdel
  keys_inj := by
    obtain ⟨chainOf, hchain⟩ := hhon.chain_gen
    intro o₁ h₁ o₂ h₂ hi₁ hi₂ hne hkey
    obtain ⟨hp₁, hc₁, hs₁⟩ := hchain o₁ (hsub o₁ h₁) hi₁
    obtain ⟨hp₂, hc₂, hs₂⟩ := hchain o₂ (hsub o₂ h₂) hi₂
    apply hne
    have hc : Sal.EmbedRGA.sidedCoordOf Γ (chainOf o₁.1) =
        Sal.EmbedRGA.sidedCoordOf Γ (chainOf o₂.1) := by
      rw [← hc₁, ← hc₂]
      exact sKey_inj hkey
    have hsame := Sal.EmbedRGA.sidedCoordOf_inj Γ hp₁ hp₂ hc
    calc o₁.1 = ((chainOf o₁.1).map Prod.snd).sum := hs₁.symm
      _ = ((chainOf o₂.1).map Prod.snd).sum := by rw [hsame]
      _ = o₂.1 := hs₂

theorem earlier_insert_mem_prefix {whole pre suffix : List (Op SOp)}
    {current parent : Op SOp} (ordered : whole.Pairwise LE)
    (split : whole = pre ++ current :: suffix)
    (parentMem : parent ∈ whole) (currentIns : sIsIns current = true)
    (parentIns : sIsIns parent = true)
    (earlier : parent.1 < current.1) : parent ∈ pre := by
  subst whole
  rw [List.mem_append] at parentMem
  rcases parentMem with hp | hp
  · exact hp
  · simp only [List.mem_cons] at hp
    rcases hp with rfl | hs
    · exact (Nat.lt_irrefl _ earlier).elim
    · have cross := (List.pairwise_append.mp ordered).2.1
      have rel := (List.pairwise_cons.mp cross).1 parent hs
      obtain ⟨ct, cr, cop⟩ := current
      obtain ⟨pt, pr, pop⟩ := parent
      cases cop with
      | del x => simp [sIsIns] at currentIns
      | ins cel cpref canchor cside =>
          cases pop with
          | del x => simp [sIsIns] at parentIns
          | ins pel ppref panchor pside =>
              simp [LE, leBool] at rel
              exact (Nat.not_le_of_lt earlier rel).elim

theorem insert_mem_prefix_of_delete {whole pre suffix : List (Op SOp)}
    {current parent : Op SOp} (ordered : whole.Pairwise LE)
    (split : whole = pre ++ current :: suffix)
    (parentMem : parent ∈ whole) (currentDel : sIsIns current = false)
    (parentIns : sIsIns parent = true) : parent ∈ pre := by
  subst whole
  rw [List.mem_append] at parentMem
  rcases parentMem with hp | hp
  · exact hp
  · simp only [List.mem_cons] at hp
    rcases hp with rfl | hs
    · rw [parentIns] at currentDel
      simp at currentDel
    · have cross := (List.pairwise_append.mp ordered).2.1
      have rel := (List.pairwise_cons.mp cross).1 parent hs
      obtain ⟨ct, cr, cop⟩ := current
      obtain ⟨pt, pr, pop⟩ := parent
      cases cop <;> cases pop <;> simp [sIsIns, LE, leBool] at *

theorem prefix_insert_only {whole pre suffix : List (Op SOp)}
    {current : Op SOp} (ordered : whole.Pairwise LE)
    (split : whole = pre ++ current :: suffix)
    (currentIns : sIsIns current = true) :
    ∀ e ∈ pre, sIsIns e = true := by
  intro e he
  subst whole
  have cross := (List.pairwise_append.mp ordered).2.2
  have rel := cross e he current List.mem_cons_self
  obtain ⟨et, er, eop⟩ := e
  obtain ⟨ct, cr, cop⟩ := current
  cases eop <;> cases cop <;> simp [sIsIns, LE, leBool] at *

end SidedWitness

def sidedSpec : SequentialMachine (Op Sal.MRDTs.Instances.SidedEmbedRGA.SOp) where
  State := List (ℕ × ℕ)
  init := [(0, 0)]
  step := Sal.MRDTs.Instances.SidedEmbedRGA.sSpecStep

def sidedSequential (Γ : OrderedPrefixCode) :
    SequentialRefinement (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ) sidedSpec where
  Honest := Sal.MRDTs.Instances.SidedEmbedRGA.sSeqOK Γ
  Rel s q := s.map Sal.MRDTs.Instances.SidedEmbedRGA.sProj = q.filter (fun p => decide (p.1 ≠ 0))
  init := rfl
  sound := by
    intro ops h
    simpa [sidedSpec, SequentialMachine.run, Sal.MRDTs.Instances.SidedEmbedRGA.sSpecFold, Sal.MRDTs.Instances.SidedEmbedRGA.sFold] using
      (Sal.MRDTs.Instances.SidedEmbedRGA.sided_seq_read (Γ := Γ) h)

theorem sidedSequential_of_mint {Γ : OrderedPrefixCode}
    {ops : List (Op Sal.MRDTs.Instances.SidedEmbedRGA.SOp)}
    (h : LinearMintHistory (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ) Sal.MRDTs.Instances.SidedEmbedRGA.sApplicable ops) : Sal.MRDTs.Instances.SidedEmbedRGA.sSeqOK Γ ops := by
  intro pre e post heq
  obtain ⟨ts, replica, op⟩ := e
  cases op with
  | ins el pref anchor side =>
      refine ⟨?_, h.guarded pre _ post heq⟩
      intro x hx
      obtain ⟨old, hold, _hins, htime⟩ :=
        Sal.MRDTs.Instances.SidedEmbedRGA.mem_sInsIds.mp hx
      rw [← htime]
      exact h.clocked pre _ post heq old hold
  | del x =>
      have hg := h.guarded pre (ts, replica, .del x) post heq
      simp only [Sal.MRDTs.Instances.SidedEmbedRGA.sApplicable] at hg
      obtain ⟨rec, hrec, hidx⟩ := List.mem_map.mp hg
      obtain ⟨iop, hiop, hins, hieq⟩ :=
        Sal.MRDTs.Instances.SidedEmbedRGA.s_fold_rec_sub Γ pre rec hrec
      refine ⟨iop, hiop, hins, ?_⟩
      rw [hieq] at hidx
      exact hidx

theorem sidedCanonical_seqOK_of {Γ : OrderedPrefixCode}
    {C : Configuration (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ)}
    (hgood : GoodConfig3 C)
    (hmint : MintHonest (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ)
      Sal.MRDTs.Instances.SidedEmbedRGA.sApplicable C)
    {v : Version} {s : (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ).State}
    {E : Set (Op Sal.MRDTs.Instances.SidedEmbedRGA.SOp)}
    (hver : C.ver v = some (s, E))
    {ops : List (Op Sal.MRDTs.Instances.SidedEmbedRGA.SOp)}
    (hperm : listPermOf ops E) :
    Sal.MRDTs.Instances.SidedEmbedRGA.sSeqOK Γ
      (SidedWitness.canonical ops) := by
  open Sal.MRDTs.Instances.SidedEmbedRGA in
    have hsub := hgood.ver_events_sub v s E hver
    have hclosed := hgood.ver_causal v s E hver
    have hhon : SHonestCore Γ C.core :=
      sHonest_core (sHonest_of_mint hmint)
    have hcan := SidedWitness.canonical_listPermOf hperm
    have hord := SidedWitness.canonical_ordered ops
    intro pre current post split
    have hordSplit : (pre ++ current :: post).Pairwise SidedWitness.LE := by
      simpa [split] using hord
    have hcurrentList : current ∈ SidedWitness.canonical ops := by
      rw [split]
      simp
    have hcurrentE : current ∈ E := (hcan.2 current).mp hcurrentList
    have hcurrentC : current ∈ C.events := hsub current hcurrentE
    obtain ⟨ts, replica, action⟩ := current
    cases action with
    | ins el pref anchor side =>
        have hpreIns : ∀ e ∈ pre, sIsIns e = true :=
          SidedWitness.prefix_insert_only hord split (by simp [sIsIns])
        have hclock : ∀ x ∈ sInsIds pre, x < ts := by
          intro x hx
          obtain ⟨old, hold, holdIns, holdTime⟩ := mem_sInsIds.mp hx
          have holdList : old ∈ SidedWitness.canonical ops := by
            rw [split]
            exact List.mem_append_left _ hold
          have holdE : old ∈ E := (hcan.2 old).mp holdList
          have cross := (List.pairwise_append.mp hordSplit).2.2
          have hleRaw := cross old hold
            (ts, replica, .ins el pref anchor side) List.mem_cons_self
          have hle : old.1 ≤ ts := by
            obtain ⟨ot, orp, oop⟩ := old
            cases oop <;> simp [sIsIns] at holdIns
            simpa [SidedWitness.LE, SidedWitness.leBool] using hleRaw
          have hne : old.1 ≠ ts := by
            intro heq
            have hop : old = (ts, replica, .ins el pref anchor side) :=
              C.core.ts_unique (hsub old holdE) hcurrentC heq
            subst old
            have hnd := hcan.1
            rw [split, List.nodup_append] at hnd
            exact hnd.2.2 _ hold _ List.mem_cons_self rfl
          rw [← holdTime]
          exact Nat.lt_of_le_of_ne hle hne
        obtain ⟨origin, horigin, _, hguard⟩ := hmint _ hcurrentC
        change sApplicable (ts, replica, .ins el pref anchor side)
          (sFold Γ origin) at hguard
        simp only [sApplicable] at hguard
        refine ⟨hclock, hguard.1, ?_⟩
        rcases hguard.2 with hroot | ⟨anchorEl, hanchorOrigin⟩
        · exact Or.inl hroot
        · obtain ⟨parent, hparentOrigin, hparentIns, hparentRec⟩ :=
            s_fold_rec_sub Γ origin (anchor, anchorEl, pref) hanchorOrigin
          have hparentPast := (horigin.2 parent).mp hparentOrigin
          have hparentE : parent ∈ E :=
            hclosed parent (ts, replica, .ins el pref anchor side)
              hparentPast.2 hcurrentE
          have hparentAll : parent ∈ SidedWitness.canonical ops :=
            (hcan.2 parent).mpr hparentE
          have hparentTime : parent.1 = anchor := by
            have hfirst := congrArg (fun r : SRec => r.1) hparentRec
            simpa [sRecOf] using hfirst.symm
          have hparentPre : parent ∈ pre :=
            SidedWitness.earlier_insert_mem_prefix hord split hparentAll
              (by simp [sIsIns]) hparentIns
              (by rw [hparentTime]; exact hguard.1)
          have hpreNodup : pre.Nodup := by
            have hnd := hcan.1
            rw [split, List.nodup_append] at hnd
            exact hnd.1
          have hpreSub : ∀ e ∈ pre, e ∈ C.events := by
            intro e he
            apply hsub e
            apply (hcan.2 e).mp
            rw [split]
            exact List.mem_append_left _ he
          have hwf := SidedWitness.wf_of_insert_only
            hpreNodup hpreSub hhon hpreIns
          have hnoDels : anchor ∉ sDels pre := by
            rw [SidedWitness.dels_nil_of_insert_only hpreIns]
            simp
          have hrecPre : (anchor, anchorEl, pref) ∈ sFold Γ pre :=
            (s_fold_mem Γ hwf (anchor, anchorEl, pref)).mpr
              ⟨⟨parent, hparentPre, hparentIns, hparentRec⟩, hnoDels⟩
          exact Or.inr ⟨anchorEl, hrecPre⟩
    | del target =>
        obtain ⟨origin, horigin, _, hguard⟩ := hmint _ hcurrentC
        change sApplicable (ts, replica, .del target) (sFold Γ origin) at hguard
        simp only [sApplicable] at hguard
        obtain ⟨rec, hrecOrigin, htarget⟩ := List.mem_map.mp hguard
        obtain ⟨parent, hparentOrigin, hparentIns, hparentRec⟩ :=
          s_fold_rec_sub Γ origin rec hrecOrigin
        have hparentPast := (horigin.2 parent).mp hparentOrigin
        have hparentE : parent ∈ E :=
          hclosed parent (ts, replica, .del target) hparentPast.2 hcurrentE
        have hparentAll : parent ∈ SidedWitness.canonical ops :=
          (hcan.2 parent).mpr hparentE
        have hparentPre : parent ∈ pre :=
          SidedWitness.insert_mem_prefix_of_delete hord split hparentAll
            (by simp [sIsIns]) hparentIns
        refine ⟨parent, hparentPre, hparentIns, ?_⟩
        rw [hparentRec] at htarget
        exact htarget

theorem sidedCanonical_seqOK {Γ : OrderedPrefixCode}
    {C : Configuration (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ)}
    (exec : CertifiedExecution (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ)
      (Sal.MRDTs.Instances.SidedEmbedRGA.generation Γ) C)
    {v : Version} {s : (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ).State}
    {E : Set (Op Sal.MRDTs.Instances.SidedEmbedRGA.SOp)}
    (hver : C.ver v = some (s, E))
    {ops : List (Op Sal.MRDTs.Instances.SidedEmbedRGA.SOp)}
    (hperm : listPermOf ops E) :
    Sal.MRDTs.Instances.SidedEmbedRGA.sSeqOK Γ
      (SidedWitness.canonical ops) := by
  apply sidedCanonical_seqOK_of
    (exec.goodConfig (fun _ hmint =>
      Sal.MRDTs.Instances.SidedEmbedRGA.s_join_at
        (Sal.MRDTs.Instances.SidedEmbedRGA.sHonest_core
          (Sal.MRDTs.Instances.SidedEmbedRGA.sHonest_of_mint hmint))))
    exec.mintHonest hver hperm

def sidedLegal (Γ : OrderedPrefixCode)
    (ops : List (Op Sal.MRDTs.Instances.SidedEmbedRGA.SOp)) : Prop :=
  ∀ pre current post, ops = pre ++ current :: post →
    match current.2.2 with
    | .ins _ pref anchor _ =>
        (∀ x ∈ Sal.MRDTs.Instances.SidedEmbedRGA.sInsIds pre,
          x < current.1) ∧
        ((anchor = 0 ∧ pref = []) ∨
          ∃ parent ∈ pre,
            Sal.MRDTs.Instances.SidedEmbedRGA.sIsIns parent = true ∧
            parent.1 = anchor ∧
            Sal.MRDTs.Instances.SidedEmbedRGA.sCoord Γ parent = pref)
    | .del target =>
        ∃ parent ∈ pre,
          Sal.MRDTs.Instances.SidedEmbedRGA.sIsIns parent = true ∧
          parent.1 = target

theorem sidedLegal_of_seqOK {Γ : OrderedPrefixCode}
    {ops : List (Op Sal.MRDTs.Instances.SidedEmbedRGA.SOp)}
    (h : Sal.MRDTs.Instances.SidedEmbedRGA.sSeqOK Γ ops) :
    sidedLegal Γ ops := by
  open Sal.MRDTs.Instances.SidedEmbedRGA in
    intro pre current post split
    have hc := h pre current post split
    obtain ⟨ts, replica, action⟩ := current
    cases action with
    | del target => exact hc
    | ins el pref anchor side =>
        refine ⟨hc.1, ?_⟩
        rcases hc.2.2 with hroot | ⟨anchorEl, hanchor⟩
        · exact Or.inl hroot
        · obtain ⟨parent, hparent, hpins, hrec⟩ :=
            s_fold_rec_sub Γ pre (anchor, anchorEl, pref) hanchor
          refine Or.inr ⟨parent, hparent, hpins, ?_, ?_⟩
          · have hfirst := congrArg (fun r : SRec => r.1) hrec
            simpa [sRecOf] using hfirst.symm
          · have hcoord := congrArg (fun r : SRec => r.2.2) hrec
            simpa [sRecOf] using hcoord.symm

noncomputable def sidedClientSpec (Γ : OrderedPrefixCode) :
    SequentialSpec (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ) where
  toSequentialMachine := sidedSpec
  Legal := sidedLegal Γ
  query := fun q _ => (q.filter (fun p => decide (p.1 ≠ 0))).map Prod.snd

def sidedRel (s : Sal.MRDTs.Instances.SidedEmbedRGA.SState)
    (q : List (ℕ × ℕ)) : Prop :=
  s.map Sal.MRDTs.Instances.SidedEmbedRGA.sProj =
    q.filter (fun p => decide (p.1 ≠ 0))

def sidedSemanticCommutes
    (a b : Op Sal.MRDTs.Instances.SidedEmbedRGA.SOp) : Prop :=
  match a.2.2, b.2.2 with
  | .ins _ _ _ _, .ins _ _ _ _ => True
  | .ins _ _ _ _, .del target => a.1 ≠ target
  | .del target, .ins _ _ _ _ => b.1 ≠ target
  | .del _, .del _ => True

theorem sidedSemanticCommutes_symm
    (a b : Op Sal.MRDTs.Instances.SidedEmbedRGA.SOp) :
    sidedSemanticCommutes a b ↔ sidedSemanticCommutes b a := by
  obtain ⟨ats₀, ar, aop⟩ := a
  obtain ⟨bt, br, bop⟩ := b
  cases aop <;> cases bop <;> simp [sidedSemanticCommutes, ne_comm]

noncomputable def sidedInteraction (Γ : OrderedPrefixCode) :
    InteractionSpec (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ) :=
  InteractionSpec.ofIndependence sidedSemanticCommutes
    sidedSemanticCommutes_symm

@[simp] theorem sidedInteraction_conflicts (Γ : OrderedPrefixCode)
    (a b : Op Sal.MRDTs.Instances.SidedEmbedRGA.SOp) :
    ((sidedInteraction Γ).interaction a b).Conflicts ↔
      ¬ sidedSemanticCommutes a b := by
  exact InteractionSpec.ofIndependence_conflicts
    (D := Sal.MRDTs.Instances.SidedEmbedRGA.S Γ)
    sidedSemanticCommutes sidedSemanticCommutes_symm a b

@[simp] theorem sidedInteraction_not_before (Γ : OrderedPrefixCode)
    (a b : Op Sal.MRDTs.Instances.SidedEmbedRGA.SOp) :
    ¬ ((sidedInteraction Γ).interaction a b).FstBeforeSnd := by
  exact InteractionSpec.ofIndependence_not_before
    (D := Sal.MRDTs.Instances.SidedEmbedRGA.S Γ)
    sidedSemanticCommutes sidedSemanticCommutes_symm a b

theorem sidedCanonical_respects_of {Γ : OrderedPrefixCode}
    {C : Configuration (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ)}
    (hgood : GoodConfig3 C)
    (hhon : Sal.MRDTs.Instances.SidedEmbedRGA.SHonestCore Γ C.core)
    {v : Version} {s : (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ).State}
    {E : Set (Op Sal.MRDTs.Instances.SidedEmbedRGA.SOp)}
    (hver : C.ver v = some (s, E))
    {ops : List (Op Sal.MRDTs.Instances.SidedEmbedRGA.SOp)}
    (hperm : listPermOf ops E) :
    respects (SidedWitness.canonical ops)
      (interactionLoOn (sidedInteraction Γ) C.core E) := by
  open Sal.MRDTs.Instances.SidedEmbedRGA in
    have hsub := hgood.ver_events_sub v s E hver
    have hcan := SidedWitness.canonical_listPermOf hperm
    have hordered := SidedWitness.canonical_ordered ops
    have hall : ∀ e ∈ SidedWitness.canonical ops, e ∈ C.events := by
      intro e he
      exact hsub e ((hcan.2 e).mp he)
    unfold respects
    generalize hwhole : SidedWitness.canonical ops = whole at hall hordered
    clear hwhole
    induction whole with
    | nil => exact List.Pairwise.nil
    | cons a rest ih =>
        rw [List.pairwise_cons] at hordered ⊢
        refine ⟨?_, ih (fun e he => hall e (List.mem_cons_of_mem _ he))
          hordered.2⟩
        intro b hb hlo
        have hab := hordered.1 b hb
        rcases hlo with hvisConflict | hrc
        · rcases hvisConflict with ⟨hvba, hconflict⟩
          have haC := hall a List.mem_cons_self
          have hbC := hall b (List.mem_cons_of_mem _ hb)
          obtain ⟨ats, ar, aop⟩ := a
          obtain ⟨bt, br, bop⟩ := b
          cases aop with
          | del ax =>
              cases bop with
              | ins bel bpref banchor bside =>
                  simp [SidedWitness.LE, SidedWitness.leBool] at hab
              | del target =>
                  simpa [sidedInteraction, InteractionSpec.ofIndependence,
                    sidedSemanticCommutes, Interaction.Conflicts] using
                    hconflict
          | ins ael apref aanchor aside =>
              cases bop with
              | ins bel bpref banchor bside =>
                  simpa [sidedInteraction, InteractionSpec.ofIndependence,
                    sidedSemanticCommutes, Interaction.Conflicts] using
                    hconflict
              | del target =>
                  have hat : ats = target := by
                    have hncBA : ¬ sidedSemanticCommutes
                        (bt, br, .del target)
                        (ats, ar, .ins ael apref aanchor aside) := by
                      exact (sidedInteraction_conflicts Γ _ _).mp hconflict
                    have hnc : ¬ sidedSemanticCommutes
                        (ats, ar, .ins ael apref aanchor aside)
                        (bt, br, .del target) := fun hcomm =>
                      hncBA ((sidedSemanticCommutes_symm _ _).mp hcomm)
                    simpa [sidedSemanticCommutes] using not_ne_iff.mp hnc
                  obtain ⟨creator, hcreatorC, hcreatorVis, hcreatorTime,
                    _⟩ := hhon.del_has_ins (bt, br, .del target) hbC target rfl
                  have hcreatorEq : creator =
                      (ats, ar, .ins ael apref aanchor aside) :=
                    C.core.ts_unique hcreatorC haC
                      (hcreatorTime.trans hat.symm)
                  subst creator
                  exact hgood.vis_irrefl _
                    (hgood.vis_trans hcreatorVis hvba)
        · exact (sidedInteraction_not_before Γ _ _) hrc.2.2.1

theorem sidedCanonical_respects {Γ : OrderedPrefixCode}
    {C : Configuration (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ)}
    (exec : CertifiedExecution (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ)
      (Sal.MRDTs.Instances.SidedEmbedRGA.generation Γ) C)
    {v : Version} {s : (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ).State}
    {E : Set (Op Sal.MRDTs.Instances.SidedEmbedRGA.SOp)}
    (hver : C.ver v = some (s, E))
    {ops : List (Op Sal.MRDTs.Instances.SidedEmbedRGA.SOp)}
    (hperm : listPermOf ops E) :
    respects (SidedWitness.canonical ops)
      (interactionLoOn (sidedInteraction Γ) C.core E) := by
  apply sidedCanonical_respects_of
    (exec.goodConfig (fun _ hmint =>
      Sal.MRDTs.Instances.SidedEmbedRGA.s_join_at
        (Sal.MRDTs.Instances.SidedEmbedRGA.sHonest_core
          (Sal.MRDTs.Instances.SidedEmbedRGA.sHonest_of_mint hmint))))
    (Sal.MRDTs.Instances.SidedEmbedRGA.sHonest_core
      (Sal.MRDTs.Instances.SidedEmbedRGA.sHonest_of_mint exec.mintHonest))
    hver hperm

theorem sided_respects_loOn_of_lo {Γ : OrderedPrefixCode}
    {C : Sal.MRDTs.Foundation.Configuration
      (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ).toCRDTSig}
    {E : Set (Op Sal.MRDTs.Instances.SidedEmbedRGA.SOp)}
    {ops : List (Op Sal.MRDTs.Instances.SidedEmbedRGA.SOp)}
    (h : respects ops (Sal.MRDTs.Foundation.lo C)) :
    respects ops (loOn C E) := by
  open Sal.MRDTs.Instances.SidedEmbedRGA in
    unfold respects at h ⊢
    apply h.imp
    intro a b hab hOn
    apply hab
    rw [loOn_iff_of_rc_either (S_rc_either Γ)] at hOn
    exact Or.inl hOn

noncomputable def sidedSequentialCorrectness (Γ : OrderedPrefixCode) :
    SequentialCorrectnessCertificate (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ)
      (Sal.MRDTs.Instances.SidedEmbedRGA.generation Γ)
      (sidedInteraction Γ) (sidedClientSpec Γ) sidedRel where
  sound C exec replay := by
    open Sal.MRDTs.Instances.SidedEmbedRGA in
      intro v s E hver
      obtain ⟨ops, hperm, hresp, hfold⟩ := replay v s E hver
      have hseq := sidedCanonical_seqOK exec hver hperm
      have hlegal := sidedLegal_of_seqOK hseq
      have hcan := SidedWitness.canonical_listPermOf hperm
      have hgood : GoodConfig3 C := exec.goodConfig (fun _ hmint =>
        s_join_at (sHonest_core (sHonest_of_mint hmint)))
      have hsub := hgood.ver_events_sub v s E hver
      have hclosed := hgood.ver_causal v s E hver
      have hhon : SHonestCore Γ C.core :=
        sHonest_core (sHonest_of_mint exec.mintHonest)
      have hwfReplay : SWf Γ ops :=
        s_wf_of_enum hhon hsub
          (fun a b hvis _ hb => hclosed a b hvis hb)
          hperm (sided_respects_loOn_of_lo hresp)
      have hwfCanonical : SWf Γ (SidedWitness.canonical ops) :=
        sWf_of_seqOK hseq
      have hcanonFold :
          sFold Γ (SidedWitness.canonical ops) = sFold Γ ops :=
        s_fold_canon Γ hwfCanonical hwfReplay
          (fun e => (hcan.2 e).trans (hperm.2 e).symm)
      have hstate : sFold Γ (SidedWitness.canonical ops) = s := by
        rw [hcanonFold]
        exact hfold
      have hsound := sided_seq_read hseq
      have hrel : sidedRel s ((sidedClientSpec Γ).run
          (SidedWitness.canonical ops)) := by
        unfold sidedRel
        change s.map sProj = (sSpecFold (SidedWitness.canonical ops)).filter
          (fun p => decide (p.1 ≠ 0))
        rw [← hstate]
        exact hsound
      refine ⟨SidedWitness.canonical ops, hcan,
        sidedCanonical_respects exec hver hperm, hlegal, hrel, ?_⟩
      intro query
      cases query
      change s.map (fun r => r.2.1) =
        (((sidedClientSpec Γ).run (SidedWitness.canonical ops)).filter
          (fun p => decide (p.1 ≠ 0))).map Prod.snd
      simpa [sProj, List.map_map, Function.comp_def] using
        congrArg (List.map Prod.snd) hrel

noncomputable def replaySided (Γ : OrderedPrefixCode) : ReplayVerifiedMRDT (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ) where
  issuance := Sal.MRDTs.Instances.SidedEmbedRGA.generation Γ
  convergence := Sal.MRDTs.Instances.SidedEmbedRGA.convergence Γ
  Machine := sidedSpec
  sequential := sidedSequential Γ
  sequential_of_mint := fun _ h => sidedSequential_of_mint h

noncomputable def sided (Γ : OrderedPrefixCode) :
    VerifiedMRDT (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ) where
  issuance := Sal.MRDTs.Instances.SidedEmbedRGA.generation Γ
  interaction := sidedInteraction Γ
  convergence := Sal.MRDTs.Instances.SidedEmbedRGA.convergence Γ
  Spec := sidedClientSpec Γ
  Rel := sidedRel
  sequentialCorrectness := sidedSequentialCorrectness Γ

#print axioms replayEmbed
#print axioms embed
#print axioms replaySided
#print axioms sided

end Sal.MRDTs.Instances.ProductionRGA
