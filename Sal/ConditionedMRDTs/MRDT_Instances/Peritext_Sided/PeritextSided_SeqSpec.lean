import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_Sided.PeritextSided_Core
import Sal.ConditionedMRDTs.Metatheory.ConditioningIntentAudit

/-!
# Sequential intent for the shipped sided Peritext core

The product guard observes text, deletions, and marks together.  This file
proves that its text projection nevertheless satisfies the independent
two-sided buffer specification.  In particular, this is not an assumption
that a concurrent execution has one global sequential history: it is the
single-client mint theorem consumed by the sequential-refinement layer.
-/

namespace Sal.ConditionedMRDTs.PeritextSided

open Sal.Emulation
open Sal.ConditionedMRDTs
open Classical

/-- Split a mixed prefix at the unique event that produced the indicated
element of its left projection. -/
private theorem split_projList₁ {A₁ A₂ : Type} {ops : List (Op (A₁ ⊕ A₂))}
    {pre : List (Op A₁)} {e : Op A₁} {post : List (Op A₁)}
    (h : projList₁ ops = pre ++ e :: post) :
    ∃ pre' post', ops = pre' ++ inlOp e :: post' ∧ projList₁ pre' = pre := by
  change List.filterMap oplOp ops = pre ++ e :: post at h
  obtain ⟨l₁, rest, hops, hl₁, hrest⟩ :=
    List.filterMap_eq_append_iff.mp h
  obtain ⟨skip, a, tail, hr, hskip, ha, _htail⟩ :=
    List.filterMap_eq_cons_iff.mp hrest
  have hae : a = inlOp e := (oplOp_eq_some.mp ha)
  subst a
  refine ⟨l₁ ++ skip, tail, ?_, ?_⟩
  · rw [hops, hr, List.append_assoc]
  · change List.filterMap oplOp (l₁ ++ skip) = pre
    rw [List.filterMap_append, hl₁]
    have : List.filterMap oplOp skip = [] := by
      simpa only [List.filterMap_eq_nil_iff] using hskip
    rw [this, List.append_nil]

/-- The runtime product's local mint discipline projects to the sided text
kernel's local mint discipline.  Cross-component mark/delete events disappear,
while their timestamps remain in the clock premise, which is stronger than
the text theorem requires. -/
theorem linearMintHistory_text {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    {ops : List (Op (Core Γ).AppOp)}
    (h : LinearMintHistory (Core Γ) (coreGuard Γ) ops) :
    LinearMintHistory (S Γ) sApplicable (projList₁ ops) := by
  constructor
  · intro pre e post heq
    obtain ⟨pre', post', hops, hpre⟩ := split_projList₁ heq
    have hg := h.guarded pre' (inlOp e) post' hops
    change coreGuard Γ (inlOp e)
      (applySeq (prodSig (S Γ) Stores).toCRDTSig
        (prodSig (S Γ) Stores).init pre') at hg
    rw [applySeq_prod, hpre] at hg
    rcases e with ⟨t, r, o⟩
    cases o with
    | ins el π a sd =>
        simpa [Core, Stores, coreGuard] using hg
    | del x =>
        exact False.elim (by simpa [coreGuard] using hg)
  · intro pre e post heq old hold
    obtain ⟨pre', post', hops, hpre⟩ := split_projList₁ heq
    apply h.clocked pre' (inlOp e) post' hops (inlOp old)
    exact mem_projList₁.mp (hpre ▸ hold)

/-- End-to-end text projection: every linearly minted shipped-core history
reads exactly as the independent two-sided buffer program. -/
theorem textSequentialSound {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    {ops : List (Op (Core Γ).AppOp)}
    (h : LinearMintHistory (Core Γ) (coreGuard Γ) ops) :
    (sRFold Γ (projList₁ ops)).map sProj = sSpecFold (projList₁ ops) :=
  sidedSequentialSound_of_linearMintHistory (linearMintHistory_text h)

/-! ## The independent rich-text machine -/

/-- Client-level state.  It deliberately contains no embedded coordinates or
OR-set instances: only the displayed buffer, deleted character ids, and
immutable mark events. -/
structure RichSeqState where
  text : List (ℕ × ℕ)
  deleted : Finset ℕ
  marks : Finset PeritextEmbed.MarkDoc.MarkD

/-- Payload observation of an OR-set instance set. -/
def osPayloads {α : Type} [DecidableEq α] (s : OSState α) : Finset α :=
  s.image (fun q => q.2.2)

/-- The ordinary editor step.  Native text deletes and OR-set removes are
included to make this a total specification; `coreGuard` restricts reachable
runtime histories to text inserts and grow-only delete/mark events. -/
def richStep (q : RichSeqState) (e : Op (Core Γ).AppOp) : RichSeqState :=
  match e.2.2 with
  | Sum.inl o => { q with text := sSpecStep q.text (e.1, e.2.1, o) }
  | Sum.inr (Sum.inl (OSOp.add x)) => { q with deleted := insert x q.deleted }
  | Sum.inr (Sum.inl (OSOp.rem x)) => { q with deleted := q.deleted.erase x }
  | Sum.inr (Sum.inr (OSOp.add m)) => { q with marks := insert m q.marks }
  | Sum.inr (Sum.inr (OSOp.rem mid)) =>
      { q with marks := q.marks.filter (fun m => m.mid ≠ mid) }

def richSequentialSpec (Γ : Sal.EmbedRGA.OrderedPrefixCode) :
    SequentialSpec (Op (Core Γ).AppOp) where
  State := RichSeqState
  init := ⟨[(0, 0)], ∅, ∅⟩
  step := richStep

/-- Concrete runtime state represents the independent editor state.  The
sentinel is filtered from the client-visible text side. -/
def richStateRel (s : (Core Γ).State) (q : RichSeqState) : Prop :=
  s.1.map sProj = q.text.filter (fun p => decide (p.1 ≠ 0)) ∧
  osPayloads s.2.1 = q.deleted ∧ osPayloads s.2.2 = q.marks

private theorem richRun_text (Γ : Sal.EmbedRGA.OrderedPrefixCode)
    (ops : List (Op (Core Γ).AppOp)) :
    ((richSequentialSpec Γ).run ops).text = sSpecFold (projList₁ ops) := by
  induction ops using List.reverseRecOn with
  | nil => rfl
  | append_singleton ops e ih =>
      change ((richSequentialSpec Γ).run ops).text =
        sSpecFold (List.filterMap oplOp ops) at ih
      simp only [richSequentialSpec] at ih
      rcases e with ⟨t, r, o⟩
      cases o with
      | inl o₁ =>
          cases o₁ <;> simp [SequentialSpec.run_append_single,
            richSequentialSpec, richStep, ih, sSpecFold_snoc, projList₁_append,
            projList₁, oplOp] <;> try rw [ih]
      | inr o₂ =>
          cases o₂ with
          | inl d => cases d <;> simp [SequentialSpec.run_append_single,
              richSequentialSpec, richStep, ih, projList₁_append, projList₁, oplOp]
              <;> try rw [ih]
          | inr m => cases m <;> simp [SequentialSpec.run_append_single,
              richSequentialSpec, richStep, ih, projList₁_append, projList₁, oplOp]
              <;> try rw [ih]

private theorem osPayloads_update {α : Type} [DecidableEq α]
    (key : α → ℕ) (s : OSState α) (e : Op (OSOp α)) :
    osPayloads (osUpdate key s e) =
      match e.2.2 with
      | .add x => insert x (osPayloads s)
      | .rem k => (osPayloads s).filter (fun x => key x ≠ k) := by
  rcases e with ⟨t, r, o⟩
  cases o with
  | add x =>
      apply Finset.ext
      intro y
      simp [osPayloads, mem_osUpdate_add, eq_comm]
  | rem k =>
      apply Finset.ext
      intro y
      simp only [osPayloads, Finset.mem_image, mem_osUpdate_rem,
        Finset.mem_filter]
      constructor
      · rintro ⟨q, ⟨hq, hk⟩, rfl⟩
        exact ⟨⟨q, hq, rfl⟩, hk⟩
      · rintro ⟨⟨q, hq, rfl⟩, hk⟩
        exact ⟨q, ⟨hq, hk⟩, rfl⟩

private theorem richRun_deleted (Γ : Sal.EmbedRGA.OrderedPrefixCode)
    (ops : List (Op (Core Γ).AppOp)) :
    ((richSequentialSpec Γ).run ops).deleted =
      osPayloads (applySeq DeleteStore.toCRDTSig DeleteStore.init
        (projList₁ (projList₂ ops))) := by
  induction ops using List.reverseRecOn with
  | nil => rfl
  | append_singleton ops e ih =>
      change ((richSequentialSpec Γ).run ops).deleted =
        osPayloads (applySeq DeleteStore.toCRDTSig DeleteStore.init
          (List.filterMap oplOp (List.filterMap oprOp ops))) at ih
      simp only [richSequentialSpec] at ih
      rcases e with ⟨t, r, o⟩
      cases o with
      | inl x => cases x <;> simp [SequentialSpec.run_append_single,
          richSequentialSpec, richStep, projList₁_append, projList₂_append,
          projList₁, projList₂, oplOp, oprOp, ih] <;> try rw [ih]
      | inr stores =>
          cases stores with
          | inl d =>
              cases d with
              | add a =>
                  simp only [SequentialSpec.run_append_single,
                    richSequentialSpec, richStep, projList₁_append,
                    projList₂_append, projList₁, projList₂, oplOp, oprOp,
                    List.filterMap_append, List.filterMap_cons,
                    List.filterMap_nil, List.append_nil]
                  rw [ih, applySeq_append_single]
                  exact (osPayloads_update id _ (t, r, OSOp.add a)).symm
              | rem a =>
                  simp only [SequentialSpec.run_append_single,
                    richSequentialSpec, richStep, projList₁_append,
                    projList₂_append, projList₁, projList₂, oplOp, oprOp,
                    List.filterMap_append, List.filterMap_cons,
                    List.filterMap_nil, List.append_nil]
                  rw [ih, applySeq_append_single]
                  change _ = osPayloads (osUpdate id
                    (applySeq DeleteStore.toCRDTSig DeleteStore.init
                      (List.filterMap oplOp (List.filterMap oprOp ops)))
                    (t, r, OSOp.rem a))
                  rw [osPayloads_update]
                  ext x
                  simp only [Finset.mem_erase, Finset.mem_filter]
                  tauto
          | inr m => cases m <;> simp [SequentialSpec.run_append_single,
              richSequentialSpec, richStep, projList₁_append, projList₂_append,
              projList₁, projList₂, oplOp, oprOp, ih] <;> try rw [ih]

private theorem richRun_marks (Γ : Sal.EmbedRGA.OrderedPrefixCode)
    (ops : List (Op (Core Γ).AppOp)) :
    ((richSequentialSpec Γ).run ops).marks =
      osPayloads (applySeq RuntimeMarkStore.toCRDTSig RuntimeMarkStore.init
        (projList₂ (projList₂ ops))) := by
  induction ops using List.reverseRecOn with
  | nil => rfl
  | append_singleton ops e ih =>
      change ((richSequentialSpec Γ).run ops).marks =
        osPayloads (applySeq RuntimeMarkStore.toCRDTSig RuntimeMarkStore.init
          (List.filterMap oprOp (List.filterMap oprOp ops))) at ih
      simp only [richSequentialSpec] at ih
      rcases e with ⟨t, r, o⟩
      cases o with
      | inl x => cases x <;> simp [SequentialSpec.run_append_single,
          richSequentialSpec, richStep, projList₂_append, projList₂, oprOp, ih]
          <;> try rw [ih]
      | inr stores =>
          cases stores with
          | inl d => cases d <;> simp [SequentialSpec.run_append_single,
              richSequentialSpec, richStep, projList₂_append, projList₂, oprOp, ih]
              <;> try rw [ih]
          | inr m =>
              cases m with
              | add a =>
                  simp only [SequentialSpec.run_append_single,
                    richSequentialSpec, richStep, projList₂_append, projList₂,
                    oprOp, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
                    List.append_nil]
                  rw [ih, applySeq_append_single]
                  exact (osPayloads_update PeritextEmbed.MarkDoc.MarkD.mid _
                    (t, r, OSOp.add a)).symm
              | rem a =>
                  simp only [SequentialSpec.run_append_single,
                    richSequentialSpec, richStep, projList₂_append, projList₂,
                    oprOp, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
                    List.append_nil]
                  rw [ih, applySeq_append_single]
                  change _ = osPayloads
                    (osUpdate PeritextEmbed.MarkDoc.MarkD.mid
                      (applySeq RuntimeMarkStore.toCRDTSig RuntimeMarkStore.init
                        (List.filterMap oprOp (List.filterMap oprOp ops)))
                      (t, r, OSOp.rem a))
                  rw [osPayloads_update]

/-- The complete local sequential-refinement theorem for the runtime-shaped
sided core.  It covers character order, logical deletion, and immutable mark
events; rendered views are therefore functions of equal client states. -/
theorem richSequentialSound {Γ : Sal.EmbedRGA.OrderedPrefixCode}
    {ops : List (Op (Core Γ).AppOp)}
    (h : LinearMintHistory (Core Γ) (coreGuard Γ) ops) :
    richStateRel
      (applySeq (Core Γ).toCRDTSig (Core Γ).init ops)
      ((richSequentialSpec Γ).run ops) := by
  change richStateRel
    (applySeq (prodSig (S Γ) Stores).toCRDTSig
      (prodSig (S Γ) Stores).init ops) _
  rw [applySeq_prod]
  change richStateRel (_, applySeq (prodSig DeleteStore RuntimeMarkStore).toCRDTSig
    (prodSig DeleteStore RuntimeMarkStore).init (projList₂ ops)) _
  rw [applySeq_prod]
  unfold richStateRel
  refine ⟨?_, ?_, ?_⟩
  · rw [richRun_text]
    exact sided_seq_read (sSeqOK_of_linearMintHistory (linearMintHistory_text h))
  · exact (richRun_deleted Γ ops).symm
  · exact (richRun_marks Γ ops).symm

#print axioms linearMintHistory_text
#print axioms textSequentialSound
#print axioms richSequentialSound

end Sal.ConditionedMRDTs.PeritextSided
