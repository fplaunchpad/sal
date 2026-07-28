import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_Recoding

/-!
# Merge-vs-remap congruence — the VC-S4 discharge for the embed remap species

`EmbedRGA_Stability_Bridge.lean` bridges the re-coding cluster to the
`StabilityVC` interface at a `SettledAt` cut, but leaves **VC-S4 (the merge
clause, `vc_merge`) unbridged**: the re-coding theorems (`eRecode_applySeq` and
friends) live at the *fold/state* level, and the embed RGA's merge congruence
was deferred to the protocol half. This file closes that gap on the data plane.

**The route** (`whiteboard/embed-recoding-note.md` §5, lifted to the ternary merge). The embed merge
`eMergeL l a b` is a *function of the (id, coordinate) records*: it (i) filters
`a`, `b` by **id** membership (`eIds`), then (ii) re-canonicalizes with the
sorted 2-merge `eMerge2`, which compares only **keys of coordinates**. The lazy
translation `eRemapSt F.f` rewrites coordinates and *fixes ids*
(`eRemapRec` keeps `.1`), so:

* the id filters are invariant (`eIds_eRemapSt`, `eRemapSt_filter`);
* the key-ordered 2-merge commutes with the re-map because H2 (`F.ord`) makes
  every head comparison agree on the coordinates at hand (`eMerge2_remap`).

Hence `merge_remap_congr`: **`eRemapSt F.f` commutes with `eMergeL`** on inputs
whose records are all at hand. Applying it with all three arguments remapped
discharges VC-S4 for the coordinate-iso relation `eRemapRel`
(`eRemapRel_merge`): a merge of three re-mapped versions is the re-map of the
merge. MIXED merges (one argument already remapped, others translated on
ingest) are the same statement — the congruence is argument-uniform.

Kernel-clean `{propext, Classical.choice, Quot.sound}`. What this does *not*
build is a full `StabilityVC` bundle: that interface's `R` must also be
*reflexive* (`vc_refl`, to seed the pre-compaction run) and carry the other VCs;
the remap relation alone is not reflexive, so the bundle wiring is the
stability-instance construction of the deferred protocol half. The **merge
congruence itself** — the piece the bridge flagged as owed — is here.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode key keyLt)

set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] [Inhabited α]

/-! ## §1 Id-filters are invariant under the coordinate re-map -/

/-- The lazy translation commutes with an **id-based** filter: `eRemapRec` fixes
`.1`, so a predicate reading only the id sees the same records. -/
theorem eRemapSt_filter (f : List Bool → List Bool) (p : ERec α → Bool)
    (hp : ∀ r : ERec α, p (eRemapRec f r) = p r) (s : EState α) :
    (eRemapSt f s).filter p = eRemapSt f (s.filter p) := by
  unfold eRemapSt
  rw [List.filter_map]
  exact congrArg _ (List.filter_congr (fun a _ => hp a))

/-! ## §2 The sorted 2-merge commutes with the re-map

`eMerge2` compares only `keyLt (key ·) (key ·)` of coordinates; H2 (`F.ord`)
makes those comparisons agree between the re-mapped and original records, so the
same branch is taken at every step. -/

/-- **`eMerge2` congruence.** On inputs whose records are at hand, merging the
re-mapped lists is the re-map of the merge. -/
theorem eMerge2_remap {Γ : OrderedPrefixCode} (F : StablePrefixMap Γ) :
    ∀ (as bs : EState α), (∀ x ∈ as, F.Dom x.2.2) → (∀ y ∈ bs, F.Dom y.2.2) →
    eMerge2 (eRemapSt F.f as) (eRemapSt F.f bs) = eRemapSt F.f (eMerge2 as bs) := by
  intro as bs hax hby
  induction as, bs using eMerge2.induct with
  | case1 ys => simp [eMerge2, eRemapSt]
  | case2 xs => cases xs <;> simp [eMerge2, eRemapSt]
  | case3 a as' b bs' h ih =>
      have hax' : ∀ x ∈ as', F.Dom x.2.2 :=
        fun x hx => hax x (List.mem_cons_of_mem _ hx)
      have hdomB : F.Dom b.2.2 := hby b List.mem_cons_self
      have hdomA : F.Dom a.2.2 := hax a List.mem_cons_self
      have hcmp : keyLt (key ((eRemapRec F.f b).2.2)) (key ((eRemapRec F.f a).2.2))
          = true := by
        show keyLt (key (F.f b.2.2)) (key (F.f a.2.2)) = true
        rw [F.ord' hdomB hdomA]; exact h
      rw [show eRemapSt F.f (a :: as') = eRemapRec F.f a :: eRemapSt F.f as' from rfl,
          show eRemapSt F.f (b :: bs') = eRemapRec F.f b :: eRemapSt F.f bs' from rfl,
          show eMerge2 (eRemapRec F.f a :: eRemapSt F.f as')
                 (eRemapRec F.f b :: eRemapSt F.f bs')
               = eRemapRec F.f a :: eMerge2 (eRemapSt F.f as')
                   (eRemapRec F.f b :: eRemapSt F.f bs')
             from by rw [eMerge2]; simp [hcmp],
          show eMerge2 (a :: as') (b :: bs') = a :: eMerge2 as' (b :: bs')
             from by rw [eMerge2]; simp [h]]
      show eRemapRec F.f a :: eMerge2 (eRemapSt F.f as')
            (eRemapRec F.f b :: eRemapSt F.f bs')
          = eRemapRec F.f a :: eRemapSt F.f (eMerge2 as' (b :: bs'))
      congr 1
      rw [show eRemapRec F.f b :: eRemapSt F.f bs' = eRemapSt F.f (b :: bs') from rfl]
      exact ih hax' hby
  | case4 a as' b bs' h ih =>
      have hby' : ∀ y ∈ bs', F.Dom y.2.2 :=
        fun y hy => hby y (List.mem_cons_of_mem _ hy)
      have hdomB : F.Dom b.2.2 := hby b List.mem_cons_self
      have hdomA : F.Dom a.2.2 := hax a List.mem_cons_self
      have hcmp : keyLt (key ((eRemapRec F.f b).2.2)) (key ((eRemapRec F.f a).2.2))
          = false := by
        show keyLt (key (F.f b.2.2)) (key (F.f a.2.2)) = false
        rw [F.ord' hdomB hdomA]; simpa using h
      rw [show eRemapSt F.f (a :: as') = eRemapRec F.f a :: eRemapSt F.f as' from rfl,
          show eRemapSt F.f (b :: bs') = eRemapRec F.f b :: eRemapSt F.f bs' from rfl,
          show eMerge2 (eRemapRec F.f a :: eRemapSt F.f as')
                 (eRemapRec F.f b :: eRemapSt F.f bs')
               = eRemapRec F.f b :: eMerge2 (eRemapRec F.f a :: eRemapSt F.f as')
                   (eRemapSt F.f bs')
             from by rw [eMerge2]; simp [hcmp],
          show eMerge2 (a :: as') (b :: bs') = b :: eMerge2 (a :: as') bs'
             from by rw [eMerge2]; simp [h]]
      show eRemapRec F.f b :: eMerge2 (eRemapRec F.f a :: eRemapSt F.f as')
            (eRemapSt F.f bs')
          = eRemapRec F.f b :: eRemapSt F.f (eMerge2 (a :: as') bs')
      congr 1
      rw [show eRemapRec F.f a :: eRemapSt F.f as' = eRemapSt F.f (a :: as') from rfl]
      exact ih hax hby'

/-! ## §3 The merge congruence and the VC-S4 discharge -/

/-- **`merge_remap_congr` — the merge clause, on the data plane.** The lazy
translation commutes with the ternary merge on inputs whose records are all at
hand: merging three re-mapped states is the re-map of the merge. The LCA
argument `l` enters only through `eIds l` (id-based filter), so no domain
hypothesis on `l` is needed. -/
theorem merge_remap_congr {Γ : OrderedPrefixCode} (F : StablePrefixMap Γ)
    (l a b : EState α)
    (ha : ∀ x ∈ a, F.Dom x.2.2) (hb : ∀ x ∈ b, F.Dom x.2.2) :
    eMergeL (eRemapSt F.f l) (eRemapSt F.f a) (eRemapSt F.f b)
      = eRemapSt F.f (eMergeL l a b) := by
  unfold eMergeL
  simp only [eIds_eRemapSt]
  rw [eRemapSt_filter F.f (fun r => decide (r.1 ∈ eIds b ∨ r.1 ∉ eIds l))
        (fun _ => rfl) a,
      eRemapSt_filter F.f (fun r => decide (r.1 ∉ eIds l ∧ r.1 ∉ eIds a))
        (fun _ => rfl) b]
  exact eMerge2_remap F (a.filter _) (b.filter _)
    (fun x hx => ha x (List.mem_of_mem_filter hx))
    (fun x hx => hb x (List.mem_of_mem_filter hx))

/-- **The coordinate-iso simulation relation** `R_S` for the remap species: the
compacted state is the lazy translation of the full state, and every full record
is at hand. This is the `R` a stability instance for the compaction would
carry (with the domain as the pair-invariant `Aux`). -/
def eRemapRel {Γ : OrderedPrefixCode} (F : StablePrefixMap Γ) (s ŝ : EState α) :
    Prop :=
  (∀ x ∈ s, F.Dom x.2.2) ∧ ŝ = eRemapSt F.f s

/-- **The VC-S4 discharge (`vc_merge`) for the embed remap species.** Given the
three merge premises related by `eRemapRel` (full left, compacted right), the
merged pair is again `eRemapRel`-related — exactly the conclusion
`R (D.mergeL sT s₁ s₂) (D.mergeL ŝT ŝ₁ ŝ₂)` that `StabilityVC.vc_merge`
demands, here for `D = E Γ α`, `D.mergeL = eMergeL`, `R = eRemapRel F`. The
domain half is preserved because merge records come only from `s₁`/`s₂`; the
equality half is `merge_remap_congr`. -/
theorem eRemapRel_merge {Γ : OrderedPrefixCode} (F : StablePrefixMap Γ)
    {sT s₁ s₂ ŝT ŝ₁ ŝ₂ : EState α}
    (hT : eRemapRel F sT ŝT) (h1 : eRemapRel F s₁ ŝ₁) (h2 : eRemapRel F s₂ ŝ₂) :
    eRemapRel F (eMergeL sT s₁ s₂) (eMergeL ŝT ŝ₁ ŝ₂) := by
  obtain ⟨_, hTe⟩ := hT
  obtain ⟨h1d, h1e⟩ := h1
  obtain ⟨h2d, h2e⟩ := h2
  refine ⟨?_, ?_⟩
  · intro x hx
    unfold eMergeL at hx
    rcases (mem_eMerge2 _ _).mp hx with hxa | hxb
    · exact h1d x (List.mem_of_mem_filter hxa)
    · exact h2d x (List.mem_of_mem_filter hxb)
  · subst hTe; subst h1e; subst h2e
    exact merge_remap_congr F sT s₁ s₂ h1d h2d

/-- The at-`(E Γ α)` restatement, pinning that this is literally
`(E Γ α).mergeL` congruence — the datatype's ternary merge used by the ternary
simulation's `Step3.merge` branch. -/
theorem embed_merge_remap_congr {Γ : OrderedPrefixCode} (F : StablePrefixMap Γ)
    (l a b : EState α)
    (ha : ∀ x ∈ a, F.Dom x.2.2) (hb : ∀ x ∈ b, F.Dom x.2.2) :
    (E Γ α).mergeL (eRemapSt F.f l) (eRemapSt F.f a) (eRemapSt F.f b)
      = eRemapSt F.f ((E Γ α).mergeL l a b) :=
  merge_remap_congr F l a b ha hb

/-! ## §4 Axiom audit -/

#print axioms eMerge2_remap
#print axioms merge_remap_congr
#print axioms eRemapRel_merge
#print axioms embed_merge_remap_congr

end Sal.ConditionedMRDTs
