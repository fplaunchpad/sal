import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_SeqSpec
import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_ReadEquiv

/-!
# The tombstoned RGA, sequentially = the naive text buffer

The corollary that closes tier 3: composing sequential soundness
(`embed_seq_sound`) with the compaction machinery gives the published
tombstoned RGA's read of a sequentially honest history, **any**
`visible_lt`-sorted enumeration of its visible ids, as exactly the
naive sequential buffer. The conclusion is code-free: the buffer never
mentions coordinates.

No `Configuration` packaging is needed: `eSeqOK` instantiates the order
core's `BirthEnv` directly (the sequential mirror of
`birthEnv_rgaFold`), with the chain assignment chosen per id from the
sequential chain lemma and pinned by unique decodability.

Standalone build target (imports the tombstoned RGA model through the
read-equivalence file, the top-level names of the published tombstoned RGA
model collide with the rehoming RGA model the umbrella file
`MRDT_Instances.lean` already reaches, so the umbrella cannot reach this
file). Build:
`lake build Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_SeqSpec_RGA`.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode PosChain coordOf coordOf_inj
  coordOf_append key_inj keyLt key keyLt_irrefl BirthEnv RealId
  visible_lt_asymm chainBefore display_iff_chainBefore
  chainBefore_visible_lt)

/-! ## The sequential chain assignment -/

/-- Per-id chain existence for a sequential history (the sequential
`e_chain_exists`): on-support chains come from `e_seq_chains` and are
unique by `ins_nodup`; off-support ids get defaults. -/
theorem e_seq_chain_at {Γ : OrderedPrefixCode} {ρ : List (Op EOp)}
    (hOK : eSeqOK Γ ρ) (t : ℕ) :
    ∃ ch : List ℕ, PosChain ch ∧ ch.sum = t ∧
      ∀ o ∈ ρ, eIsIns o = true → o.1 = t →
        eCoord Γ o = coordOf Γ ch := by
  classical
  by_cases hex : ∃ o ∈ ρ, eIsIns o = true ∧ o.1 = t
  · obtain ⟨o, ho, hi, hot⟩ := hex
    obtain ⟨ch, h1, h2, -, h4⟩ := e_seq_chains hOK o ho hi
    refine ⟨ch, h1, by rw [← hot]; exact h2, ?_⟩
    intro o' ho' hi' hot'
    have hwf := eWf_of_seqOK hOK
    have hoo : o' = o := by
      have hinj := List.inj_on_of_nodup_map
        (f := Prod.fst) (l := ρ.filter (fun o => eIsIns o))
        hwf.ins_nodup
      exact hinj (List.mem_filter.mpr ⟨ho', hi'⟩)
        (List.mem_filter.mpr ⟨ho, hi⟩) (by rw [hot', hot])
    rw [hoo]
    exact h4
  · push_neg at hex
    cases t with
    | zero =>
        exact ⟨[], by intro d hd; simp at hd, rfl,
          fun o ho hi h1 => absurd h1 (hex o ho hi)⟩
    | succ n =>
        refine ⟨[n + 1], ?_, by simp,
          fun o ho hi h1 => absurd h1 (hex o ho hi)⟩
        intro d hd
        simp at hd
        omega

/-- The sequential chain assignment (choice over per-id existence). -/
noncomputable def eChainOfSeq {Γ : OrderedPrefixCode} {ρ : List (Op EOp)}
    (hOK : eSeqOK Γ ρ) : ℕ → List ℕ :=
  fun t => Classical.choose (e_seq_chain_at hOK t)

theorem eChainOfSeq_spec {Γ : OrderedPrefixCode} {ρ : List (Op EOp)}
    (hOK : eSeqOK Γ ρ) (t : ℕ) :
    PosChain (eChainOfSeq hOK t) ∧ (eChainOfSeq hOK t).sum = t ∧
    ∀ o ∈ ρ, eIsIns o = true → o.1 = t →
      eCoord Γ o = coordOf Γ (eChainOfSeq hOK t) :=
  Classical.choose_spec (e_seq_chain_at hOK t)

theorem eChainOfSeq_zero {Γ : OrderedPrefixCode} {ρ : List (Op EOp)}
    (hOK : eSeqOK Γ ρ) : eChainOfSeq hOK 0 = [] := by
  obtain ⟨hpos, hsum, -⟩ := eChainOfSeq_spec hOK 0
  cases hch : eChainOfSeq hOK 0 with
  | nil => rfl
  | cons d ds =>
      rw [hch] at hpos hsum
      have := hpos d List.mem_cons_self
      simp [List.sum_cons] at hsum
      omega

/-! ## The birth environment, sequentially -/

/-- **`eSeqOK` instantiates the order core directly**: the sequential
mirror of `birthEnv_rgaFold`, with applicability read off the history's
own splits. -/
theorem birthEnv_rgaFold_seq {Γ : OrderedPrefixCode} {ρ : List (Op EOp)}
    (hOK : eSeqOK Γ ρ) :
    BirthEnv (rgaFold ρ) (eChainOfSeq hOK) := by
  constructor
  case anchor_lt =>
    intro c p h
    obtain ⟨r, π, e, hm⟩ := after_of_rgaFold.mp h
    obtain ⟨σ₁, σ₂, heq⟩ := List.append_of_mem hm
    have happ := (hOK σ₁ (c, r, .ins e π p) σ₂ heq).2
    simp only [eApplicable] at happ
    exact happ.1
  case anchor_real =>
    intro c p h hp0
    obtain ⟨r, π, e, hm⟩ := after_of_rgaFold.mp h
    obtain ⟨σ₁, σ₂, heq⟩ := List.append_of_mem hm
    have happ := (hOK σ₁ (c, r, .ins e π p) σ₂ heq).2
    simp only [eApplicable] at happ
    rcases happ.2 with ⟨ha0, -⟩ | ⟨el', hmem⟩
    · exact absurd ha0 hp0
    · obtain ⟨aop, haσ, hai, hae⟩ := e_fold_rec_sub Γ σ₁ (p, el', π) hmem
      have hap : aop.1 = p := (congrArg Prod.fst hae).symm
      obtain ⟨ap, ar, aop2⟩ := aop
      cases aop2 with
      | del y => simp [eIsIns] at hai
      | ins ae aπ aa =>
          simp only at hap
          subst hap
          refine ⟨aa, after_of_rgaFold.mpr ⟨ar, aπ, ae, ?_⟩⟩
          rw [heq]
          exact List.mem_append_left _ haσ
  case chain_zero => exact eChainOfSeq_zero hOK
  case chain_step =>
    intro c p h
    obtain ⟨r, π, e, hm⟩ := after_of_rgaFold.mp h
    obtain ⟨σ₁, σ₂, heq⟩ := List.append_of_mem hm
    have happ := (hOK σ₁ (c, r, .ins e π p) σ₂ heq).2
    simp only [eApplicable] at happ
    obtain ⟨hpc, hcase⟩ := happ
    have hpc' : p < c := hpc
    obtain ⟨hpos_c, -, hpin_c⟩ := eChainOfSeq_spec hOK c
    have hcoord : π ++ Γ.enc (c - p) =
        coordOf Γ (eChainOfSeq hOK c) := by
      have := hpin_c (c, r, .ins e π p) hm (by simp [eIsIns]) rfl
      simpa [eCoord] using this
    rcases hcase with ⟨hp0, hπ0⟩ | ⟨el', hmem⟩
    · subst hp0
      subst hπ0
      have h1 : coordOf Γ (eChainOfSeq hOK c) = coordOf Γ [c] := by
        rw [← hcoord]
        simp [coordOf]
      have hpos1 : PosChain [c] := by
        intro d hd
        simp at hd
        omega
      rw [coordOf_inj Γ hpos_c hpos1 h1, eChainOfSeq_zero hOK]
      simp
    · obtain ⟨aop, haσ, hai, hae⟩ := e_fold_rec_sub Γ σ₁ (p, el', π) hmem
      have hap : aop.1 = p := (congrArg Prod.fst hae).symm
      have hπval : π = eCoord Γ aop :=
        congrArg (fun q : ERec => q.2.2) hae
      obtain ⟨hpos_p, -, hpin_p⟩ := eChainOfSeq_spec hOK p
      have hπchain : π = coordOf Γ (eChainOfSeq hOK p) := by
        rw [hπval]
        refine hpin_p aop ?_ hai hap
        rw [heq]
        exact List.mem_append_left _ haσ
      have hkey : coordOf Γ (eChainOfSeq hOK c) =
          coordOf Γ (eChainOfSeq hOK p ++ [c - p]) := by
        rw [← hcoord, hπchain, coordOf_append]
        simp [coordOf]
      have hpos2 : PosChain (eChainOfSeq hOK p ++ [c - p]) := by
        intro d hd
        rcases List.mem_append.mp hd with h' | h'
        · exact hpos_p d h'
        · simp at h'
          omega
      exact coordOf_inj Γ hpos_c hpos2 hkey

/-! ## The pipeline, sequentially -/

theorem fold_coord_pinned_seq {Γ : OrderedPrefixCode} {ρ : List (Op EOp)}
    (hOK : eSeqOK Γ ρ) {r : ERec} (hr : r ∈ eFold Γ ρ) :
    r.2.2 = coordOf Γ (eChainOfSeq hOK r.1) := by
  obtain ⟨o, ho, hoi, hrec⟩ := e_fold_rec_sub Γ ρ r hr
  obtain ⟨-, -, hpin⟩ := eChainOfSeq_spec hOK r.1
  have h1 : r.2.2 = eCoord Γ o := by rw [hrec]; rfl
  have h2 : o.1 = r.1 := by rw [hrec]; rfl
  rw [h1]
  exact hpin o ho hoi h2

theorem embed_read_pairwise_seq {Γ : OrderedPrefixCode}
    {ρ : List (Op EOp)} (hOK : eSeqOK Γ ρ) :
    (eIds (eFold Γ ρ)).Pairwise (_root_.visible_lt (rgaFold ρ)) := by
  have B := birthEnv_rgaFold_seq hOK
  have hwf := eWf_of_seqOK hOK
  have hsorted := e_fold_sorted Γ hwf
  unfold eIds
  rw [List.pairwise_map]
  refine hsorted.imp_of_mem ?_
  intro r r' hr hr' hkey
  have hpin := fold_coord_pinned_seq hOK hr
  have hpin' := fold_coord_pinned_seq hOK hr'
  rw [hpin, hpin'] at hkey
  obtain ⟨hpos, -, -⟩ := eChainOfSeq_spec hOK r.1
  obtain ⟨hpos', -, -⟩ := eChainOfSeq_spec hOK r'.1
  have hchne : eChainOfSeq hOK r.1 ≠ eChainOfSeq hOK r'.1 := by
    intro heq2
    rw [heq2, keyLt_irrefl] at hkey
    exact Bool.noConfusion hkey
  exact chainBefore_visible_lt B (realId_of_fold hr) (realId_of_fold hr')
    ((display_iff_chainBefore Γ hpos hpos' hchne).mp hkey)

/-! ## The corollary -/

/-- **The tombstoned RGA, sequentially = the naive buffer.** Any
`visible_lt`-sorted enumeration of the published RGA's visible ids, on a
sequentially honest history, is exactly the naive sequential buffer's id
sequence. The conclusion never mentions the code. -/
theorem rga_seq_read_eq_buffer {Γ : OrderedPrefixCode}
    {ρ : List (Op EOp)} (hOK : eSeqOK Γ ρ) (L : List ℕ)
    (hLsort : L.Pairwise (_root_.visible_lt (rgaFold ρ)))
    (hLmem : ∀ t, t ∈ L ↔ _root_.visible (rgaFold ρ) t) :
    L = (eSpecFold ρ).map Prod.fst := by
  have hwf := eWf_of_seqOK hOK
  have hL : L = eIds (eFold Γ ρ) :=
    sorted_unique
      (fun _ _ => visible_lt_asymm (birthEnv_rgaFold_seq hOK))
      L _ hLsort (embed_read_pairwise_seq hOK)
      (fun t => (hLmem t).trans (visible_iff_eIds hwf t))
  rw [hL]
  have hids : eIds (eFold Γ ρ) =
      ((eFold Γ ρ).map eProj).map Prod.fst := by
    rw [List.map_map]
    rfl
  rw [hids, embed_seq_sound hOK]

/-- Element agreement: every buffer entry is read by the published RGA
at the same id with the same element. -/
theorem rga_seq_read_element {Γ : OrderedPrefixCode}
    {ρ : List (Op EOp)} (hOK : eSeqOK Γ ρ) {t el : ℕ}
    (h : (t, el) ∈ eSpecFold ρ) :
    _root_.readSeq_visible (rgaFold ρ) t el := by
  have hwf := eWf_of_seqOK hOK
  rw [← embed_seq_sound hOK] at h
  obtain ⟨rec, hrec, hproj⟩ := List.mem_map.mp h
  obtain ⟨t', el', co⟩ := rec
  simp only [eProj, Prod.mk.injEq] at hproj
  obtain ⟨rfl, rfl⟩ := hproj
  exact embed_rec_readSeq hwf hrec

end Sal.ConditionedMRDTs
