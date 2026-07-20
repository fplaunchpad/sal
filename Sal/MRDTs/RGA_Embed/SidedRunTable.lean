import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Induction
import Sal.MRDTs.RGA_Embed.Sided_ChainLex

/-!
# The sided run table — the run-table representation over the sided (Fugue) kernel (#73)

Design + measurement: `whiteboard/run-table-note.md` §6 (the side channel);
executable reference `whiteboard/litmus/run_table_measure.py` (the sided/Fugue
family, `build_table` with `side` set). This file extends the one-sided run
table (`Sal/MRDTs/RGA_Embed/RunTable.lean`) to the sided chain kernel
(`Sided_ChainLex`): entries carry a **side** field, runs are uniformly-`R`
maximal fusible chains (fusibility condition 3 `side(c) = R`, vacuous
one-sided, is now live), and `L` entries are stored explicitly (note §6: the
side channel collapses from one bit per level to one bit per entry).

The state is the list of live **sided** birth chains (`List SChain`, an
`SChain` = `List (Side × ℕ)`). The kept tree is the live chains plus their
dead ancestors (nonempty prefixes). An edge into `c` is **fusible** when `c`
is the unique kept child of its parent, its last entry is `(R, 1)` — side `R`
AND delta `1` — and it has its parent's liveness; a **run** is a maximal
fusible chain, hence uniformly `R`. No stability or honest-delivery
hypothesis appears: every theorem is a state-level fact about a representation
change (the measured no-stability-gate finding, sided family).

This file establishes the sided structural core through the sided
tail-attachment lemma (`stail_attachment`), the sided run-table entry type
with its side field, and the band-order comparator content (reusing
`Sided_ChainLex`'s `schainBefore` / `sEntryBefore` / `sdisplay_iff_schainBefore`),
with PASS+FAIL SPOTs pinning an L-entry directed case and the band order.
-/

namespace Sal.EmbedRGA.SidedRunTable

open Sal.EmbedRGA (Side SEntry SChain PosSChain sidedCoordOf sKey sEntryBefore
  schainBefore sBlock schainBefore_total sdisplay_iff_schainBefore
  sidedCoordOf_inj keyLt keyLt_asymm sEntryBefore_irrefl sEntryBefore_asymm)

/-! ## §0  The sided kept tree over a live sided-chain list -/

/-- The nonempty prefixes of a sided chain, short to long. -/
def sPrefixesOf (l : SChain) : List SChain :=
  (List.range l.length).map (fun k => l.take (k + 1))

theorem mem_sPrefixesOf {l c : SChain} :
    c ∈ sPrefixesOf l ↔ c ≠ [] ∧ c <+: l := by
  simp only [sPrefixesOf, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨?_, List.take_prefix _ _⟩
    intro hnil
    rcases List.take_eq_nil_iff.mp hnil with h | h
    · omega
    · subst h; simp at hk
  · rintro ⟨hne, hpre⟩
    refine ⟨c.length - 1, ?_, ?_⟩
    · have h1 : 1 ≤ c.length := List.length_pos_iff.mpr hne
      have h2 : c.length ≤ l.length := hpre.length_le
      omega
    · have h1 : 1 ≤ c.length := List.length_pos_iff.mpr hne
      have : c.length - 1 + 1 = c.length := by omega
      rw [this]
      exact (List.prefix_iff_eq_take.mp hpre).symm

/-- The sided kept tree: live records plus their dead ancestors. -/
def skeptL (L : List SChain) : List SChain :=
  (L.flatMap sPrefixesOf).dedup

theorem mem_skeptL {L : List SChain} {c : SChain} :
    c ∈ skeptL L ↔ c ≠ [] ∧ ∃ l ∈ L, c <+: l := by
  simp only [skeptL, List.mem_dedup, List.mem_flatMap]
  constructor
  · rintro ⟨l, hl, hc⟩
    obtain ⟨hne, hpre⟩ := mem_sPrefixesOf.mp hc
    exact ⟨hne, l, hl, hpre⟩
  · rintro ⟨hne, l, hl, hpre⟩
    exact ⟨l, hl, mem_sPrefixesOf.mpr ⟨hne, hpre⟩⟩

theorem nodup_skeptL (L : List SChain) : (skeptL L).Nodup :=
  List.nodup_dedup _

theorem skept_ne_nil {L : List SChain} {c : SChain} (hc : c ∈ skeptL L) :
    c ≠ [] := (mem_skeptL.mp hc).1

theorem skept_of_prefix {L : List SChain} {c p : SChain}
    (hc : c ∈ skeptL L) (hp : p <+: c) (hne : p ≠ []) : p ∈ skeptL L := by
  obtain ⟨-, l, hl, hpre⟩ := mem_skeptL.mp hc
  exact mem_skeptL.mpr ⟨hne, l, hl, hp.trans hpre⟩

theorem skept_of_live {L : List SChain} {c : SChain}
    (hc : c ∈ L) (hne : c ≠ []) : c ∈ skeptL L :=
  mem_skeptL.mpr ⟨hne, c, hc, List.prefix_refl c⟩

/-! ## §1  Sided fusible edges: uniform R runs

The note §2 fusibility, sided: the edge into `c` is fusible when (1) `c` is
the unique kept child of `c.dropLast`, (2) `delta(c) = 1` AND (3) `side(c) = R`
— jointly `c`'s last entry is `(R, 1)` — and (4) `live(c) = live(c.dropLast)`.
Condition 3 is the one made live by the sided model: runs are uniformly `R`. -/

/-- Fusibility of the edge into the sided chain `c` (last entry `(R,1)`). -/
def sfusible (L : List SChain) (c : SChain) : Bool :=
  decide (c ∈ skeptL L) && decide (c.dropLast ∈ skeptL L)
    && (c.getLastD (Side.R, 0) == (Side.R, 1))
    && decide (∀ c' ∈ skeptL L, c'.dropLast = c.dropLast → c' = c)
    && (decide (c ∈ L) == decide (c.dropLast ∈ L))

theorem sfusible_kept {L : List SChain} {c : SChain}
    (h : sfusible L c = true) : c ∈ skeptL L := by
  simp only [sfusible, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1

theorem sfusible_parent_kept {L : List SChain} {c : SChain}
    (h : sfusible L c = true) : c.dropLast ∈ skeptL L := by
  simp only [sfusible, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2

theorem sfusible_unique {L : List SChain} {c c' : SChain}
    (h : sfusible L c = true) (hc' : c' ∈ skeptL L)
    (hpar : c'.dropLast = c.dropLast) : c' = c := by
  simp only [sfusible, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2 c' hc' hpar

theorem sfusible_last {L : List SChain} {c : SChain}
    (h : sfusible L c = true) : c.getLastD (Side.R, 0) = (Side.R, 1) := by
  simp only [sfusible, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.2

theorem sfusible_ne_nil {L : List SChain} {c : SChain}
    (h : sfusible L c = true) : c ≠ [] := skept_ne_nil (sfusible_kept h)

/-- A fusible edge's chain ends in `(R, 1)` — hence its run is uniformly `R`. -/
theorem sfusible_concat {L : List SChain} {c : SChain}
    (h : sfusible L c = true) : c = c.dropLast ++ [(Side.R, 1)] := by
  rcases List.eq_nil_or_concat c with rfl | ⟨p, b, rfl⟩
  · exact absurd rfl (sfusible_ne_nil h)
  · simp only [List.concat_eq_append] at h ⊢
    have hl := sfusible_last h
    simp only [List.getLastD_concat] at hl
    rw [List.dropLast_concat, hl]

/-- A head: a kept node whose incoming edge is not fusible. -/
def sisHead (L : List SChain) (c : SChain) : Bool :=
  decide (c ∈ skeptL L) && !sfusible L c

theorem sisHead_kept {L : List SChain} {c : SChain}
    (h : sisHead L c = true) : c ∈ skeptL L := by
  simp only [sisHead, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem sisHead_not_fusible {L : List SChain} {c : SChain}
    (h : sisHead L c = true) : sfusible L c = false := by
  simp only [sisHead, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.2

theorem sisHead_of_kept_not_fusible {L : List SChain} {c : SChain}
    (hc : c ∈ skeptL L) (hf : sfusible L c = false) : sisHead L c = true := by
  simp only [sisHead, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  exact ⟨hc, hf⟩

/-! ## §2  The run-ancestor walk and the sided tail-attachment lemma -/

/-- The run-ancestor walk: climb fusible edges to the run's head. -/
def sheadOf (L : List SChain) (c : SChain) : SChain :=
  if h : sfusible L c = true then sheadOf L c.dropLast else c
  termination_by c.length
  decreasing_by
    have hne : c ≠ [] := sfusible_ne_nil h
    have : 0 < c.length := List.length_pos_iff.mpr hne
    simp only [List.length_dropLast]
    omega

theorem sheadOf_of_fusible {L : List SChain} {c : SChain}
    (h : sfusible L c = true) : sheadOf L c = sheadOf L c.dropLast := by
  rw [sheadOf, dif_pos h]

theorem sheadOf_of_not_fusible {L : List SChain} {c : SChain}
    (h : sfusible L c = false) : sheadOf L c = c := by
  rw [sheadOf, dif_neg (by simp [h])]

theorem sheadOf_prefix (L : List SChain) (c : SChain) : sheadOf L c <+: c := by
  fun_induction sheadOf L c with
  | case1 c hf ih => exact ih.trans (List.dropLast_prefix c)
  | case2 c hf => exact List.prefix_refl c

theorem sheadOf_kept {L : List SChain} {c : SChain} (hc : c ∈ skeptL L) :
    sheadOf L c ∈ skeptL L := by
  fun_induction sheadOf L c with
  | case1 c hf ih => exact ih (sfusible_parent_kept hf)
  | case2 c hf => exact hc

theorem sheadOf_isHead {L : List SChain} {c : SChain} (hc : c ∈ skeptL L) :
    sisHead L (sheadOf L c) = true := by
  fun_induction sheadOf L c with
  | case1 c hf ih => exact ih (sfusible_parent_kept hf)
  | case2 c hf =>
      exact sisHead_of_kept_not_fusible hc (Bool.eq_false_iff.mpr hf)

theorem sheadOf_eq_self_of_isHead {L : List SChain} {h : SChain}
    (hh : sisHead L h = true) : sheadOf L h = h :=
  sheadOf_of_not_fusible (sisHead_not_fusible hh)

/-- **Sided T-tail** (the load-bearing lemma, sided version): in the canonical
sided table, every entry attaches at its parent entry's last member. Kernel
form: a head's parent node has no fusible `(R,1)`-successor — a fusible
successor would be its unique kept child while the head is another kept child.
Proof is the one-sided argument with the label `(R,1)`. No honesty, no
stability. -/
theorem stail_attachment {L : List SChain} {h : SChain}
    (hh : sisHead L h = true) :
    sfusible L (h.dropLast ++ [(Side.R, 1)]) = false := by
  cases hf : sfusible L (h.dropLast ++ [(Side.R, 1)]) with
  | false => rfl
  | true =>
      exfalso
      have hd : (h.dropLast ++ [(Side.R, 1)]).dropLast = h.dropLast :=
        List.dropLast_concat
      have heq : h = h.dropLast ++ [(Side.R, 1)] :=
        sfusible_unique hf (sisHead_kept hh) (by rw [hd])
      rw [← heq] at hf
      rw [sisHead_not_fusible hh] at hf
      exact Bool.noConfusion hf

/-! ## §3  The sided run-table entry, and L entries stored explicitly

The sided entry mirrors the one-sided `RTEntry` with one added `side` bit
(note §6: "the entry header carries one side bit, and L entries are the only
L data in the table"). Runs are uniformly `R` (`sfusible_side_R`), so member
sides cost nothing; every `L` node is forced to be a head — its own explicit
entry (`Lentry_isHead`). -/

/-- A sided table entry: the one-sided header plus a `side` field. -/
structure SRTEntry where
  par   : Option (ℕ × ℕ)
  live  : Bool
  side  : Side
  delta : ℕ
  len   : ℕ
deriving DecidableEq

abbrev STable := List SRTEntry

/-- **Uniform-R runs**: a fusible edge's chain ends `(R,1)`, so within a run
every member is `R` — the side channel collapses to one bit per entry. -/
theorem sfusible_side_R {L : List SChain} {c : SChain}
    (h : sfusible L c = true) : (c.getLastD (Side.R, 0)).1 = Side.R := by
  rw [sfusible_last h]

/-- **L entries never fuse**: an `L`-sided edge fails fusibility condition 3,
so it is never fused into a run. -/
theorem Lentry_not_fusible {L : List SChain} {c : SChain}
    (hL : (c.getLastD (Side.R, 0)).1 = Side.L) : sfusible L c = false := by
  cases hf : sfusible L c with
  | false => rfl
  | true =>
      exfalso
      rw [sfusible_last hf] at hL
      exact absurd hL (by decide)

/-- **L entries stored explicitly**: every kept `L` node is a head — its own
entry — the sided run table's defining structural fact (note §6). -/
theorem Lentry_isHead {L : List SChain} {c : SChain}
    (hc : c ∈ skeptL L) (hL : (c.getLastD (Side.R, 0)).1 = Side.L) :
    sisHead L c = true :=
  sisHead_of_kept_not_fusible hc (Lentry_not_fusible hL)

/-! ## §4  The band-order comparator (sided T-cmp seed)

The sided comparator's two-case structure is licensed by `stail_attachment`
exactly as in the one-sided `cmpTable`; its **semantic core** is the sided
key order, which is `schainBefore` — including the band case `(L,·)` before
`(R,·)`. This re-exposes the kernel's marker theorem at the run-table layer;
the full entry-chain comparator refines it (owed). -/

open Sal.EmbedRGA (OrderedPrefixCode)

/-- **Sided key order = in-order display rule**: for distinct positive sided
chains the sided coordinate key comparison equals `schainBefore` — the sided
two-band order (L band ascending, node, R band descending). -/
theorem sided_keyLt_iff_schainBefore (Γ : OrderedPrefixCode) {c1 c2 : SChain}
    (h1 : PosSChain c1) (h2 : PosSChain c2) (hne : c1 ≠ c2) :
    keyLt (sKey (sidedCoordOf Γ c2)) (sKey (sidedCoordOf Γ c1)) = true ↔
      schainBefore c1 c2 :=
  sdisplay_iff_schainBefore Γ h1 h2 hne

/-! ## §5  Axiom audit -/

#print axioms stail_attachment
#print axioms Lentry_isHead
#print axioms sfusible_side_R
#print axioms sided_keyLt_iff_schainBefore

/-! ## §6  SPOTs — concrete sided executions, PASS + FAIL, hand-derived -/

namespace SidedRunTableSPOT

open Sal.EmbedRGA (unaryCode)

/-- Root `(R,1)` with an `R` delta-1 child (the R run). -/
def SR : List SChain := [[(Side.R, 1)], [(Side.R, 1), (Side.R, 1)]]

/-- Root `(R,1)` with, concurrently, an `L` child. -/
def SL : List SChain := [[(Side.R, 1)], [(Side.R, 1), (Side.L, 1)]]

/-- PASS: an `R` delta-1 child fuses — the uniform-R run. -/
theorem spot_R_fuses : sfusible SR [(Side.R, 1), (Side.R, 1)] = true := by
  native_decide

/-- PASS + FAIL (L stored explicitly): the `L` child does NOT fuse (contrast
the `R` child, `spot_R_fuses`) — it is a head, its own entry. -/
theorem spot_L_explicit :
    sfusible SL [(Side.R, 1), (Side.L, 1)] = false
    ∧ sisHead SL [(Side.R, 1), (Side.L, 1)] = true := by native_decide

/-- PASS + FAIL (band order): every `L` entry precedes every `R` entry at a
shared anchor, regardless of delta. -/
theorem spot_band_order :
    sEntryBefore (Side.L, 3) (Side.R, 5)
    ∧ ¬ sEntryBefore (Side.R, 5) (Side.L, 3) :=
  ⟨trivial, fun h => h.elim⟩

/-- PASS + FAIL (band, in the coordinate keys): under the unary code, the `L`
child of a node displays before its `R` child. -/
theorem spot_band_keyLt :
    keyLt (sKey (sidedCoordOf unaryCode [(Side.R, 1), (Side.R, 2)]))
      (sKey (sidedCoordOf unaryCode [(Side.R, 1), (Side.L, 2)])) = true
    ∧ keyLt (sKey (sidedCoordOf unaryCode [(Side.R, 1), (Side.L, 2)]))
      (sKey (sidedCoordOf unaryCode [(Side.R, 1), (Side.R, 2)])) = false := by
  native_decide

#print axioms spot_L_explicit
#print axioms spot_band_keyLt

end SidedRunTableSPOT

end Sal.EmbedRGA.SidedRunTable
