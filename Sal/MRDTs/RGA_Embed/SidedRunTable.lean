import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Induction
import Sal.MRDTs.RGA_Embed.Sided_ChainLex
import Sal.MRDTs.RGA_Embed.RunTable

/-!
# The sided run table: the run-table representation over the sided (Fugue) kernel

Design + measurement: `whiteboard/run-table-note.md` §6 (the side channel);
executable reference `whiteboard/litmus/run_table_measure.py` (the sided/Fugue
family, `build_table` with `side` set). This file extends the one-sided run
table (`Sal/MRDTs/RGA_Embed/RunTable.lean`) to the sided chain kernel
(`Sided_ChainLex`): entries carry a **side** field, runs are uniformly-`R`
maximal fusible chains (fusibility condition 3 `side(c) = R`, vacuous
one-sided, live here), and `L` entries are stored explicitly (note §6: the
side channel collapses from one bit per level to one bit per entry).

The state is the list of live **sided** birth chains (`List SChain`, an
`SChain` = `List (Side × ℕ)`). The kept tree is the live chains plus their
dead ancestors (nonempty prefixes). An edge into `c` is **fusible** when `c`
is the unique kept child of its parent, its last entry is `(R, 1)`, side `R`
AND delta `1`, and it has its parent's liveness; a **run** is a maximal
fusible chain, hence uniformly `R`. No stability or honest-delivery
hypothesis appears: every theorem is a state-level fact about a representation
change (the measured no-stability-gate finding, sided family).

This file carries the FULL sided mirror of the one-sided run-table
development: the sided tail-attachment lemma (`stail_attachment`) and
run structure (§5); the canonical sided head order (§6, `shLt` over the
flattened word stream); the representation iso BOTH directions over
labels + SIDES + liveness, deliberately NOT timestamps, for the same
post-epoch reason as one-sided, with canonicity and image side (§7,
`sStateOf_sTableOf` / `sTableOf_sStateOf` / `scanonical_sTableOf`); the full
two-case entry-chain comparator `scmpTable` licensed by `stail_attachment`,
refining the §4 band-order seed, equal to the sided key order for EVERY
ordered prefix code (§8, `scmpTable_eq_keyLt`); the in-order structural walk
(§9, `swalk_display`); merge congruence and the O(1) sided insert-extend
typing equation (§10); the walk round trip and the table-DIRECT walk
`stableWalk` with its faithfulness theorem (§11, `stableWalk_sTableOf`);
and the all-R projection bridge, on an all-R live set the sided table and
walk are the one-sided ones in lockstep (§12, `sTableOf_liftR` /
`swalk_liftR`, consuming the kernel's `schainBefore_liftR`). PASS+FAIL
SPOTs pin the L-entry case, the band order, the L-band mint display, the
band DIRECTION (the tempting wrong L sort flips a display), the
table-direct walk, and the all-R lockstep.
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
the unique kept child of `c.dropLast`, (2) `delta(c) = 1` AND (3) `side(c) = R`,
jointly `c`'s last entry is `(R, 1)`, and (4) `live(c) = live(c.dropLast)`.
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

/-- A fusible edge's chain ends in `(R, 1)`, hence its run is uniformly `R`. -/
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
form: a head's parent node has no fusible `(R,1)`-successor, a fusible
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
sides cost nothing; every `L` node is forced to be a head, its own explicit
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
every member is `R`, the side channel collapses to one bit per entry. -/
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

/-- **L entries stored explicitly**: every kept `L` node is a head, its own
entry, the sided run table's defining structural fact (note §6). -/
theorem Lentry_isHead {L : List SChain} {c : SChain}
    (hc : c ∈ skeptL L) (hL : (c.getLastD (Side.R, 0)).1 = Side.L) :
    sisHead L c = true :=
  sisHead_of_kept_not_fusible hc (Lentry_not_fusible hL)

/-! ## §4  The band-order comparator (sided T-cmp seed)

The sided comparator's two-case structure is licensed by `stail_attachment`
exactly as in the one-sided `cmpTable`; its **semantic core** is the sided
key order, which is `schainBefore`, including the band case `(L,·)` before
`(R,·)`. This re-exposes the kernel's marker theorem at the run-table layer;
the full entry-chain comparator `scmpTable` (§8) refines it, with
`scmpTable_eq_keyLt` the equality against the sided key order for every
ordered prefix code. -/

open Sal.EmbedRGA (OrderedPrefixCode)

/-- **Sided key order = in-order display rule**: for distinct positive sided
chains the sided coordinate key comparison equals `schainBefore`, the sided
two-band order (L band ascending, node, R band descending). -/
theorem sided_keyLt_iff_schainBefore (Γ : OrderedPrefixCode) {c1 c2 : SChain}
    (h1 : PosSChain c1) (h2 : PosSChain c2) (hne : c1 ≠ c2) :
    keyLt (sKey (sidedCoordOf Γ c2)) (sKey (sidedCoordOf Γ c1)) = true ↔
      schainBefore c1 c2 :=
  sdisplay_iff_schainBefore Γ h1 h2 hne

/-! ## §5  Sided runs: members, length, tail

The one-sided §3, over `SChain`: run members are the head padded by `(R,1)`
blocks, offsets are complete below the run length, the tail is where the run
stops, and heads attach at their parent run's tail (`shead_parent_is_tail`,
the consequence of `stail_attachment`). -/

theorem sprefix_dropLast_of_ne {p c : SChain} (hp : p <+: c) (hne : p ≠ c) :
    p <+: c.dropLast := by
  have hl : p.length < c.length :=
    lt_of_le_of_ne hp.length_le (fun h => hne (hp.eq_of_length h))
  have hpc : p = c.take p.length := List.prefix_iff_eq_take.mp hp
  rw [List.dropLast_eq_take, hpc]
  have : c.take p.length = (c.take (c.length - 1)).take p.length := by
    rw [List.take_take]
    congr 1
    omega
  rw [this]
  exact List.take_prefix _ _

/-- Every node is its run head extended by a block of `(R,1)` labels. -/
theorem sheadOf_replicate (L : List SChain) (c : SChain) :
    ∃ k, c = sheadOf L c ++ List.replicate k (Side.R, 1) := by
  fun_induction sheadOf L c with
  | case1 c hf ih =>
      obtain ⟨k, hk⟩ := ih
      refine ⟨k + 1, ?_⟩
      conv_lhs => rw [sfusible_concat hf, hk]
      rw [List.replicate_succ', ← List.append_assoc]
  | case2 c hf => exact ⟨0, by simp⟩

/-- Run contiguity. -/
theorem sheadOf_within {L : List SChain} {c p h : SChain}
    (hc : sheadOf L c = h) (hp1 : h <+: p) (hp2 : p <+: c) :
    sheadOf L p = h := by
  fun_induction sheadOf L c with
  | case1 c hf ih =>
      by_cases hpc : p = c
      · subst hpc
        rw [sheadOf_of_fusible hf]
        exact hc
      · exact ih hc (sprefix_dropLast_of_ne hp2 hpc)
  | case2 c hf =>
      subst hc
      have : p = c := hp2.eq_of_length
        (Nat.le_antisymm hp2.length_le hp1.length_le)
      subst this
      exact sheadOf_of_not_fusible (Bool.eq_false_iff.mpr hf)

/-- The members of the run headed by `h`. -/
def srunMembers (L : List SChain) (h : SChain) : List SChain :=
  (skeptL L).filter (fun c => sheadOf L c == h)

/-- The run's length. -/
def slenOf (L : List SChain) (h : SChain) : ℕ := (srunMembers L h).length

/-- The run's last member (sided T-tail's attachment site). -/
def stailOf (L : List SChain) (h : SChain) : SChain :=
  h ++ List.replicate (slenOf L h - 1) (Side.R, 1)

theorem mem_srunMembers {L : List SChain} {h c : SChain} :
    c ∈ srunMembers L h ↔ c ∈ skeptL L ∧ sheadOf L c = h := by
  simp [srunMembers, List.mem_filter]

theorem shead_mem_srunMembers {L : List SChain} {h : SChain}
    (hh : sisHead L h = true) : h ∈ srunMembers L h :=
  mem_srunMembers.mpr ⟨sisHead_kept hh, sheadOf_eq_self_of_isHead hh⟩

theorem srunMember_form {L : List SChain} {h c : SChain}
    (hc : c ∈ srunMembers L h) :
    c = h ++ List.replicate (c.length - h.length) (Side.R, 1) := by
  obtain ⟨hk, hh⟩ := mem_srunMembers.mp hc
  obtain ⟨k, hform⟩ := sheadOf_replicate L c
  rw [hh] at hform
  have : c.length - h.length = k := by
    rw [hform]; simp
  rw [this]
  exact hform

theorem sreplicate_offset_inj {h : SChain} {j k : ℕ}
    (heq : h ++ List.replicate j (Side.R, 1)
      = h ++ List.replicate k (Side.R, 1)) : j = k := by
  have := congrArg List.length heq
  simp at this
  exact this

theorem srunMember_down {L : List SChain} {h : SChain} {k : ℕ}
    (hk : h ++ List.replicate (k + 1) (Side.R, 1) ∈ srunMembers L h) :
    h ++ List.replicate k (Side.R, 1) ∈ srunMembers L h := by
  obtain ⟨hkept, hhead⟩ := mem_srunMembers.mp hk
  have hpre : h ++ List.replicate k (Side.R, 1)
      <+: h ++ List.replicate (k + 1) (Side.R, 1) := by
    rw [List.replicate_succ', ← List.append_assoc]
    exact List.prefix_append _ _
  have hh' : h ∈ skeptL L := hhead ▸ sheadOf_kept hkept
  have hne : h ++ List.replicate k (Side.R, 1) ≠ [] := by
    intro hnil
    cases h with
    | nil => exact skept_ne_nil hh' rfl
    | cons a as => simp at hnil
  refine mem_srunMembers.mpr ⟨skept_of_prefix hkept hpre hne, ?_⟩
  exact sheadOf_within hhead (List.prefix_append _ _) hpre

theorem srunMember_down_le {L : List SChain} {h : SChain} :
    ∀ k, h ++ List.replicate k (Side.R, 1) ∈ srunMembers L h →
    ∀ j ≤ k, h ++ List.replicate j (Side.R, 1) ∈ srunMembers L h := by
  intro k
  induction k with
  | zero =>
      intro hm j hj
      have : j = 0 := by omega
      subst this
      exact hm
  | succ k ih =>
      intro hm j hj
      rcases Nat.eq_or_lt_of_le hj with rfl | hlt
      · exact hm
      · exact ih (srunMember_down hm) j (by omega)

theorem srunMember_fusible {L : List SChain} {h : SChain} {k : ℕ}
    (hk : h ++ List.replicate (k + 1) (Side.R, 1) ∈ srunMembers L h) :
    sfusible L (h ++ List.replicate (k + 1) (Side.R, 1)) = true := by
  obtain ⟨hkept, hhead⟩ := mem_srunMembers.mp hk
  cases hf : sfusible L (h ++ List.replicate (k + 1) (Side.R, 1)) with
  | true => rfl
  | false =>
      exfalso
      have hself := sheadOf_of_not_fusible hf
      rw [hhead] at hself
      have hlen := congrArg List.length hself
      simp only [List.length_append, List.length_replicate] at hlen
      omega

theorem srunMember_offset_lt {L : List SChain} {h : SChain} {k : ℕ}
    (hk : h ++ List.replicate k (Side.R, 1) ∈ srunMembers L h) :
    k < slenOf L h := by
  have hall : ∀ j ≤ k, h ++ List.replicate j (Side.R, 1) ∈ srunMembers L h :=
    srunMember_down_le k hk
  set ms : List SChain :=
    (List.range (k + 1)).map (fun j => h ++ List.replicate j (Side.R, 1))
    with hms
  have hnd : ms.Nodup := by
    refine List.Nodup.map_on ?_ (List.nodup_range)
    intro j₁ _ j₂ _ heq
    exact sreplicate_offset_inj heq
  have hsub : ms ⊆ srunMembers L h := by
    intro c hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
    exact hall j (by simp at hj; omega)
  have hcard : ms.length ≤ (srunMembers L h).length :=
    (List.subperm_of_subset hnd hsub).length_le
  have : ms.length = k + 1 := by simp [hms]
  unfold slenOf
  omega

theorem slenOf_pos {L : List SChain} {h : SChain}
    (hh : sisHead L h = true) : 0 < slenOf L h := by
  have := shead_mem_srunMembers hh
  unfold slenOf
  exact List.length_pos_iff.mpr (List.ne_nil_of_mem this)

theorem srunMember_of_lt {L : List SChain} {h : SChain}
    (hh : sisHead L h = true) {k : ℕ} (hk : k < slenOf L h) :
    h ++ List.replicate k (Side.R, 1) ∈ srunMembers L h := by
  by_contra habs
  have hform : ∀ c ∈ srunMembers L h,
      c = h ++ List.replicate (c.length - h.length) (Side.R, 1) :=
    fun c hc => srunMember_form hc
  set offs : List ℕ := (srunMembers L h).map (fun c => c.length - h.length)
    with hoffs
  have hnd : offs.Nodup := by
    refine List.Nodup.map_on ?_ ((nodup_skeptL L).filter _)
    intro c₁ h₁ c₂ h₂ heq
    rw [hform c₁ h₁, hform c₂ h₂, heq]
  have hsub : offs ⊆ (List.range (slenOf L h)).erase k := by
    intro j hj
    rw [hoffs, List.mem_map] at hj
    obtain ⟨c, hc, rfl⟩ := hj
    have hmem : h ++ List.replicate (c.length - h.length) (Side.R, 1)
        ∈ srunMembers L h := (hform c hc) ▸ hc
    have hne : c.length - h.length ≠ k := fun heq => habs (heq ▸ hmem)
    rw [List.mem_erase_of_ne hne]
    exact List.mem_range.mpr (srunMember_offset_lt hmem)
  have hle := (List.subperm_of_subset hnd hsub).length_le
  rw [List.length_erase_of_mem (List.mem_range.mpr hk), List.length_range]
    at hle
  have hlen : offs.length = slenOf L h := by simp [hoffs, slenOf]
  have hpos : 0 < slenOf L h := slenOf_pos hh
  omega

theorem mem_srunMembers_iff {L : List SChain} {h : SChain}
    (hh : sisHead L h = true) {c : SChain} :
    c ∈ srunMembers L h
      ↔ ∃ k < slenOf L h, c = h ++ List.replicate k (Side.R, 1) := by
  constructor
  · intro hc
    refine ⟨c.length - h.length, ?_, srunMember_form hc⟩
    exact srunMember_offset_lt ((srunMember_form hc) ▸ hc)
  · rintro ⟨k, hk, rfl⟩
    exact srunMember_of_lt hh hk

theorem stailOf_mem {L : List SChain} {h : SChain}
    (hh : sisHead L h = true) : stailOf L h ∈ srunMembers L h :=
  srunMember_of_lt hh (by have := slenOf_pos hh; omega)

theorem stail_succ_not_fusible {L : List SChain} {h : SChain}
    (hh : sisHead L h = true) :
    sfusible L (stailOf L h ++ [(Side.R, 1)]) = false := by
  cases hf : sfusible L (stailOf L h ++ [(Side.R, 1)]) with
  | false => rfl
  | true =>
      exfalso
      have hform : stailOf L h ++ [(Side.R, 1)]
          = h ++ List.replicate (slenOf L h) (Side.R, 1) := by
        have hpos := slenOf_pos hh
        rw [stailOf, List.append_assoc, ← List.replicate_succ']
        congr 2
        omega
      have hmem : stailOf L h ++ [(Side.R, 1)] ∈ srunMembers L h := by
        refine mem_srunMembers.mpr ⟨sfusible_kept hf, ?_⟩
        rw [sheadOf_of_fusible hf, List.dropLast_concat]
        exact (mem_srunMembers.mp (stailOf_mem hh)).2
      rw [hform] at hmem
      exact absurd (srunMember_offset_lt hmem) (by omega)

/-- **Sided T-tail, consequence (a)**: a head's parent node is the tail of
the parent run. -/
theorem shead_parent_is_tail {L : List SChain} {h : SChain}
    (hh : sisHead L h = true) (hp : h.dropLast ∈ skeptL L) :
    h.dropLast = stailOf L (sheadOf L h.dropLast) := by
  set g := sheadOf L h.dropLast with hg
  have hgh : sisHead L g = true := sheadOf_isHead hp
  have hmem : h.dropLast ∈ srunMembers L g := mem_srunMembers.mpr ⟨hp, hg.symm⟩
  have hform := srunMember_form hmem
  set k := h.dropLast.length - g.length with hk
  have hklt : k < slenOf L g := srunMember_offset_lt (hform ▸ hmem)
  have hexact : k = slenOf L g - 1 := by
    by_contra hne
    have hklt' : k + 1 < slenOf L g := by omega
    have hsucc : g ++ List.replicate (k + 1) (Side.R, 1) ∈ srunMembers L g :=
      srunMember_of_lt hgh hklt'
    have hfus : sfusible L (g ++ List.replicate (k + 1) (Side.R, 1)) = true :=
      srunMember_fusible hsucc
    have hta := stail_attachment hh
    rw [hform] at hta
    rw [List.append_assoc, ← List.replicate_succ'] at hta
    rw [hfus] at hta
    exact Bool.noConfusion hta
  rw [stailOf, ← hexact]
  exact hform

theorem sfusible_live {L : List SChain} {c : SChain}
    (h : sfusible L c = true) : (c ∈ L) ↔ (c.dropLast ∈ L) := by
  simp only [sfusible, Bool.and_eq_true, beq_iff_eq] at h
  have h2 := h.2
  constructor
  · intro hm
    have : decide (c ∈ L) = true := decide_eq_true hm
    rw [this] at h2
    exact of_decide_eq_true h2.symm
  · intro hm
    have hd : decide (c.dropLast ∈ L) = true := decide_eq_true hm
    rw [hd] at h2
    exact of_decide_eq_true h2

theorem srun_liveness_uniform_aux {L : List SChain} {h : SChain} :
    ∀ k, h ++ List.replicate k (Side.R, 1) ∈ srunMembers L h →
      ((h ++ List.replicate k (Side.R, 1) ∈ L) ↔ (h ∈ L))
  | 0, _ => by simp
  | k + 1, hm => by
      have hfus := srunMember_fusible hm
      have hdrop : (h ++ List.replicate (k + 1) (Side.R, 1)).dropLast
          = h ++ List.replicate k (Side.R, 1) := by
        rw [List.replicate_succ', ← List.append_assoc, List.dropLast_concat]
      rw [sfusible_live hfus, hdrop]
      exact srun_liveness_uniform_aux k (srunMember_down hm)

/-- Uniform liveness along a sided run. -/
theorem srun_liveness_uniform {L : List SChain} {h c : SChain}
    (hc : c ∈ srunMembers L h) : (c ∈ L) ↔ (h ∈ L) := by
  have hform := srunMember_form hc
  rw [hform]
  exact srun_liveness_uniform_aux _ (hform ▸ hc)

/-! ## §6  The canonical sided head order

Short-lex over the flattened `(sideNat, delta)` word stream: parents
strictly precede children (lengths double), the tie-break is inherited
wholesale from the one-sided `hLt`, and injectivity of the flattening makes
it a strict total order. On lifted all-R chains it agrees with the one-sided
`hLt` (`shLt_liftR`, §13's order half). -/

open Sal.EmbedRGA.RunTable (hLt hLe hLt_irrefl hLt_asymm hLt_trans hLt_total
  hLe_total hLe_trans)

def sideNat : Side → ℕ
  | Side.R => 0
  | Side.L => 1

/-- Flatten a sided chain to an alternating `(sideNat, delta)` word. -/
def sflat (c : SChain) : List ℕ := c.flatMap (fun e => [sideNat e.1, e.2])

theorem sflat_length (c : SChain) : (sflat c).length = 2 * c.length := by
  induction c with
  | nil => rfl
  | cons e es ih =>
      simp only [sflat, List.flatMap_cons, List.length_append,
        List.length_cons, List.length_nil, List.length_cons] at ih ⊢
      omega

theorem sideNat_inj : ∀ {s1 s2 : Side}, sideNat s1 = sideNat s2 → s1 = s2 := by
  intro s1 s2
  cases s1 <;> cases s2 <;> simp [sideNat]

theorem sflat_inj : ∀ {c1 c2 : SChain}, sflat c1 = sflat c2 → c1 = c2
  | [], [], _ => rfl
  | [], e :: es, h => by
      simp [sflat, List.flatMap_cons] at h
  | e :: es, [], h => by
      simp [sflat, List.flatMap_cons] at h
  | (s1, d1) :: t1, (s2, d2) :: t2, h => by
      simp only [sflat, List.flatMap_cons, List.cons_append,
        List.nil_append] at h
      injection h with h1 h'
      injection h' with h2 h3
      rw [sideNat_inj h1, h2, sflat_inj h3]

/-- The canonical sided head order: short-lex over the flattened words. -/
def shLt (u v : SChain) : Bool := hLt (sflat u) (sflat v)

def shLe (u v : SChain) : Bool := !(shLt v u)

theorem shLt_irrefl (u : SChain) : shLt u u = false := hLt_irrefl _

theorem shLt_asymm {u v : SChain} (h : shLt u v = true) :
    shLt v u = false := hLt_asymm h

theorem shLt_trans {u v w : SChain} (h1 : shLt u v = true)
    (h2 : shLt v w = true) : shLt u w = true := hLt_trans h1 h2

theorem shLt_total {u v : SChain} (hne : u ≠ v) :
    shLt u v = true ∨ shLt v u = true :=
  hLt_total (fun h => hne (sflat_inj h))

theorem shLe_total (u v : SChain) : (shLe u v || shLe v u) = true :=
  hLe_total _ _

theorem shLe_trans {u v w : SChain} (h1 : shLe u v = true)
    (h2 : shLe v w = true) : shLe u w = true := hLe_trans h1 h2

theorem shLt_of_length_lt {u v : SChain} (h : u.length < v.length) :
    shLt u v = true := by
  have hlen : (sflat u).length < (sflat v).length := by
    rw [sflat_length, sflat_length]
    omega
  simp only [shLt, Sal.EmbedRGA.RunTable.hLt, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq]
  exact Or.inl hlen

/-- Strictly `shLt`-sorted lists with the same members are equal. -/
theorem shLt_sorted_ext : ∀ {l l' : List SChain},
    l.Pairwise (fun a b => shLt a b = true) →
    l'.Pairwise (fun a b => shLt a b = true) →
    (∀ c, c ∈ l ↔ c ∈ l') → l = l'
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, _, hmem => by
      exact absurd ((hmem y).mpr List.mem_cons_self) (by simp)
  | x :: xs, [], _, _, hmem => by
      exact absurd ((hmem x).mp List.mem_cons_self) (by simp)
  | x :: xs, y :: ys, hs, hs', hmem => by
      rcases List.pairwise_cons.mp hs with ⟨hx, hxs⟩
      rcases List.pairwise_cons.mp hs' with ⟨hy, hys⟩
      have hxy : x = y := by
        rcases List.mem_cons.mp ((hmem x).mp List.mem_cons_self) with h | h
        · exact h
        · rcases List.mem_cons.mp ((hmem y).mpr List.mem_cons_self)
            with h' | h'
          · exact h'.symm
          · have h1 := hy x h
            have h2 := hx y h'
            rw [shLt_asymm h1] at h2
            exact Bool.noConfusion h2
      subst hxy
      have htails : ∀ z, z ∈ xs ↔ z ∈ ys := by
        intro z
        constructor
        · intro hz
          rcases List.mem_cons.mp ((hmem z).mp (List.mem_cons_of_mem _ hz))
            with heq | h
          · rw [heq] at hz
            exact absurd (hx x hz) (by rw [shLt_irrefl]; simp)
          · exact h
        · intro hz
          rcases List.mem_cons.mp ((hmem z).mpr (List.mem_cons_of_mem _ hz))
            with heq | h
          · rw [heq] at hz
            exact absurd (hy x hz) (by rw [shLt_irrefl]; simp)
          · exact h
      rw [shLt_sorted_ext hxs hys htails]

/-! ## §7  Sided T-repr: the indexed run table and the representation iso

The sided entry stores the accounting header `(parent ref, liveness, SIDE,
head delta, length)` and NOT the chain. **Statement hygiene** as one-sided:
the iso is over **labels + sides + liveness**, NOT timestamps, post-epoch
labels are rank ordinals, so a timestamp-carrying iso would be false. The
side field is one bit per ENTRY (runs are uniformly `R`,
`sfusible_side_R`). -/

open Sal.EmbedRGA.RunTable (nodup_flatMap_of_disjoint pairwise_flatMap)

/-- The canonical enumeration of sided runs: the heads, `shLe`-sorted. -/
def sheadsList (L : List SChain) : List SChain :=
  ((skeptL L).filter (fun c => sisHead L c)).mergeSort shLe

theorem mem_sheadsList {L : List SChain} {c : SChain} :
    c ∈ sheadsList L ↔ sisHead L c = true := by
  rw [sheadsList, List.mem_mergeSort, List.mem_filter]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨sisHead_kept h, h⟩

theorem nodup_sheadsList (L : List SChain) : (sheadsList L).Nodup := by
  rw [sheadsList]
  exact (List.mergeSort_perm _ _).nodup_iff.mpr ((nodup_skeptL L).filter _)

theorem sorted_sheadsList (L : List SChain) :
    (sheadsList L).Pairwise (fun a b => shLt a b = true) := by
  have hle : (sheadsList L).Pairwise (fun a b => shLe a b = true) := by
    apply List.pairwise_mergeSort
    · intro a b c h1 h2
      exact shLe_trans h1 h2
    · intro a b
      exact shLe_total a b
  have hnd := nodup_sheadsList L
  refine (hle.and hnd).imp ?_
  rintro a b ⟨hab, hne⟩
  simp only [shLe, Bool.not_eq_true'] at hab
  rcases shLt_total hne with h | h
  · exact h
  · rw [h] at hab
    exact Bool.noConfusion hab

/-- The sided entry a head compiles to. -/
def sentryOfHead (L : List SChain) (h : SChain) : SRTEntry :=
  { par := if h.dropLast ∈ skeptL L
      then some ((sheadsList L).idxOf (sheadOf L h.dropLast),
                 h.dropLast.length - (sheadOf L h.dropLast).length)
      else none,
    live := decide (h ∈ L),
    side := (h.getLastD (Side.R, 0)).1,
    delta := (h.getLastD (Side.R, 0)).2,
    len := slenOf L h }

/-- The canonical sided run table of a state. -/
def sTableOf (L : List SChain) : STable :=
  (sheadsList L).map (sentryOfHead L)

/-- Recover an entry's head chain from the already-recovered earlier heads. -/
def sentryHead (heads : List SChain) (e : SRTEntry) : SChain :=
  match e.par with
  | none => [(e.side, e.delta)]
  | some (i, off) =>
      (heads.getD i []) ++ List.replicate off (Side.R, 1)
        ++ [(e.side, e.delta)]

/-- All entry head chains, recovered left to right. -/
def sheadsOf (T : STable) : List SChain :=
  T.foldl (fun acc e => acc ++ [sentryHead acc e]) []

/-- The abstraction: the live sided chains stored in the table. -/
def sStateOf (T : STable) : List SChain :=
  ((sheadsOf T).zip T).flatMap (fun p =>
    if p.2.live
    then (List.range p.2.len).map
      (fun k => p.1 ++ List.replicate k (Side.R, 1))
    else [])

theorem sheadsOf_append (T : STable) (S : STable) :
    sheadsOf (T ++ S) = S.foldl (fun acc e => acc ++ [sentryHead acc e])
      (sheadsOf T) := by
  rw [sheadsOf, List.foldl_append]
  rfl

theorem sheadsOf_snoc (T : STable) (e : SRTEntry) :
    sheadsOf (T ++ [e]) = sheadsOf T ++ [sentryHead (sheadsOf T) e] := by
  rw [sheadsOf_append]
  rfl

theorem sheadsOf_length (T : STable) : (sheadsOf T).length = T.length := by
  induction T using List.reverseRecOn with
  | nil => rfl
  | append_singleton T e ih => rw [sheadsOf_snoc]; simp [ih]

theorem sidxOf_lt_of_shLt {l : List SChain}
    (hsort : l.Pairwise (fun a b => shLt a b = true)) {a b : SChain}
    (ha : a ∈ l) (hb : b ∈ l) (hab : shLt a b = true) :
    l.idxOf a < l.idxOf b := by
  have hia : l.idxOf a < l.length := List.idxOf_lt_length_of_mem ha
  have hib : l.idxOf b < l.length := List.idxOf_lt_length_of_mem hb
  have hga : l[l.idxOf a] = a := List.getElem_idxOf hia
  have hgb : l[l.idxOf b] = b := List.getElem_idxOf hib
  rcases Nat.lt_trichotomy (l.idxOf a) (l.idxOf b) with h | h | h
  · exact h
  · exfalso
    have : a = b := (List.idxOf_inj ha).mp h
    subst this
    rw [shLt_irrefl] at hab
    exact Bool.noConfusion hab
  · exfalso
    have := List.pairwise_iff_getElem.mp hsort _ _ hib hia h
    rw [hga, hgb] at this
    rw [shLt_asymm this] at hab
    exact Bool.noConfusion hab

theorem sidxOf_getElem_nodup {l : List SChain} (hnd : l.Nodup)
    {i : ℕ} (hi : i < l.length) : l.idxOf l[i] = i := by
  have hm : l[i] ∈ l := List.getElem_mem hi
  have hlt : l.idxOf l[i] < l.length := List.idxOf_lt_length_of_mem hm
  have hg : l[l.idxOf l[i]] = l[i] := List.getElem_idxOf hlt
  exact (List.Nodup.getElem_inj_iff hnd).mp hg

theorem shead_root_singleton {L : List SChain} {h : SChain}
    (hh : sisHead L h = true) (hp : h.dropLast ∉ skeptL L) :
    ∃ e : SEntry, h = [e] := by
  rcases List.eq_nil_or_concat h with rfl | ⟨p, b, rfl⟩
  · exact absurd rfl (skept_ne_nil (sisHead_kept hh))
  · simp only [List.concat_eq_append] at *
    cases p with
    | nil => exact ⟨b, rfl⟩
    | cons a as =>
        exfalso
        apply hp
        rw [List.dropLast_concat]
        exact skept_of_prefix (sisHead_kept hh) (List.prefix_append _ _)
          (by simp)

/-- **The sided recovery step**: compiling a head and recovering it from the
earlier recovered heads round-trips. -/
theorem sentryHead_sentryOfHead {L : List SChain} {n : ℕ}
    (hn : n < (sheadsList L).length) :
    sentryHead ((sheadsList L).take n) (sentryOfHead L (sheadsList L)[n])
      = (sheadsList L)[n] := by
  set h := (sheadsList L)[n] with hh_def
  have hh : sisHead L h = true :=
    mem_sheadsList.mp (List.getElem_mem hn)
  have hne : h ≠ [] := skept_ne_nil (sisHead_kept hh)
  by_cases hp : h.dropLast ∈ skeptL L
  · set g := sheadOf L h.dropLast with hg_def
    have hgh : sisHead L g = true := sheadOf_isHead hp
    have hgm : g ∈ sheadsList L := mem_sheadsList.mpr hgh
    have hglt : shLt g h = true := by
      have h1 : g.length ≤ h.dropLast.length := (sheadOf_prefix L _).length_le
      have h2 : h.dropLast.length < h.length := by
        rw [List.length_dropLast]
        have : 0 < h.length := List.length_pos_iff.mpr hne
        omega
      exact shLt_of_length_lt (by omega)
    have hidx : (sheadsList L).idxOf g < n := by
      have := sidxOf_lt_of_shLt (sorted_sheadsList L) hgm
        (List.getElem_mem hn) hglt
      rwa [← hh_def, sidxOf_getElem_nodup (nodup_sheadsList L) hn] at this
    have hidxlen : (sheadsList L).idxOf g < (sheadsList L).length :=
      List.idxOf_lt_length_of_mem hgm
    have hgetD : ((sheadsList L).take n).getD ((sheadsList L).idxOf g) []
        = g := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hidx,
        List.getElem?_eq_getElem hidxlen]
      simp [List.getElem_idxOf]
    have hpar_form : g ++ List.replicate
        (h.dropLast.length - g.length) (Side.R, 1) = h.dropLast :=
      (srunMember_form (mem_srunMembers.mpr ⟨hp, hg_def.symm⟩)).symm
    have hentry : sentryOfHead L h =
        { par := some ((sheadsList L).idxOf g,
                       h.dropLast.length - g.length),
          live := decide (h ∈ L),
          side := (h.getLastD (Side.R, 0)).1,
          delta := (h.getLastD (Side.R, 0)).2,
          len := slenOf L h } := by
      rw [sentryOfHead]
      simp only [if_pos hp, ← hg_def]
    rw [hentry]
    simp only [sentryHead]
    rw [hgetD, hpar_form]
    obtain ⟨p, b, hpb⟩ : ∃ p b, h = p ++ [b] := by
      rcases List.eq_nil_or_concat h with hnil | ⟨p, b, hpb⟩
      · exact absurd hnil hne
      · exact ⟨p, b, by simpa using hpb⟩
    rw [hpb, List.dropLast_concat, List.getLastD_concat]
  · obtain ⟨e, he⟩ := shead_root_singleton hh hp
    have hentry : sentryOfHead L h =
        { par := none, live := decide (h ∈ L),
          side := (h.getLastD (Side.R, 0)).1,
          delta := (h.getLastD (Side.R, 0)).2,
          len := slenOf L h } := by
      rw [sentryOfHead]
      simp only [if_neg hp]
    rw [hentry]
    simp only [sentryHead]
    rw [he]
    rfl

/-- **Sided head recovery**: the fold over the canonical table recovers the
canonical head enumeration. -/
theorem sheadsOf_sTableOf (L : List SChain) :
    sheadsOf (sTableOf L) = sheadsList L := by
  have hlen : (sTableOf L).length = (sheadsList L).length := by
    simp [sTableOf]
  suffices h : ∀ n, sheadsOf ((sTableOf L).take n) = (sheadsList L).take n by
    have := h (sTableOf L).length
    rwa [List.take_length, hlen, List.take_length] at this
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      by_cases hlt : n < (sheadsList L).length
      · have hlt' : n < (sTableOf L).length := by omega
        rw [List.take_succ, List.take_succ,
            List.getElem?_eq_getElem hlt', List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some]
        rw [sheadsOf_snoc, ih]
        congr 1
        rw [show (sTableOf L)[n] = sentryOfHead L ((sheadsList L)[n]) from by
          simp [sTableOf]]
        rw [sentryHead_sentryOfHead hlt]
      · rw [List.take_succ, List.take_succ,
            List.getElem?_eq_none (by omega),
            List.getElem?_eq_none (by omega)]
        simp [ih]

theorem sStateOf_sTableOf_eq (L : List SChain) :
    sStateOf (sTableOf L)
      = (sheadsList L).flatMap (fun h =>
          if decide (h ∈ L) = true
          then (List.range (slenOf L h)).map
            (fun k => h ++ List.replicate k (Side.R, 1))
          else []) := by
  have zip_map_self : ∀ {α β : Type} (f : α → β) (l : List α),
      l.zip (l.map f) = l.map (fun a => (a, f a)) := by
    intro α β f l
    induction l with
    | nil => rfl
    | cons a l ih => simp [ih]
  rw [sStateOf, sheadsOf_sTableOf, sTableOf, zip_map_self, List.flatMap_map]
  simp [sentryOfHead, Function.comp]

/-- **Sided T-repr, losslessness (`sStateOf ∘ sTableOf = id`)**: the exact
live sided-chain set is recovered from headers alone, labels, sides and
liveness; no timestamps. -/
theorem sStateOf_sTableOf (L : List SChain) (hnil : [] ∉ L) :
    (sStateOf (sTableOf L)).Nodup
      ∧ (∀ c, c ∈ sStateOf (sTableOf L) ↔ c ∈ L) := by
  rw [sStateOf_sTableOf_eq]
  constructor
  · refine nodup_flatMap_of_disjoint (nodup_sheadsList L) ?_ ?_
    · intro h hm
      by_cases hl : decide (h ∈ L) = true
      · rw [if_pos hl]
        refine List.Nodup.map_on ?_ List.nodup_range
        intro j₁ _ j₂ _ heq
        exact sreplicate_offset_inj heq
      · rw [if_neg hl]
        exact List.nodup_nil
    · intro h hm h' hm' hne b hb hb'
      by_cases hl : decide (h ∈ L) = true
      · by_cases hl' : decide (h' ∈ L) = true
        · rw [if_pos hl] at hb
          rw [if_pos hl'] at hb'
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
          obtain ⟨k', hk', heq⟩ := List.mem_map.mp hb'
          rw [List.mem_range] at hk hk'
          have hmem : h ++ List.replicate k (Side.R, 1)
              ∈ srunMembers L h :=
            srunMember_of_lt (mem_sheadsList.mp hm) hk
          have hmem' : h' ++ List.replicate k' (Side.R, 1)
              ∈ srunMembers L h' :=
            srunMember_of_lt (mem_sheadsList.mp hm') hk'
          rw [heq] at hmem'
          exact hne ((mem_srunMembers.mp hmem).2.symm.trans
            (mem_srunMembers.mp hmem').2)
        · rw [if_neg hl'] at hb'
          simp at hb'
      · rw [if_neg hl] at hb
        simp at hb
  · intro c
    rw [List.mem_flatMap]
    constructor
    · rintro ⟨h, hm, hc⟩
      by_cases hl : decide (h ∈ L) = true
      · rw [if_pos hl] at hc
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
        rw [List.mem_range] at hk
        have hmem : h ++ List.replicate k (Side.R, 1) ∈ srunMembers L h :=
          srunMember_of_lt (mem_sheadsList.mp hm) hk
        exact (srun_liveness_uniform hmem).mpr (of_decide_eq_true hl)
      · rw [if_neg hl] at hc
        simp at hc
    · intro hc
      have hne : c ≠ [] := fun h => hnil (h ▸ hc)
      have hkept : c ∈ skeptL L := skept_of_live hc hne
      have hmem : c ∈ srunMembers L (sheadOf L c) :=
        mem_srunMembers.mpr ⟨hkept, rfl⟩
      refine ⟨sheadOf L c, mem_sheadsList.mpr (sheadOf_isHead hkept), ?_⟩
      have hlive : sheadOf L c ∈ L := (srun_liveness_uniform hmem).mp hc
      rw [if_pos (decide_eq_true hlive)]
      refine List.mem_map.mpr ⟨c.length - (sheadOf L c).length, ?_,
        (srunMember_form hmem).symm⟩
      rw [List.mem_range]
      exact srunMember_offset_lt ((srunMember_form hmem) ▸ hmem)

/-! ### Sided canonicity: the other direction of the iso -/

/-- Canonical sided tables: maximal fusible chains (`no_fuse`, now carrying
the SIDE condition, only an `R`, delta-1, same-liveness lone attachment
would have been coalesced), tail attachment, kept leaves live, backward
parent refs, canonical `shLt` order. -/
structure SCanonical (T : STable) : Prop where
  len_pos : ∀ e ∈ T, 1 ≤ e.len
  par_back : ∀ i (hi : i < T.length) p, T[i].par = some p → p.1 < i
  par_tail : ∀ i (hi : i < T.length) p, T[i].par = some p →
    ∀ (hj : p.1 < T.length), p.2 = T[p.1].len - 1
  no_fuse : ∀ i (hi : i < T.length) p, T[i].par = some p →
    ∀ (hj : p.1 < T.length), T[i].delta = 1 → T[i].side = Side.R →
    T[i].live = T[p.1].live →
    ∃ i', ∃ (_ : i' < T.length), i' ≠ i ∧ T[i'].par = some p
  leaves_live : ∀ i (hi : i < T.length), T[i].live = false →
    ∃ i', ∃ (_ : i' < T.length), ∃ off, T[i'].par = some (i, off)
  sorted : (sheadsOf T).Pairwise (fun a b => shLt a b = true)

theorem sheadsOf_prefix_append (T S : STable) :
    sheadsOf T <+: sheadsOf (T ++ S) := by
  induction S using List.reverseRecOn with
  | nil => simp
  | append_singleton S e ih =>
      rw [← List.append_assoc, sheadsOf_snoc]
      exact ih.trans (List.prefix_append _ _)

theorem sheadsOf_take (T : STable) (n : ℕ) :
    sheadsOf (T.take n) = (sheadsOf T).take n := by
  have h1 : sheadsOf (T.take n) <+: sheadsOf T := by
    conv_rhs => rw [← List.take_append_drop n T]
    exact sheadsOf_prefix_append _ _
  have h2 : (sheadsOf T).take n <+: sheadsOf T := List.take_prefix _ _
  have hlen : (sheadsOf (T.take n)).length
      = ((sheadsOf T).take n).length := by
    rw [sheadsOf_length, List.length_take, List.length_take, sheadsOf_length]
  exact (List.prefix_of_prefix_length_le h1 h2 (le_of_eq hlen)).eq_of_length
    hlen

theorem sheadsOf_getElem (T : STable) (i : ℕ) (hi : i < T.length) :
    (sheadsOf T)[i]'(by rw [sheadsOf_length]; exact hi)
      = sentryHead ((sheadsOf T).take i) T[i] := by
  have htake : T.take (i + 1) = T.take i ++ [T[i]] := by
    rw [List.take_succ, List.getElem?_eq_getElem hi]
    rfl
  have h1 : (sheadsOf T).take (i + 1)
      = (sheadsOf T).take i
        ++ [sentryHead ((sheadsOf T).take i) T[i]] := by
    rw [← sheadsOf_take, htake, sheadsOf_snoc, sheadsOf_take]
  have h2 : (sheadsOf T).take (i + 1)
      = (sheadsOf T).take i
        ++ [(sheadsOf T)[i]'(by rw [sheadsOf_length]; exact hi)] := by
    rw [List.take_succ, List.getElem?_eq_getElem]
    rfl
  have := h1.symm.trans h2
  have := List.append_cancel_left this
  injection this with h _
  exact h.symm

theorem sheadsOf_getElem_some {T : STable} {i : ℕ} (hi : i < T.length)
    {p : ℕ × ℕ} (hp : T[i].par = some p) (hlt : p.1 < i) :
    (sheadsOf T)[i]'(by rw [sheadsOf_length]; exact hi)
      = ((sheadsOf T)[p.1]'(by rw [sheadsOf_length]; omega))
        ++ List.replicate p.2 (Side.R, 1) ++ [(T[i].side, T[i].delta)] := by
  obtain ⟨p1, p2⟩ := p
  rw [sheadsOf_getElem T i hi, sentryHead, hp]
  simp only []
  have hp1 : p1 < (sheadsOf T).length := by rw [sheadsOf_length]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hlt,
    List.getElem?_eq_getElem hp1]
  rfl

theorem sheadsOf_getElem_none {T : STable} {i : ℕ} (hi : i < T.length)
    (hp : T[i].par = none) :
    (sheadsOf T)[i]'(by rw [sheadsOf_length]; exact hi)
      = [(T[i].side, T[i].delta)] := by
  rw [sheadsOf_getElem T i hi, sentryHead, hp]

theorem sheadsOf_getElem_ne_nil {T : STable} {i : ℕ} (hi : i < T.length)
    (hback : ∀ p, T[i].par = some p → p.1 < i) :
    (sheadsOf T)[i]'(by rw [sheadsOf_length]; exact hi) ≠ [] := by
  cases hp : T[i].par with
  | none => rw [sheadsOf_getElem_none hi hp]; simp
  | some p => rw [sheadsOf_getElem_some hi hp (hback p hp)]; simp

/-- Recovered head of entry `i`, total form. -/
def shsAt (T : STable) (i : ℕ) : SChain := (sheadsOf T).getD i []

theorem shsAt_eq_getElem {T : STable} {i : ℕ} (hi : i < T.length) :
    shsAt T i = (sheadsOf T)[i]'(by rw [sheadsOf_length]; exact hi) := by
  rw [shsAt, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [sheadsOf_length]; exact hi)]
  rfl

theorem shsAt_some {T : STable} {i : ℕ} (hi : i < T.length)
    {p : ℕ × ℕ} (hp : T[i].par = some p) (hlt : p.1 < i) :
    shsAt T i = shsAt T p.1 ++ List.replicate p.2 (Side.R, 1)
      ++ [(T[i].side, T[i].delta)] := by
  rw [shsAt_eq_getElem hi, shsAt_eq_getElem (by omega : p.1 < T.length)]
  exact sheadsOf_getElem_some hi hp hlt

theorem shsAt_none {T : STable} {i : ℕ} (hi : i < T.length)
    (hp : T[i].par = none) : shsAt T i = [(T[i].side, T[i].delta)] := by
  rw [shsAt_eq_getElem hi]
  exact sheadsOf_getElem_none hi hp

theorem shsAt_ne_nil {T : STable} (hC : SCanonical T) {i : ℕ}
    (hi : i < T.length) : shsAt T i ≠ [] := by
  rw [shsAt_eq_getElem hi]
  exact sheadsOf_getElem_ne_nil hi (fun p hp => hC.par_back i hi p hp)

theorem sheadsOf_nodup {T : STable} (hC : SCanonical T) :
    (sheadsOf T).Nodup :=
  hC.sorted.imp (fun {a b} hab heq => by
    subst heq
    rw [shLt_irrefl] at hab
    exact Bool.noConfusion hab)

theorem shsAt_inj {T : STable} (hC : SCanonical T) {i j : ℕ}
    (hi : i < T.length) (hj : j < T.length) (heq : shsAt T i = shsAt T j) :
    i = j := by
  rw [shsAt_eq_getElem hi, shsAt_eq_getElem hj] at heq
  exact (List.Nodup.getElem_inj_iff (sheadsOf_nodup hC)).mp heq

theorem stake_append_replicate {h : SChain} {r k : ℕ} (hrk : r ≤ k) :
    (h ++ List.replicate k (Side.R, 1)).take (h.length + r)
      = h ++ List.replicate r (Side.R, 1) := by
  rw [List.take_append, List.take_of_length_le (by omega)]
  congr 1
  rw [show h.length + r - h.length = r by omega, List.take_replicate]
  congr 1
  omega

theorem sdropLast_append_replicate_succ {h : SChain} {r : ℕ} :
    (h ++ List.replicate (r + 1) (Side.R, 1)).dropLast
      = h ++ List.replicate r (Side.R, 1) := by
  rw [List.replicate_succ', ← List.append_assoc, List.dropLast_concat]

theorem sgetLastD_append_replicate_succ {h : SChain} {r : ℕ} :
    (h ++ List.replicate (r + 1) (Side.R, 1)).getLastD (Side.R, 0)
      = (Side.R, 1) := by
  rw [List.replicate_succ', ← List.append_assoc, List.getLastD_concat]

theorem sgetLastD_append_replicate_pos {h : SChain} {r : ℕ} (hr : 1 ≤ r) :
    (h ++ List.replicate r (Side.R, 1)).getLastD (Side.R, 0)
      = (Side.R, 1) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  exact sgetLastD_append_replicate_succ

theorem sdropLast_append_replicate_pos {h : SChain} {r : ℕ} (hr : 1 ≤ r) :
    (h ++ List.replicate r (Side.R, 1)).dropLast
      = h ++ List.replicate (r - 1) (Side.R, 1) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [sdropLast_append_replicate_succ]
  simp

/-- **Sided member-chain uniqueness**: the engine of canonicity, killed in
the overlap case by tail attachment exactly as one-sided. -/
theorem smemChain_inj {T : STable} (hC : SCanonical T) :
    ∀ n (c : SChain), c.length ≤ n →
    ∀ i (_ : i < T.length) k (_ : k < T[i].len)
      (_ : c = shsAt T i ++ List.replicate k (Side.R, 1))
      j (_ : j < T.length) m (_ : m < T[j].len)
      (_ : c = shsAt T j ++ List.replicate m (Side.R, 1)),
    i = j ∧ k = m := by
  intro n
  induction n with
  | zero =>
      intro c hc i hi k hk hci j hj m hm hcj
      exfalso
      apply shsAt_ne_nil hC hi
      have : c = [] := List.length_eq_zero_iff.mp (by omega)
      rw [this] at hci
      cases hs : shsAt T i with
      | nil => rfl
      | cons a as => rw [hs] at hci; simp at hci
  | succ n ih =>
      intro c hc i hi k hk hci j hj m hm hcj
      have step : ∀ i' (_ : i' < T.length) k' (_ : k' < T[i'].len)
          (_ : c = shsAt T i' ++ List.replicate k' (Side.R, 1))
          j' (_ : j' < T.length) m' (_ : m' < T[j'].len)
          (_ : c = shsAt T j' ++ List.replicate m' (Side.R, 1)),
          (shsAt T i').length < (shsAt T j').length → False := by
        intro i' hi' k' hk' hci' j' hj' m' hm' hcj' hlen
        set r := (shsAt T j').length - (shsAt T i').length with hr
        have hr1 : 1 ≤ r := by omega
        have hclen : c.length = (shsAt T i').length + k' := by
          rw [hci']; simp
        have hrk : r ≤ k' := by
          have : (shsAt T j').length ≤ c.length := by
            rw [hcj']; simp
          omega
        have hjform : shsAt T j'
            = shsAt T i' ++ List.replicate r (Side.R, 1) := by
          have h1 : shsAt T j' = c.take (shsAt T j').length := by
            rw [hcj', List.take_append,
              List.take_of_length_le (by omega),
              show (shsAt T j').length - (shsAt T j').length = 0 by omega]
            simp
          rw [h1, hci', show (shsAt T j').length = (shsAt T i').length + r
            by omega]
          exact stake_append_replicate hrk
        cases hp : T[j'].par with
        | none =>
            have := shsAt_none hj' hp
            rw [this] at hjform
            have hlen1 := congrArg List.length hjform
            simp at hlen1
            have : shsAt T i' ≠ [] := shsAt_ne_nil hC hi'
            have : 1 ≤ (shsAt T i').length :=
              List.length_pos_iff.mpr this
            omega
        | some p =>
            have hpb : p.1 < j' := hC.par_back j' hj' p hp
            have hpl : p.1 < T.length := by omega
            have hjs : shsAt T j'
                = shsAt T p.1 ++ List.replicate p.2 (Side.R, 1)
                  ++ [(T[j'].side, T[j'].delta)] :=
              shsAt_some hj' hp hpb
            have hq : shsAt T i' ++ List.replicate (r - 1) (Side.R, 1)
                = shsAt T p.1 ++ List.replicate p.2 (Side.R, 1) := by
              have h1 : (shsAt T j').dropLast
                  = shsAt T i' ++ List.replicate (r - 1) (Side.R, 1) := by
                rw [hjform]
                exact sdropLast_append_replicate_pos hr1
              have h2 : (shsAt T j').dropLast
                  = shsAt T p.1 ++ List.replicate p.2 (Side.R, 1) := by
                rw [hjs, List.dropLast_concat]
              rw [← h1, h2]
            have hp2 : p.2 = T[p.1].len - 1 := hC.par_tail j' hj' p hp hpl
            have hplen : 1 ≤ T[p.1].len :=
              hC.len_pos _ (List.getElem_mem hpl)
            have hqlen : (shsAt T i'
                ++ List.replicate (r - 1) (Side.R, 1)).length ≤ n := by
              have : 1 ≤ (shsAt T i').length :=
                List.length_pos_iff.mpr (shsAt_ne_nil hC hi')
              simp only [List.length_append, List.length_replicate]
              omega
            have := ih (shsAt T i' ++ List.replicate (r - 1) (Side.R, 1))
              hqlen i' hi' (r - 1) (by omega) rfl
              p.1 hpl p.2 (by omega) hq
            obtain ⟨hip, hrp⟩ := this
            subst hip
            omega
      rcases Nat.lt_trichotomy (shsAt T i).length (shsAt T j).length
        with hlen | hlen | hlen
      · exact absurd (step i hi k hk hci j hj m hm hcj hlen) (fun h => h)
      · have hheads : shsAt T i = shsAt T j := by
          have h1 : shsAt T i = c.take (shsAt T i).length := by
            rw [hci, List.take_append,
              List.take_of_length_le (le_refl _)]
            simp
          have h2 : shsAt T j = c.take (shsAt T j).length := by
            rw [hcj, List.take_append,
              List.take_of_length_le (le_refl _)]
            simp
          rw [h1, h2, hlen]
        have hij : i = j := shsAt_inj hC hi hj hheads
        subst hij
        rw [hci, hheads] at hcj
        exact ⟨rfl, sreplicate_offset_inj hcj⟩
      · exact absurd (step j hj m hm hcj i hi k hk hci hlen) (fun h => h)

theorem mem_sStateOf {T : STable} {c : SChain} :
    c ∈ sStateOf T ↔ ∃ i, ∃ (_ : i < T.length), ∃ k, k < T[i].len ∧
      T[i].live = true
      ∧ c = shsAt T i ++ List.replicate k (Side.R, 1) := by
  rw [sStateOf, List.mem_flatMap]
  constructor
  · rintro ⟨⟨h, e⟩, hmem, hc⟩
    obtain ⟨i, hi, hpair⟩ := List.mem_iff_getElem.mp hmem
    have hilen : i < T.length := by
      have := hi
      simp only [List.length_zip, sheadsOf_length] at this
      omega
    rw [List.getElem_zip] at hpair
    injection hpair with hph hpe
    by_cases hl : e.live = true
    · rw [if_pos hl] at hc
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
      rw [List.mem_range] at hk
      refine ⟨i, hilen, k, ?_, ?_, ?_⟩
      · rw [hpe]; exact hk
      · rw [hpe]; exact hl
      · rw [shsAt_eq_getElem hilen, ← hph]
    · rw [if_neg hl] at hc
      simp at hc
  · rintro ⟨i, hi, k, hk, hlive, rfl⟩
    refine ⟨((sheadsOf T)[i]'(by rw [sheadsOf_length]; exact hi), T[i]),
      ?_, ?_⟩
    · exact List.mem_iff_getElem.mpr ⟨i,
        by simp [List.length_zip, sheadsOf_length]; omega,
        by rw [List.getElem_zip]⟩
    · rw [if_pos hlive]
      refine List.mem_map.mpr ⟨k, List.mem_range.mpr hk, ?_⟩
      rw [shsAt_eq_getElem hi]

theorem smemChain_extends_live {T : STable} (hC : SCanonical T) :
    ∀ d i (hi : i < T.length), T.length - i ≤ d →
    ∀ k, k < T[i].len →
    ∃ l ∈ sStateOf T, shsAt T i ++ List.replicate k (Side.R, 1) <+: l := by
  intro d
  induction d with
  | zero => intro i hi hd; omega
  | succ d ih =>
      intro i hi hd k hk
      cases hlive : T[i].live with
      | true =>
          exact ⟨shsAt T i ++ List.replicate k (Side.R, 1),
            mem_sStateOf.mpr ⟨i, hi, k, hk, hlive, rfl⟩,
            List.prefix_refl _⟩
      | false =>
          obtain ⟨i', hi', off, hpar⟩ := hC.leaves_live i hi hlive
          have hlt : i < i' := hC.par_back i' hi' (i, off) hpar
          have hoff : off = T[i].len - 1 :=
            hC.par_tail i' hi' (i, off) hpar hi
          have hform : shsAt T i' = shsAt T i
              ++ List.replicate off (Side.R, 1)
              ++ [(T[i'].side, T[i'].delta)] := shsAt_some hi' hpar hlt
          obtain ⟨l, hl, hpre⟩ := ih i' hi' (by omega) 0
            (hC.len_pos _ (List.getElem_mem hi'))
          refine ⟨l, hl, ?_⟩
          have h1 : shsAt T i ++ List.replicate k (Side.R, 1)
              <+: shsAt T i ++ List.replicate off (Side.R, 1) := by
            have : List.replicate off (Side.R, 1)
                = List.replicate k (Side.R, 1)
                  ++ List.replicate (off - k) (Side.R, 1) := by
              rw [← List.replicate_add]
              congr 1
              omega
            rw [this, ← List.append_assoc]
            exact List.prefix_append _ _
          have h2 : shsAt T i ++ List.replicate off (Side.R, 1)
              <+: shsAt T i' := by
            rw [hform]
            exact List.prefix_append _ _
          have h3 : shsAt T i' <+: shsAt T i'
              ++ List.replicate 0 (Side.R, 1) := by simp
          exact ((h1.trans h2).trans h3).trans hpre

theorem sprefix_memChain {T : STable} (hC : SCanonical T) :
    ∀ i (hi : i < T.length) k (hk : k < T[i].len) (c : SChain),
      c <+: shsAt T i ++ List.replicate k (Side.R, 1) → c ≠ [] →
      ∃ j, ∃ (_ : j < T.length), ∃ m, m < T[j].len ∧
        c = shsAt T j ++ List.replicate m (Side.R, 1) := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
      intro hi k hk c hpre hne
      rcases Nat.lt_trichotomy c.length (shsAt T i).length
        with hlen | hlen | hlen
      · have hpre' : c <+: shsAt T i := by
          refine List.prefix_of_prefix_length_le hpre
            (List.prefix_append _ _) ?_
          omega
        cases hp : T[i].par with
        | none =>
            exfalso
            have hform := shsAt_none hi hp
            rw [hform] at hlen
            simp only [List.length_cons, List.length_nil] at hlen
            have : 1 ≤ c.length := List.length_pos_iff.mpr hne
            omega
        | some p =>
            have hpb : p.1 < i := hC.par_back i hi p hp
            have hpl : p.1 < T.length := by omega
            have hform : shsAt T i
                = shsAt T p.1 ++ List.replicate p.2 (Side.R, 1)
                  ++ [(T[i].side, T[i].delta)] :=
              shsAt_some hi hp hpb
            have hp2 : p.2 = T[p.1].len - 1 := hC.par_tail i hi p hp hpl
            have hlenpos : 1 ≤ T[p.1].len :=
              hC.len_pos _ (List.getElem_mem hpl)
            have hcd : c <+: shsAt T p.1
                ++ List.replicate p.2 (Side.R, 1) := by
              have := sprefix_dropLast_of_ne hpre'
                (fun heq => by rw [heq] at hlen; omega)
              rwa [hform, List.dropLast_concat] at this
            exact ih p.1 hpb hpl p.2 (by omega) c hcd hne
      · have : c = shsAt T i :=
          (List.prefix_of_prefix_length_le hpre (List.prefix_append _ _)
            (by omega)).eq_of_length hlen
        exact ⟨i, hi, 0, by
          have := hC.len_pos _ (List.getElem_mem hi)
          omega, by simpa using this⟩
      · have hclen : c.length ≤ (shsAt T i).length + k := by
          have := hpre.length_le
          simpa using this
        set m := c.length - (shsAt T i).length with hm
        have hmk : m ≤ k := by omega
        have hcform : c = shsAt T i ++ List.replicate m (Side.R, 1) := by
          have h1 : c = (shsAt T i
              ++ List.replicate k (Side.R, 1)).take c.length :=
            List.prefix_iff_eq_take.mp hpre
          rw [h1, show c.length = (shsAt T i).length + m by omega]
          exact stake_append_replicate hmk
        exact ⟨i, hi, m, by omega, hcform⟩

theorem skept_sStateOf_iff {T : STable} (hC : SCanonical T) {c : SChain} :
    c ∈ skeptL (sStateOf T)
      ↔ ∃ i, ∃ (_ : i < T.length), ∃ k, k < T[i].len ∧
        c = shsAt T i ++ List.replicate k (Side.R, 1) := by
  constructor
  · intro hc
    obtain ⟨hne, l, hl, hpre⟩ := mem_skeptL.mp hc
    obtain ⟨j, hj, m, hm, hlive, rfl⟩ := mem_sStateOf.mp hl
    obtain ⟨j', hj', m', hm', hform⟩ :=
      sprefix_memChain hC j hj m hm c hpre hne
    exact ⟨j', hj', m', hm', hform⟩
  · rintro ⟨i, hi, k, hk, rfl⟩
    obtain ⟨l, hl, hpre⟩ := smemChain_extends_live hC T.length i hi
      (by omega) k hk
    refine mem_skeptL.mpr ⟨?_, l, hl, hpre⟩
    intro hnil
    exact shsAt_ne_nil hC hi (by
      cases hs : shsAt T i with
      | nil => rfl
      | cons a as => rw [hs] at hnil; simp at hnil)

theorem smemChain_inj' {T : STable} (hC : SCanonical T) {i j k m : ℕ}
    (hi : i < T.length) (hk : k < T[i].len)
    (hj : j < T.length) (hm : m < T[j].len)
    (heq : shsAt T i ++ List.replicate k (Side.R, 1)
      = shsAt T j ++ List.replicate m (Side.R, 1)) :
    i = j ∧ k = m :=
  smemChain_inj hC (shsAt T i ++ List.replicate k (Side.R, 1)).length _
    (le_refl _) i hi k hk rfl j hj m hm heq

theorem smemChain_live_iff {T : STable} (hC : SCanonical T) {i k : ℕ}
    (hi : i < T.length) (hk : k < T[i].len) :
    (shsAt T i ++ List.replicate k (Side.R, 1) ∈ sStateOf T)
      ↔ T[i].live = true := by
  constructor
  · intro hmem
    obtain ⟨j, hj, m, hm, hlive, heq⟩ := mem_sStateOf.mp hmem
    obtain ⟨rfl, -⟩ := smemChain_inj' hC hi hk hj hm heq
    exact hlive
  · intro hlive
    exact mem_sStateOf.mpr ⟨i, hi, k, hk, hlive, rfl⟩

theorem smemChain_fusible {T : STable} (hC : SCanonical T) {i k : ℕ}
    (hi : i < T.length) (hk1 : k + 1 < T[i].len) :
    sfusible (sStateOf T)
      (shsAt T i ++ List.replicate (k + 1) (Side.R, 1)) = true := by
  have hdrop : (shsAt T i ++ List.replicate (k + 1) (Side.R, 1)).dropLast
      = shsAt T i ++ List.replicate k (Side.R, 1) :=
    sdropLast_append_replicate_succ
  have hkept : shsAt T i ++ List.replicate (k + 1) (Side.R, 1)
      ∈ skeptL (sStateOf T) :=
    (skept_sStateOf_iff hC).mpr ⟨i, hi, k + 1, hk1, rfl⟩
  have hdkept : shsAt T i ++ List.replicate k (Side.R, 1)
      ∈ skeptL (sStateOf T) :=
    (skept_sStateOf_iff hC).mpr ⟨i, hi, k, by omega, rfl⟩
  have huniq : ∀ c' ∈ skeptL (sStateOf T),
      c'.dropLast
        = (shsAt T i ++ List.replicate (k + 1) (Side.R, 1)).dropLast →
      c' = shsAt T i ++ List.replicate (k + 1) (Side.R, 1) := by
    intro c' hc' hd
    rw [hdrop] at hd
    obtain ⟨j, hj, m, hm, rfl⟩ := (skept_sStateOf_iff hC).mp hc'
    cases m with
    | zero =>
        exfalso
        simp only [List.replicate_zero, List.append_nil] at hd ⊢
        cases hp : T[j].par with
        | none =>
            have := shsAt_none hj hp
            rw [this] at hd
            rw [show ([(T[j].side, T[j].delta)] : SChain).dropLast = []
              from rfl] at hd
            exact shsAt_ne_nil hC hi (by
              cases hs : shsAt T i with
              | nil => rfl
              | cons a as =>
                  rw [hs] at hd
                  simp at hd)
        | some p =>
            have hpb : p.1 < j := hC.par_back j hj p hp
            have hpl : p.1 < T.length := by omega
            have hform := shsAt_some hj hp hpb
            rw [hform, List.dropLast_concat] at hd
            have hp2 : p.2 = T[p.1].len - 1 := hC.par_tail j hj p hp hpl
            have hlenpos : 1 ≤ T[p.1].len :=
              hC.len_pos _ (List.getElem_mem hpl)
            obtain ⟨hip, hkp⟩ := smemChain_inj' hC hpl (by omega) hi
              (by omega) hd
            subst hip
            omega
    | succ m =>
        have hd' : shsAt T j ++ List.replicate m (Side.R, 1)
            = shsAt T i ++ List.replicate k (Side.R, 1) := by
          rw [← sdropLast_append_replicate_succ (h := shsAt T j) (r := m),
            hd]
        obtain ⟨rfl, rfl⟩ := smemChain_inj' hC hj (by omega) hi
          (by omega) hd'
        rfl
  have hlive : (shsAt T i ++ List.replicate (k + 1) (Side.R, 1)
      ∈ sStateOf T)
      ↔ ((shsAt T i ++ List.replicate (k + 1) (Side.R, 1)).dropLast
        ∈ sStateOf T) := by
    rw [hdrop, smemChain_live_iff hC hi hk1,
      smemChain_live_iff hC hi (by omega)]
  simp only [sfusible, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨⟨hkept, by rw [hdrop]; exact hdkept⟩,
    sgetLastD_append_replicate_succ⟩, huniq⟩, decide_eq_decide.mpr hlive⟩

theorem shead_not_fusible_sStateOf {T : STable} (hC : SCanonical T) {i : ℕ}
    (hi : i < T.length) : sfusible (sStateOf T) (shsAt T i) = false := by
  cases hf : sfusible (sStateOf T) (shsAt T i) with
  | false => rfl
  | true =>
      exfalso
      cases hp : T[i].par with
      | none =>
          have hform := shsAt_none hi hp
          have := sfusible_parent_kept hf
          rw [hform] at this
          rw [show ([(T[i].side, T[i].delta)] : SChain).dropLast = []
            from rfl] at this
          exact skept_ne_nil this rfl
      | some p =>
          have hpb : p.1 < i := hC.par_back i hi p hp
          have hpl : p.1 < T.length := by omega
          have hform := shsAt_some hi hp hpb
          have hp2 : p.2 = T[p.1].len - 1 := hC.par_tail i hi p hp hpl
          have hlenpos : 1 ≤ T[p.1].len :=
            hC.len_pos _ (List.getElem_mem hpl)
          have hdelta : T[i].delta = 1 ∧ T[i].side = Side.R := by
            have h1 := sfusible_concat hf
            have h2 : (shsAt T i).getLastD (Side.R, 0)
                = (T[i].side, T[i].delta) := by
              rw [hform, List.getLastD_concat]
            rcases List.eq_nil_or_concat (shsAt T i) with hnil | ⟨q, b, hqb⟩
            · exact absurd hnil (shsAt_ne_nil hC hi)
            · simp only [List.concat_eq_append] at hqb
              rw [hqb, List.getLastD_concat] at h2
              rw [hqb, List.dropLast_concat] at h1
              have hb := List.append_cancel_left h1
              injection hb with hb
              rw [hb] at h2
              injection h2 with hs hd
              exact ⟨hd.symm, hs.symm⟩
          have hlive : T[i].live = T[p.1].live := by
            have h1 := sfusible_live hf
            have hd : (shsAt T i).dropLast
                = shsAt T p.1 ++ List.replicate p.2 (Side.R, 1) := by
              rw [hform, List.dropLast_concat]
            rw [hd] at h1
            have h2 := smemChain_live_iff hC hi
              (hC.len_pos _ (List.getElem_mem hi))
            simp only [List.replicate_zero, List.append_nil] at h2
            have h3 := smemChain_live_iff hC hpl
              (by omega : p.2 < T[p.1].len)
            cases hl1 : T[i].live <;> cases hl2 : T[p.1].live
            · rfl
            · exfalso
              have := (h1.mpr (h3.mpr hl2))
              rw [h2, hl1] at this
              exact Bool.noConfusion this
            · exfalso
              have := h1.mp (h2.mpr hl1)
              rw [h3, hl2] at this
              exact Bool.noConfusion this
            · rfl
          obtain ⟨i', hi', hne, hpar'⟩ :=
            hC.no_fuse i hi p hp hpl hdelta.1 hdelta.2 hlive
          have hpb' : p.1 < i' := hC.par_back i' hi' p hpar'
          have hform' := shsAt_some hi' hpar' hpb'
          have hkept' : shsAt T i' ∈ skeptL (sStateOf T) := by
            refine (skept_sStateOf_iff hC).mpr ⟨i', hi', 0, ?_, by simp⟩
            exact hC.len_pos _ (List.getElem_mem hi')
          have hdrop' : (shsAt T i').dropLast = (shsAt T i).dropLast := by
            rw [hform, hform', List.dropLast_concat, List.dropLast_concat]
          have := sfusible_unique hf hkept' hdrop'
          exact hne (shsAt_inj hC hi' hi this)

theorem sheadOf_memChain {T : STable} (hC : SCanonical T) {i : ℕ}
    (hi : i < T.length) :
    ∀ k, k < T[i].len →
      sheadOf (sStateOf T) (shsAt T i ++ List.replicate k (Side.R, 1))
        = shsAt T i := by
  intro k
  induction k with
  | zero =>
      intro _
      simp only [List.replicate_zero, List.append_nil]
      exact sheadOf_of_not_fusible (shead_not_fusible_sStateOf hC hi)
  | succ k ih =>
      intro hk
      rw [sheadOf_of_fusible (smemChain_fusible hC hi hk),
        sdropLast_append_replicate_succ]
      exact ih (by omega)

theorem sisHead_sStateOf_iff {T : STable} (hC : SCanonical T) {c : SChain} :
    sisHead (sStateOf T) c = true
      ↔ ∃ i, ∃ (_ : i < T.length), c = shsAt T i := by
  constructor
  · intro hh
    obtain ⟨i, hi, k, hk, rfl⟩ :=
      (skept_sStateOf_iff hC).mp (sisHead_kept hh)
    cases k with
    | zero => exact ⟨i, hi, by simp⟩
    | succ k =>
        exfalso
        have := sisHead_not_fusible hh
        rw [smemChain_fusible hC hi hk] at this
        exact Bool.noConfusion this
  · rintro ⟨i, hi, rfl⟩
    refine sisHead_of_kept_not_fusible ?_ (shead_not_fusible_sStateOf hC hi)
    exact (skept_sStateOf_iff hC).mpr ⟨i, hi, 0,
      hC.len_pos _ (List.getElem_mem hi), by simp⟩

theorem slenOf_sStateOf {T : STable} (hC : SCanonical T) {i : ℕ}
    (hi : i < T.length) : slenOf (sStateOf T) (shsAt T i) = T[i].len := by
  have hperm : (srunMembers (sStateOf T) (shsAt T i)).Perm
      ((List.range T[i].len).map
        (fun k => shsAt T i ++ List.replicate k (Side.R, 1))) := by
    refine (List.perm_ext_iff_of_nodup ((nodup_skeptL _).filter _)
      ?_).mpr ?_
    · refine List.Nodup.map_on ?_ List.nodup_range
      intro j₁ _ j₂ _ heq
      exact sreplicate_offset_inj heq
    intro c
    rw [List.mem_filter, List.mem_map]
    constructor
    · rintro ⟨hkept, hhead⟩
      rw [beq_iff_eq] at hhead
      obtain ⟨j, hj, m, hm, rfl⟩ := (skept_sStateOf_iff hC).mp hkept
      rw [sheadOf_memChain hC hj m hm] at hhead
      obtain rfl := shsAt_inj hC hj hi hhead
      exact ⟨m, List.mem_range.mpr hm, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      rw [List.mem_range] at hk
      exact ⟨(skept_sStateOf_iff hC).mpr ⟨i, hi, k, hk, rfl⟩,
        by rw [beq_iff_eq]; exact sheadOf_memChain hC hi k hk⟩
  have := hperm.length_eq
  rw [slenOf, this]
  simp

theorem sheadsList_sStateOf {T : STable} (hC : SCanonical T) :
    sheadsList (sStateOf T) = sheadsOf T := by
  refine shLt_sorted_ext (sorted_sheadsList _) hC.sorted ?_
  intro c
  rw [mem_sheadsList, sisHead_sStateOf_iff hC]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [shsAt_eq_getElem hi]
    exact List.getElem_mem _
  · intro hc
    obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp hc
    have hi' : i < T.length := by rwa [sheadsOf_length] at hi
    exact ⟨i, hi', by rw [shsAt_eq_getElem hi', hgi]⟩

theorem SRTEntry.ext' {e1 e2 : SRTEntry} (h1 : e1.par = e2.par)
    (h2 : e1.live = e2.live) (h3 : e1.side = e2.side)
    (h4 : e1.delta = e2.delta) (h5 : e1.len = e2.len) : e1 = e2 := by
  cases e1; cases e2; simp_all

/-- **Sided T-repr, canonicity direction (`sTableOf ∘ sStateOf = id`)**: a
canonical sided table is recovered field for field, parent ref, liveness,
SIDE, delta, length, from the state it denotes. With `sStateOf_sTableOf`
and `scanonical_sTableOf` this closes the sided representation iso, over
labels + sides + liveness. -/
theorem sTableOf_sStateOf {T : STable} (hC : SCanonical T) :
    sTableOf (sStateOf T) = T := by
  rw [sTableOf, sheadsList_sStateOf hC]
  refine List.ext_getElem (by simp [sheadsOf_length]) ?_
  intro i hi1 hi2
  rw [List.getElem_map]
  have hi : i < T.length := hi2
  have hgi : (sheadsOf T)[i]'(by rw [sheadsOf_length]; exact hi)
      = shsAt T i := (shsAt_eq_getElem hi).symm
  rw [hgi]
  have hlen0 : 0 < T[i].len := hC.len_pos _ (List.getElem_mem hi)
  have hlast : (shsAt T i).getLastD (Side.R, 0)
      = (T[i].side, T[i].delta) := by
    cases hp : T[i].par with
    | none => rw [shsAt_none hi hp]; rfl
    | some p =>
        rw [shsAt_some hi hp (hC.par_back i hi p hp), List.getLastD_concat]
  refine SRTEntry.ext' ?_ ?_ ?_ ?_ ?_
  · show (if (shsAt T i).dropLast ∈ skeptL (sStateOf T)
      then some ((sheadsList (sStateOf T)).idxOf
                   (sheadOf (sStateOf T) (shsAt T i).dropLast),
                 (shsAt T i).dropLast.length
                   - (sheadOf (sStateOf T) (shsAt T i).dropLast).length)
      else none) = T[i].par
    cases hp : T[i].par with
    | none =>
        rw [if_neg]
        rw [shsAt_none hi hp]
        intro hmem
        exact skept_ne_nil hmem rfl
    | some p =>
        obtain ⟨p1, p2⟩ := p
        have hpb : p1 < i := hC.par_back i hi (p1, p2) hp
        have hpl : p1 < T.length := by omega
        have hp2 : p2 = T[p1].len - 1 := hC.par_tail i hi (p1, p2) hp hpl
        have hlenpos : 1 ≤ T[p1].len := hC.len_pos _ (List.getElem_mem hpl)
        have hdrop : (shsAt T i).dropLast
            = shsAt T p1 ++ List.replicate p2 (Side.R, 1) := by
          rw [shsAt_some hi hp hpb, List.dropLast_concat]
        have hkept : (shsAt T i).dropLast ∈ skeptL (sStateOf T) := by
          rw [hdrop]
          exact (skept_sStateOf_iff hC).mpr ⟨p1, hpl, p2, by omega, rfl⟩
        rw [if_pos hkept]
        have hhead : sheadOf (sStateOf T) (shsAt T i).dropLast
            = shsAt T p1 := by
          rw [hdrop]
          exact sheadOf_memChain hC hpl p2 (by omega)
        rw [hhead]
        have hidx : (sheadsList (sStateOf T)).idxOf (shsAt T p1) = p1 := by
          rw [sheadsList_sStateOf hC, shsAt_eq_getElem hpl]
          exact sidxOf_getElem_nodup (sheadsOf_nodup hC)
            (by rw [sheadsOf_length]; exact hpl)
        rw [hidx, hdrop]
        simp
  · have hiff := smemChain_live_iff hC hi hlen0
    simp only [List.replicate_zero, List.append_nil] at hiff
    show decide (shsAt T i ∈ sStateOf T) = T[i].live
    cases hl : T[i].live with
    | true => exact decide_eq_true (hiff.mpr hl)
    | false =>
        apply decide_eq_false
        intro hmem
        have := hiff.mp hmem
        rw [hl] at this
        exact Bool.noConfusion this
  · show ((shsAt T i).getLastD (Side.R, 0)).1 = T[i].side
    rw [hlast]
  · show ((shsAt T i).getLastD (Side.R, 0)).2 = T[i].delta
    rw [hlast]
  · exact slenOf_sStateOf hC hi

/-! ## §7½  Sided T-repr, image side: `sTableOf` always lands in
`SCanonical` -/

theorem sfusible_eq_true_iff {L : List SChain} {c : SChain} :
    sfusible L c = true ↔
    c ∈ skeptL L ∧ c.dropLast ∈ skeptL L
    ∧ c.getLastD (Side.R, 0) = (Side.R, 1)
    ∧ (∀ c' ∈ skeptL L, c'.dropLast = c.dropLast → c' = c)
    ∧ ((c ∈ L) ↔ (c.dropLast ∈ L)) := by
  simp only [sfusible, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    exact ⟨h1, h2, h3, h4, decide_eq_decide.mp h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, decide_eq_decide.mpr h5⟩

theorem sisHead_eq_false_of_sfusible {L : List SChain} {c : SChain}
    (h : sfusible L c = true) : sisHead L c = false := by
  simp [sisHead, h]

theorem sconcat_getLastD {c : SChain} (h : c ≠ []) :
    c = c.dropLast ++ [c.getLastD (Side.R, 0)] := by
  rcases List.eq_nil_or_concat c with rfl | ⟨q, b, rfl⟩
  · exact absurd rfl h
  · simp only [List.concat_eq_append]
    rw [List.dropLast_concat, List.getLastD_concat]

theorem schild_of_parent_eq {x p : SChain} (hne : x ≠ [])
    (hd : x.dropLast = p) :
    x = p ++ [x.getLastD (Side.R, 0)] := by
  conv_lhs => rw [sconcat_getLastD hne]
  rw [hd]

theorem stake_succ_of_prefix {m c : SChain} (h : m <+: c) (hne : m ≠ c) :
    ∃ e, m ++ [e] <+: c := by
  have hlt : m.length < c.length :=
    lt_of_le_of_ne h.length_le (fun hl => hne (h.eq_of_length hl))
  refine ⟨c[m.length], ?_⟩
  have h1 : c.take (m.length + 1) = c.take m.length ++ [c[m.length]] := by
    rw [List.take_succ, List.getElem?_eq_getElem hlt]
    rfl
  rw [← (List.prefix_iff_eq_take.mp h), ← h1] at *
  exact List.take_prefix _ _

/-- Any kept child of a run's tail is a head, `(R,1)` by `stail_attachment`
(the tail's run stops there), anything else by its label. -/
theorem stail_child_isHead {L : List SChain} {g : SChain}
    (hg : sisHead L g = true) {e : SEntry}
    (hkept : stailOf L g ++ [e] ∈ skeptL L) :
    sisHead L (stailOf L g ++ [e]) = true := by
  refine sisHead_of_kept_not_fusible hkept ?_
  by_cases he : e = (Side.R, 1)
  · subst he
    exact stail_succ_not_fusible hg
  · cases hf : sfusible L (stailOf L g ++ [e]) with
    | false => rfl
    | true =>
        exfalso
        have h1 := sfusible_concat hf
        rw [List.dropLast_concat] at h1
        have := List.append_cancel_left h1
        injection this with h'
        exact he h'

/-- **The sided escape lemma**: a kept chain below a head that is not one of
its run members exits the run at the tail through a child head. -/
theorem sescape_run {L : List SChain} {h c : SChain}
    (hh : sisHead L h = true) (hc : c ∈ skeptL L) (hpre : h <+: c)
    (hnm : sheadOf L c ≠ h) :
    ∃ q, sisHead L q = true ∧ q.dropLast = stailOf L h ∧ q <+: c := by
  have hclimb : ∀ j, j ≤ slenOf L h - 1 →
      h ++ List.replicate j (Side.R, 1) <+: c := by
    intro j
    induction j with
    | zero => intro _; simpa using hpre
    | succ j ih =>
        intro hj
        have hmj : h ++ List.replicate j (Side.R, 1) <+: c := ih (by omega)
        have hne : h ++ List.replicate j (Side.R, 1) ≠ c := by
          intro heq
          apply hnm
          rw [← heq]
          exact (mem_srunMembers.mp (srunMember_of_lt hh (by
            have := slenOf_pos hh
            omega : j < slenOf L h))).2
        obtain ⟨e, he⟩ := stake_succ_of_prefix hmj hne
        have hekept : (h ++ List.replicate j (Side.R, 1)) ++ [e]
            ∈ skeptL L := skept_of_prefix hc he (by simp)
        have hfus : sfusible L
            (h ++ List.replicate (j + 1) (Side.R, 1)) = true :=
          srunMember_fusible
            (srunMember_of_lt hh (by omega : j + 1 < slenOf L h))
        have huniq := sfusible_unique hfus hekept
          (by rw [List.dropLast_concat, sdropLast_append_replicate_succ])
        rw [← huniq]
        exact he
  have htail : stailOf L h <+: c := hclimb (slenOf L h - 1) (le_refl _)
  have htne : stailOf L h ≠ c := by
    intro heq
    apply hnm
    rw [← heq]
    exact (mem_srunMembers.mp (stailOf_mem hh)).2
  obtain ⟨e, he⟩ := stake_succ_of_prefix htail htne
  have hekept : stailOf L h ++ [e] ∈ skeptL L :=
    skept_of_prefix hc he (by simp)
  exact ⟨stailOf L h ++ [e], stail_child_isHead hh hekept,
    List.dropLast_concat, he⟩

theorem sTableOf_entry_head (L : List SChain) (i : ℕ)
    (hi : i < (sTableOf L).length) :
    ∃ h, sisHead L h = true ∧ (sheadsList L).idxOf h = i
      ∧ (sTableOf L)[i] = sentryOfHead L h := by
  have hi' : i < (sheadsList L).length := by
    simpa only [sTableOf, List.length_map] using hi
  refine ⟨(sheadsList L)[i], mem_sheadsList.mp (List.getElem_mem _),
    sidxOf_getElem_nodup (nodup_sheadsList L) hi', ?_⟩
  simp only [sTableOf, List.getElem_map]

theorem sgetElem_idx_eq {T : STable} {i j : ℕ} (hi : i < T.length)
    (hj : j < T.length) (hij : i = j) : T[i]'hi = T[j]'hj := by
  subst hij; rfl

theorem sTableOf_getElem_idxOf (L : List SChain) {h : SChain}
    (hh : sisHead L h = true)
    (hlt : (sheadsList L).idxOf h < (sTableOf L).length) :
    (sTableOf L)[(sheadsList L).idxOf h] = sentryOfHead L h := by
  have hm : h ∈ sheadsList L := mem_sheadsList.mpr hh
  simp only [sTableOf, List.getElem_map]
  congr 1
  exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hm)

/-- **Sided T-repr, image side**: `sTableOf L` is canonical, for every
`L`. -/
theorem scanonical_sTableOf (L : List SChain) : SCanonical (sTableOf L) := by
  have hlen : (sTableOf L).length = (sheadsList L).length := by
    simp [sTableOf]
  refine ⟨?len_pos, ?par_back, ?par_tail, ?no_fuse, ?leaves_live, ?sorted⟩
  case len_pos =>
    intro e he
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
    obtain ⟨h, hh, -, hentry⟩ := sTableOf_entry_head L i hi
    rw [hentry]
    exact slenOf_pos hh
  case sorted =>
    rw [sheadsOf_sTableOf]
    exact sorted_sheadsList L
  case par_back =>
    intro i hi p hp
    obtain ⟨h, hh, hidxh, hentry⟩ := sTableOf_entry_head L i hi
    rw [hentry] at hp
    simp only [sentryOfHead] at hp
    by_cases hpk : h.dropLast ∈ skeptL L
    · rw [if_pos hpk] at hp
      have hpe : p = ((sheadsList L).idxOf (sheadOf L h.dropLast),
          h.dropLast.length - (sheadOf L h.dropLast).length) := by
        injection hp with hp
        exact hp.symm
      rw [hpe]
      dsimp only
      set g := sheadOf L h.dropLast with hg_def
      have hgm : g ∈ sheadsList L := mem_sheadsList.mpr (sheadOf_isHead hpk)
      have hne : h ≠ [] := skept_ne_nil (sisHead_kept hh)
      have hglt : shLt g h = true := by
        have h1 : g.length ≤ h.dropLast.length :=
          (sheadOf_prefix L _).length_le
        have h2 : h.dropLast.length < h.length := by
          rw [List.length_dropLast]
          have : 0 < h.length := List.length_pos_iff.mpr hne
          omega
        exact shLt_of_length_lt (by omega)
      have := sidxOf_lt_of_shLt (sorted_sheadsList L) hgm
        (mem_sheadsList.mpr hh) hglt
      rwa [hidxh] at this
    · rw [if_neg hpk] at hp
      exact absurd hp (by simp)
  case par_tail =>
    intro i hi p hp hj
    obtain ⟨h, hh, hidxh, hentry⟩ := sTableOf_entry_head L i hi
    rw [hentry] at hp
    simp only [sentryOfHead] at hp
    by_cases hpk : h.dropLast ∈ skeptL L
    · rw [if_pos hpk] at hp
      have hpe : p = ((sheadsList L).idxOf (sheadOf L h.dropLast),
          h.dropLast.length - (sheadOf L h.dropLast).length) := by
        injection hp with hp
        exact hp.symm
      set g := sheadOf L h.dropLast with hg_def
      have hp1 : p.1 = (sheadsList L).idxOf g := by rw [hpe]
      have hp2 : p.2 = h.dropLast.length - g.length := by rw [hpe]
      have hjg : (sheadsList L).idxOf g < (sTableOf L).length := hp1 ▸ hj
      rw [hp2, sgetElem_idx_eq hj hjg hp1,
        sTableOf_getElem_idxOf L (sheadOf_isHead hpk) hjg]
      simp only [sentryOfHead]
      have htail := shead_parent_is_tail hh hpk
      rw [← hg_def] at htail
      have hlenpos := slenOf_pos (sheadOf_isHead hpk)
      have hdl : h.dropLast.length = g.length + (slenOf L g - 1) := by
        conv_lhs => rw [htail, stailOf]
        simp
      rw [hdl, ← hg_def]
      omega
    · rw [if_neg hpk] at hp
      exact absurd hp (by simp)
  case no_fuse =>
    intro i hi p hp hj hd1 hside hlive
    obtain ⟨h, hh, hidxh, hentry⟩ := sTableOf_entry_head L i hi
    rw [hentry] at hp hd1 hside hlive
    simp only [sentryOfHead] at hp hd1 hside hlive
    by_cases hpk : h.dropLast ∈ skeptL L
    · rw [if_pos hpk] at hp
      have hpe : p = ((sheadsList L).idxOf (sheadOf L h.dropLast),
          h.dropLast.length - (sheadOf L h.dropLast).length) := by
        injection hp with hp
        exact hp.symm
      set g := sheadOf L h.dropLast with hg_def
      have hp1 : p.1 = (sheadsList L).idxOf g := by rw [hpe]
      have hjg : (sheadsList L).idxOf g < (sTableOf L).length := hp1 ▸ hj
      rw [sgetElem_idx_eq hj hjg hp1,
        sTableOf_getElem_idxOf L (sheadOf_isHead hpk) hjg] at hlive
      simp only [sentryOfHead] at hlive
      rw [← hg_def] at hlive
      have hlast : h.getLastD (Side.R, 0) = (Side.R, 1) := by
        cases hgl : h.getLastD (Side.R, 0) with
        | mk s0 d0 =>
            rw [hgl] at hd1 hside
            simp only at hd1 hside
            rw [hside, hd1]
      have hdm : h.dropLast ∈ srunMembers L g :=
        mem_srunMembers.mpr ⟨hpk, hg_def.symm⟩
      have hlifted : (h ∈ L) ↔ (h.dropLast ∈ L) := by
        rw [srun_liveness_uniform hdm, decide_eq_decide.mp hlive]
      have hnf : sfusible L h = false := sisHead_not_fusible hh
      have hkh : h ∈ skeptL L := sisHead_kept hh
      have hnu : ¬ (∀ c' ∈ skeptL L, c'.dropLast = h.dropLast
          → c' = h) := by
        intro huniq
        rw [sfusible_eq_true_iff.mpr ⟨hkh, hpk, hlast, huniq, hlifted⟩]
          at hnf
        exact Bool.noConfusion hnf
      push_neg at hnu
      obtain ⟨c', hc'k, hc'd, hc'ne⟩ := hnu
      have hc'nf : sfusible L c' = false := by
        cases hf : sfusible L c' with
        | false => rfl
        | true =>
            exact absurd (sfusible_unique hf hkh (by rw [hc'd])).symm hc'ne
      have hc'h : sisHead L c' = true :=
        sisHead_of_kept_not_fusible hc'k hc'nf
      have hc'm : c' ∈ sheadsList L := mem_sheadsList.mpr hc'h
      have hc'lt : (sheadsList L).idxOf c' < (sTableOf L).length :=
        (List.idxOf_lt_length_of_mem hc'm).trans_eq hlen.symm
      refine ⟨(sheadsList L).idxOf c', hc'lt, ?_, ?_⟩
      · intro heq
        exact hc'ne ((List.idxOf_inj hc'm).mp (heq.trans hidxh.symm))
      · rw [hpe, sTableOf_getElem_idxOf L hc'h hc'lt]
        simp only [sentryOfHead]
        rw [if_pos (by rw [hc'd]; exact hpk), hc'd]
    · rw [if_neg hpk] at hp
      exact absurd hp (by simp)
  case leaves_live =>
    intro i hi hlivef
    obtain ⟨h, hh, hidxh, hentry⟩ := sTableOf_entry_head L i hi
    rw [hentry] at hlivef
    simp only [sentryOfHead] at hlivef
    have hhnl : h ∉ L := of_decide_eq_false hlivef
    have hkh : h ∈ skeptL L := sisHead_kept hh
    obtain ⟨hhne, l, hl, hpre⟩ := mem_skeptL.mp hkh
    have hlm : l ∈ skeptL L :=
      skept_of_live hl (fun hnil => hhne (List.prefix_nil.mp (hnil ▸ hpre)))
    have hnm : sheadOf L l ≠ h := by
      intro heq
      exact hhnl
        ((srun_liveness_uniform (mem_srunMembers.mpr ⟨hlm, heq⟩)).mp hl)
    obtain ⟨q, hqh, hqd, hqc⟩ := sescape_run hh hlm hpre hnm
    have hqm : q ∈ sheadsList L := mem_sheadsList.mpr hqh
    have hqlt : (sheadsList L).idxOf q < (sTableOf L).length :=
      (List.idxOf_lt_length_of_mem hqm).trans_eq hlen.symm
    have htk : stailOf L h ∈ skeptL L :=
      (mem_srunMembers.mp (stailOf_mem hh)).1
    have hth : sheadOf L (stailOf L h) = h :=
      (mem_srunMembers.mp (stailOf_mem hh)).2
    refine ⟨(sheadsList L).idxOf q, hqlt, q.dropLast.length - h.length, ?_⟩
    rw [sTableOf_getElem_idxOf L hqh hqlt]
    simp only [sentryOfHead]
    rw [if_pos (by rw [hqd]; exact htk), hqd, hth, hidxh]

/-! ## §8  Sided T-cmp: the two-case contracted comparator

The one-sided `cmpTable` walks two entry chains to the first difference:
same entry: offset order; prefix: ancestor first; divergence: larger
label first. The sided refinement keeps the two-case structure (licensed by
`stail_attachment`: every entry attaches at its parent's tail) but the
PREFIX case now consults the ancestor's offset against its run length: a
descendant exits its ancestor's entry at the TAIL, so if the ancestor sits
strictly before its tail it displays first regardless of the exit side,
while AT the tail the exit side decides, `R`-exits display after the
ancestor, `L`-exits before (the in-order rule). The divergence verdict is
`sEntryBefore` on the two branch entries, the band order of §4, refined
from the seed `sided_keyLt_iff_schainBefore`. -/

theorem sprefixesOf_concat (p : SChain) (b : SEntry) :
    sPrefixesOf (p ++ [b]) = sPrefixesOf p ++ [p ++ [b]] := by
  rw [sPrefixesOf, sPrefixesOf]
  rw [show (p ++ [b]).length = p.length + 1 by simp, List.range_succ,
    List.map_append]
  congr 1
  · apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    rw [List.take_append_of_le_length (by omega)]
  · simp only [List.map_cons, List.map_nil]
    rw [show List.take (p.length + 1) (p ++ [b]) = p ++ [b] from
      List.take_of_length_le (by simp)]

theorem sprefixesOf_prefix {x y : SChain} (hp : x <+: y) :
    sPrefixesOf x <+: sPrefixesOf y := by
  obtain ⟨ext, rfl⟩ := hp
  induction ext using List.reverseRecOn with
  | nil => simp
  | append_singleton ext b ih =>
      rw [← List.append_assoc, sprefixesOf_concat]
      exact ih.trans (List.prefix_append _ _)

/-- The sided entry chain: run heads from the root entry to `c`'s entry. -/
def sentryChainOf (L : List SChain) (c : SChain) : List SChain :=
  if h' : (sheadOf L c).length ≤ 1 then [sheadOf L c]
  else sentryChainOf L (sheadOf L c).dropLast ++ [sheadOf L c]
  termination_by c.length
  decreasing_by
    have h1 := (sheadOf_prefix L c).length_le
    simp only [List.length_dropLast]
    omega

theorem sentryChainOf_short {L : List SChain} {c : SChain}
    (h : (sheadOf L c).length ≤ 1) :
    sentryChainOf L c = [sheadOf L c] := by
  rw [sentryChainOf, dif_pos h]

theorem sentryChainOf_long {L : List SChain} {c : SChain}
    (h : ¬ (sheadOf L c).length ≤ 1) :
    sentryChainOf L c
      = sentryChainOf L (sheadOf L c).dropLast ++ [sheadOf L c] := by
  rw [sentryChainOf, dif_neg (by simpa using h)]

/-- Non-head run members contribute nothing to the head-filtered prefixes. -/
theorem sfilter_prefixes_run {L : List SChain} {h : SChain} :
    ∀ k, h ++ List.replicate k (Side.R, 1) ∈ skeptL L →
      sheadOf L (h ++ List.replicate k (Side.R, 1)) = h →
      (sPrefixesOf (h ++ List.replicate k (Side.R, 1))).filter
          (fun p => sisHead L p)
        = (sPrefixesOf h).filter (fun p => sisHead L p)
  | 0, _, _ => by simp
  | k + 1, hkept, hhead => by
      have hform : h ++ List.replicate (k + 1) (Side.R, 1)
          = (h ++ List.replicate k (Side.R, 1)) ++ [(Side.R, 1)] := by
        rw [List.replicate_succ', List.append_assoc]
      have hfus : sfusible L (h ++ List.replicate (k + 1) (Side.R, 1))
          = true := by
        cases hf : sfusible L (h ++ List.replicate (k + 1) (Side.R, 1)) with
        | true => rfl
        | false =>
            exfalso
            have := sheadOf_of_not_fusible hf
            rw [hhead] at this
            have := congrArg List.length this
            simp at this
      have hkept' : h ++ List.replicate k (Side.R, 1) ∈ skeptL L := by
        refine skept_of_prefix hkept ?_ ?_
        · rw [hform]
          exact List.prefix_append _ _
        · intro hnil
          have hh : h ∈ skeptL L := hhead ▸ sheadOf_kept hkept
          cases h with
          | nil => exact skept_ne_nil hh rfl
          | cons a as => simp at hnil
      have hhead' : sheadOf L (h ++ List.replicate k (Side.R, 1)) = h := by
        refine sheadOf_within hhead (List.prefix_append _ _) ?_
        rw [hform]
        exact List.prefix_append _ _
      rw [hform, sprefixesOf_concat, List.filter_append]
      rw [show ((h ++ List.replicate k (Side.R, 1)) ++ [(Side.R, 1)] : SChain)
        = h ++ List.replicate (k + 1) (Side.R, 1) from hform.symm]
      rw [show (([h ++ List.replicate (k + 1) (Side.R, 1)] :
          List SChain).filter (fun p => sisHead L p)) = [] from by
        simp [List.filter, sisHead_eq_false_of_sfusible hfus]]
      rw [List.append_nil]
      exact sfilter_prefixes_run k hkept' hhead'

/-- **Sided entry-chain characterization**: exactly the head prefixes. -/
theorem sentryChainOf_eq_filter {L : List SChain} :
    ∀ n (c : SChain), c.length ≤ n → c ∈ skeptL L →
    sentryChainOf L c = (sPrefixesOf c).filter (fun p => sisHead L p) := by
  intro n
  induction n with
  | zero =>
      intro c hc hkept
      exact absurd (List.length_pos_iff.mpr (skept_ne_nil hkept)) (by omega)
  | succ n ih =>
      intro c hc hkept
      have hh : sisHead L (sheadOf L c) = true := sheadOf_isHead hkept
      have hhkept : sheadOf L c ∈ skeptL L := sheadOf_kept hkept
      obtain ⟨k, hform⟩ := sheadOf_replicate L c
      have hrun : (sPrefixesOf c).filter (fun p => sisHead L p)
          = (sPrefixesOf (sheadOf L c)).filter (fun p => sisHead L p) := by
        conv_lhs => rw [hform]
        exact sfilter_prefixes_run k (hform ▸ hkept) (hform ▸ rfl)
      rw [hrun]
      by_cases hlen : (sheadOf L c).length ≤ 1
      · rw [sentryChainOf_short hlen]
        obtain ⟨e, he⟩ : ∃ e, sheadOf L c = [e] := by
          cases hhc : sheadOf L c with
          | nil => exact absurd hhc (skept_ne_nil hhkept)
          | cons a as =>
              rw [hhc] at hlen
              simp at hlen
              rw [hlen]
              exact ⟨a, rfl⟩
        rw [he]
        rw [show sPrefixesOf [e] = [[e]] from rfl]
        rw [List.filter_cons]
        rw [he] at hh
        simp [hh]
      · rw [sentryChainOf_long hlen]
        obtain ⟨q, b, hqb⟩ : ∃ q b, sheadOf L c = q ++ [b] := by
          rcases List.eq_nil_or_concat (sheadOf L c) with hnil | ⟨q, b, hqb⟩
          · exact absurd hnil (skept_ne_nil hhkept)
          · exact ⟨q, b, by simpa using hqb⟩
        have hqkept : (sheadOf L c).dropLast ∈ skeptL L := by
          refine skept_of_prefix hhkept (List.dropLast_prefix _) ?_
          rw [hqb, List.dropLast_concat]
          intro hnil
          rw [hnil] at hqb
          rw [hqb] at hlen
          simp at hlen
        have hqlen : (sheadOf L c).dropLast.length ≤ n := by
          have h1 := (sheadOf_prefix L c).length_le
          simp only [List.length_dropLast]
          omega
        rw [ih _ hqlen hqkept]
        rw [hqb, List.dropLast_concat, sprefixesOf_concat,
          List.filter_append]
        congr 1
        have hhb : sisHead L (q ++ [b]) = true := hqb ▸ hh
        simp [List.filter, hhb]

/-- The divergence verdict, computable: the band order on branch entries. -/
def sEntryBeforeB : SEntry → SEntry → Bool
  | (Side.R, d), (Side.R, e) => decide (e < d)
  | (Side.L, d), (Side.L, e) => decide (d < e)
  | (Side.L, _), (Side.R, _) => true
  | (Side.R, _), (Side.L, _) => false

theorem sEntryBeforeB_iff {e1 e2 : SEntry} :
    sEntryBeforeB e1 e2 = true ↔ sEntryBefore e1 e2 := by
  obtain ⟨s1, d1⟩ := e1
  obtain ⟨s2, d2⟩ := e2
  cases s1 <;> cases s2 <;>
    simp [sEntryBeforeB, sEntryBefore]

/-- First-difference walk over two sided entry chains, carrying each side's
own-entry offset AND own-run length: at exhaustion the offset-vs-tail test
plus the exit side decide (the in-order rule); at a genuine divergence the
band order decides. -/
def scmpEC : List SChain → ℕ → ℕ → List SChain → ℕ → ℕ → Bool
  | [], jx, _, [], jy, _ => decide (jx < jy)
  | [], jx, lx, gy :: _, _, _ =>
      decide (jx + 1 < lx)
        || decide ((gy.getLastD (Side.R, 0)).1 = Side.R)
  | gx :: _, _, _, [], jy, ly =>
      !(decide (jy + 1 < ly))
        && decide ((gx.getLastD (Side.R, 0)).1 = Side.L)
  | gx :: tx, jx, lx, gy :: ty, jy, ly =>
      if gx = gy then scmpEC tx jx lx ty jy ly
      else sEntryBeforeB (gx.getLastD (Side.R, 0)) (gy.getLastD (Side.R, 0))

/-- The sided table comparator: entry chains, own-entry offsets and own-run
lengths, header data only. -/
def scmpTable (L : List SChain) (x y : SChain) : Bool :=
  scmpEC (sentryChainOf L x) (x.length - (sheadOf L x).length)
    (slenOf L (sheadOf L x))
    (sentryChainOf L y) (y.length - (sheadOf L y).length)
    (slenOf L (sheadOf L y))

theorem scmpEC_consume (w a : List SChain) (jx lx : ℕ)
    (b : List SChain) (jy ly : ℕ) :
    scmpEC (w ++ a) jx lx (w ++ b) jy ly = scmpEC a jx lx b jy ly := by
  induction w with
  | nil => rfl
  | cons g w ih => simpa [scmpEC] using ih

theorem sentryChainOf_concat (L : List SChain) (c : SChain) :
    ∃ w, sentryChainOf L c = w ++ [sheadOf L c] := by
  by_cases h : (sheadOf L c).length ≤ 1
  · exact ⟨[], by rw [sentryChainOf_short h]; rfl⟩
  · exact ⟨_, sentryChainOf_long h⟩

theorem sposChain_of_kept {L : List SChain}
    (hpos : ∀ l ∈ L, PosSChain l) {c : SChain} (hc : c ∈ skeptL L) :
    PosSChain c := by
  obtain ⟨-, l, hl, hpre⟩ := mem_skeptL.mp hc
  intro e he
  exact hpos l hl e (hpre.subset he)

/-- Entry-chain decomposition at a head `p ++ [e]` sitting inside `z`. -/
theorem sEC_decompose {L : List SChain} {z p : SChain} {e : SEntry}
    (hz : z ∈ skeptL L) (hpz : p ++ [e] <+: z)
    (hhd : sisHead L (p ++ [e]) = true) :
    ∃ rz, sentryChainOf L z
      = (sPrefixesOf p).filter (fun q => sisHead L q)
        ++ (p ++ [e]) :: rz := by
  have h1 : sentryChainOf L (p ++ [e]) <+: sentryChainOf L z := by
    rw [sentryChainOf_eq_filter (p ++ [e]).length _ (le_refl _)
        (skept_of_prefix hz hpz (by simp)),
      sentryChainOf_eq_filter z.length z (le_refl _) hz]
    exact (sprefixesOf_prefix hpz).filter _
  have h2 : sentryChainOf L (p ++ [e])
      = (sPrefixesOf p).filter (fun q => sisHead L q) ++ [p ++ [e]] := by
    rw [sentryChainOf_eq_filter (p ++ [e]).length _ (le_refl _)
        (skept_of_prefix hz hpz (by simp)),
      sprefixesOf_concat, List.filter_append]
    congr 1
    simp [List.filter, hhd]
  obtain ⟨rz, hrz⟩ := h1
  exact ⟨rz, by rw [← hrz, h2, List.append_assoc]; rfl⟩

/-- `x`'s offset in its own run is below the run length. -/
theorem soffset_lt {L : List SChain} {x : SChain} (hx : x ∈ skeptL L) :
    x.length - (sheadOf L x).length < slenOf L (sheadOf L x) := by
  have hmem : x ∈ srunMembers L (sheadOf L x) :=
    mem_srunMembers.mpr ⟨hx, rfl⟩
  have hform := srunMember_form hmem
  exact srunMember_offset_lt (hform ▸ hmem)

/-- If `x` sits AT its run's tail, it IS the tail. -/
theorem seq_tail_of_offset {L : List SChain} {x : SChain}
    (hx : x ∈ skeptL L)
    (hoff : x.length - (sheadOf L x).length + 1
      = slenOf L (sheadOf L x)) :
    x = stailOf L (sheadOf L x) := by
  have hform := srunMember_form (mem_srunMembers.mpr ⟨hx, rfl⟩)
  rw [stailOf]
  conv_lhs => rw [hform]
  congr 2
  omega

/-- **Sided case A soundness, `extR`**: an ancestor displays before its
`R`-extensions. -/
theorem scmpTable_extR {L : List SChain} {x : SChain} {d : ℕ}
    {rest : SChain} (hx : x ∈ skeptL L)
    (hy : x ++ (Side.R, d) :: rest ∈ skeptL L) :
    scmpTable L x (x ++ (Side.R, d) :: rest) = true
    ∧ scmpTable L (x ++ (Side.R, d) :: rest) x = false := by
  have hpre : x <+: x ++ (Side.R, d) :: rest := ⟨(Side.R, d) :: rest, rfl⟩
  have hxney : x ≠ x ++ (Side.R, d) :: rest := by
    intro heq
    have := congrArg List.length heq
    simp at this
  have hECp : sentryChainOf L x
      <+: sentryChainOf L (x ++ (Side.R, d) :: rest) := by
    rw [sentryChainOf_eq_filter x.length x (le_refl _) hx,
      sentryChainOf_eq_filter (x ++ (Side.R, d) :: rest).length _
        (le_refl _) hy]
    exact (sprefixesOf_prefix hpre).filter _
  obtain ⟨rest', hrest⟩ := hECp
  cases rest' with
  | nil =>
      rw [List.append_nil] at hrest
      have hheads : sheadOf L x = sheadOf L (x ++ (Side.R, d) :: rest) := by
        obtain ⟨wx, hwx⟩ := sentryChainOf_concat L x
        obtain ⟨wy, hwy⟩ := sentryChainOf_concat L (x ++ (Side.R, d) :: rest)
        have h1 : wx ++ [sheadOf L x]
            = wy ++ [sheadOf L (x ++ (Side.R, d) :: rest)] := by
          rw [← hwx, ← hwy, hrest]
        have h2 := congrArg List.getLast? h1
        rw [List.getLast?_concat, List.getLast?_concat] at h2
        injection h2
      have hxlen : x.length < (x ++ (Side.R, d) :: rest).length := by
        simp
      have hhx := (sheadOf_prefix L x).length_le
      have hjlt : x.length - (sheadOf L x).length
          < (x ++ (Side.R, d) :: rest).length
            - (sheadOf L (x ++ (Side.R, d) :: rest)).length := by
        rw [← hheads]
        omega
      constructor
      · rw [scmpTable, hrest, hheads]
        rw [show scmpEC (sentryChainOf L (x ++ (Side.R, d) :: rest))
            (x.length - (sheadOf L (x ++ (Side.R, d) :: rest)).length)
            (slenOf L (sheadOf L (x ++ (Side.R, d) :: rest)))
            (sentryChainOf L (x ++ (Side.R, d) :: rest))
            ((x ++ (Side.R, d) :: rest).length
              - (sheadOf L (x ++ (Side.R, d) :: rest)).length)
            (slenOf L (sheadOf L (x ++ (Side.R, d) :: rest)))
            = scmpEC []
                (x.length - (sheadOf L (x ++ (Side.R, d) :: rest)).length)
                (slenOf L (sheadOf L (x ++ (Side.R, d) :: rest))) []
                ((x ++ (Side.R, d) :: rest).length
                  - (sheadOf L (x ++ (Side.R, d) :: rest)).length)
                (slenOf L (sheadOf L (x ++ (Side.R, d) :: rest))) from by
          rw [← List.append_nil (sentryChainOf L (x ++ (Side.R, d) :: rest))]
          exact scmpEC_consume _ _ _ _ _ _ _]
        rw [← hheads] at *
        simp only [scmpEC, decide_eq_true_eq]
        omega
      · rw [scmpTable, hrest, hheads]
        rw [show scmpEC (sentryChainOf L (x ++ (Side.R, d) :: rest))
            ((x ++ (Side.R, d) :: rest).length
              - (sheadOf L (x ++ (Side.R, d) :: rest)).length)
            (slenOf L (sheadOf L (x ++ (Side.R, d) :: rest)))
            (sentryChainOf L (x ++ (Side.R, d) :: rest))
            (x.length - (sheadOf L (x ++ (Side.R, d) :: rest)).length)
            (slenOf L (sheadOf L (x ++ (Side.R, d) :: rest)))
            = scmpEC []
                ((x ++ (Side.R, d) :: rest).length
                  - (sheadOf L (x ++ (Side.R, d) :: rest)).length)
                (slenOf L (sheadOf L (x ++ (Side.R, d) :: rest))) []
                (x.length - (sheadOf L (x ++ (Side.R, d) :: rest)).length)
                (slenOf L (sheadOf L (x ++ (Side.R, d) :: rest))) from by
          rw [← List.append_nil (sentryChainOf L (x ++ (Side.R, d) :: rest))]
          exact scmpEC_consume _ _ _ _ _ _ _]
        rw [← hheads] at *
        simp only [scmpEC, decide_eq_false_iff_not]
        omega
  | cons r rs =>
      have hECx : sentryChainOf L x
          = (sPrefixesOf x).filter (fun p => sisHead L p) :=
        sentryChainOf_eq_filter x.length x (le_refl _) hx
      have hjx := soffset_lt hx
      by_cases hjtail : x.length - (sheadOf L x).length + 1
          < slenOf L (sheadOf L x)
      · -- x strictly inside its run: x first regardless of the exit side
        constructor
        · rw [scmpTable, ← hrest]
          have h := scmpEC_consume (sentryChainOf L x) []
            (x.length - (sheadOf L x).length) (slenOf L (sheadOf L x))
            (r :: rs)
            ((x ++ (Side.R, d) :: rest).length
              - (sheadOf L (x ++ (Side.R, d) :: rest)).length)
            (slenOf L (sheadOf L (x ++ (Side.R, d) :: rest)))
          rw [List.append_nil] at h
          rw [h]
          simp only [scmpEC, Bool.or_eq_true, decide_eq_true_eq]
          exact Or.inl hjtail
        · rw [scmpTable, ← hrest]
          have h := scmpEC_consume (sentryChainOf L x) (r :: rs)
            ((x ++ (Side.R, d) :: rest).length
              - (sheadOf L (x ++ (Side.R, d) :: rest)).length)
            (slenOf L (sheadOf L (x ++ (Side.R, d) :: rest))) []
            (x.length - (sheadOf L x).length) (slenOf L (sheadOf L x))
          rw [List.append_nil] at h
          rw [h]
          have hd1 : decide (x.length - (sheadOf L x).length + 1
              < slenOf L (sheadOf L x)) = true := decide_eq_true hjtail
          simp only [scmpEC, hd1, Bool.not_true, Bool.false_and]
      · -- x AT its tail: the next entry on y's path is x ++ [(R,d)]
        have hxt : x = stailOf L (sheadOf L x) :=
          seq_tail_of_offset hx (by omega)
        have hqkept : x ++ [(Side.R, d)] ∈ skeptL L := by
          refine skept_of_prefix hy ?_ (by simp)
          refine ⟨rest, ?_⟩
          rw [List.append_assoc]
          rfl
        have hqh : sisHead L (x ++ [(Side.R, d)]) = true := by
          rw [hxt] at hqkept ⊢
          exact stail_child_isHead (sheadOf_isHead hx) hqkept
        obtain ⟨ry, hry⟩ := sEC_decompose hy
          (⟨rest, by rw [List.append_assoc]; rfl⟩ :
            x ++ [(Side.R, d)] <+: x ++ (Side.R, d) :: rest) hqh
        rw [← hECx] at hry
        have hreq : r = x ++ [(Side.R, d)] := by
          rw [hry] at hrest
          have h2 := List.append_cancel_left hrest
          simp only [List.cons.injEq] at h2
          exact h2.1
        constructor
        · rw [scmpTable, ← hrest]
          have h := scmpEC_consume (sentryChainOf L x) []
            (x.length - (sheadOf L x).length) (slenOf L (sheadOf L x))
            (r :: rs)
            ((x ++ (Side.R, d) :: rest).length
              - (sheadOf L (x ++ (Side.R, d) :: rest)).length)
            (slenOf L (sheadOf L (x ++ (Side.R, d) :: rest)))
          rw [List.append_nil] at h
          rw [h]
          simp only [scmpEC, Bool.or_eq_true, decide_eq_true_eq]
          right
          rw [hreq, List.getLastD_concat]
        · rw [scmpTable, ← hrest]
          have h := scmpEC_consume (sentryChainOf L x) (r :: rs)
            ((x ++ (Side.R, d) :: rest).length
              - (sheadOf L (x ++ (Side.R, d) :: rest)).length)
            (slenOf L (sheadOf L (x ++ (Side.R, d) :: rest))) []
            (x.length - (sheadOf L x).length) (slenOf L (sheadOf L x))
          rw [List.append_nil] at h
          rw [h]
          have hd2 : decide ((r.getLastD (Side.R, 0)).1 = Side.L)
              = false := by
            rw [hreq, List.getLastD_concat]
            simp
          simp only [scmpEC, hd2, Bool.and_false]

/-- **Sided case A soundness, `extL`**: `L`-extensions display before the
ancestor, and force the ancestor to sit at its run's tail. -/
theorem scmpTable_extL {L : List SChain} {y : SChain} {d : ℕ}
    {rest : SChain} (hy : y ∈ skeptL L)
    (hx : y ++ (Side.L, d) :: rest ∈ skeptL L) :
    scmpTable L (y ++ (Side.L, d) :: rest) y = true
    ∧ scmpTable L y (y ++ (Side.L, d) :: rest) = false := by
  have hqpre : y ++ [(Side.L, d)] <+: y ++ (Side.L, d) :: rest :=
    ⟨rest, by rw [List.append_assoc]; rfl⟩
  have hqkept : y ++ [(Side.L, d)] ∈ skeptL L :=
    skept_of_prefix hx hqpre (by simp)
  have hqh : sisHead L (y ++ [(Side.L, d)]) = true := by
    refine Lentry_isHead hqkept ?_
    rw [List.getLastD_concat]
  have hECy : sentryChainOf L y
      = (sPrefixesOf y).filter (fun p => sisHead L p) :=
    sentryChainOf_eq_filter y.length y (le_refl _) hy
  obtain ⟨rx, hrx⟩ := sEC_decompose hx hqpre hqh
  rw [← hECy] at hrx
  -- `y` is at its run's tail: an interior node's unique kept child is its
  -- `(R,1)` run successor, not the `L` child.
  have hytail : ¬ (y.length - (sheadOf L y).length + 1
      < slenOf L (sheadOf L y)) := by
    intro hlt2
    have hg : sisHead L (sheadOf L y) = true := sheadOf_isHead hy
    have hmem : sheadOf L y ++ List.replicate
        (y.length - (sheadOf L y).length + 1) (Side.R, 1)
        ∈ srunMembers L (sheadOf L y) := srunMember_of_lt hg hlt2
    have hform := srunMember_form (mem_srunMembers.mpr ⟨hy, rfl⟩)
    have hfus : sfusible L (sheadOf L y ++ List.replicate
        (y.length - (sheadOf L y).length + 1) (Side.R, 1)) = true :=
      srunMember_fusible hmem
    have hdrop : (sheadOf L y ++ List.replicate
        (y.length - (sheadOf L y).length + 1) (Side.R, 1)).dropLast
        = y := by
      rw [sdropLast_append_replicate_succ]
      exact hform.symm
    have huniq := sfusible_unique hfus hqkept
      (by rw [List.dropLast_concat, hdrop])
    -- the L child equals the R successor: sides clash
    have hlast := congrArg (fun c => List.getLastD c (Side.R, 0)) huniq
    simp only [List.getLastD_concat] at hlast
    rw [sgetLastD_append_replicate_succ] at hlast
    exact absurd (congrArg Prod.fst hlast) (by simp)
  constructor
  · rw [scmpTable, hrx]
    have h := scmpEC_consume (sentryChainOf L y)
      ((y ++ [(Side.L, d)]) :: rx)
      ((y ++ (Side.L, d) :: rest).length
        - (sheadOf L (y ++ (Side.L, d) :: rest)).length)
      (slenOf L (sheadOf L (y ++ (Side.L, d) :: rest))) []
      (y.length - (sheadOf L y).length) (slenOf L (sheadOf L y))
    rw [List.append_nil] at h
    rw [h]
    have hd1 : decide (y.length - (sheadOf L y).length + 1
        < slenOf L (sheadOf L y)) = false := decide_eq_false hytail
    have hd2 : decide (((y ++ [(Side.L, d)]).getLastD (Side.R, 0)).1
        = Side.L) = true := by
      rw [List.getLastD_concat]
      simp
    simp only [scmpEC, hd1, hd2, Bool.not_false, Bool.and_true]
  · rw [scmpTable, hrx]
    have h := scmpEC_consume (sentryChainOf L y) []
      (y.length - (sheadOf L y).length) (slenOf L (sheadOf L y))
      ((y ++ [(Side.L, d)]) :: rx)
      ((y ++ (Side.L, d) :: rest).length
        - (sheadOf L (y ++ (Side.L, d) :: rest)).length)
      (slenOf L (sheadOf L (y ++ (Side.L, d) :: rest)))
    rw [List.append_nil] at h
    rw [h]
    have hd1 : decide (y.length - (sheadOf L y).length + 1
        < slenOf L (sheadOf L y)) = false := decide_eq_false hytail
    have hd3 : decide (((y ++ [(Side.L, d)]).getLastD (Side.R, 0)).1
        = Side.R) = false := by
      rw [List.getLastD_concat]
      simp
    simp only [scmpEC, hd1, hd3, Bool.or_false]

/-- **Sided case B soundness (divergence)**: both branch heads are heads,
and the band order (`sEntryBefore`) decides. -/
theorem scmpTable_diverge {L : List SChain} {q : SChain} {e1 e2 : SEntry}
    {t1 t2 : SChain} (hx : q ++ e1 :: t1 ∈ skeptL L)
    (hy : q ++ e2 :: t2 ∈ skeptL L) (hlt : sEntryBefore e1 e2) :
    scmpTable L (q ++ e1 :: t1) (q ++ e2 :: t2) = true
    ∧ scmpTable L (q ++ e2 :: t2) (q ++ e1 :: t1) = false := by
  have hq1pre : q ++ [e1] <+: q ++ e1 :: t1 :=
    ⟨t1, by rw [List.append_assoc]; rfl⟩
  have hq2pre : q ++ [e2] <+: q ++ e2 :: t2 :=
    ⟨t2, by rw [List.append_assoc]; rfl⟩
  have hq1k : q ++ [e1] ∈ skeptL L := skept_of_prefix hx hq1pre (by simp)
  have hq2k : q ++ [e2] ∈ skeptL L := skept_of_prefix hy hq2pre (by simp)
  have he12 : e1 ≠ e2 := by
    intro heq
    exact sEntryBefore_irrefl e1 (heq ▸ hlt)
  have hqne : (q ++ [e1] : SChain) ≠ q ++ [e2] := by
    intro h
    have := List.append_cancel_left h
    injection this with h'
    exact he12 h'
  have hh1 : sisHead L (q ++ [e1]) = true := by
    refine sisHead_of_kept_not_fusible hq1k ?_
    cases hf : sfusible L (q ++ [e1]) with
    | false => rfl
    | true =>
        exfalso
        exact hqne ((sfusible_unique hf hq2k
          (by rw [List.dropLast_concat, List.dropLast_concat])).symm)
  have hh2 : sisHead L (q ++ [e2]) = true := by
    refine sisHead_of_kept_not_fusible hq2k ?_
    cases hf : sfusible L (q ++ [e2]) with
    | false => rfl
    | true =>
        exfalso
        exact hqne (sfusible_unique hf hq1k
          (by rw [List.dropLast_concat, List.dropLast_concat]))
  obtain ⟨r1, hr1⟩ := sEC_decompose hx hq1pre hh1
  obtain ⟨r2, hr2⟩ := sEC_decompose hy hq2pre hh2
  have hbB : sEntryBeforeB ((q ++ [e1]).getLastD (Side.R, 0))
      ((q ++ [e2]).getLastD (Side.R, 0)) = true := by
    rw [List.getLastD_concat, List.getLastD_concat]
    exact sEntryBeforeB_iff.mpr hlt
  have hbB' : sEntryBeforeB ((q ++ [e2]).getLastD (Side.R, 0))
      ((q ++ [e1]).getLastD (Side.R, 0)) = false := by
    rw [List.getLastD_concat, List.getLastD_concat]
    cases hbb : sEntryBeforeB e2 e1 with
    | false => rfl
    | true =>
        exact absurd (sEntryBeforeB_iff.mp hbb) (sEntryBefore_asymm hlt)
  constructor
  · rw [scmpTable, hr1, hr2, scmpEC_consume]
    simp only [scmpEC, if_neg hqne]
    exact hbB
  · rw [scmpTable, hr1, hr2, scmpEC_consume]
    simp only [scmpEC, if_neg (Ne.symm hqne)]
    exact hbB'

/-- Both `schainBefore` shapes, computed by the sided comparator. -/
theorem scmpTable_of_schainBefore {L : List SChain} {x y : SChain}
    (hx : x ∈ skeptL L) (hy : y ∈ skeptL L) (hb : schainBefore x y) :
    scmpTable L x y = true ∧ scmpTable L y x = false := by
  cases hb with
  | extL ch d rest => exact scmpTable_extL hy hx
  | extR ch d rest => exact scmpTable_extR hx hy
  | diverge q e1 e2 c1 c2 hlt => exact scmpTable_diverge hx hy hlt

/-- **Sided T-cmp, chain form**: the sided two-case comparator IS the
in-order display rule. -/
theorem scmpTable_iff_schainBefore {L : List SChain} {x y : SChain}
    (hx : x ∈ skeptL L) (hy : y ∈ skeptL L) (hne : x ≠ y) :
    (scmpTable L x y = true ↔ schainBefore x y) := by
  constructor
  · intro hcmp
    rcases schainBefore_total hne with hb | hb
    · exact hb
    · rw [(scmpTable_of_schainBefore hy hx hb).2] at hcmp
      exact Bool.noConfusion hcmp
  · exact fun hb => (scmpTable_of_schainBefore hx hy hb).1

/-- **Sided T-cmp**: the comparator over the contracted sided run tree
equals the fold's key order on the sided coordinates, for EVERY ordered
prefix code. Refines the §4 band-order seed to full entry chains. -/
theorem scmpTable_eq_keyLt (Γ : OrderedPrefixCode) {L : List SChain}
    (hpos : ∀ l ∈ L, PosSChain l) {x y : SChain}
    (hx : x ∈ skeptL L) (hy : y ∈ skeptL L) (hne : x ≠ y) :
    scmpTable L x y
      = keyLt (sKey (sidedCoordOf Γ y)) (sKey (sidedCoordOf Γ x)) := by
  have hpx : PosSChain x := sposChain_of_kept hpos hx
  have hpy : PosSChain y := sposChain_of_kept hpos hy
  cases hcmp : scmpTable L x y with
  | true =>
      exact ((sided_keyLt_iff_schainBefore Γ hpx hpy hne).mpr
        ((scmpTable_iff_schainBefore hx hy hne).mp hcmp)).symm
  | false =>
      have hnb : ¬ schainBefore x y := fun hb => by
        rw [(scmpTable_of_schainBefore hx hy hb).1] at hcmp
        exact Bool.noConfusion hcmp
      rcases schainBefore_total hne with hb | hb
      · exact absurd hb hnb
      · have := (sided_keyLt_iff_schainBefore Γ hpy hpx
          (Ne.symm hne)).mpr hb
        rw [keyLt_asymm this]

/-! ## §9  Sided T-walk: the structural walk is the in-order display

The sided walk of a run: interior members in offset order, then the
L-subtrees at the tail (older label first, ascending), then the TAIL
member, then the R-subtrees at the tail (newer label first, descending).
This is the in-order rule at run granularity: L-attachments display before
the node they hang from, and all attachments hang at the tail
(`stail_attachment`). -/

theorem sle_foldr_max : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.foldr max 0
  | [], x, hx => absurd hx (List.not_mem_nil)
  | y :: ys, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact Nat.le_max_left _ _
      · exact le_trans (sle_foldr_max ys x hx') (Nat.le_max_right _ _)

def smaxLen (L : List SChain) : ℕ :=
  ((skeptL L).map List.length).foldr max 0

theorem slength_le_smaxLen {L : List SChain} {c : SChain}
    (hc : c ∈ skeptL L) : c.length ≤ smaxLen L :=
  sle_foldr_max _ _ (List.mem_map.mpr ⟨c, hc, rfl⟩)

/-- The `L`-side child entries at node `m`, oldest label first. -/
def sLchilds (L : List SChain) (m : SChain) : List SChain :=
  ((skeptL L).filter (fun c => sisHead L c && (c.dropLast == m)
      && ((c.getLastD (Side.R, 0)).1 == Side.L))).mergeSort
    (fun a b => decide ((a.getLastD (Side.R, 0)).2
      ≤ (b.getLastD (Side.R, 0)).2))

/-- The `R`-side child entries at node `m`, newest label first. -/
def sRchilds (L : List SChain) (m : SChain) : List SChain :=
  ((skeptL L).filter (fun c => sisHead L c && (c.dropLast == m)
      && ((c.getLastD (Side.R, 0)).1 == Side.R))).mergeSort
    (fun a b => decide ((b.getLastD (Side.R, 0)).2
      ≤ (a.getLastD (Side.R, 0)).2))

theorem mem_sLchilds {L : List SChain} {m c : SChain} :
    c ∈ sLchilds L m ↔ sisHead L c = true ∧ c.dropLast = m
      ∧ (c.getLastD (Side.R, 0)).1 = Side.L := by
  rw [sLchilds, List.mem_mergeSort, List.mem_filter]
  constructor
  · rintro ⟨-, h⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨sisHead_kept h1, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨h1, h2⟩, h3⟩

theorem mem_sRchilds {L : List SChain} {m c : SChain} :
    c ∈ sRchilds L m ↔ sisHead L c = true ∧ c.dropLast = m
      ∧ (c.getLastD (Side.R, 0)).1 = Side.R := by
  rw [sRchilds, List.mem_mergeSort, List.mem_filter]
  constructor
  · rintro ⟨-, h⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨sisHead_kept h1, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨h1, h2⟩, h3⟩

theorem nodup_sLchilds (L : List SChain) (m : SChain) :
    (sLchilds L m).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr ((nodup_skeptL L).filter _)

theorem nodup_sRchilds (L : List SChain) (m : SChain) :
    (sRchilds L m).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr ((nodup_skeptL L).filter _)

theorem sorted_sLchilds (L : List SChain) (m : SChain) :
    (sLchilds L m).Pairwise (fun a b =>
      (a.getLastD (Side.R, 0)).2 ≤ (b.getLastD (Side.R, 0)).2) := by
  have h := List.pairwise_mergeSort
    (le := fun a b : SChain => decide ((a.getLastD (Side.R, 0)).2
      ≤ (b.getLastD (Side.R, 0)).2))
    (fun a b c h1 h2 => by
      rw [decide_eq_true_eq] at h1 h2 ⊢
      omega)
    (fun a b => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega)
    ((skeptL L).filter (fun c => sisHead L c && (c.dropLast == m)
      && ((c.getLastD (Side.R, 0)).1 == Side.L)))
  exact h.imp (fun hab => by
    simp only [decide_eq_true_eq] at hab
    exact hab)

theorem sorted_sRchilds (L : List SChain) (m : SChain) :
    (sRchilds L m).Pairwise (fun a b =>
      (b.getLastD (Side.R, 0)).2 ≤ (a.getLastD (Side.R, 0)).2) := by
  have h := List.pairwise_mergeSort
    (le := fun a b : SChain => decide ((b.getLastD (Side.R, 0)).2
      ≤ (a.getLastD (Side.R, 0)).2))
    (fun a b c h1 h2 => by
      rw [decide_eq_true_eq] at h1 h2 ⊢
      omega)
    (fun a b => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega)
    ((skeptL L).filter (fun c => sisHead L c && (c.dropLast == m)
      && ((c.getLastD (Side.R, 0)).1 == Side.R)))
  exact h.imp (fun hab => by
    simp only [decide_eq_true_eq] at hab
    exact hab)

/-- The sided walk below one entry: interior members, L-subtrees, the tail,
R-subtrees, the in-order rule. -/
def swalkE (L : List SChain) : ℕ → SChain → List SChain
  | 0, _ => []
  | fuel + 1, h =>
      (if h ∈ L then (List.range (slenOf L h - 1)).map
          (fun k => h ++ List.replicate k (Side.R, 1)) else [])
      ++ ((sLchilds L (stailOf L h)).flatMap (swalkE L fuel)
        ++ ((if h ∈ L then [stailOf L h] else [])
          ++ (sRchilds L (stailOf L h)).flatMap (swalkE L fuel)))

/-- The sided walk of the whole table: L-rooted subtrees (ascending), then
R-rooted subtrees (descending), nothing at the virtual root itself. -/
def swalk (L : List SChain) : List SChain :=
  (sLchilds L []).flatMap (swalkE L (smaxLen L + 1))
    ++ (sRchilds L []).flatMap (swalkE L (smaxLen L + 1))

theorem sprefix_eq_of_length {p1 p2 c : SChain} (h1 : p1 <+: c)
    (h2 : p2 <+: c) (hl : p1.length = p2.length) : p1 = p2 :=
  (List.prefix_of_prefix_length_le h1 h2 (le_of_eq hl)).eq_of_length hl

theorem schildHead_subtree_form {L : List SChain} {m q c : SChain}
    (hqh : sisHead L q = true) (hqd : q.dropLast = m) (hc : q <+: c) :
    ∃ rest, c = m ++ q.getLastD (Side.R, 0) :: rest := by
  have hqne : q ≠ [] := skept_ne_nil (sisHead_kept hqh)
  obtain ⟨ext, rfl⟩ := hc
  refine ⟨ext, ?_⟩
  conv_lhs => rw [sconcat_getLastD hqne, hqd]
  rw [List.append_assoc]
  rfl

/-- Run members in offset order display in order. -/
theorem smember_lt_before {h : SChain} {k k' : ℕ} (hkk : k < k') :
    schainBefore (h ++ List.replicate k (Side.R, 1))
      (h ++ List.replicate k' (Side.R, 1)) := by
  have hstep : h ++ List.replicate k' (Side.R, 1)
      = (h ++ List.replicate k (Side.R, 1))
        ++ (Side.R, 1) :: List.replicate (k' - k - 1) (Side.R, 1) := by
    rw [List.append_assoc]
    congr 1
    rw [show ((Side.R, 1) : SEntry) :: List.replicate (k' - k - 1)
        (Side.R, 1) = List.replicate (k' - k) (Side.R, 1) from by
      rw [← List.replicate_succ]
      congr 1
      omega]
    rw [← List.replicate_add]
    congr 1
    omega
  rw [hstep]
  exact schainBefore.extR _ 1 _

/-- An interior member displays before every chain in a tail subtree. -/
theorem smember_before_subtree {L : List SChain} {h c : SChain} {k : ℕ}
    (hklt : k + 1 < slenOf L h) {e : SEntry} {rest : SChain}
    (hc : c = stailOf L h ++ e :: rest) :
    schainBefore (h ++ List.replicate k (Side.R, 1)) c := by
  rw [hc, stailOf]
  rw [show h ++ List.replicate (slenOf L h - 1) (Side.R, 1)
      = (h ++ List.replicate k (Side.R, 1))
        ++ List.replicate (slenOf L h - 1 - k) (Side.R, 1) from by
    rw [List.append_assoc, ← List.replicate_add]
    congr 2
    omega]
  rw [List.append_assoc]
  rw [show List.replicate (slenOf L h - 1 - k) ((Side.R, 1) : SEntry)
      ++ e :: rest
      = (Side.R, 1) :: (List.replicate (slenOf L h - 2 - k) (Side.R, 1)
          ++ e :: rest) from by
    rw [show slenOf L h - 1 - k = (slenOf L h - 2 - k) + 1 by omega,
      List.replicate_succ, List.cons_append]]
  exact schainBefore.extR _ 1 _

theorem sbefore_of_R_ext {t c : SChain} {e : SEntry} {rest : SChain}
    (hside : e.1 = Side.R) (hc : c = t ++ e :: rest) :
    schainBefore t c := by
  rw [hc, show e = (Side.R, e.2) from by rw [← hside]]
  exact schainBefore.extR _ _ _

theorem sbefore_of_L_ext {t c : SChain} {e : SEntry} {rest : SChain}
    (hside : e.1 = Side.L) (hc : c = t ++ e :: rest) :
    schainBefore c t := by
  rw [hc, show e = (Side.L, e.2) from by rw [← hside]]
  exact schainBefore.extL _ _ _

theorem swalkE_sound {L : List SChain} :
    ∀ fuel (h c : SChain), sisHead L h = true → c ∈ swalkE L fuel h →
      c ∈ L ∧ h <+: c := by
  intro fuel
  induction fuel with
  | zero => intro h c _ hc; simp [swalkE] at hc
  | succ fuel ih =>
      intro h c hh hc
      rw [swalkE] at hc
      simp only [List.mem_append] at hc
      have hsub : ∀ q, sisHead L q = true → q.dropLast = stailOf L h →
          c ∈ swalkE L fuel q → c ∈ L ∧ h <+: c := by
        intro q hqh hqd hcq
        obtain ⟨hcl, hqc⟩ := ih q c hqh hcq
        refine ⟨hcl, ?_⟩
        have h1 : h <+: stailOf L h := List.prefix_append _ _
        have h2 : stailOf L h <+: q := by
          rw [← hqd]
          exact List.dropLast_prefix q
        exact (h1.trans h2).trans hqc
      rcases hc with hc | (hc | (hc | hc))
      · by_cases hl : h ∈ L
        · rw [if_pos hl] at hc
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
          rw [List.mem_range] at hk
          have hklen : k < slenOf L h := by omega
          exact ⟨(srun_liveness_uniform (srunMember_of_lt hh hklen)).mpr hl,
            List.prefix_append _ _⟩
        · rw [if_neg hl] at hc
          simp at hc
      · obtain ⟨q, hq, hcq⟩ := List.mem_flatMap.mp hc
        obtain ⟨hqh, hqd, -⟩ := mem_sLchilds.mp hq
        exact hsub q hqh hqd hcq
      · by_cases hl : h ∈ L
        · rw [if_pos hl] at hc
          rw [List.mem_singleton] at hc
          subst hc
          exact ⟨(srun_liveness_uniform (stailOf_mem hh)).mpr hl,
            List.prefix_append _ _⟩
        · rw [if_neg hl] at hc
          simp at hc
      · obtain ⟨q, hq, hcq⟩ := List.mem_flatMap.mp hc
        obtain ⟨hqh, hqd, -⟩ := mem_sRchilds.mp hq
        exact hsub q hqh hqd hcq

theorem swalkE_complete {L : List SChain} :
    ∀ fuel (h c : SChain), sisHead L h = true → c ∈ L → c ∈ skeptL L →
      h <+: c → smaxLen L + 1 - h.length ≤ fuel →
      c ∈ swalkE L fuel h := by
  intro fuel
  induction fuel with
  | zero =>
      intro h c hh _ hc hpre hfuel
      have h1 := (hpre.trans (List.prefix_refl c)).length_le
      have h2 := slength_le_smaxLen hc
      have h3 := slength_le_smaxLen (sisHead_kept hh)
      omega
  | succ fuel ih =>
      intro h c hh hcl hc hpre hfuel
      rw [swalkE]
      simp only [List.mem_append]
      by_cases hm : sheadOf L c = h
      · have hmem : c ∈ srunMembers L h := mem_srunMembers.mpr ⟨hc, hm⟩
        have hl : h ∈ L := (srun_liveness_uniform hmem).mp hcl
        have hform := srunMember_form hmem
        have hofflt : c.length - h.length < slenOf L h :=
          srunMember_offset_lt (hform ▸ hmem)
        by_cases htl : c.length - h.length + 1 < slenOf L h
        · left
          rw [if_pos hl]
          refine List.mem_map.mpr ⟨c.length - h.length, ?_, hform.symm⟩
          rw [List.mem_range]
          omega
        · right; right; left
          rw [if_pos hl, List.mem_singleton]
          rw [hform, stailOf]
          congr 2
          omega
      · obtain ⟨q, hqh, hqd, hqc⟩ := sescape_run hh hc hpre hm
        have hfuel' : smaxLen L + 1 - q.length ≤ fuel := by
          have h1 : q.length - 1 = (stailOf L h).length := by
            rw [← hqd, List.length_dropLast]
          have h2 : (stailOf L h).length = h.length + (slenOf L h - 1) := by
            rw [stailOf]; simp
          have h3 : 1 ≤ q.length :=
            List.length_pos_iff.mpr (skept_ne_nil (sisHead_kept hqh))
          have h4 := slenOf_pos hh
          omega
        cases hqside : (q.getLastD (Side.R, 0)).1 with
        | L =>
            right; left
            exact List.mem_flatMap.mpr ⟨q,
              mem_sLchilds.mpr ⟨hqh, hqd, hqside⟩,
              ih q c hqh hcl hc hqc hfuel'⟩
        | R =>
            right; right; right
            exact List.mem_flatMap.mpr ⟨q,
              mem_sRchilds.mpr ⟨hqh, hqd, hqside⟩,
              ih q c hqh hcl hc hqc hfuel'⟩

theorem swalkE_nodup {L : List SChain} :
    ∀ fuel (h : SChain), sisHead L h = true →
      (swalkE L fuel h).Nodup := by
  intro fuel
  induction fuel with
  | zero => intro h _; simp [swalkE]
  | succ fuel ih =>
      intro h hh
      have hsound : ∀ (q c : SChain), sisHead L q = true →
          q.dropLast = stailOf L h → c ∈ swalkE L fuel q →
          stailOf L h <+: c ∧ (stailOf L h).length < c.length := by
        intro q c hqh hqd hcq
        have h1 := (swalkE_sound fuel q c hqh hcq).2
        have h2 : stailOf L h <+: q := by
          rw [← hqd]
          exact List.dropLast_prefix q
        have h3 : 1 ≤ q.length :=
          List.length_pos_iff.mpr (skept_ne_nil (sisHead_kept hqh))
        have h4 := congrArg List.length hqd
        rw [List.length_dropLast] at h4
        refine ⟨h2.trans h1, ?_⟩
        have := h1.length_le
        omega
      have hsubdisj : ∀ (q q' c : SChain), sisHead L q = true →
          sisHead L q' = true → q.dropLast = stailOf L h →
          q'.dropLast = stailOf L h → q ≠ q' →
          c ∈ swalkE L fuel q → c ∉ swalkE L fuel q' := by
        intro q q' c hqh hqh' hqd hqd' hne hc hc'
        apply hne
        refine sprefix_eq_of_length (swalkE_sound fuel q c hqh hc).2
          (swalkE_sound fuel q' c hqh' hc').2 ?_
        have e1 := congrArg List.length hqd
        have e2 := congrArg List.length hqd'
        rw [List.length_dropLast] at e1 e2
        have n1 : 1 ≤ q.length :=
          List.length_pos_iff.mpr (skept_ne_nil (sisHead_kept hqh))
        have n2 : 1 ≤ q'.length :=
          List.length_pos_iff.mpr (skept_ne_nil (sisHead_kept hqh'))
        omega
      have hmemlen : ∀ c, (c ∈ (if h ∈ L then
          (List.range (slenOf L h - 1)).map
            (fun k => h ++ List.replicate k (Side.R, 1)) else [])) →
          c.length < (stailOf L h).length := by
        intro c hc
        by_cases hl : h ∈ L
        · rw [if_pos hl] at hc
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
          rw [List.mem_range] at hk
          rw [stailOf]
          simp only [List.length_append, List.length_replicate]
          omega
        · rw [if_neg hl] at hc
          simp at hc
      rw [swalkE]
      rw [List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · by_cases hl : h ∈ L
        · rw [if_pos hl]
          refine List.Nodup.map_on ?_ List.nodup_range
          intro j₁ _ j₂ _ heq
          exact sreplicate_offset_inj heq
        · rw [if_neg hl]
          exact List.nodup_nil
      · rw [List.nodup_append]
        refine ⟨?_, ?_, ?_⟩
        · refine nodup_flatMap_of_disjoint (nodup_sLchilds L _) ?_ ?_
          · intro q hq
            exact ih q (mem_sLchilds.mp hq).1
          · intro q hq q' hq' hne c hc
            obtain ⟨hqh, hqd, -⟩ := mem_sLchilds.mp hq
            obtain ⟨hqh', hqd', -⟩ := mem_sLchilds.mp hq'
            exact hsubdisj q q' c hqh hqh' hqd hqd' hne hc
        · rw [List.nodup_append]
          refine ⟨?_, ?_, ?_⟩
          · by_cases hl : h ∈ L
            · rw [if_pos hl]
              exact List.nodup_singleton _
            · rw [if_neg hl]
              exact List.nodup_nil
          · refine nodup_flatMap_of_disjoint (nodup_sRchilds L _) ?_ ?_
            · intro q hq
              exact ih q (mem_sRchilds.mp hq).1
            · intro q hq q' hq' hne c hc
              obtain ⟨hqh, hqd, -⟩ := mem_sRchilds.mp hq
              obtain ⟨hqh', hqd', -⟩ := mem_sRchilds.mp hq'
              exact hsubdisj q q' c hqh hqh' hqd hqd' hne hc
          · intro a ha b hb heq
            subst heq
            by_cases hl : h ∈ L
            · rw [if_pos hl, List.mem_singleton] at ha
              subst ha
              obtain ⟨q, hq, hcq⟩ := List.mem_flatMap.mp hb
              obtain ⟨hqh, hqd, -⟩ := mem_sRchilds.mp hq
              have := (hsound q _ hqh hqd hcq).2
              omega
            · rw [if_neg hl] at ha
              simp at ha
        · intro a ha b hb heq
          subst heq
          obtain ⟨q, hq, hcq⟩ := List.mem_flatMap.mp ha
          obtain ⟨hqh, hqd, hqs⟩ := mem_sLchilds.mp hq
          have haform := hsound q _ hqh hqd hcq
          rcases List.mem_append.mp hb with hb | hb
          · by_cases hl : h ∈ L
            · rw [if_pos hl, List.mem_singleton] at hb
              rw [hb] at haform
              omega
            · rw [if_neg hl] at hb
              simp at hb
          · obtain ⟨q', hq', hcq'⟩ := List.mem_flatMap.mp hb
            obtain ⟨hqh', hqd', hqs'⟩ := mem_sRchilds.mp hq'
            have hqq : q = q' := by
              have hp1 : q <+: a := (swalkE_sound fuel q _ hqh hcq).2
              have hp2 : q' <+: a := (swalkE_sound fuel q' _ hqh' hcq').2
              refine sprefix_eq_of_length hp1 hp2 ?_
              have e1 := congrArg List.length hqd
              have e2 := congrArg List.length hqd'
              rw [List.length_dropLast] at e1 e2
              have n1 : 1 ≤ q.length :=
                List.length_pos_iff.mpr (skept_ne_nil (sisHead_kept hqh))
              have n2 : 1 ≤ q'.length :=
                List.length_pos_iff.mpr (skept_ne_nil (sisHead_kept hqh'))
              omega
            rw [hqq, hqs'] at hqs
            exact absurd hqs (by simp)
      · intro a ha b hb heq
        subst heq
        have halen := hmemlen a ha
        simp only [List.mem_append] at hb
        rcases hb with hb | (hb | hb)
        · obtain ⟨q, hq, hcq⟩ := List.mem_flatMap.mp hb
          obtain ⟨hqh, hqd, -⟩ := mem_sLchilds.mp hq
          have := (hsound q a hqh hqd hcq).2
          omega
        · by_cases hl : h ∈ L
          · rw [if_pos hl, List.mem_singleton] at hb
            rw [hb] at halen
            omega
          · rw [if_neg hl] at hb
            simp at hb
        · obtain ⟨q, hq, hcq⟩ := List.mem_flatMap.mp hb
          obtain ⟨hqh, hqd, -⟩ := mem_sRchilds.mp hq
          have := (hsound q a hqh hqd hcq).2
          omega

theorem schild_eq_of_same_last {L : List SChain} {m q q' : SChain}
    (hqh : sisHead L q = true) (hqh' : sisHead L q' = true)
    (hqd : q.dropLast = m) (hqd' : q'.dropLast = m)
    (hlast : q.getLastD (Side.R, 0) = q'.getLastD (Side.R, 0)) :
    q = q' := by
  have h1 : q = m ++ [q.getLastD (Side.R, 0)] := by
    conv_lhs => rw [sconcat_getLastD (skept_ne_nil (sisHead_kept hqh)), hqd]
  have h2 : q' = m ++ [q'.getLastD (Side.R, 0)] := by
    conv_lhs =>
      rw [sconcat_getLastD (skept_ne_nil (sisHead_kept hqh')), hqd']
  rw [h1, h2, hlast]

theorem ssubtree_L_before_R {t b b' : SChain} {e e' : SEntry}
    {r1 r2 : SChain} (hse : e.1 = Side.L) (hse' : e'.1 = Side.R)
    (hb : b = t ++ e :: r1) (hb' : b' = t ++ e' :: r2) :
    schainBefore b b' := by
  rw [hb, hb', show e = (Side.L, e.2) from by rw [← hse],
    show e' = (Side.R, e'.2) from by rw [← hse']]
  exact schainBefore.diverge t _ _ r1 r2 trivial

theorem swalkE_pairwise {L : List SChain} :
    ∀ fuel (h : SChain), sisHead L h = true →
      (swalkE L fuel h).Pairwise schainBefore := by
  intro fuel
  induction fuel with
  | zero => intro h _; simp [swalkE]
  | succ fuel ih =>
      intro h hh
      have hsubform : ∀ (q c : SChain), sisHead L q = true →
          q.dropLast = stailOf L h → c ∈ swalkE L fuel q →
          ∃ rest, c = stailOf L h ++ q.getLastD (Side.R, 0) :: rest := by
        intro q c hqh hqd hcq
        exact schildHead_subtree_form hqh hqd
          (swalkE_sound fuel q c hqh hcq).2
      rw [swalkE]
      refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
      · by_cases hl : h ∈ L
        · rw [if_pos hl, List.pairwise_map]
          refine (List.pairwise_lt_range).imp ?_
          intro j k hjk
          exact smember_lt_before hjk
        · rw [if_neg hl]
          exact List.Pairwise.nil
      · refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
        · refine pairwise_flatMap
            (fun q hq => ih q (mem_sLchilds.mp hq).1) ?_
          have hsorted := (sorted_sLchilds L (stailOf L h)).and
            (List.nodup_iff_pairwise_ne.mp (nodup_sLchilds L (stailOf L h)))
          refine hsorted.imp_of_mem ?_
          intro q q' hqm hqm' hqq c hc c' hc'
          obtain ⟨hle, hne⟩ := hqq
          obtain ⟨hqh, hqd, hqs⟩ := mem_sLchilds.mp hqm
          obtain ⟨hqh', hqd', hqs'⟩ := mem_sLchilds.mp hqm'
          obtain ⟨r1, hr1⟩ := hsubform q c hqh hqd hc
          obtain ⟨r2, hr2⟩ := hsubform q' c' hqh' hqd' hc'
          have hdne : (q.getLastD (Side.R, 0)).2
              ≠ (q'.getLastD (Side.R, 0)).2 := by
            intro heq
            exact hne (schild_eq_of_same_last hqh hqh' hqd hqd'
              (Prod.ext (by rw [hqs, hqs']) heq))
          rw [hr1, hr2,
            show q.getLastD (Side.R, 0)
              = (Side.L, (q.getLastD (Side.R, 0)).2) from by rw [← hqs],
            show q'.getLastD (Side.R, 0)
              = (Side.L, (q'.getLastD (Side.R, 0)).2) from by rw [← hqs']]
          refine schainBefore.diverge _ _ _ _ _ ?_
          show (q.getLastD (Side.R, 0)).2 < (q'.getLastD (Side.R, 0)).2
          omega
        · refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
          · by_cases hl : h ∈ L
            · rw [if_pos hl]
              simp
            · rw [if_neg hl]
              exact List.Pairwise.nil
          · refine pairwise_flatMap
              (fun q hq => ih q (mem_sRchilds.mp hq).1) ?_
            have hsorted := (sorted_sRchilds L (stailOf L h)).and
              (List.nodup_iff_pairwise_ne.mp
                (nodup_sRchilds L (stailOf L h)))
            refine hsorted.imp_of_mem ?_
            intro q q' hqm hqm' hqq c hc c' hc'
            obtain ⟨hle, hne⟩ := hqq
            obtain ⟨hqh, hqd, hqs⟩ := mem_sRchilds.mp hqm
            obtain ⟨hqh', hqd', hqs'⟩ := mem_sRchilds.mp hqm'
            obtain ⟨r1, hr1⟩ := hsubform q c hqh hqd hc
            obtain ⟨r2, hr2⟩ := hsubform q' c' hqh' hqd' hc'
            have hdne : (q.getLastD (Side.R, 0)).2
                ≠ (q'.getLastD (Side.R, 0)).2 := by
              intro heq
              exact hne (schild_eq_of_same_last hqh hqh' hqd hqd'
                (Prod.ext (by rw [hqs, hqs']) heq))
            rw [hr1, hr2,
              show q.getLastD (Side.R, 0)
                = (Side.R, (q.getLastD (Side.R, 0)).2)
                from Prod.ext hqs rfl,
              show q'.getLastD (Side.R, 0)
                = (Side.R, (q'.getLastD (Side.R, 0)).2)
                from Prod.ext hqs' rfl]
            refine schainBefore.diverge _ _ _ _ _ ?_
            show (q'.getLastD (Side.R, 0)).2 < (q.getLastD (Side.R, 0)).2
            omega
          · intro a ha b hb
            by_cases hl : h ∈ L
            · rw [if_pos hl, List.mem_singleton] at ha
              subst ha
              obtain ⟨q, hq, hcq⟩ := List.mem_flatMap.mp hb
              obtain ⟨hqh, hqd, hqs⟩ := mem_sRchilds.mp hq
              obtain ⟨rest, hrest⟩ := hsubform q b hqh hqd hcq
              exact sbefore_of_R_ext hqs hrest
            · rw [if_neg hl] at ha
              simp at ha
        · intro a ha b hb
          obtain ⟨q, hq, hcq⟩ := List.mem_flatMap.mp ha
          obtain ⟨hqh, hqd, hqs⟩ := mem_sLchilds.mp hq
          obtain ⟨r1, hr1⟩ := hsubform q a hqh hqd hcq
          rcases List.mem_append.mp hb with hb | hb
          · by_cases hl : h ∈ L
            · rw [if_pos hl, List.mem_singleton] at hb
              subst hb
              exact sbefore_of_L_ext hqs hr1
            · rw [if_neg hl] at hb
              simp at hb
          · obtain ⟨q', hq', hcq'⟩ := List.mem_flatMap.mp hb
            obtain ⟨hqh', hqd', hqs'⟩ := mem_sRchilds.mp hq'
            obtain ⟨r2, hr2⟩ := hsubform q' b hqh' hqd' hcq'
            exact ssubtree_L_before_R hqs hqs' hr1 hr2
      · intro a ha b hb
        by_cases hl : h ∈ L
        · rw [if_pos hl] at ha
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
          rw [List.mem_range] at hk
          simp only [List.mem_append] at hb
          rcases hb with hb | (hb | hb)
          · obtain ⟨q, hq, hcq⟩ := List.mem_flatMap.mp hb
            obtain ⟨hqh, hqd, -⟩ := mem_sLchilds.mp hq
            obtain ⟨rest, hrest⟩ := hsubform q b hqh hqd hcq
            exact smember_before_subtree (by omega) hrest
          · rw [if_pos hl, List.mem_singleton] at hb
            subst hb
            rw [stailOf]
            exact smember_lt_before (by omega)
          · obtain ⟨q, hq, hcq⟩ := List.mem_flatMap.mp hb
            obtain ⟨hqh, hqd, -⟩ := mem_sRchilds.mp hq
            obtain ⟨rest, hrest⟩ := hsubform q b hqh hqd hcq
            exact smember_before_subtree (by omega) hrest
        · rw [if_neg hl] at ha
          simp at ha

theorem sroot_child_length {L : List SChain} {q : SChain}
    (hq : sisHead L q = true) (hqd : q.dropLast = []) : q.length = 1 := by
  have hl := congrArg List.length hqd
  rw [List.length_dropLast] at hl
  have n1 : 1 ≤ q.length :=
    List.length_pos_iff.mpr (skept_ne_nil (sisHead_kept hq))
  simp at hl
  omega

theorem swalk_nodup (L : List SChain) : (swalk L).Nodup := by
  have hblock : ∀ (q q' c : SChain), sisHead L q = true →
      sisHead L q' = true → q.dropLast = [] → q'.dropLast = [] →
      c ∈ swalkE L (smaxLen L + 1) q → c ∈ swalkE L (smaxLen L + 1) q' →
      q = q' := by
    intro q q' c hqh hqh' hqd hqd' hc hc'
    refine sprefix_eq_of_length (swalkE_sound _ q c hqh hc).2
      (swalkE_sound _ q' c hqh' hc').2 ?_
    rw [sroot_child_length hqh hqd, sroot_child_length hqh' hqd']
  rw [swalk, List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · refine nodup_flatMap_of_disjoint (nodup_sLchilds L []) ?_ ?_
    · intro q hq
      exact swalkE_nodup _ q (mem_sLchilds.mp hq).1
    · intro q hq q' hq' hne c hc hc'
      exact hne (hblock q q' c (mem_sLchilds.mp hq).1
        (mem_sLchilds.mp hq').1 (mem_sLchilds.mp hq).2.1
        (mem_sLchilds.mp hq').2.1 hc hc')
  · refine nodup_flatMap_of_disjoint (nodup_sRchilds L []) ?_ ?_
    · intro q hq
      exact swalkE_nodup _ q (mem_sRchilds.mp hq).1
    · intro q hq q' hq' hne c hc hc'
      exact hne (hblock q q' c (mem_sRchilds.mp hq).1
        (mem_sRchilds.mp hq').1 (mem_sRchilds.mp hq).2.1
        (mem_sRchilds.mp hq').2.1 hc hc')
  · intro a ha b hb heq
    subst heq
    obtain ⟨q, hq, hcq⟩ := List.mem_flatMap.mp ha
    obtain ⟨q', hq', hcq'⟩ := List.mem_flatMap.mp hb
    obtain ⟨hqh, hqd, hqs⟩ := mem_sLchilds.mp hq
    obtain ⟨hqh', hqd', hqs'⟩ := mem_sRchilds.mp hq'
    have hqq := hblock q q' a hqh hqh' hqd hqd' hcq hcq'
    rw [hqq, hqs'] at hqs
    exact absurd hqs (by simp)

theorem swalk_pairwise (L : List SChain) :
    (swalk L).Pairwise schainBefore := by
  have hsubform : ∀ (q c : SChain), sisHead L q = true →
      q.dropLast = [] → c ∈ swalkE L (smaxLen L + 1) q →
      ∃ rest, c = q.getLastD (Side.R, 0) :: rest := by
    intro q c hqh hqd hcq
    obtain ⟨rest, hrest⟩ := schildHead_subtree_form hqh hqd
      (swalkE_sound _ q c hqh hcq).2
    exact ⟨rest, by simpa using hrest⟩
  rw [swalk]
  refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
  · refine pairwise_flatMap (fun q hq => swalkE_pairwise _ q
      (mem_sLchilds.mp hq).1) ?_
    have hsorted := (sorted_sLchilds L []).and
      (List.nodup_iff_pairwise_ne.mp (nodup_sLchilds L []))
    refine hsorted.imp_of_mem ?_
    intro q q' hqm hqm' hqq c hc c' hc'
    obtain ⟨hle, hne⟩ := hqq
    obtain ⟨hqh, hqd, hqs⟩ := mem_sLchilds.mp hqm
    obtain ⟨hqh', hqd', hqs'⟩ := mem_sLchilds.mp hqm'
    obtain ⟨r1, hr1⟩ := hsubform q c hqh hqd hc
    obtain ⟨r2, hr2⟩ := hsubform q' c' hqh' hqd' hc'
    have hdne : (q.getLastD (Side.R, 0)).2
        ≠ (q'.getLastD (Side.R, 0)).2 := by
      intro heq
      exact hne (schild_eq_of_same_last hqh hqh' hqd hqd'
        (Prod.ext (by rw [hqs, hqs']) heq))
    rw [hr1, hr2,
      show q.getLastD (Side.R, 0)
        = (Side.L, (q.getLastD (Side.R, 0)).2) from by rw [← hqs],
      show q'.getLastD (Side.R, 0)
        = (Side.L, (q'.getLastD (Side.R, 0)).2) from by rw [← hqs']]
    refine schainBefore.diverge [] _ _ _ _ ?_
    show (q.getLastD (Side.R, 0)).2 < (q'.getLastD (Side.R, 0)).2
    omega
  · refine pairwise_flatMap (fun q hq => swalkE_pairwise _ q
      (mem_sRchilds.mp hq).1) ?_
    have hsorted := (sorted_sRchilds L []).and
      (List.nodup_iff_pairwise_ne.mp (nodup_sRchilds L []))
    refine hsorted.imp_of_mem ?_
    intro q q' hqm hqm' hqq c hc c' hc'
    obtain ⟨hle, hne⟩ := hqq
    obtain ⟨hqh, hqd, hqs⟩ := mem_sRchilds.mp hqm
    obtain ⟨hqh', hqd', hqs'⟩ := mem_sRchilds.mp hqm'
    obtain ⟨r1, hr1⟩ := hsubform q c hqh hqd hc
    obtain ⟨r2, hr2⟩ := hsubform q' c' hqh' hqd' hc'
    have hdne : (q.getLastD (Side.R, 0)).2
        ≠ (q'.getLastD (Side.R, 0)).2 := by
      intro heq
      exact hne (schild_eq_of_same_last hqh hqh' hqd hqd'
        (Prod.ext (by rw [hqs, hqs']) heq))
    rw [hr1, hr2,
      show q.getLastD (Side.R, 0)
        = (Side.R, (q.getLastD (Side.R, 0)).2) from Prod.ext hqs rfl,
      show q'.getLastD (Side.R, 0)
        = (Side.R, (q'.getLastD (Side.R, 0)).2) from Prod.ext hqs' rfl]
    refine schainBefore.diverge [] _ _ _ _ ?_
    show (q'.getLastD (Side.R, 0)).2 < (q.getLastD (Side.R, 0)).2
    omega
  · intro a ha b hb
    obtain ⟨q, hq, hcq⟩ := List.mem_flatMap.mp ha
    obtain ⟨q', hq', hcq'⟩ := List.mem_flatMap.mp hb
    obtain ⟨hqh, hqd, hqs⟩ := mem_sLchilds.mp hq
    obtain ⟨hqh', hqd', hqs'⟩ := mem_sRchilds.mp hq'
    obtain ⟨r1, hr1⟩ := hsubform q a hqh hqd hcq
    obtain ⟨r2, hr2⟩ := hsubform q' b hqh' hqd' hcq'
    exact ssubtree_L_before_R (t := []) hqs hqs' hr1 hr2

/-- **Sided T-walk, membership half**: the walk emits exactly the live
chains. -/
theorem mem_swalk {L : List SChain} (hnil : [] ∉ L) {c : SChain} :
    c ∈ swalk L ↔ c ∈ L := by
  constructor
  · intro hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨q, hq, hcq⟩ := List.mem_flatMap.mp hc
      exact (swalkE_sound _ q c (mem_sLchilds.mp hq).1 hcq).1
    · obtain ⟨q, hq, hcq⟩ := List.mem_flatMap.mp hc
      exact (swalkE_sound _ q c (mem_sRchilds.mp hq).1 hcq).1
  · intro hc
    have hne : c ≠ [] := fun h => hnil (h ▸ hc)
    have hkept : c ∈ skeptL L := skept_of_live hc hne
    obtain ⟨e, cs, rfl⟩ : ∃ e cs, c = e :: cs := by
      cases c with
      | nil => exact absurd rfl hne
      | cons e cs => exact ⟨e, cs, rfl⟩
    have hq0 : ([e] : SChain) ∈ skeptL L :=
      skept_of_prefix hkept ⟨cs, rfl⟩ (by simp)
    have hq0h : sisHead L [e] = true := by
      refine sisHead_of_kept_not_fusible hq0 ?_
      cases hf : sfusible L [e] with
      | false => rfl
      | true =>
          exfalso
          have := sfusible_parent_kept hf
          exact skept_ne_nil this rfl
    rw [swalk, List.mem_append]
    have hcomp : e :: cs ∈ swalkE L (smaxLen L + 1) [e] := by
      refine swalkE_complete _ [e] _ hq0h hc hkept ⟨cs, rfl⟩ ?_
      simp
    cases hes : (([e] : SChain).getLastD (Side.R, 0)).1 with
    | L =>
        left
        exact List.mem_flatMap.mpr ⟨[e],
          mem_sLchilds.mpr ⟨hq0h, rfl, hes⟩, hcomp⟩
    | R =>
        right
        exact List.mem_flatMap.mpr ⟨[e],
          mem_sRchilds.mpr ⟨hq0h, rfl, hes⟩, hcomp⟩

/-- **Sided T-walk, packaged**: duplicate-free, exactly the live chains,
pairwise in the in-order display, hence THE display sequence. -/
theorem swalk_display (L : List SChain) (hnil : [] ∉ L) :
    (swalk L).Nodup ∧ (∀ c, c ∈ swalk L ↔ c ∈ L)
      ∧ (swalk L).Pairwise schainBefore :=
  ⟨swalk_nodup L, fun _ => mem_swalk hnil, swalk_pairwise L⟩

/-- **Sided T-walk, key form**: descending in `keyLt` on the sided
coordinates, for every ordered prefix code. -/
theorem swalk_pairwise_keyLt (Γ : OrderedPrefixCode) {L : List SChain}
    (hpos : ∀ l ∈ L, PosSChain l) (hnil : [] ∉ L) :
    (swalk L).Pairwise (fun c1 c2 =>
      keyLt (sKey (sidedCoordOf Γ c2)) (sKey (sidedCoordOf Γ c1))
        = true) := by
  refine (swalk_pairwise L).imp_of_mem ?_
  intro c1 c2 h1 h2 hb
  have hp1 : PosSChain c1 := sposChain_of_kept hpos
    (skept_of_live ((mem_swalk hnil).mp h1)
      (fun h => hnil (h ▸ ((mem_swalk hnil).mp h1))))
  have hp2 : PosSChain c2 := sposChain_of_kept hpos
    (skept_of_live ((mem_swalk hnil).mp h2)
      (fun h => hnil (h ▸ ((mem_swalk hnil).mp h2))))
  exact Sal.EmbedRGA.schainBefore_display Γ hp1 hp2 hb

/-! ## §10  Sided T-mut: merge congruence and the O(1) typing rule -/

theorem skeptL_congr {L L' : List SChain} (hmem : ∀ c, c ∈ L ↔ c ∈ L') :
    ∀ x, x ∈ skeptL L ↔ x ∈ skeptL L' := by
  intro x
  rw [mem_skeptL, mem_skeptL]
  constructor
  · rintro ⟨hne, l, hl, hp⟩
    exact ⟨hne, l, (hmem l).mp hl, hp⟩
  · rintro ⟨hne, l, hl, hp⟩
    exact ⟨hne, l, (hmem l).mpr hl, hp⟩

theorem sfusible_congr {L L' : List SChain}
    (hmem : ∀ c, c ∈ L ↔ c ∈ L') (c : SChain) :
    sfusible L c = sfusible L' c := by
  have hk := skeptL_congr hmem
  simp only [sfusible]
  rw [decide_eq_decide.mpr (hk c), decide_eq_decide.mpr (hk c.dropLast),
    decide_eq_decide.mpr (hmem c), decide_eq_decide.mpr (hmem c.dropLast),
    decide_eq_decide.mpr (show (∀ c' ∈ skeptL L, c'.dropLast = c.dropLast
        → c' = c) ↔ (∀ c' ∈ skeptL L', c'.dropLast = c.dropLast → c' = c)
      from ⟨fun h c' hc' => h c' ((hk c').mpr hc'),
        fun h c' hc' => h c' ((hk c').mp hc')⟩)]

theorem sheadOf_congr {L L' : List SChain}
    (hmem : ∀ c, c ∈ L ↔ c ∈ L') :
    ∀ n (c : SChain), c.length ≤ n → sheadOf L c = sheadOf L' c := by
  intro n
  induction n with
  | zero =>
      intro c hc
      have : c = [] := List.length_eq_zero_iff.mp (by omega)
      subst this
      rw [sheadOf_of_not_fusible, sheadOf_of_not_fusible]
      · cases hf : sfusible L' [] with
        | false => rfl
        | true => exact absurd (sfusible_ne_nil hf) (by simp)
      · cases hf : sfusible L [] with
        | false => rfl
        | true => exact absurd (sfusible_ne_nil hf) (by simp)
  | succ n ih =>
      intro c hc
      cases hf : sfusible L c with
      | true =>
          have hf' : sfusible L' c = true := by
            rw [← sfusible_congr hmem]
            exact hf
          rw [sheadOf_of_fusible hf, sheadOf_of_fusible hf']
          refine ih c.dropLast ?_
          have : c ≠ [] := sfusible_ne_nil hf
          have : 0 < c.length := List.length_pos_iff.mpr this
          rw [List.length_dropLast]
          omega
      | false =>
          have hf' : sfusible L' c = false := by
            rw [← sfusible_congr hmem]
            exact hf
          rw [sheadOf_of_not_fusible hf, sheadOf_of_not_fusible hf']

theorem sisHead_congr {L L' : List SChain}
    (hmem : ∀ c, c ∈ L ↔ c ∈ L') (c : SChain) :
    sisHead L c = sisHead L' c := by
  simp only [sisHead]
  rw [decide_eq_decide.mpr (skeptL_congr hmem c), sfusible_congr hmem]

theorem skeptL_perm {L L' : List SChain}
    (hmem : ∀ c, c ∈ L ↔ c ∈ L') : (skeptL L).Perm (skeptL L') :=
  (List.perm_ext_iff_of_nodup (nodup_skeptL L) (nodup_skeptL L')).mpr
    (skeptL_congr hmem)

theorem slenOf_congr {L L' : List SChain}
    (hmem : ∀ c, c ∈ L ↔ c ∈ L') (h : SChain) :
    slenOf L h = slenOf L' h := by
  rw [slenOf, slenOf, srunMembers, srunMembers]
  have h1 : (skeptL L).filter (fun c => sheadOf L c == h)
      = (skeptL L).filter (fun c => sheadOf L' c == h) := by
    refine List.filter_congr ?_
    intro c hc
    rw [sheadOf_congr hmem c.length c (le_refl _)]
  rw [h1]
  exact ((skeptL_perm hmem).filter _).length_eq

theorem sheadsList_congr {L L' : List SChain}
    (hmem : ∀ c, c ∈ L ↔ c ∈ L') : sheadsList L = sheadsList L' := by
  refine shLt_sorted_ext (sorted_sheadsList L) (sorted_sheadsList L') ?_
  intro c
  rw [mem_sheadsList, mem_sheadsList, sisHead_congr hmem]

/-- **Sided T-mut (merge)**: the sided table is a function of the live
sided-chain set. -/
theorem sTableOf_congr {L L' : List SChain}
    (hmem : ∀ c, c ∈ L ↔ c ∈ L') : sTableOf L = sTableOf L' := by
  rw [sTableOf, sTableOf, ← sheadsList_congr hmem]
  refine List.map_congr_left ?_
  intro h hh
  rw [sentryOfHead, sentryOfHead]
  have hk := skeptL_congr hmem h.dropLast
  by_cases hp : h.dropLast ∈ skeptL L
  · rw [if_pos hp, if_pos (hk.mp hp)]
    rw [← sheadsList_congr hmem,
      ← sheadOf_congr hmem h.dropLast.length h.dropLast (le_refl _),
      ← slenOf_congr hmem]
    have : decide (h ∈ L) = decide (h ∈ L') := decide_eq_decide.mpr (hmem h)
    rw [this]
  · rw [if_neg hp, if_neg (fun hx => hp (hk.mpr hx))]
    rw [← slenOf_congr hmem]
    have : decide (h ∈ L) = decide (h ∈ L') := decide_eq_decide.mpr (hmem h)
    rw [this]

theorem smem_skeptL_snoc {L : List SChain} {w x : SChain} :
    x ∈ skeptL (L ++ [w]) ↔ x ∈ skeptL L ∨ (x ≠ [] ∧ x <+: w) := by
  rw [mem_skeptL, mem_skeptL]
  constructor
  · rintro ⟨hne, l, hl, hp⟩
    rcases List.mem_append.mp hl with hl | hl
    · exact Or.inl ⟨hne, l, hl, hp⟩
    · rw [List.mem_singleton] at hl
      subst hl
      exact Or.inr ⟨hne, hp⟩
  · rintro (⟨hne, l, hl, hp⟩ | ⟨hne, hp⟩)
    · exact ⟨hne, l, List.mem_append_left _ hl, hp⟩
    · exact ⟨hne, w, List.mem_append_right _ (by simp), hp⟩

section SInsertExtend

variable {L : List SChain} {a : SChain}
  (ha : a ∈ L) (hnil : ([] : SChain) ∉ L)
  (hchildless : ∀ e : SEntry, (a ++ [e]) ∉ skeptL L)

include ha hnil in
theorem sextend_kept_iff (hchildless : ∀ e : SEntry, (a ++ [e]) ∉ skeptL L) :
    ∀ x, x ∈ skeptL (L ++ [a ++ [(Side.R, 1)]])
      ↔ x ∈ skeptL L ∨ x = a ++ [(Side.R, 1)] := by
  intro x
  have hane : a ≠ [] := fun h => hnil (h ▸ ha)
  rw [smem_skeptL_snoc]
  constructor
  · rintro (hx | ⟨hne, hp⟩)
    · exact Or.inl hx
    · by_cases hx : x = a ++ [(Side.R, 1)]
      · exact Or.inr hx
      · left
        have hpa : x <+: a := by
          have := sprefix_dropLast_of_ne hp hx
          rwa [List.dropLast_concat] at this
        exact skept_of_prefix (skept_of_live ha hane) hpa hne
  · rintro (hx | h1)
    · exact Or.inl hx
    · rw [h1]
      exact Or.inr ⟨by simp, List.prefix_refl _⟩

include ha hnil hchildless in
theorem sextend_fusible_old {x : SChain} (hx : x ∈ skeptL L) :
    sfusible (L ++ [a ++ [(Side.R, 1)]]) x = sfusible L x := by
  have hkiff := sextend_kept_iff ha hnil hchildless
  have hxc : x ≠ a ++ [(Side.R, 1)] := fun h => hchildless _ (h ▸ hx)
  rw [Bool.eq_iff_iff, sfusible_eq_true_iff, sfusible_eq_true_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have hd : x.dropLast ∈ skeptL L := by
      rcases (hkiff x.dropLast).mp h2 with h | h
      · exact h
      · exfalso
        apply hchildless (Side.R, 1)
        rw [← h]
        exact skept_of_prefix hx (List.dropLast_prefix x)
          (by rw [h]; simp)
    have hdc : x.dropLast ≠ a ++ [(Side.R, 1)] := fun h =>
      hchildless _ (h ▸ hd)
    refine ⟨hx, hd, h3, ?_, ?_⟩
    · intro c' hc' hpar
      exact h4 c' ((hkiff c').mpr (Or.inl hc')) hpar
    · rw [show (x ∈ L) ↔ (x ∈ L ++ [a ++ [(Side.R, 1)]]) from
        ⟨fun h => List.mem_append_left _ h,
         fun h => by
          rcases List.mem_append.mp h with h | h
          · exact h
          · rw [List.mem_singleton] at h
            exact absurd h hxc⟩]
      rw [show (x.dropLast ∈ L) ↔ (x.dropLast ∈ L ++ [a ++ [(Side.R, 1)]])
        from ⟨fun h => List.mem_append_left _ h,
         fun h => by
          rcases List.mem_append.mp h with h | h
          · exact h
          · rw [List.mem_singleton] at h
            exact absurd h hdc⟩]
      exact h5
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have hdc : x.dropLast ≠ a ++ [(Side.R, 1)] := fun h =>
      hchildless _ (h ▸ h2)
    refine ⟨(hkiff x).mpr (Or.inl hx),
      (hkiff x.dropLast).mpr (Or.inl h2), h3, ?_, ?_⟩
    · intro c' hc' hpar
      rcases (hkiff c').mp hc' with hc' | h1'
      · exact h4 c' hc' hpar
      · exfalso
        rw [h1', List.dropLast_concat] at hpar
        apply hchildless (x.getLastD (Side.R, 0))
        rw [← schild_of_parent_eq (skept_ne_nil hx) hpar.symm]
        exact hx
    · rw [show (x ∈ L ++ [a ++ [(Side.R, 1)]]) ↔ (x ∈ L) from
        ⟨fun h => by
          rcases List.mem_append.mp h with h | h
          · exact h
          · rw [List.mem_singleton] at h
            exact absurd h hxc,
         fun h => List.mem_append_left _ h⟩]
      rw [show (x.dropLast ∈ L ++ [a ++ [(Side.R, 1)]])
          ↔ (x.dropLast ∈ L) from
        ⟨fun h => by
          rcases List.mem_append.mp h with h | h
          · exact h
          · rw [List.mem_singleton] at h
            exact absurd h hdc,
         fun h => List.mem_append_left _ h⟩]
      exact h5

include ha hnil hchildless in
theorem sextend_fusible_new :
    sfusible (L ++ [a ++ [(Side.R, 1)]]) (a ++ [(Side.R, 1)]) = true := by
  have hane : a ≠ [] := fun h => hnil (h ▸ ha)
  have hkiff := sextend_kept_iff ha hnil hchildless
  rw [sfusible_eq_true_iff]
  refine ⟨(hkiff _).mpr (Or.inr rfl), ?_, ?_, ?_, ?_⟩
  · rw [List.dropLast_concat]
    exact (hkiff a).mpr (Or.inl (skept_of_live ha hane))
  · rw [List.getLastD_concat]
  · intro c' hc' hpar
    rw [List.dropLast_concat] at hpar
    rcases (hkiff c').mp hc' with hc' | h1'
    · exfalso
      apply hchildless (c'.getLastD (Side.R, 0))
      rw [← schild_of_parent_eq (skept_ne_nil hc') hpar]
      exact hc'
    · exact h1'
  · rw [List.dropLast_concat]
    constructor
    · intro _
      exact List.mem_append_left _ ha
    · intro _
      exact List.mem_append_right _ (by simp)

include ha hnil hchildless in
theorem sextend_isHead_old {x : SChain} (hx : x ∈ skeptL L) :
    sisHead (L ++ [a ++ [(Side.R, 1)]]) x = sisHead L x := by
  simp only [sisHead]
  rw [sextend_fusible_old ha hnil hchildless hx,
    decide_eq_decide.mpr (show x ∈ skeptL (L ++ [a ++ [(Side.R, 1)]])
        ↔ x ∈ skeptL L from
      ⟨fun _ => hx,
       fun _ => (sextend_kept_iff ha hnil hchildless x).mpr (Or.inl hx)⟩)]

include ha hnil hchildless in
theorem sextend_headOf_old :
    ∀ n (x : SChain), x.length ≤ n → x ∈ skeptL L →
      sheadOf (L ++ [a ++ [(Side.R, 1)]]) x = sheadOf L x := by
  intro n
  induction n with
  | zero =>
      intro x hx hkx
      exact absurd (List.length_pos_iff.mpr (skept_ne_nil hkx)) (by omega)
  | succ n ih =>
      intro x hx hkx
      cases hf : sfusible L x with
      | true =>
          rw [sheadOf_of_fusible ((sextend_fusible_old ha hnil hchildless
            hkx).trans hf), sheadOf_of_fusible hf]
          refine ih x.dropLast ?_ (sfusible_parent_kept hf)
          have : 0 < x.length := List.length_pos_iff.mpr (skept_ne_nil hkx)
          rw [List.length_dropLast]
          omega
      | false =>
          rw [sheadOf_of_not_fusible ((sextend_fusible_old ha hnil
            hchildless hkx).trans hf), sheadOf_of_not_fusible hf]

include ha hnil hchildless in
theorem sextend_headOf_new :
    sheadOf (L ++ [a ++ [(Side.R, 1)]]) (a ++ [(Side.R, 1)])
      = sheadOf L a := by
  have hane : a ≠ [] := fun h => hnil (h ▸ ha)
  rw [sheadOf_of_fusible (sextend_fusible_new ha hnil hchildless),
    List.dropLast_concat]
  exact sextend_headOf_old ha hnil hchildless a.length a (le_refl _)
    (skept_of_live ha hane)

include ha hnil hchildless in
theorem sextend_headsList :
    sheadsList (L ++ [a ++ [(Side.R, 1)]]) = sheadsList L := by
  refine shLt_sorted_ext (sorted_sheadsList _) (sorted_sheadsList _) ?_
  intro c
  rw [mem_sheadsList, mem_sheadsList]
  constructor
  · intro h
    rcases (sextend_kept_iff ha hnil hchildless c).mp (sisHead_kept h)
      with hold | h1
    · rwa [sextend_isHead_old ha hnil hchildless hold] at h
    · exfalso
      have h2 := sisHead_not_fusible h
      rw [h1, sextend_fusible_new ha hnil hchildless] at h2
      exact Bool.noConfusion h2
  · intro h
    rw [sextend_isHead_old ha hnil hchildless (sisHead_kept h)]
    exact h

include ha hnil hchildless in
theorem sextend_lenOf {h : SChain} (hh : sisHead L h = true) :
    slenOf (L ++ [a ++ [(Side.R, 1)]]) h
      = slenOf L h + (if h = sheadOf L a then 1 else 0) := by
  have hperm : (srunMembers (L ++ [a ++ [(Side.R, 1)]]) h).Perm
      (if h = sheadOf L a then (a ++ [(Side.R, 1)]) :: srunMembers L h
       else srunMembers L h) := by
    refine (List.perm_ext_iff_of_nodup ((nodup_skeptL _).filter _)
      ?_).mpr ?_
    · by_cases hcase : h = sheadOf L a
      · rw [if_pos hcase]
        exact List.Pairwise.cons
          (fun y hy heq => hchildless _
            (heq ▸ (mem_srunMembers.mp hy).1))
          ((nodup_skeptL L).filter _)
      · rw [if_neg hcase]
        exact (nodup_skeptL L).filter _
    · intro x
      simp only [List.mem_filter, beq_iff_eq]
      constructor
      · rintro ⟨hxk, hxh⟩
        rcases (sextend_kept_iff ha hnil hchildless x).mp hxk
          with hold | h1
        · rw [sextend_headOf_old ha hnil hchildless x.length x (le_refl _)
            hold] at hxh
          by_cases hcase : h = sheadOf L a
          · rw [if_pos hcase]
            exact List.mem_cons_of_mem _ (mem_srunMembers.mpr ⟨hold, hxh⟩)
          · rw [if_neg hcase]
            exact mem_srunMembers.mpr ⟨hold, hxh⟩
        · subst h1
          rw [sextend_headOf_new ha hnil hchildless] at hxh
          rw [if_pos hxh.symm]
          exact List.mem_cons_self
      · intro hx
        by_cases hcase : h = sheadOf L a
        · rw [if_pos hcase] at hx
          rcases List.mem_cons.mp hx with h1 | hx
          · rw [h1]
            exact ⟨(sextend_kept_iff ha hnil hchildless _).mpr
                (Or.inr rfl),
              by rw [sextend_headOf_new ha hnil hchildless, hcase]⟩
          · obtain ⟨hxk, hxh⟩ := mem_srunMembers.mp hx
            exact ⟨(sextend_kept_iff ha hnil hchildless x).mpr
                (Or.inl hxk),
              by rw [sextend_headOf_old ha hnil hchildless x.length x
                (le_refl _) hxk]; exact hxh⟩
        · rw [if_neg hcase] at hx
          obtain ⟨hxk, hxh⟩ := mem_srunMembers.mp hx
          exact ⟨(sextend_kept_iff ha hnil hchildless x).mpr (Or.inl hxk),
            by rw [sextend_headOf_old ha hnil hchildless x.length x
              (le_refl _) hxk]; exact hxh⟩
  have hlen := hperm.length_eq
  by_cases hcase : h = sheadOf L a
  · rw [if_pos hcase] at hlen
    rw [if_pos hcase]
    rw [slenOf, slenOf, hlen]
    simp
  · rw [if_neg hcase] at hlen
    rw [if_neg hcase]
    rw [slenOf, slenOf, hlen]
    omega

include ha hnil hchildless in
/-- **Sided T-mut (typing / insert extends a run)**: appending an `(R,1)`
child to a childless live node bumps ONE `len` field, O(1) sided table
work per keystroke. -/
theorem sTableOf_insert_extend :
    sTableOf (L ++ [a ++ [(Side.R, 1)]])
      = (sheadsList L).map (fun h =>
          if h = sheadOf L a
          then { sentryOfHead L h with len := (sentryOfHead L h).len + 1 }
          else sentryOfHead L h) := by
  rw [sTableOf, sextend_headsList ha hnil hchildless]
  refine List.map_congr_left ?_
  intro h hh
  have hhead : sisHead L h = true := mem_sheadsList.mp hh
  have hkept : h ∈ skeptL L := sisHead_kept hhead
  have hne_c : h ≠ a ++ [(Side.R, 1)] := fun heq =>
    hchildless _ (heq ▸ hkept)
  have hdne_c : h.dropLast ≠ a ++ [(Side.R, 1)] := by
    intro heq
    apply hchildless (Side.R, 1)
    rw [← heq]
    exact skept_of_prefix hkept (List.dropLast_prefix h)
      (by rw [heq]; simp)
  have hcond : (h.dropLast ∈ skeptL (L ++ [a ++ [(Side.R, 1)]]))
      ↔ (h.dropLast ∈ skeptL L) := by
    rw [sextend_kept_iff ha hnil hchildless]
    exact ⟨fun hor => hor.resolve_right (fun h' => absurd h' hdne_c),
      Or.inl⟩
  have hlive : (h ∈ L ++ [a ++ [(Side.R, 1)]]) ↔ (h ∈ L) := by
    constructor
    · intro hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hm
      · rw [List.mem_singleton] at hm
        exact absurd hm hne_c
    · exact fun hm => List.mem_append_left _ hm
  have hfields : sentryOfHead (L ++ [a ++ [(Side.R, 1)]]) h
      = { sentryOfHead L h with
          len := slenOf L h + (if h = sheadOf L a then 1 else 0) } := by
    rw [sentryOfHead, sentryOfHead]
    by_cases hp : h.dropLast ∈ skeptL L
    · rw [if_pos (hcond.mpr hp), if_pos hp]
      rw [sextend_headsList ha hnil hchildless,
        sextend_headOf_old ha hnil hchildless h.dropLast.length h.dropLast
          (le_refl _) hp,
        decide_eq_decide.mpr hlive,
        sextend_lenOf ha hnil hchildless hhead]
    · rw [if_neg (fun hx => hp (hcond.mp hx)), if_neg hp]
      rw [decide_eq_decide.mpr hlive,
        sextend_lenOf ha hnil hchildless hhead]
  rw [hfields]
  by_cases hcase : h = sheadOf L a
  · rw [if_pos hcase, if_pos hcase]
    rfl
  · rw [if_neg hcase, if_neg hcase]
    refine SRTEntry.ext' rfl rfl rfl rfl ?_
    show slenOf L h + 0 = (sentryOfHead L h).len
    rw [Nat.add_zero]
    rfl

end SInsertExtend

/-! ## §11  Sided T-walk faithfulness and the literal table walk

`schainBefore` is a strict linear order, so `Nodup` pairwise-sorted lists
are unique enumerations of their member sets; the sided walk survives the
representation round trip, and the table-DIRECT walk (`stableWalk`), entry
headers, parent refs and `shsAt` address arithmetic only, `sStateOf` never
materialized, reproduces it. -/

theorem schainBefore_cons_head {x y : SEntry} {xs ys : SChain}
    (hxy : x ≠ y) (h : schainBefore (x :: xs) (y :: ys)) :
    sEntryBefore x y := by
  rcases Sal.EmbedRGA.schainBefore_inv h with ⟨d, rest, heq⟩ |
    ⟨d, rest, heq⟩ | ⟨q, e1, e2, t1, t2, hlt, ha, hb⟩
  · rw [List.cons_append] at heq
    injection heq with h1 _
    exact absurd h1 hxy
  · rw [List.cons_append] at heq
    injection heq with h1 _
    exact absurd h1.symm hxy
  · cases q with
    | nil =>
        simp only [List.nil_append] at ha hb
        injection ha with h3 _
        injection hb with h4 _
        rw [← h3, ← h4] at hlt
        exact hlt
    | cons z q' =>
        rw [List.cons_append] at ha hb
        injection ha with h3 _
        injection hb with h4 _
        exact absurd (h3.trans h4.symm) hxy

theorem schainBefore_irrefl (x : SChain) : ¬ schainBefore x x :=
  fun h => Sal.EmbedRGA.schainBefore_ne h rfl

theorem schainBefore_asymm : ∀ {c1 c2 : SChain},
    schainBefore c1 c2 → ¬ schainBefore c2 c1 := by
  intro c1
  induction c1 with
  | nil =>
      intro c2 h h'
      obtain ⟨d, rest, heq⟩ := Sal.EmbedRGA.schainBefore_nil_left h
      obtain ⟨d', rest', heq'⟩ := Sal.EmbedRGA.schainBefore_nil_right h'
      rw [heq] at heq'
      injection heq' with h1 _
      exact absurd (congrArg Prod.fst h1) (by simp)
  | cons x xs ih =>
      intro c2 h h'
      cases c2 with
      | nil =>
          obtain ⟨d, rest, heq⟩ := Sal.EmbedRGA.schainBefore_nil_right h
          obtain ⟨d', rest', heq'⟩ := Sal.EmbedRGA.schainBefore_nil_left h'
          rw [heq] at heq'
          injection heq' with h1 _
          exact absurd (congrArg Prod.fst h1) (by simp)
      | cons y ys =>
          by_cases hxy : x = y
          · subst hxy
            exact ih (Sal.EmbedRGA.schainBefore_cons_strip h)
              (Sal.EmbedRGA.schainBefore_cons_strip h')
          · exact sEntryBefore_asymm (schainBefore_cons_head hxy h)
              (schainBefore_cons_head (Ne.symm hxy) h')

/-- **Uniqueness of the sorted sided enumeration.** -/
theorem schainBefore_sorted_ext : ∀ {l l' : List SChain},
    l.Pairwise schainBefore → l'.Pairwise schainBefore →
    (∀ c, c ∈ l ↔ c ∈ l') → l = l'
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, hmem =>
      absurd ((hmem _).mpr List.mem_cons_self) (by simp)
  | _ :: _, [], _, _, hmem =>
      absurd ((hmem _).mp List.mem_cons_self) (by simp)
  | x :: xs, y :: ys, hs, hs', hmem => by
      rcases List.pairwise_cons.mp hs with ⟨hx, hxs⟩
      rcases List.pairwise_cons.mp hs' with ⟨hy, hys⟩
      have hxy : x = y := by
        rcases List.mem_cons.mp ((hmem x).mp List.mem_cons_self) with h | h
        · exact h
        · rcases List.mem_cons.mp ((hmem y).mpr List.mem_cons_self)
            with h' | h'
          · exact h'.symm
          · exact absurd (hy x h) (schainBefore_asymm (hx y h'))
      subst hxy
      have htails : ∀ z, z ∈ xs ↔ z ∈ ys := by
        intro z
        constructor
        · intro hz
          rcases List.mem_cons.mp ((hmem z).mp (List.mem_cons_of_mem _ hz))
            with heq | h
          · rw [heq] at hz
            exact absurd (hx x hz) (schainBefore_irrefl _)
          · exact h
        · intro hz
          rcases List.mem_cons.mp ((hmem z).mpr (List.mem_cons_of_mem _ hz))
            with heq | h
          · rw [heq] at hz
            exact absurd (hy x hz) (schainBefore_irrefl _)
          · exact h
      rw [schainBefore_sorted_ext hxs hys htails]

/-- **Sided T-walk, representation round trip.** -/
theorem swalk_sStateOf_sTableOf {L : List SChain} (hnil : [] ∉ L) :
    swalk (sStateOf (sTableOf L)) = swalk L := by
  have hiff := (sStateOf_sTableOf L hnil).2
  have hnil' : [] ∉ sStateOf (sTableOf L) := fun h => hnil ((hiff []).mp h)
  refine schainBefore_sorted_ext (swalk_pairwise _) (swalk_pairwise _) ?_
  intro c
  rw [mem_swalk hnil', mem_swalk hnil]
  exact hiff c

/-! ### The literal sided table walk -/

def sentryAt (T : STable) (j : ℕ) : SRTEntry :=
  T.getD j ⟨none, false, Side.R, 0, 0⟩

theorem sentryAt_eq {T : STable} {j : ℕ} (hj : j < T.length) :
    sentryAt T j = T[j] := by
  rw [sentryAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

/-- The `L`-side attachments of entry `i`, oldest label first. -/
def sattachedAtL (T : STable) (i : ℕ) : List ℕ :=
  ((List.range T.length).filter
    (fun j => ((sentryAt T j).par.map Prod.fst == some i)
      && ((sentryAt T j).side == Side.L))).mergeSort
    (fun j k => decide ((sentryAt T j).delta ≤ (sentryAt T k).delta))

/-- The `R`-side attachments of entry `i`, newest label first. -/
def sattachedAtR (T : STable) (i : ℕ) : List ℕ :=
  ((List.range T.length).filter
    (fun j => ((sentryAt T j).par.map Prod.fst == some i)
      && ((sentryAt T j).side == Side.R))).mergeSort
    (fun j k => decide ((sentryAt T k).delta ≤ (sentryAt T j).delta))

/-- The `L`-side roots, oldest label first. -/
def srootsAtL (T : STable) : List ℕ :=
  ((List.range T.length).filter
    (fun j => ((sentryAt T j).par == none)
      && ((sentryAt T j).side == Side.L))).mergeSort
    (fun j k => decide ((sentryAt T j).delta ≤ (sentryAt T k).delta))

/-- The `R`-side roots, newest label first. -/
def srootsAtR (T : STable) : List ℕ :=
  ((List.range T.length).filter
    (fun j => ((sentryAt T j).par == none)
      && ((sentryAt T j).side == Side.R))).mergeSort
    (fun j k => decide ((sentryAt T k).delta ≤ (sentryAt T j).delta))

/-- The sided walk below one entry, consulting the table alone. -/
def swalkT (T : STable) : ℕ → ℕ → List SChain
  | 0, _ => []
  | fuel + 1, i =>
      (if (sentryAt T i).live
       then (List.range ((sentryAt T i).len - 1)).map
         (fun k => shsAt T i ++ List.replicate k (Side.R, 1))
       else [])
      ++ ((sattachedAtL T i).flatMap (swalkT T fuel)
        ++ ((if (sentryAt T i).live
             then [shsAt T i
               ++ List.replicate ((sentryAt T i).len - 1) (Side.R, 1)]
             else [])
          ++ (sattachedAtR T i).flatMap (swalkT T fuel)))

def sfuelOf (T : STable) : ℕ := (T.map SRTEntry.len).sum + 1

/-- **The literal sided T-walk**: the in-order display, emitted run by run
directly from the sided table. -/
def stableWalk (T : STable) : List SChain :=
  (srootsAtL T).flatMap (swalkT T (sfuelOf T))
    ++ (srootsAtR T).flatMap (swalkT T (sfuelOf T))

theorem mem_sattachedAtL {T : STable} {i j : ℕ} :
    j ∈ sattachedAtL T i
      ↔ j < T.length ∧ (∃ off, (sentryAt T j).par = some (i, off))
        ∧ (sentryAt T j).side = Side.L := by
  rw [sattachedAtL, List.mem_mergeSort, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    obtain ⟨h2, h3⟩ := h2
    refine ⟨h1, ?_, h3⟩
    cases hp : (sentryAt T j).par with
    | none =>
        rw [hp] at h2
        simp at h2
    | some pr =>
        obtain ⟨p1, p2⟩ := pr
        rw [hp] at h2
        simp only [Option.map_some] at h2
        injection h2 with h2
        exact ⟨p2, by rw [h2]⟩
  · rintro ⟨h1, ⟨off, h2⟩, h3⟩
    refine ⟨h1, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨by rw [h2]; rfl, h3⟩

theorem mem_sattachedAtR {T : STable} {i j : ℕ} :
    j ∈ sattachedAtR T i
      ↔ j < T.length ∧ (∃ off, (sentryAt T j).par = some (i, off))
        ∧ (sentryAt T j).side = Side.R := by
  rw [sattachedAtR, List.mem_mergeSort, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    obtain ⟨h2, h3⟩ := h2
    refine ⟨h1, ?_, h3⟩
    cases hp : (sentryAt T j).par with
    | none =>
        rw [hp] at h2
        simp at h2
    | some pr =>
        obtain ⟨p1, p2⟩ := pr
        rw [hp] at h2
        simp only [Option.map_some] at h2
        injection h2 with h2
        exact ⟨p2, by rw [h2]⟩
  · rintro ⟨h1, ⟨off, h2⟩, h3⟩
    refine ⟨h1, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨by rw [h2]; rfl, h3⟩

theorem mem_srootsAtL {T : STable} {j : ℕ} :
    j ∈ srootsAtL T
      ↔ j < T.length ∧ (sentryAt T j).par = none
        ∧ (sentryAt T j).side = Side.L := by
  rw [srootsAtL, List.mem_mergeSort, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact ⟨h1, h2.1, h2.2⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨h2, h3⟩

theorem mem_srootsAtR {T : STable} {j : ℕ} :
    j ∈ srootsAtR T
      ↔ j < T.length ∧ (sentryAt T j).par = none
        ∧ (sentryAt T j).side = Side.R := by
  rw [srootsAtR, List.mem_mergeSort, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact ⟨h1, h2.1, h2.2⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨h2, h3⟩

/-- Strictly delta-ascending sided lists are fixed by their member set. -/
theorem sdeltaAsc_sorted_ext : ∀ {l l' : List SChain},
    l.Pairwise (fun a b =>
      (a.getLastD (Side.R, 0)).2 < (b.getLastD (Side.R, 0)).2) →
    l'.Pairwise (fun a b =>
      (a.getLastD (Side.R, 0)).2 < (b.getLastD (Side.R, 0)).2) →
    (∀ c, c ∈ l ↔ c ∈ l') → l = l'
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, _, hmem =>
      absurd ((hmem y).mpr List.mem_cons_self) (by simp)
  | x :: xs, [], _, _, hmem =>
      absurd ((hmem x).mp List.mem_cons_self) (by simp)
  | x :: xs, y :: ys, hs, hs', hmem => by
      rcases List.pairwise_cons.mp hs with ⟨hx, hxs⟩
      rcases List.pairwise_cons.mp hs' with ⟨hy, hys⟩
      have hxy : x = y := by
        rcases List.mem_cons.mp ((hmem x).mp List.mem_cons_self) with h | h
        · exact h
        · rcases List.mem_cons.mp ((hmem y).mpr List.mem_cons_self)
            with h' | h'
          · exact h'.symm
          · have h1 := hy x h
            have h2 := hx y h'
            omega
      subst hxy
      have htails : ∀ z, z ∈ xs ↔ z ∈ ys := by
        intro z
        constructor
        · intro hz
          rcases List.mem_cons.mp ((hmem z).mp (List.mem_cons_of_mem _ hz))
            with heq | h
          · rw [heq] at hz
            have := hx x hz
            omega
          · exact h
        · intro hz
          rcases List.mem_cons.mp ((hmem z).mpr (List.mem_cons_of_mem _ hz))
            with heq | h
          · rw [heq] at hz
            have := hy x hz
            omega
          · exact h
      rw [sdeltaAsc_sorted_ext hxs hys htails]

/-- Strictly delta-descending sided lists are fixed by their member set. -/
theorem sdeltaDesc_sorted_ext : ∀ {l l' : List SChain},
    l.Pairwise (fun a b =>
      (b.getLastD (Side.R, 0)).2 < (a.getLastD (Side.R, 0)).2) →
    l'.Pairwise (fun a b =>
      (b.getLastD (Side.R, 0)).2 < (a.getLastD (Side.R, 0)).2) →
    (∀ c, c ∈ l ↔ c ∈ l') → l = l'
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, _, hmem =>
      absurd ((hmem y).mpr List.mem_cons_self) (by simp)
  | x :: xs, [], _, _, hmem =>
      absurd ((hmem x).mp List.mem_cons_self) (by simp)
  | x :: xs, y :: ys, hs, hs', hmem => by
      rcases List.pairwise_cons.mp hs with ⟨hx, hxs⟩
      rcases List.pairwise_cons.mp hs' with ⟨hy, hys⟩
      have hxy : x = y := by
        rcases List.mem_cons.mp ((hmem x).mp List.mem_cons_self) with h | h
        · exact h
        · rcases List.mem_cons.mp ((hmem y).mpr List.mem_cons_self)
            with h' | h'
          · exact h'.symm
          · have h1 := hy x h
            have h2 := hx y h'
            omega
      subst hxy
      have htails : ∀ z, z ∈ xs ↔ z ∈ ys := by
        intro z
        constructor
        · intro hz
          rcases List.mem_cons.mp ((hmem z).mp (List.mem_cons_of_mem _ hz))
            with heq | h
          · rw [heq] at hz
            have := hx x hz
            omega
          · exact h
        · intro hz
          rcases List.mem_cons.mp ((hmem z).mpr (List.mem_cons_of_mem _ hz))
            with heq | h
          · rw [heq] at hz
            have := hy x hz
            omega
          · exact h
      rw [sdeltaDesc_sorted_ext hxs hys htails]

open Sal.EmbedRGA.RunTable (flatMap_congr_mem flatMap_map' foldr_max_le)

theorem sLchilds_pairwise_strict (L : List SChain) (m : SChain) :
    (sLchilds L m).Pairwise (fun a b =>
      (a.getLastD (Side.R, 0)).2 < (b.getLastD (Side.R, 0)).2) := by
  have hs := (sorted_sLchilds L m).and
    (List.nodup_iff_pairwise_ne.mp (nodup_sLchilds L m))
  refine hs.imp_of_mem ?_
  intro q q' hqm hqm' hqq
  obtain ⟨hle, hne⟩ := hqq
  rcases Nat.lt_or_ge (q.getLastD (Side.R, 0)).2
    (q'.getLastD (Side.R, 0)).2 with h | h
  · exact h
  · exfalso
    obtain ⟨hqh, hqd, hqs⟩ := mem_sLchilds.mp hqm
    obtain ⟨hqh', hqd', hqs'⟩ := mem_sLchilds.mp hqm'
    have hdeq : (q.getLastD (Side.R, 0)).2
        = (q'.getLastD (Side.R, 0)).2 := by omega
    exact hne (schild_eq_of_same_last hqh hqh' hqd hqd'
      (Prod.ext (by rw [hqs, hqs']) hdeq))

theorem sRchilds_pairwise_strict (L : List SChain) (m : SChain) :
    (sRchilds L m).Pairwise (fun a b =>
      (b.getLastD (Side.R, 0)).2 < (a.getLastD (Side.R, 0)).2) := by
  have hs := (sorted_sRchilds L m).and
    (List.nodup_iff_pairwise_ne.mp (nodup_sRchilds L m))
  refine hs.imp_of_mem ?_
  intro q q' hqm hqm' hqq
  obtain ⟨hle, hne⟩ := hqq
  rcases Nat.lt_or_ge (q'.getLastD (Side.R, 0)).2
    (q.getLastD (Side.R, 0)).2 with h | h
  · exact h
  · exfalso
    obtain ⟨hqh, hqd, hqs⟩ := mem_sRchilds.mp hqm
    obtain ⟨hqh', hqd', hqs'⟩ := mem_sRchilds.mp hqm'
    have hdeq : (q.getLastD (Side.R, 0)).2
        = (q'.getLastD (Side.R, 0)).2 := by omega
    exact hne (schild_eq_of_same_last hqh hqh' hqd hqd'
      (Prod.ext (by rw [hqs, hqs']) hdeq))

theorem sattachedAtL_nodup (T : STable) (i : ℕ) :
    (sattachedAtL T i).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (List.nodup_range.filter _)

theorem sattachedAtR_nodup (T : STable) (i : ℕ) :
    (sattachedAtR T i).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (List.nodup_range.filter _)

theorem srootsAtL_nodup (T : STable) : (srootsAtL T).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (List.nodup_range.filter _)

theorem srootsAtR_nodup (T : STable) : (srootsAtR T).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (List.nodup_range.filter _)

theorem sattachedAtL_pairwise_delta (T : STable) (i : ℕ) :
    (sattachedAtL T i).Pairwise (fun j k =>
      decide ((sentryAt T j).delta ≤ (sentryAt T k).delta) = true) := by
  apply List.pairwise_mergeSort
  · intro a b c h1 h2
    rw [decide_eq_true_eq] at h1 h2 ⊢
    omega
  · intro a b
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega

theorem sattachedAtR_pairwise_delta (T : STable) (i : ℕ) :
    (sattachedAtR T i).Pairwise (fun j k =>
      decide ((sentryAt T k).delta ≤ (sentryAt T j).delta) = true) := by
  apply List.pairwise_mergeSort
  · intro a b c h1 h2
    rw [decide_eq_true_eq] at h1 h2 ⊢
    omega
  · intro a b
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega

theorem srootsAtL_pairwise_delta (T : STable) :
    (srootsAtL T).Pairwise (fun j k =>
      decide ((sentryAt T j).delta ≤ (sentryAt T k).delta) = true) := by
  apply List.pairwise_mergeSort
  · intro a b c h1 h2
    rw [decide_eq_true_eq] at h1 h2 ⊢
    omega
  · intro a b
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega

theorem srootsAtR_pairwise_delta (T : STable) :
    (srootsAtR T).Pairwise (fun j k =>
      decide ((sentryAt T k).delta ≤ (sentryAt T j).delta) = true) := by
  apply List.pairwise_mergeSort
  · intro a b c h1 h2
    rw [decide_eq_true_eq] at h1 h2 ⊢
    omega
  · intro a b
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega

theorem shsAt_getLastD {T : STable} (hC : SCanonical T) {j : ℕ}
    (hj : j < T.length) :
    (shsAt T j).getLastD (Side.R, 0) = (T[j].side, T[j].delta) := by
  cases hp : T[j].par with
  | none => rw [shsAt_none hj hp]; rfl
  | some p =>
      rw [shsAt_some hj hp (hC.par_back j hj p hp), List.getLastD_concat]

/-- `L`-side attachments map to the `L` child heads at the parent's tail,
order included. -/
theorem sattachedAtL_map_shsAt {T : STable} (hC : SCanonical T) {i : ℕ}
    (hi : i < T.length) :
    (sattachedAtL T i).map (shsAt T)
      = sLchilds (sStateOf T) (stailOf (sStateOf T) (shsAt T i)) := by
  refine sdeltaAsc_sorted_ext ?_ (sLchilds_pairwise_strict _ _) ?_
  · rw [List.pairwise_map]
    refine ((sattachedAtL_pairwise_delta T i).and
      (List.nodup_iff_pairwise_ne.mp (sattachedAtL_nodup T i))).imp_of_mem
      ?_
    intro j k hj hk hjk
    obtain ⟨hle, hne⟩ := hjk
    rw [decide_eq_true_eq] at hle
    obtain ⟨hjl, ⟨offj, hpj⟩, hsj⟩ := mem_sattachedAtL.mp hj
    obtain ⟨hkl, ⟨offk, hpk⟩, hsk⟩ := mem_sattachedAtL.mp hk
    rw [sentryAt_eq hjl] at hpj hsj
    rw [sentryAt_eq hkl] at hpk hsk
    rw [sentryAt_eq hjl, sentryAt_eq hkl] at hle
    rw [shsAt_getLastD hC hjl, shsAt_getLastD hC hkl]
    rcases Nat.lt_or_ge T[j].delta T[k].delta with h | h
    · exact h
    · exfalso
      have hdeq : T[j].delta = T[k].delta := by omega
      have hoffj : offj = T[i].len - 1 := hC.par_tail j hjl _ hpj hi
      have hoffk : offk = T[i].len - 1 := hC.par_tail k hkl _ hpk hi
      refine hne (shsAt_inj hC hjl hkl ?_)
      rw [shsAt_some hjl hpj (hC.par_back j hjl _ hpj),
        shsAt_some hkl hpk (hC.par_back k hkl _ hpk)]
      rw [hdeq, hoffj, hoffk, hsj, hsk]
  · intro c
    rw [List.mem_map, mem_sLchilds]
    constructor
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨hjl, ⟨off, hpj⟩, hsj⟩ := mem_sattachedAtL.mp hj
      rw [sentryAt_eq hjl] at hpj hsj
      have hjb : i < j := hC.par_back j hjl _ hpj
      have hform := shsAt_some hjl hpj hjb
      have hofftail : off = T[i].len - 1 := hC.par_tail j hjl _ hpj hi
      refine ⟨(sisHead_sStateOf_iff hC).mpr ⟨j, hjl, rfl⟩, ?_, ?_⟩
      · rw [hform, List.dropLast_concat, stailOf, slenOf_sStateOf hC hi,
          hofftail]
      · rw [shsAt_getLastD hC hjl]
        exact hsj
    · rintro ⟨hqh, hqd, hqs⟩
      obtain ⟨j, hjl, rfl⟩ := (sisHead_sStateOf_iff hC).mp hqh
      refine ⟨j, ?_, rfl⟩
      rw [shsAt_getLastD hC hjl] at hqs
      cases hp : T[j].par with
      | none =>
          exfalso
          have hform := shsAt_none hjl hp
          rw [hform] at hqd
          have htne : stailOf (sStateOf T) (shsAt T i) ≠ [] := by
            rw [stailOf]
            intro hnil2
            have := congrArg List.length hnil2
            simp only [List.length_append, List.length_replicate,
              List.length_nil] at this
            have h2 := List.length_pos_iff.mpr (shsAt_ne_nil hC hi)
            omega
          exact htne (by rw [← hqd]; rfl)
      | some pr =>
          have hjb := hC.par_back j hjl pr hp
          have hplen : pr.1 < T.length := by omega
          have hform := shsAt_some hjl hp hjb
          have hptail : pr.2 = T[pr.1].len - 1 :=
            hC.par_tail j hjl pr hp hplen
          rw [hform, List.dropLast_concat, stailOf,
            slenOf_sStateOf hC hi] at hqd
          have hlp : 1 ≤ T[pr.1].len :=
            hC.len_pos _ (List.getElem_mem hplen)
          have hli : 1 ≤ T[i].len := hC.len_pos _ (List.getElem_mem hi)
          obtain ⟨hpe, hoe⟩ := smemChain_inj' hC hplen (by omega) hi
            (by omega) hqd
          refine mem_sattachedAtL.mpr ⟨hjl, ⟨pr.2, ?_⟩, ?_⟩
          · rw [sentryAt_eq hjl, hp, ← hpe]
          · rw [sentryAt_eq hjl]
            exact hqs

/-- `R`-side attachments map to the `R` child heads at the parent's tail. -/
theorem sattachedAtR_map_shsAt {T : STable} (hC : SCanonical T) {i : ℕ}
    (hi : i < T.length) :
    (sattachedAtR T i).map (shsAt T)
      = sRchilds (sStateOf T) (stailOf (sStateOf T) (shsAt T i)) := by
  refine sdeltaDesc_sorted_ext ?_ (sRchilds_pairwise_strict _ _) ?_
  · rw [List.pairwise_map]
    refine ((sattachedAtR_pairwise_delta T i).and
      (List.nodup_iff_pairwise_ne.mp (sattachedAtR_nodup T i))).imp_of_mem
      ?_
    intro j k hj hk hjk
    obtain ⟨hle, hne⟩ := hjk
    rw [decide_eq_true_eq] at hle
    obtain ⟨hjl, ⟨offj, hpj⟩, hsj⟩ := mem_sattachedAtR.mp hj
    obtain ⟨hkl, ⟨offk, hpk⟩, hsk⟩ := mem_sattachedAtR.mp hk
    rw [sentryAt_eq hjl] at hpj hsj
    rw [sentryAt_eq hkl] at hpk hsk
    rw [sentryAt_eq hjl, sentryAt_eq hkl] at hle
    rw [shsAt_getLastD hC hjl, shsAt_getLastD hC hkl]
    rcases Nat.lt_or_ge T[k].delta T[j].delta with h | h
    · exact h
    · exfalso
      have hdeq : T[j].delta = T[k].delta := by omega
      have hoffj : offj = T[i].len - 1 := hC.par_tail j hjl _ hpj hi
      have hoffk : offk = T[i].len - 1 := hC.par_tail k hkl _ hpk hi
      refine hne (shsAt_inj hC hjl hkl ?_)
      rw [shsAt_some hjl hpj (hC.par_back j hjl _ hpj),
        shsAt_some hkl hpk (hC.par_back k hkl _ hpk)]
      rw [hdeq, hoffj, hoffk, hsj, hsk]
  · intro c
    rw [List.mem_map, mem_sRchilds]
    constructor
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨hjl, ⟨off, hpj⟩, hsj⟩ := mem_sattachedAtR.mp hj
      rw [sentryAt_eq hjl] at hpj hsj
      have hjb : i < j := hC.par_back j hjl _ hpj
      have hform := shsAt_some hjl hpj hjb
      have hofftail : off = T[i].len - 1 := hC.par_tail j hjl _ hpj hi
      refine ⟨(sisHead_sStateOf_iff hC).mpr ⟨j, hjl, rfl⟩, ?_, ?_⟩
      · rw [hform, List.dropLast_concat, stailOf, slenOf_sStateOf hC hi,
          hofftail]
      · rw [shsAt_getLastD hC hjl]
        exact hsj
    · rintro ⟨hqh, hqd, hqs⟩
      obtain ⟨j, hjl, rfl⟩ := (sisHead_sStateOf_iff hC).mp hqh
      refine ⟨j, ?_, rfl⟩
      rw [shsAt_getLastD hC hjl] at hqs
      cases hp : T[j].par with
      | none =>
          exfalso
          have hform := shsAt_none hjl hp
          rw [hform] at hqd
          have htne : stailOf (sStateOf T) (shsAt T i) ≠ [] := by
            rw [stailOf]
            intro hnil2
            have := congrArg List.length hnil2
            simp only [List.length_append, List.length_replicate,
              List.length_nil] at this
            have h2 := List.length_pos_iff.mpr (shsAt_ne_nil hC hi)
            omega
          exact htne (by rw [← hqd]; rfl)
      | some pr =>
          have hjb := hC.par_back j hjl pr hp
          have hplen : pr.1 < T.length := by omega
          have hform := shsAt_some hjl hp hjb
          have hptail : pr.2 = T[pr.1].len - 1 :=
            hC.par_tail j hjl pr hp hplen
          rw [hform, List.dropLast_concat, stailOf,
            slenOf_sStateOf hC hi] at hqd
          have hlp : 1 ≤ T[pr.1].len :=
            hC.len_pos _ (List.getElem_mem hplen)
          have hli : 1 ≤ T[i].len := hC.len_pos _ (List.getElem_mem hi)
          obtain ⟨hpe, hoe⟩ := smemChain_inj' hC hplen (by omega) hi
            (by omega) hqd
          refine mem_sattachedAtR.mpr ⟨hjl, ⟨pr.2, ?_⟩, ?_⟩
          · rw [sentryAt_eq hjl, hp, ← hpe]
          · rw [sentryAt_eq hjl]
            exact hqs

theorem srootsAtL_map_shsAt {T : STable} (hC : SCanonical T) :
    (srootsAtL T).map (shsAt T) = sLchilds (sStateOf T) [] := by
  refine sdeltaAsc_sorted_ext ?_ (sLchilds_pairwise_strict _ _) ?_
  · rw [List.pairwise_map]
    refine ((srootsAtL_pairwise_delta T).and
      (List.nodup_iff_pairwise_ne.mp (srootsAtL_nodup T))).imp_of_mem ?_
    intro j k hj hk hjk
    obtain ⟨hle, hne⟩ := hjk
    rw [decide_eq_true_eq] at hle
    obtain ⟨hjl, hpj, hsj⟩ := mem_srootsAtL.mp hj
    obtain ⟨hkl, hpk, hsk⟩ := mem_srootsAtL.mp hk
    rw [sentryAt_eq hjl] at hpj hsj
    rw [sentryAt_eq hkl] at hpk hsk
    rw [sentryAt_eq hjl, sentryAt_eq hkl] at hle
    rw [shsAt_getLastD hC hjl, shsAt_getLastD hC hkl]
    rcases Nat.lt_or_ge T[j].delta T[k].delta with h | h
    · exact h
    · exfalso
      have hdeq : T[j].delta = T[k].delta := by omega
      refine hne (shsAt_inj hC hjl hkl ?_)
      rw [shsAt_none hjl hpj, shsAt_none hkl hpk, hdeq, hsj, hsk]
  · intro c
    rw [List.mem_map, mem_sLchilds]
    constructor
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨hjl, hpj, hsj⟩ := mem_srootsAtL.mp hj
      rw [sentryAt_eq hjl] at hpj hsj
      refine ⟨(sisHead_sStateOf_iff hC).mpr ⟨j, hjl, rfl⟩, ?_, ?_⟩
      · rw [shsAt_none hjl hpj]
        rfl
      · rw [shsAt_getLastD hC hjl]
        exact hsj
    · rintro ⟨hqh, hqd, hqs⟩
      obtain ⟨j, hjl, rfl⟩ := (sisHead_sStateOf_iff hC).mp hqh
      refine ⟨j, ?_, rfl⟩
      rw [shsAt_getLastD hC hjl] at hqs
      refine mem_srootsAtL.mpr ⟨hjl, ?_, by rw [sentryAt_eq hjl]; exact hqs⟩
      rw [sentryAt_eq hjl]
      cases hp : T[j].par with
      | none => rfl
      | some pr =>
          exfalso
          have hjb := hC.par_back j hjl pr hp
          have hform := shsAt_some hjl hp hjb
          rw [hform, List.dropLast_concat] at hqd
          have := shsAt_ne_nil hC (show pr.1 < T.length by omega)
          cases hs : shsAt T pr.1 with
          | nil => exact this hs
          | cons a as =>
              rw [hs] at hqd
              simp at hqd

theorem srootsAtR_map_shsAt {T : STable} (hC : SCanonical T) :
    (srootsAtR T).map (shsAt T) = sRchilds (sStateOf T) [] := by
  refine sdeltaDesc_sorted_ext ?_ (sRchilds_pairwise_strict _ _) ?_
  · rw [List.pairwise_map]
    refine ((srootsAtR_pairwise_delta T).and
      (List.nodup_iff_pairwise_ne.mp (srootsAtR_nodup T))).imp_of_mem ?_
    intro j k hj hk hjk
    obtain ⟨hle, hne⟩ := hjk
    rw [decide_eq_true_eq] at hle
    obtain ⟨hjl, hpj, hsj⟩ := mem_srootsAtR.mp hj
    obtain ⟨hkl, hpk, hsk⟩ := mem_srootsAtR.mp hk
    rw [sentryAt_eq hjl] at hpj hsj
    rw [sentryAt_eq hkl] at hpk hsk
    rw [sentryAt_eq hjl, sentryAt_eq hkl] at hle
    rw [shsAt_getLastD hC hjl, shsAt_getLastD hC hkl]
    rcases Nat.lt_or_ge T[k].delta T[j].delta with h | h
    · exact h
    · exfalso
      have hdeq : T[j].delta = T[k].delta := by omega
      refine hne (shsAt_inj hC hjl hkl ?_)
      rw [shsAt_none hjl hpj, shsAt_none hkl hpk, hdeq, hsj, hsk]
  · intro c
    rw [List.mem_map, mem_sRchilds]
    constructor
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨hjl, hpj, hsj⟩ := mem_srootsAtR.mp hj
      rw [sentryAt_eq hjl] at hpj hsj
      refine ⟨(sisHead_sStateOf_iff hC).mpr ⟨j, hjl, rfl⟩, ?_, ?_⟩
      · rw [shsAt_none hjl hpj]
        rfl
      · rw [shsAt_getLastD hC hjl]
        exact hsj
    · rintro ⟨hqh, hqd, hqs⟩
      obtain ⟨j, hjl, rfl⟩ := (sisHead_sStateOf_iff hC).mp hqh
      refine ⟨j, ?_, rfl⟩
      rw [shsAt_getLastD hC hjl] at hqs
      refine mem_srootsAtR.mpr ⟨hjl, ?_, by rw [sentryAt_eq hjl]; exact hqs⟩
      rw [sentryAt_eq hjl]
      cases hp : T[j].par with
      | none => rfl
      | some pr =>
          exfalso
          have hjb := hC.par_back j hjl pr hp
          have hform := shsAt_some hjl hp hjb
          rw [hform, List.dropLast_concat] at hqd
          have := shsAt_ne_nil hC (show pr.1 < T.length by omega)
          cases hs : shsAt T pr.1 with
          | nil => exact this hs
          | cons a as =>
              rw [hs] at hqd
              simp at hqd

/-- **The sided T-walk simulation**: at matched fuel, the table-direct walk
below entry `i` IS the state walk below its head. -/
theorem swalkT_eq_swalkE {T : STable} (hC : SCanonical T) :
    ∀ fuel i, i < T.length →
      swalkT T fuel i = swalkE (sStateOf T) fuel (shsAt T i) := by
  intro fuel
  induction fuel with
  | zero =>
      intro i hi
      rfl
  | succ fuel ih =>
      intro i hi
      rw [swalkT, swalkE, sentryAt_eq hi]
      have hlive : (shsAt T i ∈ sStateOf T) ↔ T[i].live = true := by
        have := smemChain_live_iff hC hi
          (hC.len_pos _ (List.getElem_mem hi))
        simpa using this
      have hchildL : (sattachedAtL T i).flatMap (swalkT T fuel)
          = (sLchilds (sStateOf T)
              (stailOf (sStateOf T) (shsAt T i))).flatMap
              (swalkE (sStateOf T) fuel) := by
        rw [← sattachedAtL_map_shsAt hC hi, flatMap_map']
        refine flatMap_congr_mem ?_
        intro j hj
        exact ih j (mem_sattachedAtL.mp hj).1
      have hchildR : (sattachedAtR T i).flatMap (swalkT T fuel)
          = (sRchilds (sStateOf T)
              (stailOf (sStateOf T) (shsAt T i))).flatMap
              (swalkE (sStateOf T) fuel) := by
        rw [← sattachedAtR_map_shsAt hC hi, flatMap_map']
        refine flatMap_congr_mem ?_
        intro j hj
        exact ih j (mem_sattachedAtR.mp hj).1
      have htail : stailOf (sStateOf T) (shsAt T i)
          = shsAt T i ++ List.replicate (T[i].len - 1) (Side.R, 1) := by
        rw [stailOf, slenOf_sStateOf hC hi]
      rw [hchildL, hchildR, slenOf_sStateOf hC hi, htail]
      by_cases hl : T[i].live = true
      · rw [if_pos hl, if_pos hl, if_pos (hlive.mpr hl),
          if_pos (hlive.mpr hl)]
      · rw [if_neg hl, if_neg hl, if_neg (fun hm => hl (hlive.mp hm)),
          if_neg (fun hm => hl (hlive.mp hm))]

theorem shsAt_length_le {T : STable} (hC : SCanonical T) :
    ∀ i, i < T.length →
      (shsAt T i).length ≤ ((T.take i).map SRTEntry.len).sum + 1 := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
      intro hi
      cases hp : T[i].par with
      | none =>
          rw [shsAt_none hi hp]
          simp
      | some p =>
          have hpb := hC.par_back i hi p hp
          have hpl : p.1 < T.length := by omega
          rw [shsAt_some hi hp hpb]
          have h1 := ih p.1 hpb hpl
          have hp2 : p.2 = T[p.1].len - 1 := hC.par_tail i hi p hp hpl
          have hlp : 1 ≤ T[p.1].len := hC.len_pos _ (List.getElem_mem hpl)
          have hmin : min (p.1 + 1) i = p.1 + 1 := by omega
          have h2 : T.take i
              = T.take (p.1 + 1) ++ (T.take i).drop (p.1 + 1) := by
            conv_lhs => rw [← List.take_append_drop (p.1 + 1) (T.take i)]
            rw [List.take_take, hmin]
          have h3 : ((T.take i).map SRTEntry.len).sum
              = ((T.take (p.1 + 1)).map SRTEntry.len).sum
                + (((T.take i).drop (p.1 + 1)).map SRTEntry.len).sum := by
            conv_lhs => rw [h2]
            rw [List.map_append, List.sum_append]
          have h4 : T.take (p.1 + 1) = T.take p.1 ++ [T[p.1]] := by
            rw [List.take_succ, List.getElem?_eq_getElem hpl]
            rfl
          have h5 : ((T.take (p.1 + 1)).map SRTEntry.len).sum
              = ((T.take p.1).map SRTEntry.len).sum + T[p.1].len := by
            rw [h4, List.map_append, List.sum_append]
            simp
          simp only [List.length_append, List.length_replicate,
            List.length_cons, List.length_nil]
          omega

theorem smaxLen_sStateOf_le {T : STable} (hC : SCanonical T) :
    smaxLen (sStateOf T) ≤ (T.map SRTEntry.len).sum := by
  rw [smaxLen]
  refine foldr_max_le _ ?_
  intro y hy
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
  obtain ⟨i, hi, k, hk, rfl⟩ := (skept_sStateOf_iff hC).mp hc
  have h1 := shsAt_length_le hC i hi
  have h2 : ((T.take i).map SRTEntry.len).sum + T[i].len
      ≤ (T.map SRTEntry.len).sum := by
    have hdrop : T.drop i = T[i] :: T.drop (i + 1) :=
      List.drop_eq_getElem_cons hi
    have h3 : (T.map SRTEntry.len).sum
        = ((T.take i).map SRTEntry.len).sum
          + ((T.drop i).map SRTEntry.len).sum := by
      conv_lhs => rw [← List.take_append_drop i T]
      rw [List.map_append, List.sum_append]
    rw [h3, hdrop]
    simp only [List.map_cons, List.sum_cons]
    omega
  simp only [List.length_append, List.length_replicate]
  omega

theorem swalkE_fuel_ext {L : List SChain} (hnil : [] ∉ L) {h : SChain}
    (hh : sisHead L h = true) {f1 f2 : ℕ}
    (h1 : smaxLen L + 1 - h.length ≤ f1)
    (h2 : smaxLen L + 1 - h.length ≤ f2) :
    swalkE L f1 h = swalkE L f2 h := by
  refine schainBefore_sorted_ext (swalkE_pairwise f1 h hh)
    (swalkE_pairwise f2 h hh) ?_
  intro c
  have hmemf : ∀ f, smaxLen L + 1 - h.length ≤ f →
      (c ∈ swalkE L f h ↔ c ∈ L ∧ h <+: c) := by
    intro f hf
    constructor
    · intro hc
      exact swalkE_sound f h c hh hc
    · rintro ⟨hcl, hpre⟩
      exact swalkE_complete f h c hh hcl
        (skept_of_live hcl (fun hn => hnil (hn ▸ hcl))) hpre hf
  rw [hmemf f1 h1, hmemf f2 h2]

theorem sStateOf_nil_not_mem {T : STable} (hC : SCanonical T) :
    [] ∉ sStateOf T := by
  intro hm
  obtain ⟨i, hi, k, hk, heq⟩ := mem_sStateOf.mp hm
  have hne := shsAt_ne_nil hC hi
  cases hs : shsAt T i with
  | nil => exact hne hs
  | cons a as =>
      rw [hs] at heq
      simp at heq

/-- **Sided T-walk, literal (canonical tables)**: the table-direct sided
walk of any canonical sided table IS the state walk of its denotation. -/
theorem stableWalk_eq_swalk {T : STable} (hC : SCanonical T) :
    stableWalk T = swalk (sStateOf T) := by
  have hnil := sStateOf_nil_not_mem hC
  have hfuel : ∀ j, j < T.length →
      swalkT T (sfuelOf T) j
        = swalkE (sStateOf T) (smaxLen (sStateOf T) + 1) (shsAt T j) := by
    intro j hjl
    rw [swalkT_eq_swalkE hC _ j hjl]
    refine swalkE_fuel_ext hnil
      ((sisHead_sStateOf_iff hC).mpr ⟨j, hjl, rfl⟩) ?_ ?_
    · have hb := smaxLen_sStateOf_le hC
      rw [sfuelOf]
      omega
    · omega
  rw [stableWalk, swalk, ← srootsAtL_map_shsAt hC, ← srootsAtR_map_shsAt hC,
    flatMap_map', flatMap_map']
  have hL : (srootsAtL T).flatMap (swalkT T (sfuelOf T))
      = (srootsAtL T).flatMap (fun j =>
          swalkE (sStateOf T) (smaxLen (sStateOf T) + 1) (shsAt T j)) := by
    refine flatMap_congr_mem ?_
    intro j hj
    exact hfuel j (mem_srootsAtL.mp hj).1
  have hR : (srootsAtR T).flatMap (swalkT T (sfuelOf T))
      = (srootsAtR T).flatMap (fun j =>
          swalkE (sStateOf T) (smaxLen (sStateOf T) + 1) (shsAt T j)) := by
    refine flatMap_congr_mem ?_
    intro j hj
    exact hfuel j (mem_srootsAtR.mp hj).1
  rw [hL, hR]

/-- **Sided T-walk, literal: the faithfulness theorem**: build the sided
run table, read it back with the table-direct walk: the in-order display of
the live sided-chain set, verbatim. -/
theorem stableWalk_sTableOf {L : List SChain} (hnil : [] ∉ L) :
    stableWalk (sTableOf L) = swalk L :=
  (stableWalk_eq_swalk (scanonical_sTableOf L)).trans
    (swalk_sStateOf_sTableOf hnil)

/-! ## §12  The all-R projection bridge: lockstep with the one-sided table

On an all-R live set the sided development PROJECTS to the one-sided one:
the sided table is the one-sided table with `side := R` stamped on every
entry (`sTableOf_liftR`), and the sided walk is the one-sided walk lifted
(`swalk_liftR`, consuming the kernel's fragment theorem
`schainBefore_liftR`). The current embed datatype is literally the
L-uninhabited fragment of the sided development. -/

theorem liftR_dropLast (c : List ℕ) :
    (liftR c).dropLast = liftR c.dropLast := by
  simp only [liftR]
  rw [List.dropLast_eq_take, List.dropLast_eq_take, List.length_map,
    List.map_take]

theorem liftR_getLastD : ∀ (c : List ℕ) (d0 : ℕ),
    (liftR c).getLastD (Side.R, d0) = (Side.R, c.getLastD d0)
  | [], _ => rfl
  | d :: cs, d0 => by
      show ((Side.R, d) :: liftR cs).getLastD (Side.R, d0) = _
      rw [List.getLastD_cons, List.getLastD_cons]
      exact liftR_getLastD cs d

theorem liftR_ne_nil {c : List ℕ} (h : c ≠ []) : liftR c ≠ [] := by
  cases c with
  | nil => exact absurd rfl h
  | cons d ds => simp [liftR]

theorem liftR_eq_nil {c : List ℕ} (h : liftR c = []) : c = [] := by
  cases c with
  | nil => rfl
  | cons d ds => simp [liftR] at h

theorem liftR_length (c : List ℕ) : (liftR c).length = c.length := by
  simp [liftR]

theorem mem_map_liftR {L : List (List ℕ)} {c : List ℕ} :
    liftR c ∈ L.map liftR ↔ c ∈ L := by
  constructor
  · intro h
    obtain ⟨c', hc', heq⟩ := List.mem_map.mp h
    rwa [liftR_inj heq] at hc'
  · intro h
    exact List.mem_map.mpr ⟨c, h, rfl⟩

theorem mem_skeptL_liftR {L : List (List ℕ)} {x : SChain} :
    x ∈ skeptL (L.map liftR)
      ↔ ∃ c, c ∈ RunTable.keptL L ∧ x = liftR c := by
  rw [mem_skeptL]
  constructor
  · rintro ⟨hne, l, hl, hp⟩
    obtain ⟨l0, hl0, rfl⟩ := List.mem_map.mp hl
    have hxlen : x.length ≤ l0.length := by
      have := hp.length_le
      rwa [liftR_length] at this
    have hx : x = liftR (l0.take x.length) := by
      have h1 := List.prefix_iff_eq_take.mp hp
      simp only [liftR] at h1 ⊢
      conv_lhs => rw [h1]
      rw [← List.map_take]
    refine ⟨l0.take x.length, ?_, hx⟩
    refine RunTable.mem_keptL.mpr ⟨?_, l0, hl0, List.take_prefix _ _⟩
    intro hnil
    rw [hx, hnil] at hne
    exact hne rfl
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨hne, l, hl, hp⟩ := RunTable.mem_keptL.mp hc
    exact ⟨liftR_ne_nil hne, liftR l, List.mem_map.mpr ⟨l, hl, rfl⟩,
      hp.map _⟩

theorem skeptL_liftR_iff {L : List (List ℕ)} {c : List ℕ} :
    liftR c ∈ skeptL (L.map liftR) ↔ c ∈ RunTable.keptL L := by
  rw [mem_skeptL_liftR]
  constructor
  · rintro ⟨c', hc', heq⟩
    rwa [liftR_inj heq]
  · intro h
    exact ⟨c, h, rfl⟩

theorem sfusible_liftR {L : List (List ℕ)} (c : List ℕ) :
    sfusible (L.map liftR) (liftR c) = RunTable.fusible L c := by
  rw [Bool.eq_iff_iff, sfusible_eq_true_iff, RunTable.fusible_eq_true_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨skeptL_liftR_iff.mp h1, ?_, ?_, ?_, ?_⟩
    · rw [liftR_dropLast] at h2
      exact skeptL_liftR_iff.mp h2
    · rw [liftR_getLastD] at h3
      exact congrArg Prod.snd h3
    · intro c' hc' hpar
      have := h4 (liftR c') (skeptL_liftR_iff.mpr hc')
        (by rw [liftR_dropLast, liftR_dropLast, hpar])
      exact liftR_inj this
    · rw [← mem_map_liftR (L := L) (c := c),
        ← mem_map_liftR (L := L) (c := c.dropLast), ← liftR_dropLast]
      exact h5
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨skeptL_liftR_iff.mpr h1, ?_, ?_, ?_, ?_⟩
    · rw [liftR_dropLast]
      exact skeptL_liftR_iff.mpr h2
    · rw [liftR_getLastD, h3]
    · intro c'' hc'' hpar
      obtain ⟨c', hc', rfl⟩ := mem_skeptL_liftR.mp hc''
      have hpar' : c'.dropLast = c.dropLast := by
        rw [liftR_dropLast, liftR_dropLast] at hpar
        exact liftR_inj hpar
      rw [h4 c' hc' hpar']
    · rw [liftR_dropLast, mem_map_liftR, mem_map_liftR]
      exact h5

theorem sheadOf_liftR {L : List (List ℕ)} :
    ∀ (c : List ℕ),
      sheadOf (L.map liftR) (liftR c) = liftR (RunTable.headOf L c) := by
  intro c
  fun_induction RunTable.headOf L c with
  | case1 c hf ih =>
      have hf' : sfusible (L.map liftR) (liftR c) = true := by
        rw [sfusible_liftR]
        exact hf
      rw [sheadOf_of_fusible hf', liftR_dropLast]
      exact ih
  | case2 c hf =>
      have hf' : sfusible (L.map liftR) (liftR c) = false := by
        rw [sfusible_liftR]
        exact Bool.eq_false_iff.mpr hf
      exact sheadOf_of_not_fusible hf'

theorem sisHead_liftR {L : List (List ℕ)} (c : List ℕ) :
    sisHead (L.map liftR) (liftR c) = RunTable.isHead L c := by
  simp only [sisHead, RunTable.isHead]
  rw [sfusible_liftR, decide_eq_decide.mpr (skeptL_liftR_iff (L := L))]

theorem srunMembers_liftR {L : List (List ℕ)} (h : List ℕ) :
    (srunMembers (L.map liftR) (liftR h)).Perm
      ((RunTable.runMembers L h).map liftR) := by
  refine (List.perm_ext_iff_of_nodup ((nodup_skeptL _).filter _)
    ?_).mpr ?_
  · refine List.Nodup.map_on ?_ ((RunTable.nodup_keptL L).filter _)
    intro a _ b _ heq
    exact liftR_inj heq
  · intro x
    show x ∈ srunMembers (L.map liftR) (liftR h) ↔ _
    rw [mem_srunMembers, List.mem_map]
    constructor
    · rintro ⟨hk, hhd⟩
      obtain ⟨c, hc, rfl⟩ := mem_skeptL_liftR.mp hk
      refine ⟨c, RunTable.mem_runMembers.mpr ⟨hc, ?_⟩, rfl⟩
      rw [sheadOf_liftR] at hhd
      exact liftR_inj hhd
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨hck, hchd⟩ := RunTable.mem_runMembers.mp hc
      exact ⟨skeptL_liftR_iff.mpr hck, by rw [sheadOf_liftR, hchd]⟩

theorem slenOf_liftR {L : List (List ℕ)} (h : List ℕ) :
    slenOf (L.map liftR) (liftR h) = RunTable.lenOf L h := by
  rw [slenOf, RunTable.lenOf, (srunMembers_liftR h).length_eq,
    List.length_map]

theorem keyLt_sflat_liftR : ∀ {u v : List ℕ}, u.length = v.length →
    keyLt (sflat (liftR u)) (sflat (liftR v)) = keyLt u v
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
      have hlen : xs.length = ys.length := by simpa using h
      have hstep : ∀ (A B : List ℕ),
          keyLt (0 :: x :: A) (0 :: y :: B) = keyLt (x :: A) (y :: B) := by
        intro A B
        simp [Sal.EmbedRGA.keyLt]
      rw [show sflat (liftR (x :: xs)) = 0 :: x :: sflat (liftR xs)
          from rfl,
        show sflat (liftR (y :: ys)) = 0 :: y :: sflat (liftR ys)
          from rfl, hstep]
      by_cases hxy : x < y
      · simp [Sal.EmbedRGA.keyLt, hxy]
      · by_cases hyx : y < x
        · simp [Sal.EmbedRGA.keyLt, hxy, hyx]
        · have hrec := keyLt_sflat_liftR (u := xs) (v := ys) hlen
          simp [Sal.EmbedRGA.keyLt, hxy, hyx, hrec]

theorem shLt_liftR (u v : List ℕ) :
    shLt (liftR u) (liftR v) = RunTable.hLt u v := by
  simp only [shLt, Sal.EmbedRGA.RunTable.hLt, sflat_length, liftR_length]
  rcases Nat.lt_trichotomy u.length v.length with h | h | h
  · have h1 : 2 * u.length < 2 * v.length := by omega
    simp [h, h1]
  · have h1 : ¬ (2 * u.length < 2 * v.length) := by omega
    have h2 : (2 * u.length = 2 * v.length) := by omega
    have h4 : ¬ (u.length < v.length) := by omega
    simp [h, h1, h2, h4, keyLt_sflat_liftR h]
  · have h1 : ¬ (2 * u.length < 2 * v.length) := by omega
    have h2 : ¬ (2 * u.length = 2 * v.length) := by omega
    have h3 : ¬ (u.length = v.length) := by omega
    have h4 : ¬ (u.length < v.length) := by omega
    simp [h1, h2, h3, h4]

theorem sheadsList_liftR (L : List (List ℕ)) :
    sheadsList (L.map liftR) = (RunTable.headsList L).map liftR := by
  refine shLt_sorted_ext (sorted_sheadsList _) ?_ ?_
  · rw [List.pairwise_map]
    refine (RunTable.sorted_headsList L).imp ?_
    intro a b hab
    rw [shLt_liftR]
    exact hab
  · intro c
    rw [mem_sheadsList, List.mem_map]
    constructor
    · intro hc
      obtain ⟨c0, hc0, rfl⟩ := mem_skeptL_liftR.mp (sisHead_kept hc)
      rw [sisHead_liftR] at hc
      exact ⟨c0, RunTable.mem_headsList.mpr hc, rfl⟩
    · rintro ⟨c0, hc0, rfl⟩
      rw [sisHead_liftR]
      exact RunTable.mem_headsList.mp hc0

theorem sidxOf_map_liftR : ∀ (l : List (List ℕ)) (g : List ℕ),
    (l.map liftR).idxOf (liftR g) = l.idxOf g
  | [], g => rfl
  | a :: l, g => by
      simp only [List.map_cons, List.idxOf_cons]
      by_cases hag : a = g
      · subst hag
        simp
      · have h1 : (liftR a == liftR g) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          intro heq
          exact hag (liftR_inj heq)
        have h2 : (a == g) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          exact hag
        rw [h1, h2]
        simp [sidxOf_map_liftR l g]

/-- The entry embedding of the all-R fragment: stamp `side := R`. -/
def liftEntry (e : Sal.EmbedRGA.RunTable.RTEntry) : SRTEntry :=
  ⟨e.par, e.live, Side.R, e.delta, e.len⟩

/-- **The all-R projection bridge (table half)**: on an all-R live set the
sided table IS the one-sided table with the `R` side bit stamped on, the
two developments run in lockstep on the current datatype. -/
theorem sTableOf_liftR (L : List (List ℕ)) :
    sTableOf (L.map liftR)
      = (RunTable.tableOf L).map liftEntry := by
  rw [sTableOf, RunTable.tableOf, sheadsList_liftR, List.map_map,
    List.map_map]
  refine List.map_congr_left ?_
  intro h hh
  have hhL : RunTable.isHead L h = true := RunTable.mem_headsList.mp hh
  show sentryOfHead (L.map liftR) (liftR h)
    = liftEntry (RunTable.entryOfHead L h)
  have hlast := liftR_getLastD h 0
  rw [sentryOfHead, RunTable.entryOfHead, liftEntry]
  by_cases hdk : h.dropLast ∈ RunTable.keptL L
  · rw [if_pos (by rw [liftR_dropLast]; exact skeptL_liftR_iff.mpr hdk),
      if_pos hdk]
    refine SRTEntry.ext' ?_ ?_ ?_ ?_ ?_
    · show some ((sheadsList (L.map liftR)).idxOf
          (sheadOf (L.map liftR) (liftR h).dropLast),
        (liftR h).dropLast.length
          - (sheadOf (L.map liftR) (liftR h).dropLast).length) = _
      rw [liftR_dropLast, sheadOf_liftR, sheadsList_liftR,
        sidxOf_map_liftR, liftR_length, liftR_length]
    · show decide (liftR h ∈ L.map liftR) = decide (h ∈ L)
      exact decide_eq_decide.mpr mem_map_liftR
    · show ((liftR h).getLastD (Side.R, 0)).1 = Side.R
      rw [hlast]
    · show ((liftR h).getLastD (Side.R, 0)).2 = h.getLastD 0
      rw [hlast]
    · exact slenOf_liftR h
  · rw [if_neg (fun hx => hdk (skeptL_liftR_iff.mp
        (by rwa [liftR_dropLast] at hx))),
      if_neg hdk]
    refine SRTEntry.ext' rfl ?_ ?_ ?_ ?_
    · show decide (liftR h ∈ L.map liftR) = decide (h ∈ L)
      exact decide_eq_decide.mpr mem_map_liftR
    · show ((liftR h).getLastD (Side.R, 0)).1 = Side.R
      rw [hlast]
    · show ((liftR h).getLastD (Side.R, 0)).2 = h.getLastD 0
      rw [hlast]
    · exact slenOf_liftR h

/-- **The all-R projection bridge (walk half)**, consuming the kernel's
fragment theorem `schainBefore_liftR`: on an all-R live set the sided
in-order walk is the one-sided walk, lifted. -/
theorem swalk_liftR (L : List (List ℕ)) (hpos : ∀ l ∈ L, PosChain l)
    (hnil : [] ∉ L) :
    swalk (L.map liftR) = (RunTable.walk L).map liftR := by
  have hnil' : ([] : SChain) ∉ L.map liftR := by
    intro h
    obtain ⟨c, hc, heq⟩ := List.mem_map.mp h
    exact hnil ((liftR_eq_nil heq) ▸ hc)
  refine schainBefore_sorted_ext (swalk_pairwise _) ?_ ?_
  · rw [List.pairwise_map]
    refine (RunTable.walk_pairwise L).imp_of_mem ?_
    intro c1 c2 h1 h2 hb
    have hp1 : PosChain c1 := RunTable.posChain_of_kept hpos
      (RunTable.kept_of_live ((RunTable.mem_walk hnil).mp h1)
        (fun h => hnil (h ▸ (RunTable.mem_walk hnil).mp h1)))
    have hp2 : PosChain c2 := RunTable.posChain_of_kept hpos
      (RunTable.kept_of_live ((RunTable.mem_walk hnil).mp h2)
        (fun h => hnil (h ▸ (RunTable.mem_walk hnil).mp h2)))
    exact (schainBefore_liftR hp1 hp2 (RunTable.chainBefore_ne hb)).mpr hb
  · intro c
    rw [mem_swalk hnil']
    constructor
    · intro hc
      obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
      exact List.mem_map.mpr ⟨c0, (RunTable.mem_walk hnil).mpr hc0, rfl⟩
    · intro hc
      obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
      exact mem_map_liftR.mpr ((RunTable.mem_walk hnil).mp hc0)

/-! ## §13  Axiom audit -/

#print axioms stail_attachment
#print axioms Lentry_isHead
#print axioms sfusible_side_R
#print axioms sided_keyLt_iff_schainBefore
#print axioms shead_parent_is_tail
#print axioms sStateOf_sTableOf
#print axioms sTableOf_sStateOf
#print axioms scanonical_sTableOf
#print axioms scmpTable_iff_schainBefore
#print axioms scmpTable_eq_keyLt
#print axioms swalk_display
#print axioms swalk_pairwise_keyLt
#print axioms sTableOf_congr
#print axioms sTableOf_insert_extend
#print axioms swalk_sStateOf_sTableOf
#print axioms stableWalk_eq_swalk
#print axioms stableWalk_sTableOf
#print axioms sTableOf_liftR
#print axioms swalk_liftR

/-! ## §6  SPOTs: concrete sided executions, PASS + FAIL, hand-derived -/

namespace SidedRunTableSPOT

open Sal.EmbedRGA (unaryCode)

/-- Root `(R,1)` with an `R` delta-1 child (the R run). -/
def SR : List SChain := [[(Side.R, 1)], [(Side.R, 1), (Side.R, 1)]]

/-- Root `(R,1)` with, concurrently, an `L` child. -/
def SL : List SChain := [[(Side.R, 1)], [(Side.R, 1), (Side.L, 1)]]

/-- PASS: an `R` delta-1 child fuses, the uniform-R run. -/
theorem spot_R_fuses : sfusible SR [(Side.R, 1), (Side.R, 1)] = true := by
  native_decide

/-- PASS + FAIL (L stored explicitly): the `L` child does NOT fuse (contrast
the `R` child, `spot_R_fuses`), it is a head, its own entry. -/
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

/-! ### Directed sided SPOTs: the L-band mint, the band direction, the
table-direct walk, and the all-R lockstep, PASS + FAIL, hand-derived -/

/-- A node with one `L` child and one `R` child: the L-band mint case. -/
def S1 : List SChain :=
  [[(Side.R, 1)], [(Side.R, 1), (Side.L, 1)], [(Side.R, 1), (Side.R, 2)]]

/-- PASS (sided table, hand-derived): three singleton entries; the heads
sort `[(R,1)]` (shorter first), then the `R` child before the `L` child
(`sflat` tie-break `[0,1,0,2] < [0,1,1,1]`); both children attach at
`(0, 0)`; the side bit is per entry. -/
theorem spot_sided_table :
    sTableOf S1 = [⟨none, true, Side.R, 1, 1⟩,
      ⟨some (0, 0), true, Side.R, 2, 1⟩,
      ⟨some (0, 0), true, Side.L, 1, 1⟩] := by native_decide

/-- PASS (the L-band mint): in-order display, the L band, then the node,
then the R band. Hand-derived: the walk of the root run emits L-subtrees,
the tail, R-subtrees. -/
theorem spot_sided_walk :
    swalk S1 = [[(Side.R, 1), (Side.L, 1)], [(Side.R, 1)],
      [(Side.R, 1), (Side.R, 2)]] := by native_decide

/-- PASS: the table-direct sided walk agrees with the state walk on the
mint case (the concrete pin of `stableWalk_sTableOf`). -/
theorem spot_sided_tableWalk : stableWalk (sTableOf S1) = swalk S1 := by
  native_decide

/-- Two `L` children, deltas 1 and 2. -/
def S2 : List SChain :=
  [[(Side.R, 1)], [(Side.R, 1), (Side.L, 1)], [(Side.R, 1), (Side.L, 2)]]

/-- PASS + FAIL (the band direction): among `L` siblings the OLDER label
displays first, the tempting degenerate order (L band sorted like the R
band, newest first) flips the display. Hand-derived: `sEntryBefore
(L,1) (L,2)` iff `1 < 2`. -/
theorem spot_sided_L_direction :
    swalk S2 = [[(Side.R, 1), (Side.L, 1)], [(Side.R, 1), (Side.L, 2)],
      [(Side.R, 1)]]
    ∧ swalk S2 ≠ [[(Side.R, 1), (Side.L, 2)], [(Side.R, 1), (Side.L, 1)],
      [(Side.R, 1)]] := by native_decide

/-- The one-sided D1 state (`spot_d1_split`'s `L7`), as label chains. -/
def L7s : List (List ℕ) :=
  [[1], [1, 1], [1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1], [1, 1, 1, 4]]

/-- PASS (all-R lockstep, table half): on the lifted D1 state the sided
table is the one-sided D1 table (`⟨none,true,1,3⟩, ⟨some (0,2),true,1,3⟩,
⟨some (0,2),true,4,1⟩`, hand-derived in the instance SPOT) with `side := R`
stamped on every entry, the concrete pin of `sTableOf_liftR`. -/
theorem spot_allR_lockstep_table :
    sTableOf (L7s.map liftR)
      = [⟨none, true, Side.R, 1, 3⟩, ⟨some (0, 2), true, Side.R, 1, 3⟩,
         ⟨some (0, 2), true, Side.R, 4, 1⟩]
    ∧ sTableOf (L7s.map liftR)
      = (Sal.EmbedRGA.RunTable.tableOf L7s).map liftEntry := by
  native_decide

/-- PASS (all-R lockstep, walk half): the sided in-order walk of the lifted
D1 state is the one-sided walk (`abcXdef`), lifted, the concrete pin of
`swalk_liftR`. -/
theorem spot_allR_lockstep_walk :
    swalk (L7s.map liftR) = (Sal.EmbedRGA.RunTable.walk L7s).map liftR := by
  native_decide

#print axioms spot_sided_table
#print axioms spot_sided_walk
#print axioms spot_sided_tableWalk
#print axioms spot_sided_L_direction
#print axioms spot_allR_lockstep_table
#print axioms spot_allR_lockstep_walk

end SidedRunTableSPOT

end Sal.EmbedRGA.SidedRunTable
