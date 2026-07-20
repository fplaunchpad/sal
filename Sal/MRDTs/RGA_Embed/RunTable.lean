import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Induction
import Sal.MRDTs.RGA_Embed.RGA_Embed_ChainLex

/-!
# The run table — the certified representation layer of the embed RGA (#73)

Design + measurement: `whiteboard/run-table-note.md` (20.9–27.2 b/ch, 38x–141x
below fused chains); executable reference `whiteboard/litmus/run_table_measure.py`
(295k comparator checks, 150 PBT trials). This file is the pure order/
representation theory over the chain kernel; the instance-facing simulation and
the epoch composition live in
`Sal/ConditionedMRDTs/MRDT_Instances/EmbedRGA/EmbedRGA_RunTable.lean`.

The state, at kernel level, is the **list of live birth chains** (`List ℕ`
labels — the one-sided model, where the note's side condition 3 is vacuous).
The **kept tree** is the live chains plus their dead ancestors = the nonempty
prefixes of live chains (tombstone-freedom unchanged: everything else is
gone). An edge into `c` is **fusible** when `c` is the unique kept child of
its parent, its label is `1`, and it has its parent's liveness; a **run** is a
maximal fusible chain. No stability or honest-delivery hypothesis appears
anywhere in this file: every theorem is a state-level fact about a
representation change — the formal content of the measured **no-stability-gate**
finding (the settled-cut hypothesis appears exactly once, in T-epoch, in the
instance file).
-/

namespace Sal.EmbedRGA.RunTable

open Sal.EmbedRGA (keyLt keyLe key coordOf OrderedPrefixCode PosChain
  chainBefore)

/-! ## §0  The kept tree over a live chain list -/

/-- The nonempty prefixes of a chain, short to long. -/
def prefixesOf (l : List ℕ) : List (List ℕ) :=
  (List.range l.length).map (fun k => l.take (k + 1))

theorem mem_prefixesOf {l c : List ℕ} :
    c ∈ prefixesOf l ↔ c ≠ [] ∧ c <+: l := by
  simp only [prefixesOf, List.mem_map, List.mem_range]
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

/-- The kept tree: live records plus their dead ancestors, i.e. the nonempty
prefixes of live chains, deduplicated. -/
def keptL (L : List (List ℕ)) : List (List ℕ) :=
  (L.flatMap prefixesOf).dedup

theorem mem_keptL {L : List (List ℕ)} {c : List ℕ} :
    c ∈ keptL L ↔ c ≠ [] ∧ ∃ l ∈ L, c <+: l := by
  simp only [keptL, List.mem_dedup, List.mem_flatMap]
  constructor
  · rintro ⟨l, hl, hc⟩
    obtain ⟨hne, hpre⟩ := mem_prefixesOf.mp hc
    exact ⟨hne, l, hl, hpre⟩
  · rintro ⟨hne, l, hl, hpre⟩
    exact ⟨l, hl, mem_prefixesOf.mpr ⟨hne, hpre⟩⟩

theorem nodup_keptL (L : List (List ℕ)) : (keptL L).Nodup :=
  List.nodup_dedup _

theorem kept_ne_nil {L : List (List ℕ)} {c : List ℕ} (hc : c ∈ keptL L) :
    c ≠ [] := (mem_keptL.mp hc).1

theorem kept_of_prefix {L : List (List ℕ)} {c p : List ℕ}
    (hc : c ∈ keptL L) (hp : p <+: c) (hne : p ≠ []) : p ∈ keptL L := by
  obtain ⟨-, l, hl, hpre⟩ := mem_keptL.mp hc
  exact mem_keptL.mpr ⟨hne, l, hl, hp.trans hpre⟩

theorem kept_of_live {L : List (List ℕ)} {c : List ℕ}
    (hc : c ∈ L) (hne : c ≠ []) : c ∈ keptL L :=
  mem_keptL.mpr ⟨hne, c, hc, List.prefix_refl c⟩

/-! ## §1  Fusible edges, heads, and the run-ancestor walk

The note §2: the edge from `p` to its child `c` is fusible when (1) `c` is the
unique kept child of `p`, (2) `delta(c) = 1`, (3) `side(c) = R` — vacuous
one-sided — and (4) `live(c) = live(p)`. Edges out of the root sentinel are
never fusible (the parent must itself be kept). -/

/-- Fusibility of the edge into `c` (from `c.dropLast`). -/
def fusible (L : List (List ℕ)) (c : List ℕ) : Bool :=
  decide (c ∈ keptL L) && decide (c.dropLast ∈ keptL L)
    && (c.getLastD 0 == 1)
    && decide (∀ c' ∈ keptL L, c'.dropLast = c.dropLast → c' = c)
    && (decide (c ∈ L) == decide (c.dropLast ∈ L))

theorem fusible_kept {L : List (List ℕ)} {c : List ℕ}
    (h : fusible L c = true) : c ∈ keptL L := by
  simp only [fusible, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1

theorem fusible_parent_kept {L : List (List ℕ)} {c : List ℕ}
    (h : fusible L c = true) : c.dropLast ∈ keptL L := by
  simp only [fusible, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2

theorem fusible_unique {L : List (List ℕ)} {c c' : List ℕ}
    (h : fusible L c = true) (hc' : c' ∈ keptL L)
    (hpar : c'.dropLast = c.dropLast) : c' = c := by
  simp only [fusible, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2 c' hc' hpar

theorem fusible_live {L : List (List ℕ)} {c : List ℕ}
    (h : fusible L c = true) : (c ∈ L) ↔ (c.dropLast ∈ L) := by
  simp only [fusible, Bool.and_eq_true, beq_iff_eq] at h
  have := h.2
  constructor
  · intro hm
    have : decide (c ∈ L) = true := decide_eq_true hm
    rw [this] at h
    exact of_decide_eq_true h.2.symm
  · intro hm
    have hd : decide (c.dropLast ∈ L) = true := decide_eq_true hm
    rw [hd] at h
    exact of_decide_eq_true h.2

theorem fusible_ne_nil {L : List (List ℕ)} {c : List ℕ}
    (h : fusible L c = true) : c ≠ [] := kept_ne_nil (fusible_kept h)

/-- A fusible edge's chain ends in the label `1`. -/
theorem fusible_concat {L : List (List ℕ)} {c : List ℕ}
    (h : fusible L c = true) : c = c.dropLast ++ [1] := by
  rcases List.eq_nil_or_concat c with rfl | ⟨p, b, rfl⟩
  · exact absurd rfl (fusible_ne_nil h)
  · simp only [List.concat_eq_append] at h ⊢
    simp only [fusible, Bool.and_eq_true, beq_iff_eq, List.getLastD_concat] at h
    rw [List.dropLast_concat, h.1.1.2]

/-- A head: a kept node whose incoming edge is not fusible — the first member
of its run. -/
def isHead (L : List (List ℕ)) (c : List ℕ) : Bool :=
  decide (c ∈ keptL L) && !fusible L c

theorem isHead_kept {L : List (List ℕ)} {c : List ℕ}
    (h : isHead L c = true) : c ∈ keptL L := by
  simp only [isHead, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem isHead_not_fusible {L : List (List ℕ)} {c : List ℕ}
    (h : isHead L c = true) : fusible L c = false := by
  simp only [isHead, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.2

theorem isHead_of_kept_not_fusible {L : List (List ℕ)} {c : List ℕ}
    (hc : c ∈ keptL L) (hf : fusible L c = false) : isHead L c = true := by
  simp only [isHead, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  exact ⟨hc, hf⟩

/-- The run-ancestor walk: climb fusible edges to the run's head. -/
def headOf (L : List (List ℕ)) (c : List ℕ) : List ℕ :=
  if h : fusible L c = true then headOf L c.dropLast else c
  termination_by c.length
  decreasing_by
    have hne : c ≠ [] := fusible_ne_nil h
    have : 0 < c.length := List.length_pos_iff.mpr hne
    simp only [List.length_dropLast]
    omega

theorem headOf_of_fusible {L : List (List ℕ)} {c : List ℕ}
    (h : fusible L c = true) : headOf L c = headOf L c.dropLast := by
  rw [headOf, dif_pos h]

theorem headOf_of_not_fusible {L : List (List ℕ)} {c : List ℕ}
    (h : fusible L c = false) : headOf L c = c := by
  rw [headOf, dif_neg (by simp [h])]

theorem headOf_prefix (L : List (List ℕ)) (c : List ℕ) : headOf L c <+: c := by
  fun_induction headOf L c with
  | case1 c hf ih =>
      exact ih.trans (List.dropLast_prefix c)
  | case2 c hf => exact List.prefix_refl c

theorem headOf_kept {L : List (List ℕ)} {c : List ℕ} (hc : c ∈ keptL L) :
    headOf L c ∈ keptL L := by
  fun_induction headOf L c with
  | case1 c hf ih => exact ih (fusible_parent_kept hf)
  | case2 c hf => exact hc

theorem headOf_isHead {L : List (List ℕ)} {c : List ℕ} (hc : c ∈ keptL L) :
    isHead L (headOf L c) = true := by
  fun_induction headOf L c with
  | case1 c hf ih => exact ih (fusible_parent_kept hf)
  | case2 c hf =>
      exact isHead_of_kept_not_fusible hc (Bool.eq_false_iff.mpr hf)

/-- Every node is its run head extended by a block of `1` labels. -/
theorem headOf_replicate (L : List (List ℕ)) (c : List ℕ) :
    ∃ k, c = headOf L c ++ List.replicate k 1 := by
  fun_induction headOf L c with
  | case1 c hf ih =>
      obtain ⟨k, hk⟩ := ih
      refine ⟨k + 1, ?_⟩
      conv_lhs => rw [fusible_concat hf, hk]
      rw [List.replicate_succ', ← List.append_assoc]
  | case2 c hf => exact ⟨0, by simp⟩

theorem headOf_eq_self_of_isHead {L : List (List ℕ)} {h : List ℕ}
    (hh : isHead L h = true) : headOf L h = h :=
  headOf_of_not_fusible (isHead_not_fusible hh)

/-- A strict prefix is a prefix of the `dropLast`. -/
theorem prefix_dropLast_of_ne {p c : List ℕ} (hp : p <+: c) (hne : p ≠ c) :
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

/-- Run contiguity: everything between a run's head and one of its members is
in the same run. -/
theorem headOf_within {L : List (List ℕ)} {c p h : List ℕ}
    (hc : headOf L c = h) (hp1 : h <+: p) (hp2 : p <+: c) :
    headOf L p = h := by
  fun_induction headOf L c with
  | case1 c hf ih =>
      by_cases hpc : p = c
      · subst hpc
        rw [headOf_of_fusible hf]
        exact hc
      · exact ih hc (prefix_dropLast_of_ne hp2 hpc)
  | case2 c hf =>
      subst hc
      have : p = c := hp2.eq_of_length
        (Nat.le_antisymm hp2.length_le hp1.length_le)
      subst this
      exact headOf_of_not_fusible (Bool.eq_false_iff.mpr hf)

/-! ## §2  T-tail — the tail-attachment lemma

The note §3, the load-bearing discovery: **in the canonical table, every entry
attaches at its parent entry's last member.** Kernel form: a head's parent
node has no fusible successor (its run stops there), because a fusible
successor would be its *unique* kept child while the head is *another* kept
child. Consumed by: the parent-offset derivability corollary
(`head_parent_is_tail`), the comparator's case-A soundness (`cmp` below: an
entry-chain prefix really is a node ancestor), and the walk's partition
argument. No honesty, no stability, no reachability hypothesis. -/

theorem tail_attachment {L : List (List ℕ)} {h : List ℕ}
    (hh : isHead L h = true) :
    fusible L (h.dropLast ++ [1]) = false := by
  cases hf : fusible L (h.dropLast ++ [1]) with
  | false => rfl
  | true =>
      exfalso
      have hd : (h.dropLast ++ [1]).dropLast = h.dropLast :=
        List.dropLast_concat
      have heq : h = h.dropLast ++ [1] :=
        fusible_unique hf (isHead_kept hh) (by rw [hd])
      rw [← heq] at hf
      rw [isHead_not_fusible hh] at hf
      exact Bool.noConfusion hf

/-! ## §3  Runs: members, length, tail -/

/-- The members of the run headed by `h` (empty unless `h` is a head). -/
def runMembers (L : List (List ℕ)) (h : List ℕ) : List (List ℕ) :=
  (keptL L).filter (fun c => headOf L c == h)

/-- The run's length (the header's `length` field). -/
def lenOf (L : List (List ℕ)) (h : List ℕ) : ℕ := (runMembers L h).length

/-- The run's last member — where every attachment sits (T-tail). -/
def tailOf (L : List (List ℕ)) (h : List ℕ) : List ℕ :=
  h ++ List.replicate (lenOf L h - 1) 1

theorem mem_runMembers {L : List (List ℕ)} {h c : List ℕ} :
    c ∈ runMembers L h ↔ c ∈ keptL L ∧ headOf L c = h := by
  simp [runMembers, List.mem_filter]

theorem head_mem_runMembers {L : List (List ℕ)} {h : List ℕ}
    (hh : isHead L h = true) : h ∈ runMembers L h :=
  mem_runMembers.mpr ⟨isHead_kept hh, headOf_eq_self_of_isHead hh⟩

/-- Every member is the head extended by its offset in `1`s. -/
theorem runMember_form {L : List (List ℕ)} {h c : List ℕ}
    (hc : c ∈ runMembers L h) :
    c = h ++ List.replicate (c.length - h.length) 1 := by
  obtain ⟨hk, hh⟩ := mem_runMembers.mp hc
  obtain ⟨k, hform⟩ := headOf_replicate L c
  rw [hh] at hform
  have : c.length - h.length = k := by
    rw [hform]; simp
  rw [this]
  exact hform

theorem replicate_offset_inj {h : List ℕ} {j k : ℕ}
    (heq : h ++ List.replicate j 1 = h ++ List.replicate k 1) : j = k := by
  have := congrArg List.length heq
  simp at this
  exact this

/-- Downward closure inside a run. -/
theorem runMember_down {L : List (List ℕ)} {h : List ℕ} {k : ℕ}
    (hk : h ++ List.replicate (k + 1) 1 ∈ runMembers L h) :
    h ++ List.replicate k 1 ∈ runMembers L h := by
  obtain ⟨hkept, hhead⟩ := mem_runMembers.mp hk
  have hpre : h ++ List.replicate k 1 <+: h ++ List.replicate (k + 1) 1 := by
    rw [List.replicate_succ', ← List.append_assoc]
    exact List.prefix_append _ _
  have hh' : h ∈ keptL L := hhead ▸ headOf_kept hkept
  have hne : h ++ List.replicate k 1 ≠ [] := by
    intro hnil
    cases h with
    | nil => exact kept_ne_nil hh' rfl
    | cons a as => simp at hnil
  refine mem_runMembers.mpr ⟨kept_of_prefix hkept hpre hne, ?_⟩
  exact headOf_within hhead (List.prefix_append _ _) hpre

theorem runMember_down_le {L : List (List ℕ)} {h : List ℕ} :
    ∀ k, h ++ List.replicate k 1 ∈ runMembers L h →
    ∀ j ≤ k, h ++ List.replicate j 1 ∈ runMembers L h := by
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
      · exact ih (runMember_down hm) j (by omega)

/-- Non-head members' incoming edges are fusible. -/
theorem runMember_fusible {L : List (List ℕ)} {h : List ℕ} {k : ℕ}
    (hk : h ++ List.replicate (k + 1) 1 ∈ runMembers L h) :
    fusible L (h ++ List.replicate (k + 1) 1) = true := by
  obtain ⟨hkept, hhead⟩ := mem_runMembers.mp hk
  cases hf : fusible L (h ++ List.replicate (k + 1) 1) with
  | true => rfl
  | false =>
      exfalso
      have hself := headOf_of_not_fusible hf
      rw [hhead] at hself
      have hlen := congrArg List.length hself
      simp only [List.length_append, List.length_replicate] at hlen
      omega

/-- Offsets present in a run are below the run's length. -/
theorem runMember_offset_lt {L : List (List ℕ)} {h : List ℕ} {k : ℕ}
    (hk : h ++ List.replicate k 1 ∈ runMembers L h) : k < lenOf L h := by
  have hall : ∀ j ≤ k, h ++ List.replicate j 1 ∈ runMembers L h :=
    runMember_down_le k hk
  set ms : List (List ℕ) :=
    (List.range (k + 1)).map (fun j => h ++ List.replicate j 1) with hms
  have hnd : ms.Nodup := by
    refine List.Nodup.map_on ?_ (List.nodup_range)
    intro j₁ _ j₂ _ heq
    exact replicate_offset_inj heq
  have hsub : ms ⊆ runMembers L h := by
    intro c hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
    exact hall j (by simp at hj; omega)
  have hcard : ms.length ≤ (runMembers L h).length :=
    (List.subperm_of_subset hnd hsub).length_le
  have : ms.length = k + 1 := by simp [hms]
  unfold lenOf
  omega

theorem lenOf_pos {L : List (List ℕ)} {h : List ℕ}
    (hh : isHead L h = true) : 0 < lenOf L h := by
  have := head_mem_runMembers hh
  unfold lenOf
  exact List.length_pos_iff.mpr (List.ne_nil_of_mem this)

/-- Offset completeness: every offset below the run length is a member. -/
theorem runMember_of_lt {L : List (List ℕ)} {h : List ℕ}
    (hh : isHead L h = true) {k : ℕ} (hk : k < lenOf L h) :
    h ++ List.replicate k 1 ∈ runMembers L h := by
  by_contra habs
  -- every member's offset lands in (range lenOf) minus {k}: pigeonhole
  have hform : ∀ c ∈ runMembers L h,
      c = h ++ List.replicate (c.length - h.length) 1 :=
    fun c hc => runMember_form hc
  set offs : List ℕ := (runMembers L h).map (fun c => c.length - h.length)
    with hoffs
  have hnd : offs.Nodup := by
    refine List.Nodup.map_on ?_ ((nodup_keptL L).filter _)
    intro c₁ h₁ c₂ h₂ heq
    rw [hform c₁ h₁, hform c₂ h₂, heq]
  have hsub : offs ⊆ (List.range (lenOf L h)).erase k := by
    intro j hj
    rw [hoffs, List.mem_map] at hj
    obtain ⟨c, hc, rfl⟩ := hj
    have hmem : h ++ List.replicate (c.length - h.length) 1 ∈ runMembers L h :=
      (hform c hc) ▸ hc
    have hne : c.length - h.length ≠ k := fun heq => habs (heq ▸ hmem)
    rw [List.mem_erase_of_ne hne]
    exact List.mem_range.mpr (runMember_offset_lt hmem)
  have hle := (List.subperm_of_subset hnd hsub).length_le
  rw [List.length_erase_of_mem (List.mem_range.mpr hk), List.length_range]
    at hle
  have hlen : offs.length = lenOf L h := by simp [hoffs, lenOf]
  have hpos : 0 < lenOf L h := lenOf_pos hh
  omega

/-- The run-membership characterization: exactly the offsets `0 … len − 1`. -/
theorem mem_runMembers_iff {L : List (List ℕ)} {h : List ℕ}
    (hh : isHead L h = true) {c : List ℕ} :
    c ∈ runMembers L h ↔ ∃ k < lenOf L h, c = h ++ List.replicate k 1 := by
  constructor
  · intro hc
    refine ⟨c.length - h.length, ?_, runMember_form hc⟩
    exact runMember_offset_lt ((runMember_form hc) ▸ hc)
  · rintro ⟨k, hk, rfl⟩
    exact runMember_of_lt hh hk

theorem tailOf_mem {L : List (List ℕ)} {h : List ℕ}
    (hh : isHead L h = true) : tailOf L h ∈ runMembers L h :=
  runMember_of_lt hh (by have := lenOf_pos hh; omega)

/-- The tail is where the run stops: its successor edge is never fusible. -/
theorem tail_succ_not_fusible {L : List (List ℕ)} {h : List ℕ}
    (hh : isHead L h = true) :
    fusible L (tailOf L h ++ [1]) = false := by
  cases hf : fusible L (tailOf L h ++ [1]) with
  | false => rfl
  | true =>
      exfalso
      have hform : tailOf L h ++ [1] = h ++ List.replicate (lenOf L h) 1 := by
        have hpos := lenOf_pos hh
        rw [tailOf, List.append_assoc, ← List.replicate_succ']
        congr 2
        omega
      have hmem : tailOf L h ++ [1] ∈ runMembers L h := by
        refine mem_runMembers.mpr ⟨fusible_kept hf, ?_⟩
        rw [headOf_of_fusible hf, List.dropLast_concat]
        exact (mem_runMembers.mp (tailOf_mem hh)).2
      rw [hform] at hmem
      exact absurd (runMember_offset_lt hmem) (by omega)

/-- **T-tail, consequence (a)**: a head's parent node is the *tail* of the
parent run — the `parent offset` header field is derivable (parent length − 1),
exactly the note §3's accounting remark. -/
theorem head_parent_is_tail {L : List (List ℕ)} {h : List ℕ}
    (hh : isHead L h = true) (hp : h.dropLast ∈ keptL L) :
    h.dropLast = tailOf L (headOf L h.dropLast) := by
  set g := headOf L h.dropLast with hg
  have hgh : isHead L g = true := headOf_isHead hp
  have hmem : h.dropLast ∈ runMembers L g := mem_runMembers.mpr ⟨hp, hg.symm⟩
  have hform := runMember_form hmem
  set k := h.dropLast.length - g.length with hk
  have hklt : k < lenOf L g := runMember_offset_lt (hform ▸ hmem)
  have hexact : k = lenOf L g - 1 := by
    by_contra hne
    have hklt' : k + 1 < lenOf L g := by omega
    have hsucc : g ++ List.replicate (k + 1) 1 ∈ runMembers L g :=
      runMember_of_lt hgh hklt'
    have hfus : fusible L (g ++ List.replicate (k + 1) 1) = true :=
      runMember_fusible hsucc
    have hta := tail_attachment hh
    rw [hform] at hta
    rw [List.append_assoc, ← List.replicate_succ'] at hta
    rw [hfus] at hta
    exact Bool.noConfusion hta
  rw [tailOf, ← hexact]
  exact hform

theorem run_liveness_uniform_aux {L : List (List ℕ)} {h : List ℕ} :
    ∀ k, h ++ List.replicate k 1 ∈ runMembers L h →
      ((h ++ List.replicate k 1 ∈ L) ↔ (h ∈ L))
  | 0, _ => by simp
  | k + 1, hm => by
      have hfus := runMember_fusible hm
      have hdrop : (h ++ List.replicate (k + 1) 1).dropLast
          = h ++ List.replicate k 1 := by
        rw [List.replicate_succ', ← List.append_assoc, List.dropLast_concat]
      rw [fusible_live hfus, hdrop]
      exact run_liveness_uniform_aux k (runMember_down hm)

/-- **Uniform liveness along a run** (fusibility condition 4, propagated). -/
theorem run_liveness_uniform {L : List (List ℕ)} {h c : List ℕ}
    (hc : c ∈ runMembers L h) : (c ∈ L) ↔ (h ∈ L) := by
  have hform := runMember_form hc
  rw [hform]
  exact run_liveness_uniform_aux _ (hform ▸ hc)

/-! ## §4  T-repr — the indexed run table and the representation iso

The honest representation: an entry stores the note §2's accounting header —
`(liveness, parent entry ref, offset in parent, head delta, length)` — and
NOT the chain. Chains are recovered by following parent refs. **Statement
hygiene** (note §10): the iso is over **labels and liveness only** (the side
channel is vacuous in the one-sided kernel), NOT timestamps — after one
re-coding epoch labels are rank ordinals that deliberately forget time, so
an iso claiming timestamps would be false post-epoch. -/

/-- A table entry. `par = none` for a root-attached run, else
`(parent entry index, attachment offset)`. Members after the head implicitly
carry label `1`; liveness is uniform along the run. -/
structure RTEntry where
  par   : Option (ℕ × ℕ)
  live  : Bool
  delta : ℕ
  len   : ℕ
deriving DecidableEq, Repr

/-- The run table: entries in the canonical (short-lex of heads) order. -/
abbrev Table := List RTEntry

/-- Canonical enumeration order on heads: shorter first — so parent entries
precede their children — and `keyLt`-lexicographic within a length. -/
def hLt (u v : List ℕ) : Bool :=
  decide (u.length < v.length)
    || (decide (u.length = v.length) && keyLt u v)

def hLe (u v : List ℕ) : Bool := !(hLt v u)

open Sal.EmbedRGA (keyLt_irrefl keyLt_asymm keyLt_trans keyLt_total) in
theorem hLt_irrefl (u : List ℕ) : hLt u u = false := by
  simp [hLt, keyLt_irrefl]

open Sal.EmbedRGA (keyLt_irrefl keyLt_asymm keyLt_trans keyLt_total) in
theorem hLt_asymm {u v : List ℕ} (h : hLt u v = true) : hLt v u = false := by
  simp only [hLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  rcases h with h | ⟨hlen, hkey⟩
  · simp [Nat.not_lt.mpr (Nat.le_of_lt h), Nat.ne_of_gt h]
  · simp [hlen, keyLt_asymm hkey]

open Sal.EmbedRGA (keyLt_irrefl keyLt_asymm keyLt_trans keyLt_total) in
theorem hLt_trans {u v w : List ℕ} (h1 : hLt u v = true)
    (h2 : hLt v w = true) : hLt u w = true := by
  simp only [hLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    at h1 h2 ⊢
  rcases h1 with h1 | ⟨hl1, hk1⟩ <;> rcases h2 with h2 | ⟨hl2, hk2⟩
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, keyLt_trans hk1 hk2⟩

open Sal.EmbedRGA (keyLt_irrefl keyLt_asymm keyLt_trans keyLt_total) in
theorem hLt_total {u v : List ℕ} (hne : u ≠ v) :
    hLt u v = true ∨ hLt v u = true := by
  simp only [hLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  rcases Nat.lt_trichotomy u.length v.length with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases keyLt_total hne with hk | hk
    · exact Or.inl (Or.inr ⟨h, hk⟩)
    · exact Or.inr (Or.inr ⟨h.symm, hk⟩)
  · exact Or.inr (Or.inl h)

theorem hLe_total (u v : List ℕ) : (hLe u v || hLe v u) = true := by
  simp only [hLe, Bool.or_eq_true, Bool.not_eq_true']
  by_cases h : hLt v u = true
  · exact Or.inr (hLt_asymm h)
  · exact Or.inl (Bool.eq_false_iff.mpr h)

theorem hLe_trans {u v w : List ℕ} (h1 : hLe u v = true)
    (h2 : hLe v w = true) : hLe u w = true := by
  simp only [hLe, Bool.not_eq_true'] at h1 h2 ⊢
  cases hwu : hLt w u with
  | false => rfl
  | true =>
      exfalso
      rcases eq_or_ne u v with rfl | hne
      · rw [h2] at hwu
        exact Bool.noConfusion hwu
      · rcases hLt_total hne with h | h
        · rw [hLt_trans hwu h] at h2
          exact Bool.noConfusion h2
        · rw [h] at h1
          exact Bool.noConfusion h1

/-- The canonical enumeration of runs: the heads, short-lex sorted. -/
def headsList (L : List (List ℕ)) : List (List ℕ) :=
  ((keptL L).filter (fun c => isHead L c)).mergeSort hLe

theorem mem_headsList {L : List (List ℕ)} {c : List ℕ} :
    c ∈ headsList L ↔ isHead L c = true := by
  rw [headsList, List.mem_mergeSort, List.mem_filter]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨isHead_kept h, h⟩

theorem nodup_headsList (L : List (List ℕ)) : (headsList L).Nodup := by
  rw [headsList]
  exact (List.mergeSort_perm _ _).nodup_iff.mpr ((nodup_keptL L).filter _)

theorem sorted_headsList (L : List (List ℕ)) :
    (headsList L).Pairwise (fun a b => hLt a b = true) := by
  have hle : (headsList L).Pairwise (fun a b => hLe a b = true) := by
    apply List.pairwise_mergeSort
    · intro a b c h1 h2
      exact hLe_trans h1 h2
    · intro a b
      exact hLe_total a b
  have hnd := nodup_headsList L
  refine (hle.and hnd).imp ?_
  rintro a b ⟨hab, hne⟩
  simp only [hLe, Bool.not_eq_true'] at hab
  rcases hLt_total hne with h | h
  · exact h
  · rw [h] at hab
    exact Bool.noConfusion hab

/-- The entry a head compiles to: the accounting header fields, nothing else.
The parent ref is the index of the parent node's run in the canonical
enumeration; the attachment offset is stored although T-tail makes it
derivable (`head_parent_is_tail`), mirroring the note §7's accounting. -/
def entryOfHead (L : List (List ℕ)) (h : List ℕ) : RTEntry :=
  { par := if h.dropLast ∈ keptL L
      then some ((headsList L).idxOf (headOf L h.dropLast),
                 h.dropLast.length - (headOf L h.dropLast).length)
      else none,
    live := decide (h ∈ L),
    delta := h.getLastD 0,
    len := lenOf L h }

/-- The canonical run table of a state. -/
def tableOf (L : List (List ℕ)) : Table :=
  (headsList L).map (entryOfHead L)

/-- Recover an entry's head chain from the already-recovered heads of the
entries before it (parent refs point strictly backward). -/
def entryHead (heads : List (List ℕ)) (e : RTEntry) : List ℕ :=
  match e.par with
  | none => [e.delta]
  | some (i, off) => (heads.getD i []) ++ List.replicate off 1 ++ [e.delta]

/-- All entry head chains, recovered left to right. -/
def headsOf (T : Table) : List (List ℕ) :=
  T.foldl (fun acc e => acc ++ [entryHead acc e]) []

/-- The abstraction: the live chains stored in the table — each live entry
contributes its members, head chain extended by the offset in `1`s. -/
def stateOf (T : Table) : List (List ℕ) :=
  ((headsOf T).zip T).flatMap (fun p =>
    if p.2.live
    then (List.range p.2.len).map (fun k => p.1 ++ List.replicate k 1)
    else [])

theorem headsOf_append (T : Table) (S : Table) :
    headsOf (T ++ S) = S.foldl (fun acc e => acc ++ [entryHead acc e])
      (headsOf T) := by
  rw [headsOf, List.foldl_append]
  rfl

theorem headsOf_snoc (T : Table) (e : RTEntry) :
    headsOf (T ++ [e]) = headsOf T ++ [entryHead (headsOf T) e] := by
  rw [headsOf_append]
  rfl

theorem headsOf_length (T : Table) : (headsOf T).length = T.length := by
  induction T using List.reverseRecOn with
  | nil => rfl
  | append_singleton T e ih => rw [headsOf_snoc]; simp [ih]

/-- Position of an element in a strictly sorted list is order-monotone. -/
theorem idxOf_lt_of_hLt {l : List (List ℕ)}
    (hsort : l.Pairwise (fun a b => hLt a b = true)) {a b : List ℕ}
    (ha : a ∈ l) (hb : b ∈ l) (hab : hLt a b = true) :
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
    rw [hLt_irrefl] at hab
    exact Bool.noConfusion hab
  · exfalso
    have := List.pairwise_iff_getElem.mp hsort _ _ hib hia h
    rw [hga, hgb] at this
    rw [hLt_asymm this] at hab
    exact Bool.noConfusion hab

/-- In a Nodup list, `idxOf` inverts `getElem`. -/
theorem idxOf_getElem_nodup {l : List (List ℕ)} (hnd : l.Nodup)
    {i : ℕ} (hi : i < l.length) : l.idxOf l[i] = i := by
  have hm : l[i] ∈ l := List.getElem_mem hi
  have hlt : l.idxOf l[i] < l.length := List.idxOf_lt_length_of_mem hm
  have hg : l[l.idxOf l[i]] = l[i] := List.getElem_idxOf hlt
  exact (List.Nodup.getElem_inj_iff hnd).mp hg

/-- A head whose parent node is not kept sits at the root: length 1. -/
theorem head_root_singleton {L : List (List ℕ)} {h : List ℕ}
    (hh : isHead L h = true) (hp : h.dropLast ∉ keptL L) :
    ∃ d, h = [d] := by
  rcases List.eq_nil_or_concat h with rfl | ⟨p, b, rfl⟩
  · exact absurd rfl (kept_ne_nil (isHead_kept hh))
  · simp only [List.concat_eq_append] at *
    cases p with
    | nil => exact ⟨b, rfl⟩
    | cons a as =>
        exfalso
        apply hp
        rw [List.dropLast_concat]
        exact kept_of_prefix (isHead_kept hh) (List.prefix_append _ _)
          (by simp)

/-- **The recovery step**: compiling a head to its entry and recovering the
head from the previously recovered heads round-trips. This is where the
backward parent refs and the canonical order earn their keep. -/
theorem entryHead_entryOfHead {L : List (List ℕ)} {n : ℕ}
    (hn : n < (headsList L).length) :
    entryHead ((headsList L).take n) (entryOfHead L (headsList L)[n])
      = (headsList L)[n] := by
  set h := (headsList L)[n] with hh_def
  have hh : isHead L h = true :=
    mem_headsList.mp (List.getElem_mem hn)
  have hne : h ≠ [] := kept_ne_nil (isHead_kept hh)
  by_cases hp : h.dropLast ∈ keptL L
  · -- attached: recover through the parent entry
    set g := headOf L h.dropLast with hg_def
    have hgh : isHead L g = true := headOf_isHead hp
    have hgm : g ∈ headsList L := mem_headsList.mpr hgh
    have hglt : hLt g h = true := by
      have h1 : g.length ≤ h.dropLast.length := (headOf_prefix L _).length_le
      have h2 : h.dropLast.length < h.length := by
        rw [List.length_dropLast]
        have : 0 < h.length := List.length_pos_iff.mpr hne
        omega
      simp only [hLt, Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inl (by omega)
    have hidx : (headsList L).idxOf g < n := by
      have := idxOf_lt_of_hLt (sorted_headsList L) hgm
        (List.getElem_mem hn) hglt
      rwa [← hh_def, idxOf_getElem_nodup (nodup_headsList L) hn] at this
    have hidxlen : (headsList L).idxOf g < (headsList L).length :=
      List.idxOf_lt_length_of_mem hgm
    have hgetD : ((headsList L).take n).getD ((headsList L).idxOf g) [] = g := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hidx,
        List.getElem?_eq_getElem hidxlen]
      simp [List.getElem_idxOf]
    have hpar_form : g ++ List.replicate (h.dropLast.length - g.length) 1
        = h.dropLast :=
      (runMember_form (mem_runMembers.mpr ⟨hp, hg_def.symm⟩)).symm
    have hentry : entryOfHead L h =
        { par := some ((headsList L).idxOf g,
                       h.dropLast.length - g.length),
          live := decide (h ∈ L), delta := h.getLastD 0,
          len := lenOf L h } := by
      rw [entryOfHead]
      simp only [if_pos hp, ← hg_def]
    rw [hentry]
    simp only [entryHead]
    rw [hgetD, hpar_form]
    obtain ⟨p, b, hpb⟩ : ∃ p b, h = p ++ [b] := by
      rcases List.eq_nil_or_concat h with hnil | ⟨p, b, hpb⟩
      · exact absurd hnil hne
      · exact ⟨p, b, by simpa using hpb⟩
    rw [hpb, List.dropLast_concat, List.getLastD_concat]
  · -- root: the head is its own delta
    obtain ⟨d, hd⟩ := head_root_singleton hh hp
    have hentry : entryOfHead L h =
        { par := none, live := decide (h ∈ L),
          delta := h.getLastD 0, len := lenOf L h } := by
      rw [entryOfHead]
      simp only [if_neg hp]
    rw [hentry]
    simp only [entryHead]
    rw [hd]
    rfl

/-- **Head recovery**: the fold over the canonical table recovers exactly the
canonical head enumeration. -/
theorem headsOf_tableOf (L : List (List ℕ)) :
    headsOf (tableOf L) = headsList L := by
  have hlen : (tableOf L).length = (headsList L).length := by simp [tableOf]
  suffices h : ∀ n, headsOf ((tableOf L).take n) = (headsList L).take n by
    have := h (tableOf L).length
    rwa [List.take_length, hlen, List.take_length] at this
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      by_cases hlt : n < (headsList L).length
      · have hlt' : n < (tableOf L).length := by omega
        rw [List.take_succ, List.take_succ,
            List.getElem?_eq_getElem hlt', List.getElem?_eq_getElem hlt]
        simp only [Option.toList_some]
        rw [headsOf_snoc, ih]
        congr 1
        rw [show (tableOf L)[n] = entryOfHead L ((headsList L)[n]) from by
          simp [tableOf]]
        rw [entryHead_entryOfHead hlt]
      · rw [List.take_succ, List.take_succ,
            List.getElem?_eq_none (by omega),
            List.getElem?_eq_none (by omega)]
        simp [ih]

theorem stateOf_tableOf_eq (L : List (List ℕ)) :
    stateOf (tableOf L)
      = (headsList L).flatMap (fun h =>
          if decide (h ∈ L) = true
          then (List.range (lenOf L h)).map (fun k => h ++ List.replicate k 1)
          else []) := by
  have zip_map_self : ∀ {α β : Type} (f : α → β) (l : List α),
      l.zip (l.map f) = l.map (fun a => (a, f a)) := by
    intro α β f l
    induction l with
    | nil => rfl
    | cons a l ih => simp [ih]
  rw [stateOf, headsOf_tableOf, tableOf, zip_map_self, List.flatMap_map]
  simp [entryOfHead, Function.comp]

/-- Nodup of a flatMap over nodup blocks with pairwise-disjoint images. -/
theorem nodup_flatMap_of_disjoint {α β : Type} {l : List α} {f : α → List β}
    (hnd : l.Nodup) (hblock : ∀ a ∈ l, (f a).Nodup)
    (hdisj : ∀ a ∈ l, ∀ a' ∈ l, a ≠ a' → ∀ b ∈ f a, b ∉ f a') :
    (l.flatMap f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.flatMap_cons, List.nodup_append]
      have hal := List.pairwise_cons.mp hnd
      refine ⟨hblock a List.mem_cons_self, ?_, ?_⟩
      · exact ih hal.2
          (fun a' ha' => hblock a' (List.mem_cons_of_mem _ ha'))
          (fun a' ha' a'' ha'' => hdisj a' (List.mem_cons_of_mem _ ha')
            a'' (List.mem_cons_of_mem _ ha''))
      · intro b hb b' hb' heq
        subst heq
        obtain ⟨a', ha', hba'⟩ := List.mem_flatMap.mp hb'
        exact hdisj a List.mem_cons_self a' (List.mem_cons_of_mem _ ha')
          (hal.1 a' ha') b hb hba'

/-- **T-repr, losslessness direction (`stateOf ∘ tableOf = id`)**: from the
table alone — parent refs, offsets, deltas, lengths, liveness flags; no
chains, no timestamps — the exact set of live label chains is recovered.
This is the note's zero-tolerance reconstruction gate as a theorem, and the
content of the iso: **labels and liveness** (the side channel is vacuously
`R` one-sided; timestamps are deliberately not claimed, since post-epoch
labels are rank ordinals). -/
theorem stateOf_tableOf (L : List (List ℕ)) (hnil : [] ∉ L) :
    (stateOf (tableOf L)).Nodup
      ∧ (∀ c, c ∈ stateOf (tableOf L) ↔ c ∈ L) := by
  rw [stateOf_tableOf_eq]
  constructor
  · refine nodup_flatMap_of_disjoint (nodup_headsList L) ?_ ?_
    · intro h hm
      by_cases hl : decide (h ∈ L) = true
      · rw [if_pos hl]
        refine List.Nodup.map_on ?_ List.nodup_range
        intro j₁ _ j₂ _ heq
        exact replicate_offset_inj heq
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
          have hmem : h ++ List.replicate k 1 ∈ runMembers L h :=
            runMember_of_lt (mem_headsList.mp hm) hk
          have hmem' : h' ++ List.replicate k' 1 ∈ runMembers L h' :=
            runMember_of_lt (mem_headsList.mp hm') hk'
          rw [heq] at hmem'
          exact hne ((mem_runMembers.mp hmem).2.symm.trans
            (mem_runMembers.mp hmem').2)
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
        have hmem : h ++ List.replicate k 1 ∈ runMembers L h :=
          runMember_of_lt (mem_headsList.mp hm) hk
        exact (run_liveness_uniform hmem).mpr (of_decide_eq_true hl)
      · rw [if_neg hl] at hc
        simp at hc
    · intro hc
      have hne : c ≠ [] := fun h => hnil (h ▸ hc)
      have hkept : c ∈ keptL L := kept_of_live hc hne
      have hmem : c ∈ runMembers L (headOf L c) :=
        mem_runMembers.mpr ⟨hkept, rfl⟩
      refine ⟨headOf L c, mem_headsList.mpr (headOf_isHead hkept), ?_⟩
      have hlive : headOf L c ∈ L := (run_liveness_uniform hmem).mp hc
      rw [if_pos (decide_eq_true hlive)]
      refine List.mem_map.mpr ⟨c.length - (headOf L c).length, ?_,
        (runMember_form hmem).symm⟩
      rw [List.mem_range]
      exact runMember_offset_lt ((runMember_form hmem) ▸ hmem)

/-! ### Canonicity: the other direction of the iso

`Canonical` is the note §10's characterization of the canonical table —
maximal fusible chains (`no_fuse`: a lone delta-1 same-liveness attachment
would have been coalesced; D4's forced inverse rule as a *hypothesis* the
theorem cannot do without), tail attachment (`par_tail`, as a field
equation), uniform liveness (built into the entry granularity), keptness
(`leaves_live`: a dead leaf run is not kept), well-formed sibling structure
(`sib_delta`), backward parent refs, and the canonical enumeration order. -/

structure Canonical (T : Table) : Prop where
  len_pos : ∀ e ∈ T, 1 ≤ e.len
  par_back : ∀ i (hi : i < T.length) p, T[i].par = some p → p.1 < i
  par_tail : ∀ i (hi : i < T.length) p, T[i].par = some p →
    ∀ (hj : p.1 < T.length), p.2 = T[p.1].len - 1
  no_fuse : ∀ i (hi : i < T.length) p, T[i].par = some p →
    ∀ (hj : p.1 < T.length), T[i].delta = 1 → T[i].live = T[p.1].live →
    ∃ i', ∃ (_ : i' < T.length), i' ≠ i ∧ T[i'].par = some p
  leaves_live : ∀ i (hi : i < T.length), T[i].live = false →
    ∃ i', ∃ (_ : i' < T.length), ∃ off, T[i'].par = some (i, off)
  sorted : (headsOf T).Pairwise (fun a b => hLt a b = true)

theorem headsOf_prefix_append (T S : Table) :
    headsOf T <+: headsOf (T ++ S) := by
  induction S using List.reverseRecOn with
  | nil => simp
  | append_singleton S e ih =>
      rw [← List.append_assoc, headsOf_snoc]
      exact ih.trans (List.prefix_append _ _)

theorem headsOf_take (T : Table) (n : ℕ) :
    headsOf (T.take n) = (headsOf T).take n := by
  have h1 : headsOf (T.take n) <+: headsOf T := by
    conv_rhs => rw [← List.take_append_drop n T]
    exact headsOf_prefix_append _ _
  have h2 : (headsOf T).take n <+: headsOf T := List.take_prefix _ _
  have hlen : (headsOf (T.take n)).length = ((headsOf T).take n).length := by
    rw [headsOf_length, List.length_take, List.length_take, headsOf_length]
  exact (List.prefix_of_prefix_length_le h1 h2 (le_of_eq hlen)).eq_of_length
    hlen

/-- The positional recovery formula. -/
theorem headsOf_getElem (T : Table) (i : ℕ) (hi : i < T.length) :
    (headsOf T)[i]'(by rw [headsOf_length]; exact hi)
      = entryHead ((headsOf T).take i) T[i] := by
  have htake : T.take (i + 1) = T.take i ++ [T[i]] := by
    rw [List.take_succ, List.getElem?_eq_getElem hi]
    rfl
  have h1 : (headsOf T).take (i + 1)
      = (headsOf T).take i ++ [entryHead ((headsOf T).take i) T[i]] := by
    rw [← headsOf_take, htake, headsOf_snoc, headsOf_take]
  have h2 : (headsOf T).take (i + 1)
      = (headsOf T).take i
        ++ [(headsOf T)[i]'(by rw [headsOf_length]; exact hi)] := by
    rw [List.take_succ, List.getElem?_eq_getElem]
    rfl
  have := h1.symm.trans h2
  have := List.append_cancel_left this
  injection this with h _
  exact h.symm

/-- Recovered head, attached form. -/
theorem headsOf_getElem_some {T : Table} {i : ℕ} (hi : i < T.length)
    {p : ℕ × ℕ} (hp : T[i].par = some p) (hlt : p.1 < i) :
    (headsOf T)[i]'(by rw [headsOf_length]; exact hi)
      = ((headsOf T)[p.1]'(by rw [headsOf_length]; omega))
        ++ List.replicate p.2 1 ++ [T[i].delta] := by
  obtain ⟨p1, p2⟩ := p
  rw [headsOf_getElem T i hi, entryHead, hp]
  simp only []
  have hp1 : p1 < (headsOf T).length := by rw [headsOf_length]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hlt,
    List.getElem?_eq_getElem hp1]
  rfl

/-- Recovered head, root form. -/
theorem headsOf_getElem_none {T : Table} {i : ℕ} (hi : i < T.length)
    (hp : T[i].par = none) :
    (headsOf T)[i]'(by rw [headsOf_length]; exact hi) = [T[i].delta] := by
  rw [headsOf_getElem T i hi, entryHead, hp]

/-- Recovered heads are nonempty. -/
theorem headsOf_getElem_ne_nil {T : Table} {i : ℕ} (hi : i < T.length)
    (hback : ∀ p, T[i].par = some p → p.1 < i) :
    (headsOf T)[i]'(by rw [headsOf_length]; exact hi) ≠ [] := by
  cases hp : T[i].par with
  | none => rw [headsOf_getElem_none hi hp]; simp
  | some p => rw [headsOf_getElem_some hi hp (hback p hp)]; simp

/-- Recovered head of entry `i`, total form (`[]` out of range). -/
def hsAt (T : Table) (i : ℕ) : List ℕ := (headsOf T).getD i []

theorem hsAt_eq_getElem {T : Table} {i : ℕ} (hi : i < T.length) :
    hsAt T i = (headsOf T)[i]'(by rw [headsOf_length]; exact hi) := by
  rw [hsAt, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [headsOf_length]; exact hi)]
  rfl

theorem hsAt_some {T : Table} {i : ℕ} (hi : i < T.length)
    {p : ℕ × ℕ} (hp : T[i].par = some p) (hlt : p.1 < i) :
    hsAt T i = hsAt T p.1 ++ List.replicate p.2 1 ++ [T[i].delta] := by
  rw [hsAt_eq_getElem hi, hsAt_eq_getElem (by omega : p.1 < T.length)]
  exact headsOf_getElem_some hi hp hlt

theorem hsAt_none {T : Table} {i : ℕ} (hi : i < T.length)
    (hp : T[i].par = none) : hsAt T i = [T[i].delta] := by
  rw [hsAt_eq_getElem hi]
  exact headsOf_getElem_none hi hp

theorem hsAt_ne_nil {T : Table} (hC : Canonical T) {i : ℕ}
    (hi : i < T.length) : hsAt T i ≠ [] := by
  rw [hsAt_eq_getElem hi]
  exact headsOf_getElem_ne_nil hi (fun p hp => hC.par_back i hi p hp)

theorem headsOf_nodup {T : Table} (hC : Canonical T) :
    (headsOf T).Nodup :=
  hC.sorted.imp (fun {a b} hab heq => by
    subst heq
    rw [hLt_irrefl] at hab
    exact Bool.noConfusion hab)

theorem hsAt_inj {T : Table} (hC : Canonical T) {i j : ℕ}
    (hi : i < T.length) (hj : j < T.length) (heq : hsAt T i = hsAt T j) :
    i = j := by
  rw [hsAt_eq_getElem hi, hsAt_eq_getElem hj] at heq
  exact (List.Nodup.getElem_inj_iff (headsOf_nodup hC)).mp heq

/-- Take out of a padded chain. -/
theorem take_append_replicate {h : List ℕ} {r k : ℕ} (hrk : r ≤ k) :
    (h ++ List.replicate k 1).take (h.length + r)
      = h ++ List.replicate r 1 := by
  rw [List.take_append, List.take_of_length_le (by omega)]
  congr 1
  rw [show h.length + r - h.length = r by omega, List.take_replicate]
  congr 1
  omega

/-- Dropping the last `1` of a padded chain. -/
theorem dropLast_append_replicate_succ {h : List ℕ} {r : ℕ} :
    (h ++ List.replicate (r + 1) 1).dropLast = h ++ List.replicate r 1 := by
  rw [List.replicate_succ', ← List.append_assoc, List.dropLast_concat]

theorem getLastD_append_replicate_succ {h : List ℕ} {r : ℕ} :
    (h ++ List.replicate (r + 1) 1).getLastD 0 = 1 := by
  rw [List.replicate_succ', ← List.append_assoc, List.getLastD_concat]

theorem getLastD_append_replicate_pos {h : List ℕ} {r : ℕ} (hr : 1 ≤ r) :
    (h ++ List.replicate r 1).getLastD 0 = 1 := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  exact getLastD_append_replicate_succ

theorem dropLast_append_replicate_pos {h : List ℕ} {r : ℕ} (hr : 1 ≤ r) :
    (h ++ List.replicate r 1).dropLast = h ++ List.replicate (r - 1) 1 := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [dropLast_append_replicate_succ]
  simp

/-- **Member-chain uniqueness** — the engine of canonicity. A kept chain
decodes to a unique `(entry, offset)` address. The killing blow in the
overlap case is *tail attachment* (`par_tail`): a delta-1 child hangs at its
parent's tail, so a member sitting past the tail would exceed the parent's
length. -/
theorem memChain_inj {T : Table} (hC : Canonical T) :
    ∀ n (c : List ℕ), c.length ≤ n →
    ∀ i (_ : i < T.length) k (_ : k < T[i].len)
      (_ : c = hsAt T i ++ List.replicate k 1)
      j (_ : j < T.length) m (_ : m < T[j].len)
      (_ : c = hsAt T j ++ List.replicate m 1),
    i = j ∧ k = m := by
  intro n
  induction n with
  | zero =>
      intro c hc i hi k hk hci j hj m hm hcj
      exfalso
      apply hsAt_ne_nil hC hi
      have : c = [] := List.length_eq_zero_iff.mp (by omega)
      rw [this] at hci
      cases hs : hsAt T i with
      | nil => rfl
      | cons a as => rw [hs] at hci; simp at hci
  | succ n ih =>
      intro c hc i hi k hk hci j hj m hm hcj
      -- the asymmetric overlap case, factored
      have step : ∀ i' (_ : i' < T.length) k' (_ : k' < T[i'].len)
          (_ : c = hsAt T i' ++ List.replicate k' 1)
          j' (_ : j' < T.length) m' (_ : m' < T[j'].len)
          (_ : c = hsAt T j' ++ List.replicate m' 1),
          (hsAt T i').length < (hsAt T j').length → False := by
        intro i' hi' k' hk' hci' j' hj' m' hm' hcj' hlen
        set r := (hsAt T j').length - (hsAt T i').length with hr
        have hr1 : 1 ≤ r := by omega
        have hclen : c.length = (hsAt T i').length + k' := by
          rw [hci']; simp
        have hrk : r ≤ k' := by
          have : (hsAt T j').length ≤ c.length := by
            rw [hcj']; simp
          omega
        have hjform : hsAt T j' = hsAt T i' ++ List.replicate r 1 := by
          have h1 : hsAt T j' = c.take (hsAt T j').length := by
            rw [hcj', List.take_append,
              List.take_of_length_le (by omega),
              show (hsAt T j').length - (hsAt T j').length = 0 by omega]
            simp
          rw [h1, hci', show (hsAt T j').length = (hsAt T i').length + r
            by omega]
          exact take_append_replicate hrk
        cases hp : T[j'].par with
        | none =>
            have := hsAt_none hj' hp
            rw [this] at hjform
            have hlen1 := congrArg List.length hjform
            simp at hlen1
            have : hsAt T i' ≠ [] := hsAt_ne_nil hC hi'
            have : 1 ≤ (hsAt T i').length :=
              List.length_pos_iff.mpr this
            omega
        | some p =>
            have hpb : p.1 < j' := hC.par_back j' hj' p hp
            have hpl : p.1 < T.length := by omega
            have hjs : hsAt T j'
                = hsAt T p.1 ++ List.replicate p.2 1 ++ [T[j'].delta] :=
              hsAt_some hj' hp hpb
            -- the branch label is 1
            have hdelta : T[j'].delta = 1 := by
              have h1 : (hsAt T j').getLastD 0 = T[j'].delta := by
                rw [hjs, List.getLastD_concat]
              have h2 : (hsAt T j').getLastD 0 = 1 := by
                rw [hjform]
                exact getLastD_append_replicate_pos hr1
              omega
            -- the shared parent node, two ways
            have hq : hsAt T i' ++ List.replicate (r - 1) 1
                = hsAt T p.1 ++ List.replicate p.2 1 := by
              have h1 : (hsAt T j').dropLast
                  = hsAt T i' ++ List.replicate (r - 1) 1 := by
                rw [hjform]
                exact dropLast_append_replicate_pos hr1
              have h2 : (hsAt T j').dropLast
                  = hsAt T p.1 ++ List.replicate p.2 1 := by
                rw [hjs, List.dropLast_concat]
              rw [← h1, h2]
            have hp2 : p.2 = T[p.1].len - 1 := hC.par_tail j' hj' p hp hpl
            have hplen : 1 ≤ T[p.1].len :=
              hC.len_pos _ (List.getElem_mem hpl)
            have hqlen : (hsAt T i' ++ List.replicate (r - 1) 1).length ≤ n := by
              have : 1 ≤ (hsAt T i').length :=
                List.length_pos_iff.mpr (hsAt_ne_nil hC hi')
              simp only [List.length_append, List.length_replicate]
              omega
            have := ih (hsAt T i' ++ List.replicate (r - 1) 1) hqlen
              i' hi' (r - 1) (by omega) rfl
              p.1 hpl p.2 (by omega) hq
            obtain ⟨hip, hrp⟩ := this
            -- tail attachment: r = parent len, but r ≤ k' < parent len
            subst hip
            omega
      rcases Nat.lt_trichotomy (hsAt T i).length (hsAt T j).length
        with hlen | hlen | hlen
      · exact absurd (step i hi k hk hci j hj m hm hcj hlen) (fun h => h)
      · have hheads : hsAt T i = hsAt T j := by
          have h1 : hsAt T i = c.take (hsAt T i).length := by
            rw [hci, List.take_append,
              List.take_of_length_le (le_refl _)]
            simp
          have h2 : hsAt T j = c.take (hsAt T j).length := by
            rw [hcj, List.take_append,
              List.take_of_length_le (le_refl _)]
            simp
          rw [h1, h2, hlen]
        have hij : i = j := hsAt_inj hC hi hj hheads
        subst hij
        rw [hci, hheads] at hcj
        exact ⟨rfl, replicate_offset_inj hcj⟩
      · exact absurd (step j hj m hm hcj i hi k hk hci hlen) (fun h => h)

/-- Membership in `stateOf`: exactly the live entries' member chains. -/
theorem mem_stateOf {T : Table} {c : List ℕ} :
    c ∈ stateOf T ↔ ∃ i, ∃ (_ : i < T.length), ∃ k, k < T[i].len ∧
      T[i].live = true ∧ c = hsAt T i ++ List.replicate k 1 := by
  rw [stateOf, List.mem_flatMap]
  constructor
  · rintro ⟨⟨h, e⟩, hmem, hc⟩
    obtain ⟨i, hi, hpair⟩ := List.mem_iff_getElem.mp hmem
    have hilen : i < T.length := by
      have := hi
      simp only [List.length_zip, headsOf_length] at this
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
      · rw [hsAt_eq_getElem hilen, ← hph]
    · rw [if_neg hl] at hc
      simp at hc
  · rintro ⟨i, hi, k, hk, hlive, rfl⟩
    refine ⟨((headsOf T)[i]'(by rw [headsOf_length]; exact hi), T[i]),
      ?_, ?_⟩
    · exact List.mem_iff_getElem.mpr ⟨i,
        by simp [List.length_zip, headsOf_length]; omega,
        by rw [List.getElem_zip]⟩
    · rw [if_pos hlive]
      refine List.mem_map.mpr ⟨k, List.mem_range.mpr hk, ?_⟩
      rw [hsAt_eq_getElem hi]

/-- Every member chain extends to a live chain of the state (`leaves_live`
descending). -/
theorem memChain_extends_live {T : Table} (hC : Canonical T) :
    ∀ d i (hi : i < T.length), T.length - i ≤ d →
    ∀ k, k < T[i].len →
    ∃ l ∈ stateOf T, hsAt T i ++ List.replicate k 1 <+: l := by
  intro d
  induction d with
  | zero => intro i hi hd; omega
  | succ d ih =>
      intro i hi hd k hk
      cases hlive : T[i].live with
      | true =>
          exact ⟨hsAt T i ++ List.replicate k 1,
            mem_stateOf.mpr ⟨i, hi, k, hk, hlive, rfl⟩, List.prefix_refl _⟩
      | false =>
          obtain ⟨i', hi', off, hpar⟩ := hC.leaves_live i hi hlive
          have hlt : i < i' := hC.par_back i' hi' (i, off) hpar
          have hoff : off = T[i].len - 1 := hC.par_tail i' hi' (i, off) hpar hi
          have hform : hsAt T i' = hsAt T i ++ List.replicate off 1
              ++ [T[i'].delta] := hsAt_some hi' hpar hlt
          obtain ⟨l, hl, hpre⟩ := ih i' hi' (by omega) 0
            (hC.len_pos _ (List.getElem_mem hi'))
          refine ⟨l, hl, ?_⟩
          have h1 : hsAt T i ++ List.replicate k 1
              <+: hsAt T i ++ List.replicate off 1 := by
            have : List.replicate off 1
                = List.replicate k 1 ++ List.replicate (off - k) 1 := by
              rw [← List.replicate_add]
              congr 1
              omega
            rw [this, ← List.append_assoc]
            exact List.prefix_append _ _
          have h2 : hsAt T i ++ List.replicate off 1 <+: hsAt T i' := by
            rw [hform]
            exact List.prefix_append _ _
          have h3 : hsAt T i' <+: hsAt T i' ++ List.replicate 0 1 := by simp
          exact ((h1.trans h2).trans h3).trans hpre

/-- Prefixes of member chains are member chains (ancestor closure). -/
theorem prefix_memChain {T : Table} (hC : Canonical T) :
    ∀ i (hi : i < T.length) k (hk : k < T[i].len) (c : List ℕ),
      c <+: hsAt T i ++ List.replicate k 1 → c ≠ [] →
      ∃ j, ∃ (_ : j < T.length), ∃ m, m < T[j].len ∧
        c = hsAt T j ++ List.replicate m 1 := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
      intro hi k hk c hpre hne
      rcases Nat.lt_trichotomy c.length (hsAt T i).length with hlen | hlen | hlen
      · -- strictly inside the head: descend to the parent entry
        have hpre' : c <+: hsAt T i := by
          refine List.prefix_of_prefix_length_le hpre (List.prefix_append _ _) ?_
          omega
        cases hp : T[i].par with
        | none =>
            exfalso
            have hform := hsAt_none hi hp
            rw [hform] at hlen
            simp only [List.length_cons, List.length_nil] at hlen
            have : 1 ≤ c.length := List.length_pos_iff.mpr hne
            omega
        | some p =>
            have hpb : p.1 < i := hC.par_back i hi p hp
            have hpl : p.1 < T.length := by omega
            have hform : hsAt T i
                = hsAt T p.1 ++ List.replicate p.2 1 ++ [T[i].delta] :=
              hsAt_some hi hp hpb
            have hp2 : p.2 = T[p.1].len - 1 := hC.par_tail i hi p hp hpl
            have hlenpos : 1 ≤ T[p.1].len :=
              hC.len_pos _ (List.getElem_mem hpl)
            have hcd : c <+: hsAt T p.1 ++ List.replicate p.2 1 := by
              have := prefix_dropLast_of_ne hpre'
                (fun heq => by rw [heq] at hlen; omega)
              rwa [hform, List.dropLast_concat] at this
            exact ih p.1 hpb hpl p.2 (by omega) c hcd hne
      · -- exactly the head
        have : c = hsAt T i :=
          (List.prefix_of_prefix_length_le hpre (List.prefix_append _ _)
            (by omega)).eq_of_length hlen
        exact ⟨i, hi, 0, by
          have := hC.len_pos _ (List.getElem_mem hi)
          omega, by simpa using this⟩
      · -- inside the run: a shallower member
        have hclen : c.length ≤ (hsAt T i).length + k := by
          have := hpre.length_le
          simpa using this
        set m := c.length - (hsAt T i).length with hm
        have hmk : m ≤ k := by omega
        have hcform : c = hsAt T i ++ List.replicate m 1 := by
          have h1 : c = (hsAt T i ++ List.replicate k 1).take c.length :=
            List.prefix_iff_eq_take.mp hpre
          rw [h1, show c.length = (hsAt T i).length + m by omega]
          exact take_append_replicate hmk
        exact ⟨i, hi, m, by omega, hcform⟩

/-- **Kept-tree characterization**: the kept chains of the recovered state
are exactly the member chains of the table. -/
theorem kept_stateOf_iff {T : Table} (hC : Canonical T) {c : List ℕ} :
    c ∈ keptL (stateOf T) ↔ ∃ i, ∃ (_ : i < T.length), ∃ k, k < T[i].len ∧
      c = hsAt T i ++ List.replicate k 1 := by
  constructor
  · intro hc
    obtain ⟨hne, l, hl, hpre⟩ := mem_keptL.mp hc
    obtain ⟨j, hj, m, hm, hlive, rfl⟩ := mem_stateOf.mp hl
    obtain ⟨j', hj', m', hm', hform⟩ := prefix_memChain hC j hj m hm c hpre hne
    exact ⟨j', hj', m', hm', hform⟩
  · rintro ⟨i, hi, k, hk, rfl⟩
    obtain ⟨l, hl, hpre⟩ := memChain_extends_live hC T.length i hi
      (by omega) k hk
    refine mem_keptL.mpr ⟨?_, l, hl, hpre⟩
    intro hnil
    exact hsAt_ne_nil hC hi (by
      cases hs : hsAt T i with
      | nil => rfl
      | cons a as => rw [hs] at hnil; simp at hnil)

/-- Uniqueness, packaged at the two-decompositions interface. -/
theorem memChain_inj' {T : Table} (hC : Canonical T) {i j k m : ℕ}
    (hi : i < T.length) (hk : k < T[i].len)
    (hj : j < T.length) (hm : m < T[j].len)
    (heq : hsAt T i ++ List.replicate k 1 = hsAt T j ++ List.replicate m 1) :
    i = j ∧ k = m :=
  memChain_inj hC (hsAt T i ++ List.replicate k 1).length _ (le_refl _)
    i hi k hk rfl j hj m hm heq

/-- A member chain is live in the recovered state iff its entry is live. -/
theorem memChain_live_iff {T : Table} (hC : Canonical T) {i k : ℕ}
    (hi : i < T.length) (hk : k < T[i].len) :
    (hsAt T i ++ List.replicate k 1 ∈ stateOf T) ↔ T[i].live = true := by
  constructor
  · intro hmem
    obtain ⟨j, hj, m, hm, hlive, heq⟩ := mem_stateOf.mp hmem
    obtain ⟨rfl, -⟩ := memChain_inj' hC hi hk hj hm heq
    exact hlive
  · intro hlive
    exact mem_stateOf.mpr ⟨i, hi, k, hk, hlive, rfl⟩

/-- Interior member edges of the recovered state are fusible. -/
theorem memChain_fusible {T : Table} (hC : Canonical T) {i k : ℕ}
    (hi : i < T.length) (hk1 : k + 1 < T[i].len) :
    fusible (stateOf T) (hsAt T i ++ List.replicate (k + 1) 1) = true := by
  have hdrop : (hsAt T i ++ List.replicate (k + 1) 1).dropLast
      = hsAt T i ++ List.replicate k 1 := dropLast_append_replicate_succ
  have hkept : hsAt T i ++ List.replicate (k + 1) 1 ∈ keptL (stateOf T) :=
    (kept_stateOf_iff hC).mpr ⟨i, hi, k + 1, hk1, rfl⟩
  have hdkept : hsAt T i ++ List.replicate k 1 ∈ keptL (stateOf T) :=
    (kept_stateOf_iff hC).mpr ⟨i, hi, k, by omega, rfl⟩
  have huniq : ∀ c' ∈ keptL (stateOf T),
      c'.dropLast = (hsAt T i ++ List.replicate (k + 1) 1).dropLast →
      c' = hsAt T i ++ List.replicate (k + 1) 1 := by
    intro c' hc' hd
    rw [hdrop] at hd
    obtain ⟨j, hj, m, hm, rfl⟩ := (kept_stateOf_iff hC).mp hc'
    cases m with
    | zero =>
        exfalso
        simp only [List.replicate_zero, List.append_nil] at hd ⊢
        cases hp : T[j].par with
        | none =>
            have := hsAt_none hj hp
            rw [this] at hd
            rw [show ([T[j].delta] : List ℕ).dropLast = [] from rfl] at hd
            exact hsAt_ne_nil hC hi (by
              cases hs : hsAt T i with
              | nil => rfl
              | cons a as =>
                  rw [hs] at hd
                  simp at hd)
        | some p =>
            have hpb : p.1 < j := hC.par_back j hj p hp
            have hpl : p.1 < T.length := by omega
            have hform := hsAt_some hj hp hpb
            rw [hform, List.dropLast_concat] at hd
            have hp2 : p.2 = T[p.1].len - 1 := hC.par_tail j hj p hp hpl
            have hlenpos : 1 ≤ T[p.1].len :=
              hC.len_pos _ (List.getElem_mem hpl)
            obtain ⟨hip, hkp⟩ := memChain_inj' hC hpl (by omega) hi
              (by omega) hd
            subst hip
            omega
    | succ m =>
        have hd' : hsAt T j ++ List.replicate m 1
            = hsAt T i ++ List.replicate k 1 := by
          rw [← dropLast_append_replicate_succ (h := hsAt T j) (r := m), hd]
        obtain ⟨rfl, rfl⟩ := memChain_inj' hC hj (by omega) hi (by omega) hd'
        rfl
  have hlive : (hsAt T i ++ List.replicate (k + 1) 1 ∈ stateOf T)
      ↔ ((hsAt T i ++ List.replicate (k + 1) 1).dropLast ∈ stateOf T) := by
    rw [hdrop, memChain_live_iff hC hi hk1, memChain_live_iff hC hi (by omega)]
  simp only [fusible, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨⟨hkept, by rw [hdrop]; exact hdkept⟩,
    getLastD_append_replicate_succ⟩, huniq⟩, decide_eq_decide.mpr hlive⟩

/-- Recovered heads are not fusible in the recovered state. -/
theorem head_not_fusible_stateOf {T : Table} (hC : Canonical T) {i : ℕ}
    (hi : i < T.length) : fusible (stateOf T) (hsAt T i) = false := by
  cases hf : fusible (stateOf T) (hsAt T i) with
  | false => rfl
  | true =>
      exfalso
      cases hp : T[i].par with
      | none =>
          have hform := hsAt_none hi hp
          have := fusible_parent_kept hf
          rw [hform] at this
          rw [show ([T[i].delta] : List ℕ).dropLast = [] from rfl] at this
          exact kept_ne_nil this rfl
      | some p =>
          have hpb : p.1 < i := hC.par_back i hi p hp
          have hpl : p.1 < T.length := by omega
          have hform := hsAt_some hi hp hpb
          have hp2 : p.2 = T[p.1].len - 1 := hC.par_tail i hi p hp hpl
          have hlenpos : 1 ≤ T[p.1].len :=
            hC.len_pos _ (List.getElem_mem hpl)
          -- the branch label is 1
          have hdelta : T[i].delta = 1 := by
            have h1 := fusible_concat hf
            have h2 : (hsAt T i).getLastD 0 = T[i].delta := by
              rw [hform, List.getLastD_concat]
            rcases List.eq_nil_or_concat (hsAt T i) with hnil | ⟨q, b, hqb⟩
            · exact absurd hnil (hsAt_ne_nil hC hi)
            · simp only [List.concat_eq_append] at hqb
              rw [hqb, List.getLastD_concat] at h2
              rw [hqb, List.dropLast_concat] at h1
              have := List.append_cancel_left h1
              injection this with hb
              omega
          -- liveness matches across the edge
          have hlive : T[i].live = T[p.1].live := by
            have h1 := fusible_live hf
            have hd : (hsAt T i).dropLast
                = hsAt T p.1 ++ List.replicate p.2 1 := by
              rw [hform, List.dropLast_concat]
            rw [hd] at h1
            have h2 := memChain_live_iff hC hi
              (hC.len_pos _ (List.getElem_mem hi))
            simp only [List.replicate_zero, List.append_nil] at h2
            have h3 := memChain_live_iff hC hpl (by omega : p.2 < T[p.1].len)
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
          -- no_fuse: another sibling attaches at the same tail
          obtain ⟨i', hi', hne, hpar'⟩ :=
            hC.no_fuse i hi p hp hpl hdelta hlive
          have hpb' : p.1 < i' := hC.par_back i' hi' p hpar'
          have hform' := hsAt_some hi' hpar' hpb'
          have hkept' : hsAt T i' ∈ keptL (stateOf T) := by
            refine (kept_stateOf_iff hC).mpr ⟨i', hi', 0, ?_, by simp⟩
            exact hC.len_pos _ (List.getElem_mem hi')
          have hdrop' : (hsAt T i').dropLast = (hsAt T i).dropLast := by
            rw [hform, hform', List.dropLast_concat, List.dropLast_concat]
          have := fusible_unique hf hkept' hdrop'
          exact hne (hsAt_inj hC hi' hi this)

/-- The run-ancestor walk of the recovered state lands on the entry head. -/
theorem headOf_memChain {T : Table} (hC : Canonical T) {i : ℕ}
    (hi : i < T.length) :
    ∀ k, k < T[i].len →
      headOf (stateOf T) (hsAt T i ++ List.replicate k 1) = hsAt T i := by
  intro k
  induction k with
  | zero =>
      intro _
      simp only [List.replicate_zero, List.append_nil]
      exact headOf_of_not_fusible (head_not_fusible_stateOf hC hi)
  | succ k ih =>
      intro hk
      rw [headOf_of_fusible (memChain_fusible hC hi hk),
        dropLast_append_replicate_succ]
      exact ih (by omega)

/-- The recovered state's heads are exactly the recovered entry heads. -/
theorem isHead_stateOf_iff {T : Table} (hC : Canonical T) {c : List ℕ} :
    isHead (stateOf T) c = true
      ↔ ∃ i, ∃ (_ : i < T.length), c = hsAt T i := by
  constructor
  · intro hh
    obtain ⟨i, hi, k, hk, rfl⟩ := (kept_stateOf_iff hC).mp (isHead_kept hh)
    cases k with
    | zero => exact ⟨i, hi, by simp⟩
    | succ k =>
        exfalso
        have := isHead_not_fusible hh
        rw [memChain_fusible hC hi hk] at this
        exact Bool.noConfusion this
  · rintro ⟨i, hi, rfl⟩
    refine isHead_of_kept_not_fusible ?_ (head_not_fusible_stateOf hC hi)
    exact (kept_stateOf_iff hC).mpr ⟨i, hi, 0,
      hC.len_pos _ (List.getElem_mem hi), by simp⟩

/-- The run length of a recovered head is the entry's `len` field. -/
theorem lenOf_stateOf {T : Table} (hC : Canonical T) {i : ℕ}
    (hi : i < T.length) : lenOf (stateOf T) (hsAt T i) = T[i].len := by
  have hperm : (runMembers (stateOf T) (hsAt T i)).Perm
      ((List.range T[i].len).map (fun k => hsAt T i ++ List.replicate k 1)) := by
    refine (List.perm_ext_iff_of_nodup ((nodup_keptL _).filter _) ?_).mpr ?_
    · refine List.Nodup.map_on ?_ List.nodup_range
      intro j₁ _ j₂ _ heq
      exact replicate_offset_inj heq
    intro c
    rw [List.mem_filter, List.mem_map]
    constructor
    · rintro ⟨hkept, hhead⟩
      rw [beq_iff_eq] at hhead
      obtain ⟨j, hj, m, hm, rfl⟩ := (kept_stateOf_iff hC).mp hkept
      rw [headOf_memChain hC hj m hm] at hhead
      obtain rfl := hsAt_inj hC hj hi hhead
      exact ⟨m, List.mem_range.mpr hm, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      rw [List.mem_range] at hk
      exact ⟨(kept_stateOf_iff hC).mpr ⟨i, hi, k, hk, rfl⟩,
        by rw [beq_iff_eq]; exact headOf_memChain hC hi k hk⟩
  have := hperm.length_eq
  rw [lenOf, this]
  simp

/-- Strictly `hLt`-sorted lists with the same members are equal. -/
theorem hLt_sorted_ext : ∀ {l l' : List (List ℕ)},
    l.Pairwise (fun a b => hLt a b = true) →
    l'.Pairwise (fun a b => hLt a b = true) →
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
        · rcases List.mem_cons.mp ((hmem y).mpr List.mem_cons_self) with h' | h'
          · exact h'.symm
          · have h1 := hy x h
            have h2 := hx y h'
            rw [hLt_asymm h1] at h2
            exact Bool.noConfusion h2
      subst hxy
      have htails : ∀ z, z ∈ xs ↔ z ∈ ys := by
        intro z
        constructor
        · intro hz
          rcases List.mem_cons.mp ((hmem z).mp (List.mem_cons_of_mem _ hz))
            with rfl | h
          · exact absurd (hx z hz) (by rw [hLt_irrefl]; simp)
          · exact h
        · intro hz
          rcases List.mem_cons.mp ((hmem z).mpr (List.mem_cons_of_mem _ hz))
            with rfl | h
          · exact absurd (hy z hz) (by rw [hLt_irrefl]; simp)
          · exact h
      rw [hLt_sorted_ext hxs hys htails]

/-- The canonical head enumeration of the recovered state IS the table's
recovered head sequence — order included. -/
theorem headsList_stateOf {T : Table} (hC : Canonical T) :
    headsList (stateOf T) = headsOf T := by
  refine hLt_sorted_ext (sorted_headsList _) hC.sorted ?_
  intro c
  rw [mem_headsList, isHead_stateOf_iff hC]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [hsAt_eq_getElem hi]
    exact List.getElem_mem _
  · intro hc
    obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp hc
    have hi' : i < T.length := by rwa [headsOf_length] at hi
    exact ⟨i, hi', by rw [hsAt_eq_getElem hi', hgi]⟩

theorem RTEntry.ext' {e1 e2 : RTEntry} (h1 : e1.par = e2.par)
    (h2 : e1.live = e2.live) (h3 : e1.delta = e2.delta)
    (h4 : e1.len = e2.len) : e1 = e2 := by
  cases e1; cases e2; simp_all

/-- **T-repr, canonicity direction (`tableOf ∘ stateOf = id`)**: a canonical
table — maximal fusible chains (`no_fuse`), tail attachment (`par_tail`),
kept leaves live, canonical order — is recovered *exactly*, field for field,
from the state it denotes. Together with `stateOf_tableOf` this is the
representation iso of the note §10, over labels and liveness. Without
`no_fuse` the theorem is false: a run split in two re-canonicalizes to ONE
entry (directed case D4, the drift the coalesce rule exists to prevent);
the SPOT pins that concretely. -/
theorem tableOf_stateOf {T : Table} (hC : Canonical T) :
    tableOf (stateOf T) = T := by
  rw [tableOf, headsList_stateOf hC]
  refine List.ext_getElem (by simp [headsOf_length]) ?_
  intro i hi1 hi2
  rw [List.getElem_map]
  have hi : i < T.length := hi2
  have hgi : (headsOf T)[i]'(by rw [headsOf_length]; exact hi) = hsAt T i :=
    (hsAt_eq_getElem hi).symm
  rw [hgi]
  have hlen0 : 0 < T[i].len := hC.len_pos _ (List.getElem_mem hi)
  refine RTEntry.ext' ?_ ?_ ?_ ?_
  · -- par
    show (if (hsAt T i).dropLast ∈ keptL (stateOf T)
      then some ((headsList (stateOf T)).idxOf
                   (headOf (stateOf T) (hsAt T i).dropLast),
                 (hsAt T i).dropLast.length
                   - (headOf (stateOf T) (hsAt T i).dropLast).length)
      else none) = T[i].par
    cases hp : T[i].par with
    | none =>
        rw [if_neg]
        rw [hsAt_none hi hp]
        intro hmem
        exact kept_ne_nil hmem rfl
    | some p =>
        obtain ⟨p1, p2⟩ := p
        have hpb : p1 < i := hC.par_back i hi (p1, p2) hp
        have hpl : p1 < T.length := by omega
        have hp2 : p2 = T[p1].len - 1 := hC.par_tail i hi (p1, p2) hp hpl
        have hlenpos : 1 ≤ T[p1].len := hC.len_pos _ (List.getElem_mem hpl)
        have hdrop : (hsAt T i).dropLast
            = hsAt T p1 ++ List.replicate p2 1 := by
          rw [hsAt_some hi hp hpb, List.dropLast_concat]
        have hkept : (hsAt T i).dropLast ∈ keptL (stateOf T) := by
          rw [hdrop]
          exact (kept_stateOf_iff hC).mpr ⟨p1, hpl, p2, by omega, rfl⟩
        rw [if_pos hkept]
        have hhead : headOf (stateOf T) (hsAt T i).dropLast = hsAt T p1 := by
          rw [hdrop]
          exact headOf_memChain hC hpl p2 (by omega)
        rw [hhead]
        have hidx : (headsList (stateOf T)).idxOf (hsAt T p1) = p1 := by
          rw [headsList_stateOf hC, hsAt_eq_getElem hpl]
          exact idxOf_getElem_nodup (headsOf_nodup hC)
            (by rw [headsOf_length]; exact hpl)
        rw [hidx, hdrop]
        simp
  · -- live
    have hiff := memChain_live_iff hC hi hlen0
    simp only [List.replicate_zero, List.append_nil] at hiff
    show decide (hsAt T i ∈ stateOf T) = T[i].live
    cases hl : T[i].live with
    | true => exact decide_eq_true (hiff.mpr hl)
    | false =>
        apply decide_eq_false
        intro hmem
        have := hiff.mp hmem
        rw [hl] at this
        exact Bool.noConfusion this
  · -- delta
    show (hsAt T i).getLastD 0 = T[i].delta
    cases hp : T[i].par with
    | none => rw [hsAt_none hi hp]; rfl
    | some p =>
        rw [hsAt_some hi hp (hC.par_back i hi p hp), List.getLastD_concat]
  · -- len
    exact lenOf_stateOf hC hi

/-! ## §5  T-cmp — the two-case contracted comparator

The Python `make_cmp`, one-sided: walk the two entry chains to the first
difference. Same entry: offset order. One chain a prefix of the other:
ancestor entry first (sound because, by **T-tail**, the descendant exits the
ancestor's run at its tail, above every member — case A). Two branch entries
at one divergence node: larger label first (case B; the divergence node's
children are distinct kept children, so *neither* branch edge is fusible and
both branch heads sit in the chains — the two-case structure is total). The
`(ts, agent)` tie oracle of the Python rides in the labels: at kernel level
distinct siblings have distinct labels, exactly as the chain comparator
`chainBefore` consumes them. -/

theorem prefixesOf_concat (p : List ℕ) (b : ℕ) :
    prefixesOf (p ++ [b]) = prefixesOf p ++ [p ++ [b]] := by
  rw [prefixesOf, prefixesOf]
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

theorem prefixesOf_prefix {x y : List ℕ} (hp : x <+: y) :
    prefixesOf x <+: prefixesOf y := by
  obtain ⟨ext, rfl⟩ := hp
  induction ext using List.reverseRecOn with
  | nil => simp
  | append_singleton ext b ih =>
      rw [← List.append_assoc, prefixesOf_concat]
      exact ih.trans (List.prefix_append _ _)

/-- The entry chain: run heads from the root entry to `c`'s entry. -/
def entryChainOf (L : List (List ℕ)) (c : List ℕ) : List (List ℕ) :=
  if h' : (headOf L c).length ≤ 1 then [headOf L c]
  else entryChainOf L (headOf L c).dropLast ++ [headOf L c]
  termination_by c.length
  decreasing_by
    have h1 := (headOf_prefix L c).length_le
    simp only [List.length_dropLast]
    omega

theorem entryChainOf_short {L : List (List ℕ)} {c : List ℕ}
    (h : (headOf L c).length ≤ 1) : entryChainOf L c = [headOf L c] := by
  rw [entryChainOf, dif_pos h]

theorem entryChainOf_long {L : List (List ℕ)} {c : List ℕ}
    (h : ¬ (headOf L c).length ≤ 1) :
    entryChainOf L c
      = entryChainOf L (headOf L c).dropLast ++ [headOf L c] := by
  rw [entryChainOf, dif_neg (by simpa using h)]

theorem isHead_eq_false_of_fusible {L : List (List ℕ)} {c : List ℕ}
    (h : fusible L c = true) : isHead L c = false := by
  simp [isHead, h]

/-- Non-head run members contribute nothing to the head-filtered prefixes. -/
theorem filter_prefixes_run {L : List (List ℕ)} {h : List ℕ} :
    ∀ k, h ++ List.replicate k 1 ∈ keptL L →
      headOf L (h ++ List.replicate k 1) = h →
      (prefixesOf (h ++ List.replicate k 1)).filter (fun p => isHead L p)
        = (prefixesOf h).filter (fun p => isHead L p)
  | 0, _, _ => by simp
  | k + 1, hkept, hhead => by
      have hform : h ++ List.replicate (k + 1) 1
          = (h ++ List.replicate k 1) ++ [1] := by
        rw [List.replicate_succ', List.append_assoc]
      have hfus : fusible L (h ++ List.replicate (k + 1) 1) = true := by
        cases hf : fusible L (h ++ List.replicate (k + 1) 1) with
        | true => rfl
        | false =>
            exfalso
            have := headOf_of_not_fusible hf
            rw [hhead] at this
            have := congrArg List.length this
            simp at this
      have hkept' : h ++ List.replicate k 1 ∈ keptL L := by
        refine kept_of_prefix hkept ?_ ?_
        · rw [hform]; exact List.prefix_append _ _
        · intro hnil
          have hh : h ∈ keptL L := hhead ▸ headOf_kept hkept
          cases h with
          | nil => exact kept_ne_nil hh rfl
          | cons a as => simp at hnil
      have hhead' : headOf L (h ++ List.replicate k 1) = h := by
        refine headOf_within hhead (List.prefix_append _ _) ?_
        rw [hform]; exact List.prefix_append _ _
      rw [hform, prefixesOf_concat, List.filter_append]
      rw [show ((h ++ List.replicate k 1) ++ [1] : List ℕ)
        = h ++ List.replicate (k + 1) 1 from hform.symm]
      rw [show (([h ++ List.replicate (k + 1) 1] : List (List ℕ)).filter
          (fun p => isHead L p)) = [] from by
        simp [List.filter, isHead_eq_false_of_fusible hfus]]
      rw [List.append_nil]
      exact filter_prefixes_run k hkept' hhead'

/-- **Entry-chain characterization**: the entry chain is exactly the list of
head prefixes of `c`, short to long. -/
theorem entryChainOf_eq_filter {L : List (List ℕ)} :
    ∀ n (c : List ℕ), c.length ≤ n → c ∈ keptL L →
    entryChainOf L c = (prefixesOf c).filter (fun p => isHead L p) := by
  intro n
  induction n with
  | zero =>
      intro c hc hkept
      exact absurd (List.length_pos_iff.mpr (kept_ne_nil hkept)) (by omega)
  | succ n ih =>
      intro c hc hkept
      have hh : isHead L (headOf L c) = true := headOf_isHead hkept
      have hhkept : headOf L c ∈ keptL L := headOf_kept hkept
      -- collapse the run suffix
      obtain ⟨k, hform⟩ := headOf_replicate L c
      have hrun : (prefixesOf c).filter (fun p => isHead L p)
          = (prefixesOf (headOf L c)).filter (fun p => isHead L p) := by
        conv_lhs => rw [hform]
        exact filter_prefixes_run k (hform ▸ hkept) (hform ▸ rfl)
      rw [hrun]
      by_cases hlen : (headOf L c).length ≤ 1
      · rw [entryChainOf_short hlen]
        obtain ⟨d, hd⟩ : ∃ d, headOf L c = [d] := by
          cases hhc : headOf L c with
          | nil => exact absurd hhc (kept_ne_nil hhkept)
          | cons a as =>
              rw [hhc] at hlen
              simp at hlen
              rw [hlen]
              exact ⟨a, rfl⟩
        rw [hd]
        rw [show prefixesOf [d] = [[d]] from rfl]
        rw [List.filter_cons]
        rw [hd] at hh
        simp [hh]
      · rw [entryChainOf_long hlen]
        obtain ⟨q, b, hqb⟩ : ∃ q b, headOf L c = q ++ [b] := by
          rcases List.eq_nil_or_concat (headOf L c) with hnil | ⟨q, b, hqb⟩
          · exact absurd hnil (kept_ne_nil hhkept)
          · exact ⟨q, b, by simpa using hqb⟩
        have hqkept : (headOf L c).dropLast ∈ keptL L := by
          refine kept_of_prefix hhkept (List.dropLast_prefix _) ?_
          rw [hqb, List.dropLast_concat]
          intro hnil
          rw [hnil] at hqb
          rw [hqb] at hlen
          simp at hlen
        have hqlen : (headOf L c).dropLast.length ≤ n := by
          have h1 := (headOf_prefix L c).length_le
          simp only [List.length_dropLast]
          omega
        rw [ih _ hqlen hqkept]
        rw [hqb, List.dropLast_concat, prefixesOf_concat, List.filter_append]
        congr 1
        have hhb : isHead L (q ++ [b]) = true := hqb ▸ hh
        simp [List.filter, hhb]

/-- First-difference walk over two entry chains, with same-entry offsets. -/
def cmpEC : List (List ℕ) → ℕ → List (List ℕ) → ℕ → Bool
  | [], jx, [], jy => decide (jx < jy)
  | [], _, _ :: _, _ => true
  | _ :: _, _, [], _ => false
  | gx :: tx, jx, gy :: ty, jy =>
      if gx = gy then cmpEC tx jx ty jy
      else decide (gy.getLastD 0 < gx.getLastD 0)

/-- The table comparator: consults entry chains and header data only. -/
def cmpTable (L : List (List ℕ)) (x y : List ℕ) : Bool :=
  cmpEC (entryChainOf L x) (x.length - (headOf L x).length)
        (entryChainOf L y) (y.length - (headOf L y).length)

theorem cmpEC_consume (w a : List (List ℕ)) (jx : ℕ)
    (b : List (List ℕ)) (jy : ℕ) :
    cmpEC (w ++ a) jx (w ++ b) jy = cmpEC a jx b jy := by
  induction w with
  | nil => rfl
  | cons g w ih => simpa [cmpEC] using ih

theorem entryChainOf_concat (L : List (List ℕ)) (c : List ℕ) :
    ∃ w, entryChainOf L c = w ++ [headOf L c] := by
  by_cases h : (headOf L c).length ≤ 1
  · exact ⟨[], by rw [entryChainOf_short h]; rfl⟩
  · exact ⟨_, entryChainOf_long h⟩

theorem posChain_of_kept {L : List (List ℕ)}
    (hpos : ∀ l ∈ L, PosChain l) {c : List ℕ} (hc : c ∈ keptL L) :
    PosChain c := by
  obtain ⟨-, l, hl, hpre⟩ := mem_keptL.mp hc
  intro d hd
  exact hpos l hl d (hpre.subset hd)

/-- Case A soundness: an ancestor's entry chain is a prefix of the
descendant's, and comparing there is offset order or ancestor-first. -/
theorem cmpTable_prefix {L : List (List ℕ)} {x y : List ℕ}
    (hx : x ∈ keptL L) (hy : y ∈ keptL L) (hp : x <+: y) (hne : x ≠ y) :
    cmpTable L x y = true ∧ cmpTable L y x = false := by
  have hECp : entryChainOf L x <+: entryChainOf L y := by
    rw [entryChainOf_eq_filter x.length x (le_refl _) hx,
        entryChainOf_eq_filter y.length y (le_refl _) hy]
    exact (prefixesOf_prefix hp).filter _
  obtain ⟨rest, hrest⟩ := hECp
  cases rest with
  | nil =>
      -- same entry: offset order decides
      rw [List.append_nil] at hrest
      have hheads : headOf L x = headOf L y := by
        obtain ⟨wx, hwx⟩ := entryChainOf_concat L x
        obtain ⟨wy, hwy⟩ := entryChainOf_concat L y
        have h1 : wx ++ [headOf L x] = wy ++ [headOf L y] := by
          rw [← hwx, ← hwy, hrest]
        have h2 := congrArg List.getLast? h1
        rw [List.getLast?_concat, List.getLast?_concat] at h2
        injection h2
      have hxlen : x.length < y.length :=
        lt_of_le_of_ne hp.length_le (fun h => hne (hp.eq_of_length h))
      have hhx := (headOf_prefix L x).length_le
      have hjlt : x.length - (headOf L x).length
          < y.length - (headOf L y).length := by
        rw [← hheads]
        have := (headOf_prefix L x).length_le
        omega
      constructor
      · rw [cmpTable, hrest, hheads]
        rw [show cmpEC (entryChainOf L y) (x.length - (headOf L y).length)
            (entryChainOf L y) (y.length - (headOf L y).length)
            = cmpEC [] (x.length - (headOf L y).length) []
                (y.length - (headOf L y).length) from by
          rw [← List.append_nil (entryChainOf L y)]
          exact cmpEC_consume _ _ _ _ _]
        rw [← hheads] at *
        simp [cmpEC]
        omega
      · rw [cmpTable, hrest, hheads]
        rw [show cmpEC (entryChainOf L y) (y.length - (headOf L y).length)
            (entryChainOf L y) (x.length - (headOf L y).length)
            = cmpEC [] (y.length - (headOf L y).length) []
                (x.length - (headOf L y).length) from by
          rw [← List.append_nil (entryChainOf L y)]
          exact cmpEC_consume _ _ _ _ _]
        rw [← hheads] at *
        simp [cmpEC]
        omega
  | cons r rs =>
      -- ancestor entry: x's chain is a strict prefix
      constructor
      · rw [cmpTable, ← hrest]
        have h := cmpEC_consume (entryChainOf L x) []
          (x.length - (headOf L x).length) (r :: rs)
          (y.length - (headOf L y).length)
        rw [List.append_nil] at h
        rw [h]
        rfl
      · rw [cmpTable, ← hrest]
        have h := cmpEC_consume (entryChainOf L x) (r :: rs)
          (y.length - (headOf L y).length) []
          (x.length - (headOf L x).length)
        rw [List.append_nil] at h
        rw [h]
        rfl

/-- Case B soundness: at a genuine divergence both branch heads are heads
(two kept children of one node cannot fuse), and the larger label wins. -/
theorem cmpTable_diverge {L : List (List ℕ)} {p : List ℕ} {dx dy : ℕ}
    {x y : List ℕ} (hx : x ∈ keptL L) (hy : y ∈ keptL L)
    (hpx : p ++ [dx] <+: x) (hpy : p ++ [dy] <+: y) (hne : dx ≠ dy) :
    cmpTable L x y = decide (dy < dx)
      ∧ cmpTable L y x = decide (dx < dy) := by
  have hqx : p ++ [dx] ∈ keptL L := kept_of_prefix hx hpx (by simp)
  have hqy : p ++ [dy] ∈ keptL L := kept_of_prefix hy hpy (by simp)
  have hqne : (p ++ [dx] : List ℕ) ≠ p ++ [dy] := by
    intro h
    have := List.append_cancel_left h
    injection this with h'
    exact hne h'
  have hhx : isHead L (p ++ [dx]) = true := by
    refine isHead_of_kept_not_fusible hqx ?_
    cases hf : fusible L (p ++ [dx]) with
    | false => rfl
    | true =>
        exfalso
        exact hqne ((fusible_unique hf hqy
          (by rw [List.dropLast_concat, List.dropLast_concat])).symm)
  have hhy : isHead L (p ++ [dy]) = true := by
    refine isHead_of_kept_not_fusible hqy ?_
    cases hf : fusible L (p ++ [dy]) with
    | false => rfl
    | true =>
        exfalso
        exact hqne (fusible_unique hf hqx
          (by rw [List.dropLast_concat, List.dropLast_concat]))
  -- entry chains decompose at the divergence
  have hdec : ∀ (z : List ℕ) (d : ℕ), z ∈ keptL L → p ++ [d] <+: z →
      isHead L (p ++ [d]) = true →
      ∃ rz, entryChainOf L z
        = (prefixesOf p).filter (fun q => isHead L q) ++ (p ++ [d]) :: rz := by
    intro z d hz hpz hhd
    have h1 : entryChainOf L (p ++ [d]) <+: entryChainOf L z := by
      rw [entryChainOf_eq_filter (p ++ [d]).length _ (le_refl _)
          (kept_of_prefix hz hpz (by simp)),
        entryChainOf_eq_filter z.length z (le_refl _) hz]
      exact (prefixesOf_prefix hpz).filter _
    have h2 : entryChainOf L (p ++ [d])
        = (prefixesOf p).filter (fun q => isHead L q) ++ [p ++ [d]] := by
      rw [entryChainOf_eq_filter (p ++ [d]).length _ (le_refl _)
          (kept_of_prefix hz hpz (by simp)),
        prefixesOf_concat, List.filter_append]
      congr 1
      simp [List.filter, hhd]
    obtain ⟨rz, hrz⟩ := h1
    exact ⟨rz, by rw [← hrz, h2, List.append_assoc]; rfl⟩
  obtain ⟨rx, hrx⟩ := hdec x dx hx hpx hhx
  obtain ⟨ry, hry⟩ := hdec y dy hy hpy hhy
  constructor
  · rw [cmpTable, hrx, hry, cmpEC_consume]
    simp only [cmpEC, if_neg hqne]
    rw [List.getLastD_concat, List.getLastD_concat]
  · rw [cmpTable, hrx, hry, cmpEC_consume]
    simp only [cmpEC, if_neg (Ne.symm hqne)]
    rw [List.getLastD_concat, List.getLastD_concat]

/-- Both `chainBefore` constructors, computed by the table comparator. -/
theorem cmpTable_of_chainBefore {L : List (List ℕ)} {x y : List ℕ}
    (hx : x ∈ keptL L) (hy : y ∈ keptL L) (hb : chainBefore x y) :
    cmpTable L x y = true ∧ cmpTable L y x = false := by
  cases hb with
  | ancestor ch ext hne' =>
      refine cmpTable_prefix hx hy (List.prefix_append _ _) ?_
      intro heq
      have := congrArg List.length heq
      simp at this
      exact hne' this
  | newer p d e ch1 ch2 hlt =>
      have hpx' : p ++ [d] <+: p ++ d :: ch1 :=
        ⟨ch1, by rw [List.append_assoc]; rfl⟩
      have hpy' : p ++ [e] <+: p ++ e :: ch2 :=
        ⟨ch2, by rw [List.append_assoc]; rfl⟩
      have hd := cmpTable_diverge (dx := d) (dy := e) hx hy hpx' hpy'
        (by omega)
      rw [hd.1, hd.2]
      constructor
      · simpa using hlt
      · simp
        omega

/-- **T-cmp, chain form**: the two-case contracted comparator IS the chain
display order. -/
theorem cmpTable_iff_chainBefore {L : List (List ℕ)} {x y : List ℕ}
    (hx : x ∈ keptL L) (hy : y ∈ keptL L) (hne : x ≠ y) :
    (cmpTable L x y = true ↔ chainBefore x y) := by
  constructor
  · intro hcmp
    rcases Sal.EmbedRGA.chainBefore_total hne with hb | hb
    · exact hb
    · rw [(cmpTable_of_chainBefore hy hx hb).2] at hcmp
      exact Bool.noConfusion hcmp
  · exact fun hb => (cmpTable_of_chainBefore hx hy hb).1

/-- **T-cmp**: the comparator over the contracted run tree equals the fold's
key order `keyLt` on the immutable coordinates — parametric in the ordered
prefix code, with the label order standing where the Python's `(ts, agent)`
tie oracle rides (neither representation encodes it; the labels carry it on
both sides identically). -/
theorem cmpTable_eq_keyLt (Γ : OrderedPrefixCode) {L : List (List ℕ)}
    (hpos : ∀ l ∈ L, PosChain l) {x y : List ℕ}
    (hx : x ∈ keptL L) (hy : y ∈ keptL L) (hne : x ≠ y) :
    cmpTable L x y = keyLt (key (coordOf Γ y)) (key (coordOf Γ x)) := by
  have hpx : PosChain x := posChain_of_kept hpos hx
  have hpy : PosChain y := posChain_of_kept hpos hy
  cases hcmp : cmpTable L x y with
  | true =>
      exact ((Sal.EmbedRGA.display_iff_chainBefore Γ hpx hpy hne).mpr
        ((cmpTable_iff_chainBefore hx hy hne).mp hcmp)).symm
  | false =>
      have hnb : ¬ chainBefore x y := fun hb => by
        rw [(cmpTable_of_chainBefore hx hy hb).1] at hcmp
        exact Bool.noConfusion hcmp
      rcases Sal.EmbedRGA.chainBefore_total hne with hb | hb
      · exact absurd hb hnb
      · have := (Sal.EmbedRGA.display_iff_chainBefore Γ hpy hpx
          (Ne.symm hne)).mpr hb
        rw [Sal.EmbedRGA.keyLt_asymm this]

/-! ## §6  T-walk — the structural walk is the display

One-sided walk (Python `table_walk`): an entry emits its live members in
offset order, then its attachment subtrees at the tail, newest (largest
label) first. The partition argument — everything below a run either sits in
the run or exits at its *tail* — is T-tail again. -/

theorem le_foldr_max : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.foldr max 0
  | [], x, hx => absurd hx (List.not_mem_nil)
  | y :: ys, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact Nat.le_max_left _ _
      · exact le_trans (le_foldr_max ys x hx') (Nat.le_max_right _ _)

def maxLen (L : List (List ℕ)) : ℕ := ((keptL L).map List.length).foldr max 0

theorem length_le_maxLen {L : List (List ℕ)} {c : List ℕ}
    (hc : c ∈ keptL L) : c.length ≤ maxLen L :=
  le_foldr_max _ _ (List.mem_map.mpr ⟨c, hc, rfl⟩)

/-- The child entries attached at node `m`, newest label first. -/
def childHeads (L : List (List ℕ)) (m : List ℕ) : List (List ℕ) :=
  ((keptL L).filter (fun c => isHead L c && (c.dropLast == m))).mergeSort
    (fun a b => decide (b.getLastD 0 ≤ a.getLastD 0))

theorem mem_childHeads {L : List (List ℕ)} {m c : List ℕ} :
    c ∈ childHeads L m ↔ isHead L c = true ∧ c.dropLast = m := by
  rw [childHeads, List.mem_mergeSort, List.mem_filter]
  constructor
  · rintro ⟨-, h⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact h
  · rintro ⟨h1, h2⟩
    exact ⟨isHead_kept h1, by simp [h1, h2]⟩

theorem nodup_childHeads (L : List (List ℕ)) (m : List ℕ) :
    (childHeads L m).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr ((nodup_keptL L).filter _)

theorem sorted_childHeads (L : List (List ℕ)) (m : List ℕ) :
    (childHeads L m).Pairwise
      (fun a b => b.getLastD 0 ≤ a.getLastD 0) := by
  have h := List.pairwise_mergeSort
    (le := fun a b : List ℕ => decide (b.getLastD 0 ≤ a.getLastD 0))
    (fun a b c h1 h2 => by
      rw [decide_eq_true_eq] at h1 h2 ⊢
      omega)
    (fun a b => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Nat.le_total (b.getLastD 0) (a.getLastD 0))
    ((keptL L).filter (fun c => isHead L c && (c.dropLast == m)))
  exact h.imp (fun hab => by
    simp only [decide_eq_true_eq] at hab
    exact hab)

/-- The walk below one entry. -/
def walkE (L : List (List ℕ)) : ℕ → List ℕ → List (List ℕ)
  | 0, _ => []
  | fuel + 1, h =>
      (if h ∈ L then (List.range (lenOf L h)).map
          (fun k => h ++ List.replicate k 1) else [])
      ++ (childHeads L (tailOf L h)).flatMap (walkE L fuel)

/-- The walk of the whole table. -/
def walk (L : List (List ℕ)) : List (List ℕ) :=
  (childHeads L []).flatMap (walkE L (maxLen L + 1))

/-- Next node on the path towards a strict extension. -/
theorem take_succ_of_prefix {m c : List ℕ} (h : m <+: c) (hne : m ≠ c) :
    ∃ d, m ++ [d] <+: c := by
  have hlt : m.length < c.length :=
    lt_of_le_of_ne h.length_le (fun hl => hne (h.eq_of_length hl))
  refine ⟨c[m.length], ?_⟩
  have h1 : c.take (m.length + 1) = c.take m.length ++ [c[m.length]] := by
    rw [List.take_succ, List.getElem?_eq_getElem hlt]
    rfl
  rw [← (List.prefix_iff_eq_take.mp h), ← h1] at *
  exact List.take_prefix _ _

/-- **The escape lemma** (T-tail in walk clothing): a kept chain below a head
that is not one of its run members exits the run at the tail, through a
child head. -/
theorem escape_run {L : List (List ℕ)} {h c : List ℕ}
    (hh : isHead L h = true) (hc : c ∈ keptL L) (hpre : h <+: c)
    (hnm : headOf L c ≠ h) :
    ∃ q, isHead L q = true ∧ q.dropLast = tailOf L h ∧ q <+: c := by
  -- climb the run: every member up to the tail is a prefix of c
  have hclimb : ∀ j, j ≤ lenOf L h - 1 → h ++ List.replicate j 1 <+: c := by
    intro j
    induction j with
    | zero => intro _; simpa using hpre
    | succ j ih =>
        intro hj
        have hmj : h ++ List.replicate j 1 <+: c := ih (by omega)
        have hne : h ++ List.replicate j 1 ≠ c := by
          intro heq
          apply hnm
          rw [← heq]
          exact (mem_runMembers.mp (runMember_of_lt hh (by
            have := lenOf_pos hh
            omega : j < lenOf L h))).2
        obtain ⟨d, hd⟩ := take_succ_of_prefix hmj hne
        have hdkept : (h ++ List.replicate j 1) ++ [d] ∈ keptL L :=
          kept_of_prefix hc hd (by simp)
        have hfus : fusible L (h ++ List.replicate (j + 1) 1) = true :=
          runMember_fusible (runMember_of_lt hh (by omega : j + 1 < lenOf L h))
        have huniq := fusible_unique hfus hdkept
          (by rw [List.dropLast_concat, dropLast_append_replicate_succ])
        rw [← huniq]
        exact hd
  have htail : tailOf L h <+: c := hclimb (lenOf L h - 1) (le_refl _)
  have htne : tailOf L h ≠ c := by
    intro heq
    apply hnm
    rw [← heq]
    exact (mem_runMembers.mp (tailOf_mem hh)).2
  obtain ⟨d, hd⟩ := take_succ_of_prefix htail htne
  have hdkept : tailOf L h ++ [d] ∈ keptL L :=
    kept_of_prefix hc hd (by simp)
  refine ⟨tailOf L h ++ [d], ?_, List.dropLast_concat, hd⟩
  refine isHead_of_kept_not_fusible hdkept ?_
  by_cases hd1 : d = 1
  · subst hd1
    exact tail_succ_not_fusible hh
  · cases hf : fusible L (tailOf L h ++ [d]) with
    | false => rfl
    | true =>
        exfalso
        have := fusible_concat hf
        rw [List.dropLast_concat] at this
        have := List.append_cancel_left this
        injection this with h'
        exact hd1 h'

/-- Walk soundness: everything emitted is live and sits below the entry. -/
theorem walkE_sound {L : List (List ℕ)} :
    ∀ fuel (h c : List ℕ), isHead L h = true → c ∈ walkE L fuel h →
      c ∈ L ∧ h <+: c := by
  intro fuel
  induction fuel with
  | zero => intro h c _ hc; simp [walkE] at hc
  | succ fuel ih =>
      intro h c hh hc
      rw [walkE, List.mem_append] at hc
      rcases hc with hc | hc
      · by_cases hl : h ∈ L
        · rw [if_pos hl] at hc
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
          rw [List.mem_range] at hk
          exact ⟨(run_liveness_uniform (runMember_of_lt hh hk)).mpr hl,
            List.prefix_append _ _⟩
        · rw [if_neg hl] at hc
          simp at hc
      · obtain ⟨q, hq, hcq⟩ := List.mem_flatMap.mp hc
        obtain ⟨hqh, hqd⟩ := mem_childHeads.mp hq
        obtain ⟨hcl, hqc⟩ := ih q c hqh hcq
        refine ⟨hcl, ?_⟩
        have h1 : h <+: tailOf L h := List.prefix_append _ _
        have h2 : tailOf L h <+: q := by
          rw [← hqd]
          exact List.dropLast_prefix q
        exact (h1.trans h2).trans hqc

/-- Walk completeness: with enough fuel, every live chain below the entry is
emitted. -/
theorem walkE_complete {L : List (List ℕ)} :
    ∀ fuel (h c : List ℕ), isHead L h = true → c ∈ L → c ∈ keptL L →
      h <+: c → maxLen L + 1 - h.length ≤ fuel →
      c ∈ walkE L fuel h := by
  intro fuel
  induction fuel with
  | zero =>
      intro h c hh _ hc hpre hfuel
      have h1 := (hpre.trans (List.prefix_refl c)).length_le
      have h2 := length_le_maxLen hc
      have h3 := length_le_maxLen (isHead_kept hh)
      omega
  | succ fuel ih =>
      intro h c hh hcl hc hpre hfuel
      rw [walkE, List.mem_append]
      by_cases hm : headOf L c = h
      · left
        have hmem : c ∈ runMembers L h := mem_runMembers.mpr ⟨hc, hm⟩
        have hl : h ∈ L := (run_liveness_uniform hmem).mp hcl
        rw [if_pos hl]
        refine List.mem_map.mpr ⟨c.length - h.length, ?_, ?_⟩
        · exact List.mem_range.mpr
            (runMember_offset_lt ((runMember_form hmem) ▸ hmem))
        · exact (runMember_form hmem).symm
      · right
        obtain ⟨q, hqh, hqd, hqc⟩ := escape_run hh hc hpre hm
        refine List.mem_flatMap.mpr ⟨q, mem_childHeads.mpr ⟨hqh, hqd⟩, ?_⟩
        refine ih q c hqh hcl hc hqc ?_
        have h1 : q.length - 1 = (tailOf L h).length := by
          rw [← hqd, List.length_dropLast]
        have h2 : (tailOf L h).length = h.length + (lenOf L h - 1) := by
          rw [tailOf]; simp
        have h3 : 1 ≤ q.length :=
          List.length_pos_iff.mpr (kept_ne_nil (isHead_kept hqh))
        have h4 := lenOf_pos hh
        omega

theorem pairwise_flatMap {α β : Type} {R : β → β → Prop} {l : List α}
    {f : α → List β} (hblock : ∀ a ∈ l, (f a).Pairwise R)
    (hcross : l.Pairwise (fun a a' => ∀ b ∈ f a, ∀ b' ∈ f a', R b b')) :
    (l.flatMap f).Pairwise R := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.flatMap_cons, List.pairwise_append]
      obtain ⟨hca, hcl⟩ := List.pairwise_cons.mp hcross
      refine ⟨hblock a List.mem_cons_self,
        ih (fun a' ha' => hblock a' (List.mem_cons_of_mem _ ha')) hcl, ?_⟩
      intro b hb b' hb'
      obtain ⟨a', ha', hba'⟩ := List.mem_flatMap.mp hb'
      exact hca a' ha' b hb b' hba'

theorem prefix_eq_of_length {p1 p2 c : List ℕ} (h1 : p1 <+: c)
    (h2 : p2 <+: c) (hl : p1.length = p2.length) : p1 = p2 :=
  (List.prefix_of_prefix_length_le h1 h2 (le_of_eq hl)).eq_of_length hl

theorem concat_getLastD {c : List ℕ} (h : c ≠ []) :
    c = c.dropLast ++ [c.getLastD 0] := by
  rcases List.eq_nil_or_concat c with rfl | ⟨q, b, rfl⟩
  · exact absurd rfl h
  · simp only [List.concat_eq_append]
    rw [List.dropLast_concat, List.getLastD_concat]

/-- Child heads' subtree chains: shape at the divergence. -/
theorem childHead_subtree_form {L : List (List ℕ)} {m q c : List ℕ}
    (hq : q ∈ childHeads L m) (hc : q <+: c) :
    ∃ rest, c = m ++ q.getLastD 0 :: rest := by
  obtain ⟨hqh, hqd⟩ := mem_childHeads.mp hq
  have hqne : q ≠ [] := kept_ne_nil (isHead_kept hqh)
  obtain ⟨ext, rfl⟩ := hc
  refine ⟨ext, ?_⟩
  conv_lhs => rw [concat_getLastD hqne, hqd]
  rw [List.append_assoc]
  rfl

theorem walkE_nodup {L : List (List ℕ)} :
    ∀ fuel (h : List ℕ), isHead L h = true → (walkE L fuel h).Nodup := by
  intro fuel
  induction fuel with
  | zero => intro h _; simp [walkE]
  | succ fuel ih =>
      intro h hh
      rw [walkE, List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · by_cases hl : h ∈ L
        · rw [if_pos hl]
          refine List.Nodup.map_on ?_ List.nodup_range
          intro j₁ _ j₂ _ heq
          exact replicate_offset_inj heq
        · rw [if_neg hl]; exact List.nodup_nil
      · refine nodup_flatMap_of_disjoint (nodup_childHeads L _) ?_ ?_
        · intro q hq
          exact ih q (mem_childHeads.mp hq).1
        · intro q hq q' hq' hne c hc hc'
          have h1 := (walkE_sound fuel q c (mem_childHeads.mp hq).1 hc).2
          have h2 := (walkE_sound fuel q' c (mem_childHeads.mp hq').1 hc').2
          apply hne
          refine prefix_eq_of_length h1 h2 ?_
          have e1 : q.dropLast = tailOf L h := (mem_childHeads.mp hq).2
          have e2 : q'.dropLast = tailOf L h := (mem_childHeads.mp hq').2
          have l1 := congrArg List.length e1
          have l2 := congrArg List.length e2
          rw [List.length_dropLast] at l1 l2
          have n1 : 1 ≤ q.length := List.length_pos_iff.mpr
            (kept_ne_nil (isHead_kept (mem_childHeads.mp hq).1))
          have n2 : 1 ≤ q'.length := List.length_pos_iff.mpr
            (kept_ne_nil (isHead_kept (mem_childHeads.mp hq').1))
          omega
      · intro a ha b hb heq
        subst heq
        by_cases hl : h ∈ L
        · rw [if_pos hl] at ha
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
          rw [List.mem_range] at hk
          obtain ⟨q, hq, hcq⟩ := List.mem_flatMap.mp hb
          have h1 := (walkE_sound fuel q _ (mem_childHeads.mp hq).1 hcq).2
          have e1 : q.dropLast = tailOf L h := (mem_childHeads.mp hq).2
          have hlen1 := h1.length_le
          rw [List.length_append, List.length_replicate] at hlen1
          have l1 := congrArg List.length e1
          rw [List.length_dropLast, tailOf, List.length_append,
            List.length_replicate] at l1
          have n1 : 1 ≤ q.length := List.length_pos_iff.mpr
            (kept_ne_nil (isHead_kept (mem_childHeads.mp hq).1))
          have h4 := lenOf_pos hh
          omega
        · rw [if_neg hl] at ha
          simp at ha

theorem walkE_pairwise {L : List (List ℕ)} :
    ∀ fuel (h : List ℕ), isHead L h = true →
      (walkE L fuel h).Pairwise chainBefore := by
  intro fuel
  induction fuel with
  | zero => intro h _; simp [walkE]
  | succ fuel ih =>
      intro h hh
      rw [walkE, List.pairwise_append]
      refine ⟨?_, ?_, ?_⟩
      · -- members in offset order: ancestor chain
        by_cases hl : h ∈ L
        · rw [if_pos hl]
          rw [List.pairwise_map]
          refine (List.pairwise_lt_range).imp ?_
          intro j k hjk
          rw [show h ++ List.replicate k 1
              = (h ++ List.replicate j 1) ++ List.replicate (k - j) 1 from by
            rw [List.append_assoc, ← List.replicate_add]
            congr 2
            omega]
          exact chainBefore.ancestor _ _ (by
            intro hnil
            have := congrArg List.length hnil
            simp at this
            omega)
        · rw [if_neg hl]; exact List.Pairwise.nil
      · -- across and within subtrees
        refine pairwise_flatMap (fun q hq => ih q (mem_childHeads.mp hq).1) ?_
        have hsorted := (sorted_childHeads L (tailOf L h)).and
          (List.nodup_iff_pairwise_ne.mp (nodup_childHeads L (tailOf L h)))
        refine hsorted.imp_of_mem ?_
        intro q q' hqm hqm' ⟨hle, hne⟩ c hc c' hc'
        have h1 := (walkE_sound fuel q c (mem_childHeads.mp hqm).1 hc).2
        have h2 := (walkE_sound fuel q' c' (mem_childHeads.mp hqm').1 hc').2
        obtain ⟨r1, hr1⟩ := childHead_subtree_form hqm h1
        obtain ⟨r2, hr2⟩ := childHead_subtree_form hqm' h2
        rw [hr1, hr2]
        refine chainBefore.newer _ _ _ _ _ ?_
        have hdne : q.getLastD 0 ≠ q'.getLastD 0 := by
          intro heq
          apply hne
          have e1 : q.dropLast = tailOf L h := (mem_childHeads.mp hqm).2
          have e2 : q'.dropLast = tailOf L h := (mem_childHeads.mp hqm').2
          conv_lhs => rw [concat_getLastD
            (kept_ne_nil (isHead_kept (mem_childHeads.mp hqm).1))]
          conv_rhs => rw [concat_getLastD
            (kept_ne_nil (isHead_kept (mem_childHeads.mp hqm').1))]
          rw [e1, e2, heq]
        omega
      · -- members before every subtree chain
        intro a ha b hb
        by_cases hl : h ∈ L
        · rw [if_pos hl] at ha
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
          rw [List.mem_range] at hk
          obtain ⟨q, hq, hcq⟩ := List.mem_flatMap.mp hb
          have h1 := (walkE_sound fuel q b (mem_childHeads.mp hq).1 hcq).2
          have e1 : q.dropLast = tailOf L h := (mem_childHeads.mp hq).2
          have hmt : h ++ List.replicate k 1 <+: tailOf L h := by
            rw [tailOf, show List.replicate (lenOf L h - 1) 1
                = List.replicate k 1 ++ List.replicate (lenOf L h - 1 - k) 1
              from by rw [← List.replicate_add]; congr 1; omega,
              ← List.append_assoc]
            exact List.prefix_append _ _
          have htq : tailOf L h <+: q := by
            rw [← e1]; exact List.dropLast_prefix q
          obtain ⟨ext, hext⟩ := (hmt.trans htq).trans h1
          rw [← hext]
          refine chainBefore.ancestor _ _ ?_
          intro hnil
          subst hnil
          rw [List.append_nil] at hext
          have hlen := congrArg List.length hext
          have l1 := congrArg List.length e1
          have := h1.length_le
          rw [List.length_dropLast, tailOf] at l1
          have n1 : 1 ≤ q.length := List.length_pos_iff.mpr
            (kept_ne_nil (isHead_kept (mem_childHeads.mp hq).1))
          simp only [List.length_append, List.length_replicate] at *
          have h4 := lenOf_pos hh
          omega
        · rw [if_neg hl] at ha
          simp at ha

theorem childHead_root_length {L : List (List ℕ)} {q : List ℕ}
    (hq : q ∈ childHeads L []) : q.length = 1 := by
  obtain ⟨hqh, hqd⟩ := mem_childHeads.mp hq
  have := congrArg List.length hqd
  rw [List.length_dropLast] at this
  have n1 : 1 ≤ q.length := List.length_pos_iff.mpr
    (kept_ne_nil (isHead_kept hqh))
  simp at this
  omega

theorem walk_nodup (L : List (List ℕ)) : (walk L).Nodup := by
  rw [walk]
  refine nodup_flatMap_of_disjoint (nodup_childHeads L []) ?_ ?_
  · intro q hq
    exact walkE_nodup _ q (mem_childHeads.mp hq).1
  · intro q hq q' hq' hne c hc hc'
    have h1 := (walkE_sound _ q c (mem_childHeads.mp hq).1 hc).2
    have h2 := (walkE_sound _ q' c (mem_childHeads.mp hq').1 hc').2
    exact hne (prefix_eq_of_length h1 h2
      (by rw [childHead_root_length hq, childHead_root_length hq']))

/-- **T-walk, order half**: the walk is pairwise in display order. -/
theorem walk_pairwise (L : List (List ℕ)) :
    (walk L).Pairwise chainBefore := by
  rw [walk]
  refine pairwise_flatMap (fun q hq => walkE_pairwise _ q
    (mem_childHeads.mp hq).1) ?_
  have hsorted := (sorted_childHeads L []).and
    (List.nodup_iff_pairwise_ne.mp (nodup_childHeads L []))
  refine hsorted.imp_of_mem ?_
  intro q q' hqm hqm' ⟨hle, hne⟩ c hc c' hc'
  have h1 := (walkE_sound _ q c (mem_childHeads.mp hqm).1 hc).2
  have h2 := (walkE_sound _ q' c' (mem_childHeads.mp hqm').1 hc').2
  obtain ⟨r1, hr1⟩ := childHead_subtree_form hqm h1
  obtain ⟨r2, hr2⟩ := childHead_subtree_form hqm' h2
  rw [hr1, hr2]
  refine chainBefore.newer _ _ _ _ _ ?_
  have hdne : q.getLastD 0 ≠ q'.getLastD 0 := by
    intro heq
    apply hne
    have e1 := (mem_childHeads.mp hqm).2
    have e2 := (mem_childHeads.mp hqm').2
    conv_lhs => rw [concat_getLastD
      (kept_ne_nil (isHead_kept (mem_childHeads.mp hqm).1))]
    conv_rhs => rw [concat_getLastD
      (kept_ne_nil (isHead_kept (mem_childHeads.mp hqm').1))]
    rw [e1, e2, heq]
  omega

/-- **T-walk, membership half**: the walk emits exactly the live chains. -/
theorem mem_walk {L : List (List ℕ)} (hnil : [] ∉ L) {c : List ℕ} :
    c ∈ walk L ↔ c ∈ L := by
  constructor
  · intro hc
    obtain ⟨q, hq, hcq⟩ := List.mem_flatMap.mp hc
    exact (walkE_sound _ q c (mem_childHeads.mp hq).1 hcq).1
  · intro hc
    have hne : c ≠ [] := fun h => hnil (h ▸ hc)
    have hkept : c ∈ keptL L := kept_of_live hc hne
    obtain ⟨d, cs, rfl⟩ : ∃ d cs, c = d :: cs := by
      cases c with
      | nil => exact absurd rfl hne
      | cons d cs => exact ⟨d, cs, rfl⟩
    have hq0 : ([d] : List ℕ) ∈ keptL L :=
      kept_of_prefix hkept ⟨cs, rfl⟩ (by simp)
    have hq0h : isHead L [d] = true := by
      refine isHead_of_kept_not_fusible hq0 ?_
      cases hf : fusible L [d] with
      | false => rfl
      | true =>
          exfalso
          have := fusible_parent_kept hf
          exact kept_ne_nil this rfl
    rw [walk]
    refine List.mem_flatMap.mpr ⟨[d], mem_childHeads.mpr ⟨hq0h, rfl⟩, ?_⟩
    refine walkE_complete _ [d] _ hq0h hc hkept ⟨cs, rfl⟩ ?_
    simp

/-- **T-walk, packaged** (walk = query): the structural walk of the run
table is a duplicate-free enumeration of exactly the live chains, pairwise
in display (`chainBefore`) order — which pins it to THE display sequence,
strict orders having unique sorted enumerations. No stability hypothesis. -/
theorem walk_display (L : List (List ℕ)) (hnil : [] ∉ L) :
    (walk L).Nodup ∧ (∀ c, c ∈ walk L ↔ c ∈ L)
      ∧ (walk L).Pairwise chainBefore :=
  ⟨walk_nodup L, fun _ => mem_walk hnil, walk_pairwise L⟩

/-- **T-walk, key form**: the walk is descending in `keyLt` on the coded
coordinates — the exact sort order of the fold's document — for any ordered
prefix code. -/
theorem walk_pairwise_keyLt (Γ : OrderedPrefixCode) {L : List (List ℕ)}
    (hpos : ∀ l ∈ L, PosChain l) (hnil : [] ∉ L) :
    (walk L).Pairwise (fun c1 c2 =>
      keyLt (key (coordOf Γ c2)) (key (coordOf Γ c1)) = true) := by
  refine (walk_pairwise L).imp_of_mem ?_
  intro c1 c2 h1 h2 hb
  have hp1 : PosChain c1 := posChain_of_kept hpos
    (kept_of_live (mem_walk hnil |>.mp h1)
      (fun h => hnil (h ▸ (mem_walk hnil |>.mp h1))))
  have hp2 : PosChain c2 := posChain_of_kept hpos
    (kept_of_live (mem_walk hnil |>.mp h2)
      (fun h => hnil (h ▸ (mem_walk hnil |>.mp h2))))
  exact Sal.EmbedRGA.chainBefore_display Γ hp1 hp2 hb

/-! ## §7  T-mut — simulation of the mutation rules

The table is a **function of the live-chain set** (`tableOf_congr`): that is
the merge rule (a merge delivers the union of event sets, and the union's
table is the rebuild — no order or arrival dependence), and it is what makes
every other rule statable set-wise. The typing rule (`tableOf_insert_extend`)
is proved generically: extending a childless live node by a delta-1 child
bumps ONE `len` field — O(1) table work for a keystroke. The remaining rules
(mid-run split, the delete liveness split, delete-vanish with cascade,
coalesce as the forced delete-inverse, vanished-anchor materialization) are
pinned by the instance SPOTs (D1–D5 shapes) and their generic forms are
recorded as owed. -/

theorem keptL_congr {L L' : List (List ℕ)} (hmem : ∀ c, c ∈ L ↔ c ∈ L') :
    ∀ x, x ∈ keptL L ↔ x ∈ keptL L' := by
  intro x
  rw [mem_keptL, mem_keptL]
  constructor
  · rintro ⟨hne, l, hl, hp⟩
    exact ⟨hne, l, (hmem l).mp hl, hp⟩
  · rintro ⟨hne, l, hl, hp⟩
    exact ⟨hne, l, (hmem l).mpr hl, hp⟩

theorem fusible_congr {L L' : List (List ℕ)}
    (hmem : ∀ c, c ∈ L ↔ c ∈ L') (c : List ℕ) :
    fusible L c = fusible L' c := by
  have hk := keptL_congr hmem
  simp only [fusible]
  rw [decide_eq_decide.mpr (hk c), decide_eq_decide.mpr (hk c.dropLast),
    decide_eq_decide.mpr (hmem c), decide_eq_decide.mpr (hmem c.dropLast),
    decide_eq_decide.mpr (show (∀ c' ∈ keptL L, c'.dropLast = c.dropLast
        → c' = c) ↔ (∀ c' ∈ keptL L', c'.dropLast = c.dropLast → c' = c) from
      ⟨fun h c' hc' => h c' ((hk c').mpr hc'),
       fun h c' hc' => h c' ((hk c').mp hc')⟩)]

theorem headOf_congr {L L' : List (List ℕ)}
    (hmem : ∀ c, c ∈ L ↔ c ∈ L') :
    ∀ n (c : List ℕ), c.length ≤ n → headOf L c = headOf L' c := by
  intro n
  induction n with
  | zero =>
      intro c hc
      have : c = [] := List.length_eq_zero_iff.mp (by omega)
      subst this
      rw [headOf_of_not_fusible, headOf_of_not_fusible]
      · cases hf : fusible L' [] with
        | false => rfl
        | true => exact absurd (fusible_ne_nil hf) (by simp)
      · cases hf : fusible L [] with
        | false => rfl
        | true => exact absurd (fusible_ne_nil hf) (by simp)
  | succ n ih =>
      intro c hc
      cases hf : fusible L c with
      | true =>
          have hf' : fusible L' c = true := by
            rw [← fusible_congr hmem]; exact hf
          rw [headOf_of_fusible hf, headOf_of_fusible hf']
          refine ih c.dropLast ?_
          have : c ≠ [] := fusible_ne_nil hf
          have : 0 < c.length := List.length_pos_iff.mpr this
          rw [List.length_dropLast]
          omega
      | false =>
          have hf' : fusible L' c = false := by
            rw [← fusible_congr hmem]; exact hf
          rw [headOf_of_not_fusible hf, headOf_of_not_fusible hf']

theorem isHead_congr {L L' : List (List ℕ)}
    (hmem : ∀ c, c ∈ L ↔ c ∈ L') (c : List ℕ) :
    isHead L c = isHead L' c := by
  simp only [isHead]
  rw [decide_eq_decide.mpr (keptL_congr hmem c), fusible_congr hmem]

theorem keptL_perm {L L' : List (List ℕ)}
    (hmem : ∀ c, c ∈ L ↔ c ∈ L') : (keptL L).Perm (keptL L') :=
  (List.perm_ext_iff_of_nodup (nodup_keptL L) (nodup_keptL L')).mpr
    (keptL_congr hmem)

theorem lenOf_congr {L L' : List (List ℕ)}
    (hmem : ∀ c, c ∈ L ↔ c ∈ L') (h : List ℕ) :
    lenOf L h = lenOf L' h := by
  rw [lenOf, lenOf, runMembers, runMembers]
  have h1 : (keptL L).filter (fun c => headOf L c == h)
      = (keptL L).filter (fun c => headOf L' c == h) := by
    refine List.filter_congr ?_
    intro c hc
    rw [headOf_congr hmem c.length c (le_refl _)]
  rw [h1]
  exact ((keptL_perm hmem).filter _).length_eq

theorem headsList_congr {L L' : List (List ℕ)}
    (hmem : ∀ c, c ∈ L ↔ c ∈ L') : headsList L = headsList L' := by
  refine hLt_sorted_ext (sorted_headsList L) (sorted_headsList L') ?_
  intro c
  rw [mem_headsList, mem_headsList, isHead_congr hmem]

/-- **T-mut (merge): the table is a function of the live-chain set.** Two
states with the same live chains — a merge's union of event sets however
delivered, in whatever order — compile to the *identical* canonical table.
This is the incremental-equals-canonical PBT gate, generically. -/
theorem tableOf_congr {L L' : List (List ℕ)}
    (hmem : ∀ c, c ∈ L ↔ c ∈ L') : tableOf L = tableOf L' := by
  rw [tableOf, tableOf, ← headsList_congr hmem]
  refine List.map_congr_left ?_
  intro h hh
  rw [entryOfHead, entryOfHead]
  have hk := keptL_congr hmem h.dropLast
  by_cases hp : h.dropLast ∈ keptL L
  · rw [if_pos hp, if_pos (hk.mp hp)]
    rw [← headsList_congr hmem,
      ← headOf_congr hmem h.dropLast.length h.dropLast (le_refl _),
      ← lenOf_congr hmem]
    have : decide (h ∈ L) = decide (h ∈ L') := decide_eq_decide.mpr (hmem h)
    rw [this]
  · rw [if_neg hp, if_neg (fun hx => hp (hk.mpr hx))]
    rw [← lenOf_congr hmem]
    have : decide (h ∈ L) = decide (h ∈ L') := decide_eq_decide.mpr (hmem h)
    rw [this]

/-! ### The typing rule: extend a run in O(1) table work -/

theorem fusible_eq_true_iff {L : List (List ℕ)} {c : List ℕ} :
    fusible L c = true ↔
    c ∈ keptL L ∧ c.dropLast ∈ keptL L ∧ c.getLastD 0 = 1
    ∧ (∀ c' ∈ keptL L, c'.dropLast = c.dropLast → c' = c)
    ∧ ((c ∈ L) ↔ (c.dropLast ∈ L)) := by
  simp only [fusible, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    exact ⟨h1, h2, h3, h4, decide_eq_decide.mp h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, decide_eq_decide.mpr h5⟩

theorem child_of_parent_eq {x p : List ℕ} (hne : x ≠ [])
    (hd : x.dropLast = p) : x = p ++ [x.getLastD 0] := by
  conv_lhs => rw [concat_getLastD hne]
  rw [hd]

section InsertExtend

variable {L : List (List ℕ)} {a : List ℕ}
  (ha : a ∈ L) (hnil : ([] : List ℕ) ∉ L)
  (hchildless : ∀ d, (a ++ [d]) ∉ keptL L)

include ha hnil in
theorem extend_kept_iff (hchildless : ∀ d, (a ++ [d]) ∉ keptL L) :
    ∀ x, x ∈ keptL (L ++ [a ++ [1]]) ↔ x ∈ keptL L ∨ x = a ++ [1] := by
  intro x
  have hane : a ≠ [] := fun h => hnil (h ▸ ha)
  rw [mem_keptL]
  constructor
  · rintro ⟨hne, l, hl, hp⟩
    rcases List.mem_append.mp hl with hl | hl
    · exact Or.inl (mem_keptL.mpr ⟨hne, l, hl, hp⟩)
    · rw [List.mem_singleton] at hl
      subst hl
      by_cases hx : x = a ++ [1]
      · exact Or.inr hx
      · left
        have hpa : x <+: a := by
          have := prefix_dropLast_of_ne hp hx
          rwa [List.dropLast_concat] at this
        exact mem_keptL.mpr ⟨hne, a, ha, hpa⟩
  · rintro (hx | rfl)
    · obtain ⟨hne, l, hl, hp⟩ := mem_keptL.mp hx
      exact ⟨hne, l, List.mem_append_left _ hl, hp⟩
    · exact ⟨by simp, a ++ [1], List.mem_append_right _ (by simp),
        List.prefix_refl _⟩

include ha hnil hchildless in
theorem extend_new_not_kept : a ++ [1] ∉ keptL L := hchildless 1

include ha hnil hchildless in
theorem extend_fusible_old {x : List ℕ} (hx : x ∈ keptL L) :
    fusible (L ++ [a ++ [1]]) x = fusible L x := by
  have hane : a ≠ [] := fun h => hnil (h ▸ ha)
  have hkiff := extend_kept_iff ha hnil hchildless
  have hxc : x ≠ a ++ [1] := fun h => hchildless 1 (h ▸ hx)
  rw [Bool.eq_iff_iff, fusible_eq_true_iff, fusible_eq_true_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have hd : x.dropLast ∈ keptL L := by
      rcases (hkiff x.dropLast).mp h2 with h | h
      · exact h
      · exfalso
        apply hchildless 1
        rw [← h]
        exact kept_of_prefix hx (List.dropLast_prefix x)
          (by rw [h]; simp)
    have hdc : x.dropLast ≠ a ++ [1] := fun h =>
      hchildless 1 (h ▸ hd)
    refine ⟨hx, hd, h3, ?_, ?_⟩
    · intro c' hc' hpar
      exact h4 c' ((hkiff c').mpr (Or.inl hc')) hpar
    · rw [show (x ∈ L) ↔ (x ∈ L ++ [a ++ [1]]) from
        ⟨fun h => List.mem_append_left _ h,
         fun h => by
          rcases List.mem_append.mp h with h | h
          · exact h
          · rw [List.mem_singleton] at h; exact absurd h hxc⟩]
      rw [show (x.dropLast ∈ L) ↔ (x.dropLast ∈ L ++ [a ++ [1]]) from
        ⟨fun h => List.mem_append_left _ h,
         fun h => by
          rcases List.mem_append.mp h with h | h
          · exact h
          · rw [List.mem_singleton] at h; exact absurd h hdc⟩]
      exact h5
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have hdc : x.dropLast ≠ a ++ [1] := fun h =>
      hchildless 1 (h ▸ h2)
    refine ⟨(hkiff x).mpr (Or.inl hx),
      (hkiff x.dropLast).mpr (Or.inl h2), h3, ?_, ?_⟩
    · intro c' hc' hpar
      rcases (hkiff c').mp hc' with hc' | rfl
      · exact h4 c' hc' hpar
      · exfalso
        rw [List.dropLast_concat] at hpar
        apply hchildless (x.getLastD 0)
        rw [← child_of_parent_eq (kept_ne_nil hx) hpar.symm]
        exact hx
    · rw [show (x ∈ L ++ [a ++ [1]]) ↔ (x ∈ L) from
        ⟨fun h => by
          rcases List.mem_append.mp h with h | h
          · exact h
          · rw [List.mem_singleton] at h; exact absurd h hxc,
         fun h => List.mem_append_left _ h⟩]
      rw [show (x.dropLast ∈ L ++ [a ++ [1]]) ↔ (x.dropLast ∈ L) from
        ⟨fun h => by
          rcases List.mem_append.mp h with h | h
          · exact h
          · rw [List.mem_singleton] at h; exact absurd h hdc,
         fun h => List.mem_append_left _ h⟩]
      exact h5

include ha hnil hchildless in
theorem extend_fusible_new :
    fusible (L ++ [a ++ [1]]) (a ++ [1]) = true := by
  have hane : a ≠ [] := fun h => hnil (h ▸ ha)
  have hkiff := extend_kept_iff ha hnil hchildless
  rw [fusible_eq_true_iff]
  refine ⟨(hkiff _).mpr (Or.inr rfl), ?_, ?_, ?_, ?_⟩
  · rw [List.dropLast_concat]
    exact (hkiff a).mpr (Or.inl (kept_of_live ha hane))
  · rw [List.getLastD_concat]
  · intro c' hc' hpar
    rw [List.dropLast_concat] at hpar
    rcases (hkiff c').mp hc' with hc' | rfl
    · exfalso
      apply hchildless (c'.getLastD 0)
      rw [← child_of_parent_eq (kept_ne_nil hc') hpar]
      exact hc'
    · rfl
  · rw [List.dropLast_concat]
    constructor
    · intro _
      exact List.mem_append_left _ ha
    · intro _
      exact List.mem_append_right _ (by simp)

include ha hnil hchildless in
theorem extend_isHead_old {x : List ℕ} (hx : x ∈ keptL L) :
    isHead (L ++ [a ++ [1]]) x = isHead L x := by
  simp only [isHead]
  rw [extend_fusible_old ha hnil hchildless hx,
    decide_eq_decide.mpr (show x ∈ keptL (L ++ [a ++ [1]]) ↔ x ∈ keptL L from
      ⟨fun _ => hx,
       fun _ => (extend_kept_iff ha hnil hchildless x).mpr (Or.inl hx)⟩)]

include ha hnil hchildless in
theorem extend_headOf_old :
    ∀ n (x : List ℕ), x.length ≤ n → x ∈ keptL L →
      headOf (L ++ [a ++ [1]]) x = headOf L x := by
  intro n
  induction n with
  | zero =>
      intro x hx hkx
      exact absurd (List.length_pos_iff.mpr (kept_ne_nil hkx)) (by omega)
  | succ n ih =>
      intro x hx hkx
      cases hf : fusible L x with
      | true =>
          rw [headOf_of_fusible ((extend_fusible_old ha hnil hchildless
            hkx).trans hf), headOf_of_fusible hf]
          refine ih x.dropLast ?_ (fusible_parent_kept hf)
          have : 0 < x.length := List.length_pos_iff.mpr (kept_ne_nil hkx)
          rw [List.length_dropLast]
          omega
      | false =>
          rw [headOf_of_not_fusible ((extend_fusible_old ha hnil hchildless
            hkx).trans hf), headOf_of_not_fusible hf]

include ha hnil hchildless in
theorem extend_headOf_new :
    headOf (L ++ [a ++ [1]]) (a ++ [1]) = headOf L a := by
  have hane : a ≠ [] := fun h => hnil (h ▸ ha)
  rw [headOf_of_fusible (extend_fusible_new ha hnil hchildless),
    List.dropLast_concat]
  exact extend_headOf_old ha hnil hchildless a.length a (le_refl _)
    (kept_of_live ha hane)

include ha hnil hchildless in
theorem extend_headsList : headsList (L ++ [a ++ [1]]) = headsList L := by
  refine hLt_sorted_ext (sorted_headsList _) (sorted_headsList _) ?_
  intro c
  rw [mem_headsList, mem_headsList]
  constructor
  · intro h
    rcases (extend_kept_iff ha hnil hchildless c).mp (isHead_kept h)
      with hold | rfl
    · rwa [extend_isHead_old ha hnil hchildless hold] at h
    · exfalso
      have h1 := isHead_not_fusible h
      rw [extend_fusible_new ha hnil hchildless] at h1
      exact Bool.noConfusion h1
  · intro h
    rw [extend_isHead_old ha hnil hchildless (isHead_kept h)]
    exact h

include ha hnil hchildless in
theorem extend_lenOf {h : List ℕ} (hh : isHead L h = true) :
    lenOf (L ++ [a ++ [1]]) h
      = lenOf L h + (if h = headOf L a then 1 else 0) := by
  have hperm : (runMembers (L ++ [a ++ [1]]) h).Perm
      (if h = headOf L a then (a ++ [1]) :: runMembers L h
       else runMembers L h) := by
    refine (List.perm_ext_iff_of_nodup ((nodup_keptL _).filter _) ?_).mpr ?_
    · by_cases hcase : h = headOf L a
      · rw [if_pos hcase]
        exact List.Pairwise.cons
          (fun y hy heq => hchildless 1
            (heq ▸ (mem_runMembers.mp hy).1))
          ((nodup_keptL L).filter _)
      · rw [if_neg hcase]
        exact (nodup_keptL L).filter _
    · intro x
      simp only [List.mem_filter, beq_iff_eq]
      constructor
      · rintro ⟨hxk, hxh⟩
        rcases (extend_kept_iff ha hnil hchildless x).mp hxk with hold | rfl
        · rw [extend_headOf_old ha hnil hchildless x.length x (le_refl _)
            hold] at hxh
          by_cases hcase : h = headOf L a
          · rw [if_pos hcase]
            exact List.mem_cons_of_mem _ (mem_runMembers.mpr ⟨hold, hxh⟩)
          · rw [if_neg hcase]
            exact mem_runMembers.mpr ⟨hold, hxh⟩
        · rw [extend_headOf_new ha hnil hchildless] at hxh
          rw [if_pos hxh.symm]
          exact List.mem_cons_self
      · intro hx
        by_cases hcase : h = headOf L a
        · rw [if_pos hcase] at hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨(extend_kept_iff ha hnil hchildless _).mpr (Or.inr rfl),
              by rw [extend_headOf_new ha hnil hchildless, hcase]⟩
          · obtain ⟨hxk, hxh⟩ := mem_runMembers.mp hx
            exact ⟨(extend_kept_iff ha hnil hchildless x).mpr (Or.inl hxk),
              by rw [extend_headOf_old ha hnil hchildless x.length x
                (le_refl _) hxk]; exact hxh⟩
        · rw [if_neg hcase] at hx
          obtain ⟨hxk, hxh⟩ := mem_runMembers.mp hx
          exact ⟨(extend_kept_iff ha hnil hchildless x).mpr (Or.inl hxk),
            by rw [extend_headOf_old ha hnil hchildless x.length x
              (le_refl _) hxk]; exact hxh⟩
  have hlen := hperm.length_eq
  by_cases hcase : h = headOf L a
  · rw [if_pos hcase] at hlen
    rw [if_pos hcase]
    rw [lenOf, lenOf, hlen]
    simp
  · rw [if_neg hcase] at hlen
    rw [if_neg hcase]
    rw [lenOf, lenOf, hlen]
    omega

include ha hnil hchildless in
/-- **T-mut (typing / insert extends a run)**: appending a delta-1 child to
a childless live node re-canonicalizes to the SAME table with ONE `len`
field bumped — the coalesce-after-attach path, O(1) table work per
keystroke. The other insert shape (anchor interior or label ≠ 1, the mid-run
split / new-entry rule) and the delete family are pinned concretely by the
instance SPOTs; their generic forms are recorded as owed. -/
theorem tableOf_insert_extend :
    tableOf (L ++ [a ++ [1]])
      = (headsList L).map (fun h =>
          if h = headOf L a
          then { entryOfHead L h with len := (entryOfHead L h).len + 1 }
          else entryOfHead L h) := by
  rw [tableOf, extend_headsList ha hnil hchildless]
  refine List.map_congr_left ?_
  intro h hh
  have hhead : isHead L h = true := mem_headsList.mp hh
  have hkept : h ∈ keptL L := isHead_kept hhead
  have hne_c : h ≠ a ++ [1] := fun heq => hchildless 1 (heq ▸ hkept)
  have hdne_c : h.dropLast ≠ a ++ [1] := by
    intro heq
    apply hchildless 1
    rw [← heq]
    exact kept_of_prefix hkept (List.dropLast_prefix h) (by rw [heq]; simp)
  have hcond : (h.dropLast ∈ keptL (L ++ [a ++ [1]]))
      ↔ (h.dropLast ∈ keptL L) := by
    rw [extend_kept_iff ha hnil hchildless]
    exact ⟨fun hor => hor.resolve_right (fun h' => absurd h' hdne_c),
      Or.inl⟩
  have hlive : (h ∈ L ++ [a ++ [1]]) ↔ (h ∈ L) := by
    constructor
    · intro hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hm
      · rw [List.mem_singleton] at hm
        exact absurd hm hne_c
    · exact fun hm => List.mem_append_left _ hm
  have hfields : entryOfHead (L ++ [a ++ [1]]) h
      = { entryOfHead L h with
          len := lenOf L h + (if h = headOf L a then 1 else 0) } := by
    rw [entryOfHead, entryOfHead]
    by_cases hp : h.dropLast ∈ keptL L
    · rw [if_pos (hcond.mpr hp), if_pos hp]
      rw [extend_headsList ha hnil hchildless,
        extend_headOf_old ha hnil hchildless h.dropLast.length h.dropLast
          (le_refl _) hp,
        decide_eq_decide.mpr hlive,
        extend_lenOf ha hnil hchildless hhead]
    · rw [if_neg (fun hx => hp (hcond.mp hx)), if_neg hp]
      rw [decide_eq_decide.mpr hlive,
        extend_lenOf ha hnil hchildless hhead]
  rw [hfields]
  by_cases hcase : h = headOf L a
  · rw [if_pos hcase, if_pos hcase]
    rfl
  · rw [if_neg hcase, if_neg hcase]
    refine RTEntry.ext' rfl rfl rfl ?_
    show lenOf L h + 0 = (entryOfHead L h).len
    rw [Nat.add_zero]
    rfl

end InsertExtend

/-! ## §7¼  T-mut — the four remaining mutation rules, as generic perturbations

`tableOf_insert_extend` (§7) is the happy insert path (childless live anchor,
`delta = 1`: coalesce-after-attach, one `len` bump). The four rules that the
predecessor left SPOT-pinned are promoted here to **generic** state-level
theorems, each stated as the perturbation of `keptL`/`fusible`/`isHead` (hence
`headOf`, `lenOf`, `tableOf`) under the operation on the live-chain set.
These are exactly the structural facts the instance SPOTs D1/D2/D4/D5 pin
concretely. As everywhere in this file, no stability or honesty hypothesis
appears. -/

/-- **Insert-family `keptL` perturbation** (the shared root of D1/D5 and the
`tableOf_insert_extend` keptL side): adding a chain `w` to the live set adds
exactly `w`'s nonempty prefixes to the kept tree. -/
theorem mem_keptL_snoc {L : List (List ℕ)} {w x : List ℕ} :
    x ∈ keptL (L ++ [w]) ↔ x ∈ keptL L ∨ (x ≠ [] ∧ x <+: w) := by
  rw [mem_keptL, mem_keptL]
  constructor
  · rintro ⟨hne, l, hl, hp⟩
    rcases List.mem_append.mp hl with hl | hl
    · exact Or.inl ⟨hne, l, hl, hp⟩
    · rw [List.mem_singleton] at hl; subst hl; exact Or.inr ⟨hne, hp⟩
  · rintro (⟨hne, l, hl, hp⟩ | ⟨hne, hp⟩)
    · exact ⟨hne, l, List.mem_append_left _ hl, hp⟩
    · exact ⟨hne, w, List.mem_append_right _ (by simp), hp⟩

/-! ### D2 — delete of a node with kept children: the liveness split

Deleting `x` (which still has a kept descendant) leaves the kept tree
untouched (`delete_keptL_eq`) but flips `x` dead, breaking fusibility on both
of `x`'s incident edges when the neighbours are live: the run carrying `x`
splits into the live prefix, the dead singleton `x`, and the live suffix
(SPOT `spot_d2_liveness_split`). -/

section DeleteLiveness

variable {L L' : List (List ℕ)} {x : List ℕ}
  (hxne : x ≠ [])
  (hchild : ∃ e, x ++ [e] ∈ keptL L)
  (hmem' : ∀ c, c ∈ L' ↔ (c ∈ L ∧ c ≠ x))

include hchild hmem' in
/-- **D2, keptL invariance**: a delete that keeps a descendant leaves the kept
tree pointwise unchanged (the dead node survives as a dead ancestor). -/
theorem delete_keptL_eq (c : List ℕ) : c ∈ keptL L' ↔ c ∈ keptL L := by
  rw [mem_keptL, mem_keptL]
  constructor
  · rintro ⟨hne, l, hl, hp⟩
    exact ⟨hne, l, ((hmem' l).mp hl).1, hp⟩
  · rintro ⟨hne, l, hl, hp⟩
    by_cases hlx : l = x
    · obtain ⟨e, he⟩ := hchild
      obtain ⟨-, l', hl', hp'⟩ := mem_keptL.mp he
      have hl'x : l' ≠ x := by
        intro heq
        have hle := hp'.length_le
        rw [heq] at hle
        simp only [List.length_append, List.length_cons, List.length_nil]
          at hle
        omega
      refine ⟨hne, l', (hmem' l').mpr ⟨hl', hl'x⟩, ?_⟩
      rw [hlx] at hp
      exact hp.trans ((List.prefix_append x [e]).trans hp')
    · exact ⟨hne, l, (hmem' l).mpr ⟨hl, hlx⟩, hp⟩

include hmem' in
theorem delete_x_dead : x ∉ L' := fun hm => ((hmem' x).mp hm).2 rfl

include hxne hmem' in
/-- **D2, the run breaks *before* `x`**: with `x` dead and its (live) parent
still live, `x`'s incoming edge is no longer fusible — `x` becomes a head. -/
theorem delete_fusible_x_false (hpar : x.dropLast ∈ L) :
    fusible L' x = false := by
  cases hf : fusible L' x with
  | false => rfl
  | true =>
      exfalso
      have hlv := fusible_live hf
      have hxL' : x ∉ L' := delete_x_dead hmem'
      have hdxne : x.dropLast ≠ x := by
        intro heq
        have hpos := List.length_pos_iff.mpr hxne
        have := congrArg List.length heq
        rw [List.length_dropLast] at this; omega
      exact hxL' (hlv.mpr ((hmem' x.dropLast).mpr ⟨hpar, hdxne⟩))

include hmem' in
/-- **D2, the run breaks *after* `x`**: `x`'s (live) run successor loses its
fusible edge into the now-dead `x` — a second head. -/
theorem delete_fusible_succ_false {e : ℕ} (hsucc : x ++ [e] ∈ L) :
    fusible L' (x ++ [e]) = false := by
  cases hf : fusible L' (x ++ [e]) with
  | false => rfl
  | true =>
      exfalso
      have hlv := fusible_live hf
      rw [List.dropLast_concat] at hlv
      have hxL' : x ∉ L' := delete_x_dead hmem'
      have hsne : x ++ [e] ≠ x := by
        intro heq; have := congrArg List.length heq; simp at this
      exact hxL' (hlv.mp ((hmem' (x ++ [e])).mpr ⟨hsucc, hsne⟩))

end DeleteLiveness

/-! ### D1 — concurrent insert at an interior node: the mid-run split

Anchoring a second child `a ++ [d]` (`d ≠ 1`) at a node `a` that already has a
run successor `a ++ [1]` turns `a` into a branch point: **both** children
become heads, so the run carrying `a` splits into the `a`-prefix run, the
`a ++ [1]` suffix run, and the `a ++ [d]` singleton (SPOT `spot_d1_split`). -/

section MidRunSplit

variable {L : List (List ℕ)} {a : List ℕ} {d : ℕ}
  (hsucc : a ++ [1] ∈ keptL L) (hd : d ≠ 1)

theorem split_new_kept : a ++ [d] ∈ keptL (L ++ [a ++ [d]]) :=
  mem_keptL_snoc.mpr (Or.inr ⟨by simp, List.prefix_refl _⟩)

include hsucc in
theorem split_succ_kept : a ++ [1] ∈ keptL (L ++ [a ++ [d]]) :=
  mem_keptL_snoc.mpr (Or.inl hsucc)

include hd in
/-- **D1, the new child is a head**: `delta = d ≠ 1` fails fusibility. -/
theorem split_new_isHead : isHead (L ++ [a ++ [d]]) (a ++ [d]) = true := by
  refine isHead_of_kept_not_fusible split_new_kept ?_
  cases hf : fusible (L ++ [a ++ [d]]) (a ++ [d]) with
  | false => rfl
  | true =>
      exfalso
      have hg := (fusible_eq_true_iff.mp hf).2.2.1
      rw [List.getLastD_concat] at hg
      exact hd hg

include hsucc hd in
/-- **D1, the former run successor becomes a head**: `a` now has two kept
children, so `a ++ [1]` is no longer `a`'s unique kept child — the run splits
here. -/
theorem split_succ_isHead : isHead (L ++ [a ++ [d]]) (a ++ [1]) = true := by
  refine isHead_of_kept_not_fusible (split_succ_kept hsucc) ?_
  cases hf : fusible (L ++ [a ++ [d]]) (a ++ [1]) with
  | false => rfl
  | true =>
      exfalso
      have huniq := (fusible_eq_true_iff.mp hf).2.2.2.1
      have heq := huniq (a ++ [d]) split_new_kept
        (by rw [List.dropLast_concat, List.dropLast_concat])
      have := List.append_cancel_left heq
      injection this with h'
      exact hd h'

end MidRunSplit

/-! ### D5 — delivery under a vanished anchor: materialization

An op delivered against an anchor `m` that vanished locally (deleted while
childless, so `m ∉ keptL L`) carries `m`'s coordinate. Attaching the op's
chain `m ++ [d]` re-materializes `m` as **dead** kept structure: `m` becomes
kept again (`materialize_kept`) yet is not live (`materialize_dead`) — the
run-table cost of tombstone-freedom, paid with information the op carries
(SPOT `spot_d5_materialize`). -/

section Materialize

variable {L : List (List ℕ)} {m : List ℕ} {d : ℕ}
  (hmne : m ≠ []) (hvanished : m ∉ keptL L)

include hmne in
theorem materialize_kept : m ∈ keptL (L ++ [m ++ [d]]) :=
  mem_keptL_snoc.mpr (Or.inr ⟨hmne, List.prefix_append m [d]⟩)

include hmne hvanished in
theorem materialize_dead : m ∉ (L ++ [m ++ [d]]) := by
  intro hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hvanished (kept_of_live hm hmne)
  · rw [List.mem_singleton] at hm
    have := congrArg List.length hm; simp at this

end Materialize

/-! ### D4 — deleting the interloper re-coalesces: the FORCED delete-inverse

The inverse of D1, and the finding the note flags a paper proof would hand-wave
(§10): removing the childless interloper `a ++ [d]` makes `a ++ [1]` `a`'s
**unique** kept child again, so the edge re-fuses. Without this coalesce the
table stays split and drifts from canonical (SPOT `spot_d4_coalesce_necessity`).
`honly` records that in the pre-delete state `a`'s only kept children are the
run successor and the interloper. -/

section Coalesce

variable {L L' : List (List ℕ)} {a : List ℕ} {d : ℕ}
  (hane : a ≠ []) (hd : d ≠ 1)
  (hleaf : ∀ e, (a ++ [d]) ++ [e] ∉ keptL L)
  (hsucc : a ++ [1] ∈ keptL L)
  (hlv : (a ++ [1] ∈ L) ↔ (a ∈ L))
  (honly : ∀ c' ∈ keptL L, c'.dropLast = a → c' = a ++ [1] ∨ c' = a ++ [d])
  (hmem' : ∀ c, c ∈ L' ↔ (c ∈ L ∧ c ≠ a ++ [d]))

include hleaf hmem' in
/-- **D4, the interloper vanishes**: a childless leaf, once removed, leaves no
kept trace. -/
theorem coalesce_vanished : a ++ [d] ∉ keptL L' := by
  intro hk
  obtain ⟨-, l, hl, hp⟩ := mem_keptL.mp hk
  have hlne : l ≠ a ++ [d] := ((hmem' l).mp hl).2
  obtain ⟨e, he⟩ := take_succ_of_prefix hp (fun heq => hlne heq.symm)
  exact hleaf e (mem_keptL.mpr ⟨by simp, l, ((hmem' l).mp hl).1, he⟩)

include hd hleaf hsucc hmem' in
/-- **D4, keptL perturbation**: the kept tree loses exactly the interloper. -/
theorem coalesce_keptL (c : List ℕ) :
    c ∈ keptL L' ↔ (c ∈ keptL L ∧ c ≠ a ++ [d]) := by
  constructor
  · intro hk
    obtain ⟨hne, l, hl, hp⟩ := mem_keptL.mp hk
    exact ⟨mem_keptL.mpr ⟨hne, l, ((hmem' l).mp hl).1, hp⟩,
      fun hceq => (coalesce_vanished hleaf hmem') (hceq ▸ hk)⟩
  · rintro ⟨hk, hcne⟩
    obtain ⟨hne, l, hl, hp⟩ := mem_keptL.mp hk
    by_cases hlx : l = a ++ [d]
    · have hca : c <+: a := by
        rw [hlx] at hp
        have := prefix_dropLast_of_ne hp hcne
        rwa [List.dropLast_concat] at this
      obtain ⟨-, l₁, hl₁, hp₁⟩ := mem_keptL.mp hsucc
      have hl₁ne : l₁ ≠ a ++ [d] := by
        intro heq
        rw [heq] at hp₁
        have heqp := hp₁.eq_of_length (by simp)
        have := List.append_cancel_left heqp
        injection this with h'; exact hd h'.symm
      exact mem_keptL.mpr ⟨hne, l₁, (hmem' l₁).mpr ⟨hl₁, hl₁ne⟩,
        hca.trans ((List.prefix_append a [1]).trans hp₁)⟩
    · exact mem_keptL.mpr ⟨hne, l, (hmem' l).mpr ⟨hl, hlx⟩, hp⟩

include hane hd hleaf hsucc hlv honly hmem' in
/-- **D4, the edge re-fuses**: after the delete, `a ++ [1]`'s incoming edge is
fusible again — the coalesce. (In the pre-delete state it was split, D1.) -/
theorem coalesce_restored : fusible L' (a ++ [1]) = true := by
  have hkiff := coalesce_keptL (L := L) (L' := L') hd hleaf hsucc hmem'
  have hane_d : a ≠ a ++ [d] := fun heq => by
    have := congrArg List.length heq; simp at this
  have hsucc_d : a ++ [1] ≠ a ++ [d] := fun heq => by
    have := List.append_cancel_left heq; injection this with h'; exact hd h'.symm
  have hak : a ∈ keptL L := kept_of_prefix hsucc (List.prefix_append a [1]) hane
  rw [fusible_eq_true_iff]
  refine ⟨(hkiff (a ++ [1])).mpr ⟨hsucc, hsucc_d⟩, ?_, ?_, ?_, ?_⟩
  · rw [List.dropLast_concat]; exact (hkiff a).mpr ⟨hak, hane_d⟩
  · rw [List.getLastD_concat]
  · intro c' hc' hpar
    rw [List.dropLast_concat] at hpar
    have hc'p := (hkiff c').mp hc'
    rcases honly c' hc'p.1 hpar with h | h
    · exact h
    · exact absurd h hc'p.2
  · rw [List.dropLast_concat]
    constructor
    · intro hm
      exact (hmem' a).mpr ⟨hlv.mp ((hmem' (a ++ [1])).mp hm).1, hane_d⟩
    · intro hm
      exact (hmem' (a ++ [1])).mpr ⟨hlv.mpr ((hmem' a).mp hm).1, hsucc_d⟩

end Coalesce

/-! ## §7½  T-repr, image side — `tableOf` always lands in `Canonical`

`tableOf_stateOf` (§4) is the retraction on canonical inputs. Here is the
image direction: **every** `tableOf L` is a canonical table. Together with
`stateOf_tableOf` and `tableOf_stateOf` this closes the representation iso to
a genuine bijection between live-chain sets (up to `keptL`) and canonical
tables — the note §10's characterization "canonical = maximal fusible chains,
uniform liveness, tail attachment" is not just *recognized* by `Canonical`,
it is exactly the image of `tableOf`. No stability hypothesis. -/

/-- Indexing `tableOf` at `i`: the head sitting there is a head at index `i`,
compiling to that entry — packaged without a dependent `getElem` in scope. -/
theorem tableOf_entry_head (L : List (List ℕ)) (i : ℕ)
    (hi : i < (tableOf L).length) :
    ∃ h, isHead L h = true ∧ (headsList L).idxOf h = i
      ∧ (tableOf L)[i] = entryOfHead L h := by
  have hi' : i < (headsList L).length := by
    simpa only [tableOf, List.length_map] using hi
  refine ⟨(headsList L)[i], mem_headsList.mp (List.getElem_mem _),
    idxOf_getElem_nodup (nodup_headsList L) hi', ?_⟩
  simp only [tableOf, List.getElem_map]

/-- `getElem` at equal indices, dodging the dependent-proof motive block. -/
theorem getElem_idx_eq {T : Table} {i j : ℕ} (hi : i < T.length)
    (hj : j < T.length) (hij : i = j) : T[i]'hi = T[j]'hj := by
  subst hij; rfl

/-- Indexing `tableOf` at a known head's position: compiles that head. -/
theorem tableOf_getElem_idxOf (L : List (List ℕ)) {h : List ℕ}
    (hh : isHead L h = true)
    (hlt : (headsList L).idxOf h < (tableOf L).length) :
    (tableOf L)[(headsList L).idxOf h] = entryOfHead L h := by
  have hm : h ∈ headsList L := mem_headsList.mpr hh
  simp only [tableOf, List.getElem_map]
  congr 1
  exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hm)

/-- **T-repr, image side**: `tableOf L` is a canonical table, for every `L`. -/
theorem canonical_tableOf (L : List (List ℕ)) : Canonical (tableOf L) := by
  have hlen : (tableOf L).length = (headsList L).length := by simp [tableOf]
  refine ⟨?len_pos, ?par_back, ?par_tail, ?no_fuse, ?leaves_live, ?sorted⟩
  case len_pos =>
    intro e he
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
    obtain ⟨h, hh, -, hentry⟩ := tableOf_entry_head L i hi
    rw [hentry]; exact lenOf_pos hh
  case sorted =>
    rw [headsOf_tableOf]; exact sorted_headsList L
  case par_back =>
    intro i hi p hp
    obtain ⟨h, hh, hidxh, hentry⟩ := tableOf_entry_head L i hi
    rw [hentry] at hp; simp only [entryOfHead] at hp
    by_cases hpk : h.dropLast ∈ keptL L
    · rw [if_pos hpk] at hp
      have hpe : p = ((headsList L).idxOf (headOf L h.dropLast),
          h.dropLast.length - (headOf L h.dropLast).length) := by
        injection hp with hp; exact hp.symm
      rw [hpe]; dsimp only
      set g := headOf L h.dropLast with hg_def
      have hgm : g ∈ headsList L := mem_headsList.mpr (headOf_isHead hpk)
      have hne : h ≠ [] := kept_ne_nil (isHead_kept hh)
      have hglt : hLt g h = true := by
        have h1 : g.length ≤ h.dropLast.length := (headOf_prefix L _).length_le
        have h2 : h.dropLast.length < h.length := by
          rw [List.length_dropLast]
          have : 0 < h.length := List.length_pos_iff.mpr hne
          omega
        simp only [hLt, Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inl (by omega)
      have := idxOf_lt_of_hLt (sorted_headsList L) hgm
        (mem_headsList.mpr hh) hglt
      rwa [hidxh] at this
    · rw [if_neg hpk] at hp; exact absurd hp (by simp)
  case par_tail =>
    intro i hi p hp hj
    obtain ⟨h, hh, hidxh, hentry⟩ := tableOf_entry_head L i hi
    rw [hentry] at hp; simp only [entryOfHead] at hp
    by_cases hpk : h.dropLast ∈ keptL L
    · rw [if_pos hpk] at hp
      have hpe : p = ((headsList L).idxOf (headOf L h.dropLast),
          h.dropLast.length - (headOf L h.dropLast).length) := by
        injection hp with hp; exact hp.symm
      set g := headOf L h.dropLast with hg_def
      have hp1 : p.1 = (headsList L).idxOf g := by rw [hpe]
      have hp2 : p.2 = h.dropLast.length - g.length := by rw [hpe]
      have hjg : (headsList L).idxOf g < (tableOf L).length := hp1 ▸ hj
      rw [hp2, getElem_idx_eq hj hjg hp1,
        tableOf_getElem_idxOf L (headOf_isHead hpk) hjg]
      simp only [entryOfHead]
      have htail := head_parent_is_tail hh hpk
      rw [← hg_def] at htail
      have hlenpos := lenOf_pos (headOf_isHead hpk)
      have hdl : h.dropLast.length = g.length + (lenOf L g - 1) := by
        conv_lhs => rw [htail, tailOf]
        simp
      rw [hdl, ← hg_def]; omega
    · rw [if_neg hpk] at hp; exact absurd hp (by simp)
  case no_fuse =>
    intro i hi p hp hj hd1 hlive
    obtain ⟨h, hh, hidxh, hentry⟩ := tableOf_entry_head L i hi
    rw [hentry] at hp hd1 hlive; simp only [entryOfHead] at hp hd1 hlive
    by_cases hpk : h.dropLast ∈ keptL L
    · rw [if_pos hpk] at hp
      have hpe : p = ((headsList L).idxOf (headOf L h.dropLast),
          h.dropLast.length - (headOf L h.dropLast).length) := by
        injection hp with hp; exact hp.symm
      set g := headOf L h.dropLast with hg_def
      have hp1 : p.1 = (headsList L).idxOf g := by rw [hpe]
      have hjg : (headsList L).idxOf g < (tableOf L).length := hp1 ▸ hj
      rw [getElem_idx_eq hj hjg hp1,
        tableOf_getElem_idxOf L (headOf_isHead hpk) hjg] at hlive
      simp only [entryOfHead] at hlive
      rw [← hg_def] at hlive
      have hdm : h.dropLast ∈ runMembers L g :=
        mem_runMembers.mpr ⟨hpk, hg_def.symm⟩
      have hlifted : (h ∈ L) ↔ (h.dropLast ∈ L) := by
        rw [run_liveness_uniform hdm, decide_eq_decide.mp hlive]
      have hnf : fusible L h = false := isHead_not_fusible hh
      have hkh : h ∈ keptL L := isHead_kept hh
      have hnu : ¬ (∀ c' ∈ keptL L, c'.dropLast = h.dropLast → c' = h) := by
        intro huniq
        rw [fusible_eq_true_iff.mpr ⟨hkh, hpk, hd1, huniq, hlifted⟩] at hnf
        exact Bool.noConfusion hnf
      push_neg at hnu
      obtain ⟨c', hc'k, hc'd, hc'ne⟩ := hnu
      have hc'nf : fusible L c' = false := by
        cases hf : fusible L c' with
        | false => rfl
        | true => exact absurd (fusible_unique hf hkh (by rw [hc'd])).symm hc'ne
      have hc'h : isHead L c' = true := isHead_of_kept_not_fusible hc'k hc'nf
      have hc'm : c' ∈ headsList L := mem_headsList.mpr hc'h
      have hc'lt : (headsList L).idxOf c' < (tableOf L).length :=
        (List.idxOf_lt_length_of_mem hc'm).trans_eq hlen.symm
      refine ⟨(headsList L).idxOf c', hc'lt, ?_, ?_⟩
      · intro heq
        exact hc'ne ((List.idxOf_inj hc'm).mp (heq.trans hidxh.symm))
      · rw [hpe, tableOf_getElem_idxOf L hc'h hc'lt]
        simp only [entryOfHead]
        rw [if_pos (by rw [hc'd]; exact hpk), hc'd]
    · rw [if_neg hpk] at hp; exact absurd hp (by simp)
  case leaves_live =>
    intro i hi hlivef
    obtain ⟨h, hh, hidxh, hentry⟩ := tableOf_entry_head L i hi
    rw [hentry] at hlivef; simp only [entryOfHead] at hlivef
    have hhnl : h ∉ L := of_decide_eq_false hlivef
    have hkh : h ∈ keptL L := isHead_kept hh
    obtain ⟨hhne, l, hl, hpre⟩ := mem_keptL.mp hkh
    have hlm : l ∈ keptL L :=
      kept_of_live hl (fun hnil => hhne (List.prefix_nil.mp (hnil ▸ hpre)))
    have hnm : headOf L l ≠ h := by
      intro heq
      exact hhnl ((run_liveness_uniform (mem_runMembers.mpr ⟨hlm, heq⟩)).mp hl)
    obtain ⟨q, hqh, hqd, hqc⟩ := escape_run hh hlm hpre hnm
    have hqm : q ∈ headsList L := mem_headsList.mpr hqh
    have hqlt : (headsList L).idxOf q < (tableOf L).length :=
      (List.idxOf_lt_length_of_mem hqm).trans_eq hlen.symm
    have htk : tailOf L h ∈ keptL L := (mem_runMembers.mp (tailOf_mem hh)).1
    have hth : headOf L (tailOf L h) = h := (mem_runMembers.mp (tailOf_mem hh)).2
    refine ⟨(headsList L).idxOf q, hqlt, q.dropLast.length - h.length, ?_⟩
    rw [tableOf_getElem_idxOf L hqh hqlt]
    simp only [entryOfHead]
    rw [if_pos (by rw [hqd]; exact htk), hqd, hth, hidxh]

/-! ## §7¾  T-walk, representation faithfulness — the walk survives the round trip

`chainBefore` is a strict linear order (irreflexive, antisymmetric, total), so
a `Nodup` list that is pairwise `chainBefore` is the *unique* sorted
enumeration of its element set (`chainBefore_sorted_ext`). Hence the walk is
determined by the live-chain set alone: building the run table, recovering the
state, and walking it reproduces the original walk verbatim
(`walk_stateOf_tableOf`). This is the display-identity gate at the level of
the representation round trip. (The fully table-*direct* structural walk —
emitting run by run without materializing `stateOf` — is SPOT-verified at D1
in the instance file; its generic promotion is the remaining T-walk item.) -/

/-- Inversion of `chainBefore` into its two verdict shapes. -/
theorem chainBefore_inv {c1 c2 : List ℕ} (h : chainBefore c1 c2) :
    (∃ ext, ext ≠ [] ∧ c2 = c1 ++ ext) ∨
    (∃ p d e t1 t2, e < d ∧ c1 = p ++ d :: t1 ∧ c2 = p ++ e :: t2) := by
  cases h with
  | ancestor ch ext hne => exact Or.inl ⟨ext, hne, rfl⟩
  | newer p d e t1 t2 hlt => exact Or.inr ⟨p, d, e, t1, t2, hlt, rfl, rfl⟩

theorem chainBefore_ne {c1 c2 : List ℕ} (h : chainBefore c1 c2) : c1 ≠ c2 := by
  cases h with
  | ancestor ch ext hne =>
      intro heq
      have hl := congrArg List.length heq
      simp only [List.length_append] at hl
      exact hne (by rw [← List.length_eq_zero_iff]; omega)
  | newer p d e t1 t2 hlt =>
      intro heq
      have h2 := List.append_cancel_left heq
      injection h2 with h3 _
      omega

theorem chainBefore_irrefl (x : List ℕ) : ¬ chainBefore x x :=
  fun h => chainBefore_ne h rfl

theorem chainBefore_nil_right {z : List ℕ} (h : chainBefore z []) : False := by
  rcases chainBefore_inv h with ⟨ext, hne, heq⟩ | ⟨p, d, e, t1, t2, hlt, h1, h2⟩
  · exact hne (by rw [← List.length_eq_zero_iff]
                  have := congrArg List.length heq
                  simp only [List.length_append, List.length_nil] at this
                  omega)
  · simp at h2

/-- A shared head strips off the chain order. -/
theorem chainBefore_cons_strip {x : ℕ} {a b : List ℕ}
    (h : chainBefore (x :: a) (x :: b)) : chainBefore a b := by
  rcases chainBefore_inv h with ⟨ext, hne, heq⟩ | ⟨p, d, e, t1, t2, hlt, ha, hb⟩
  · rw [List.cons_append] at heq
    injection heq with _ h2
    rw [h2]
    exact chainBefore.ancestor a ext hne
  · cases p with
    | nil =>
        simp only [List.nil_append] at ha hb
        injection ha with h3 _
        injection hb with h5 _
        rw [← h3, ← h5] at hlt
        exact absurd hlt (Nat.lt_irrefl x)
    | cons y p' =>
        rw [List.cons_append] at ha hb
        injection ha with _ h4
        injection hb with _ h6
        rw [h4, h6]
        exact chainBefore.newer p' d e t1 t2 hlt

/-- Distinct heads decide the chain order at position 0: the larger label
displays first. -/
theorem chainBefore_cons_head_lt {x y : ℕ} {xs ys : List ℕ} (hxy : x ≠ y)
    (h : chainBefore (x :: xs) (y :: ys)) : y < x := by
  rcases chainBefore_inv h with ⟨ext, hne, heq⟩ | ⟨p, d, e, t1, t2, hlt, ha, hb⟩
  · rw [List.cons_append] at heq
    injection heq with hyx _
    exact absurd hyx.symm hxy
  · cases p with
    | nil =>
        simp only [List.nil_append] at ha hb
        injection ha with hxd _
        injection hb with hye _
        rw [hxd, hye]; exact hlt
    | cons z p' =>
        rw [List.cons_append] at ha hb
        injection ha with hxz _
        injection hb with hyz _
        exact absurd (hxz.trans hyz.symm) hxy

theorem chainBefore_asymm : ∀ {c1 c2 : List ℕ},
    chainBefore c1 c2 → ¬ chainBefore c2 c1 := by
  intro c1
  induction c1 with
  | nil => intro c2 _ h'; exact chainBefore_nil_right h'
  | cons x xs ih =>
      intro c2 h h'
      cases c2 with
      | nil => exact chainBefore_nil_right h
      | cons y ys =>
          by_cases hxy : x = y
          · subst hxy
            exact ih (chainBefore_cons_strip h) (chainBefore_cons_strip h')
          · have h1 := chainBefore_cons_head_lt hxy h
            have h2 := chainBefore_cons_head_lt (Ne.symm hxy) h'
            omega

/-- **Uniqueness of the sorted enumeration**: a `Nodup`, pairwise-`chainBefore`
list is fixed by its element set (`chainBefore` is a strict linear order). -/
theorem chainBefore_sorted_ext : ∀ {l l' : List (List ℕ)},
    l.Pairwise chainBefore → l'.Pairwise chainBefore →
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
        · rcases List.mem_cons.mp ((hmem y).mpr List.mem_cons_self) with h' | h'
          · exact h'.symm
          · exact absurd (hy x h) (chainBefore_asymm (hx y h'))
      subst hxy
      have htails : ∀ z, z ∈ xs ↔ z ∈ ys := by
        intro z
        constructor
        · intro hz
          rcases List.mem_cons.mp ((hmem z).mp (List.mem_cons_of_mem _ hz))
            with rfl | h
          · exact absurd (hx z hz) (chainBefore_irrefl _)
          · exact h
        · intro hz
          rcases List.mem_cons.mp ((hmem z).mpr (List.mem_cons_of_mem _ hz))
            with rfl | h
          · exact absurd (hy z hz) (chainBefore_irrefl _)
          · exact h
      rw [chainBefore_sorted_ext hxs hys htails]

/-- **T-walk, representation round trip**: building the run table from `L`,
recovering the state, and walking it reproduces `walk L` exactly — the walk is
a function of the live-chain set, so it survives the representation round trip
losslessly. No stability hypothesis. -/
theorem walk_stateOf_tableOf {L : List (List ℕ)} (hnil : [] ∉ L) :
    walk (stateOf (tableOf L)) = walk L := by
  have hiff := (stateOf_tableOf L hnil).2
  have hnil' : [] ∉ stateOf (tableOf L) := fun h => hnil ((hiff []).mp h)
  refine chainBefore_sorted_ext (walk_pairwise _) (walk_pairwise _) ?_
  intro c
  rw [mem_walk hnil', mem_walk hnil]
  exact hiff c

/-! ## §8  Axiom audit -/

#print axioms tail_attachment
#print axioms head_parent_is_tail
#print axioms stateOf_tableOf
#print axioms tableOf_stateOf
#print axioms cmpTable_iff_chainBefore
#print axioms cmpTable_eq_keyLt
#print axioms walk_display
#print axioms walk_pairwise_keyLt
#print axioms tableOf_congr
#print axioms tableOf_insert_extend
#print axioms canonical_tableOf
#print axioms mem_keptL_snoc
#print axioms delete_keptL_eq
#print axioms delete_fusible_x_false
#print axioms split_succ_isHead
#print axioms materialize_kept
#print axioms coalesce_restored
#print axioms chainBefore_asymm
#print axioms chainBefore_sorted_ext
#print axioms walk_stateOf_tableOf

end Sal.EmbedRGA.RunTable
