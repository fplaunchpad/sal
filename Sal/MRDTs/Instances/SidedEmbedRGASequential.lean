import Sal.MRDTs.Instances.SidedEmbedRGA

/-!
# Sequential-spec soundness: the sided embedded-chain RGA

Tier 3 (`EmbedRGA_SeqSpec.lean`) at the sided instance: the naive
TWO-SIDED text buffer. Entries are `(id, element)` pairs plus a root
SENTINEL entry (id 0) kept in the buffer so both insert directions have a
splice point: `ins … a R` splices immediately AFTER `a`'s entry, `ins … a
L` immediately BEFORE it, `del x` filters; the read drops the sentinel.
Because the sentinel is always present, the front insert is not a special
case: the anchor `a = 0` IS the sentinel.

The heart is the pair of **sided adjacency lemmas** at the kernel order
(`schainBefore_snocR_iff`, `schainBefore_snocL_iff`): a fresh R-extension
of an anchor displays immediately after it (its delta beats every
existing R-continuation, by sum-telescoping against the fresh stamp, and
the anchor's L-descendants sit on the other side), and a fresh
L-extension displays immediately before it (the L band is mirrored, so
the newest L-child hugs the node from above). The rooted fold `sRFold`
(the canonical state seeded with the sentinel record) makes both lemmas
apply uniformly, root anchor included: the sentinel's chain is `[]`.

Capstone: `sided_seq_sound`, under the datatype's own sequential
discipline `sSeqOK` (monotone insert stamps + `sApplicable` at each
fold), the rooted canonical state IS the two-sided buffer program, record
for record; `sided_seq_read` drops the sentinel on both sides.
-/

namespace Sal.MRDTs.Instances.SidedEmbedRGA

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode keyLt sKey sBlock Side SChain
  PosSChain sidedCoordOf sidedCoordOf_append sidedCoordOf_inj unaryCode
  schainBefore schainBefore_inv sEntryBefore keyLt_total keyLt_irrefl
  keyLt_asymm sdisplay_iff_schainBefore)

set_option linter.unusedSectionVars false

/-! ## §A  The naive two-sided buffer -/

/-- The user-visible projection of a record: `(id, element)`. -/
def sProj (r : SRec) : ℕ × ℕ := (r.1, r.2.1)

/-- The sentinel record: id 0, the empty coordinate (the virtual root's
key `[3]` sits exactly between the root's L-region and R-region). -/
def rootRec : SRec := (0, 0, [])

/-- Splice `p` immediately after the entry with id `a`. -/
def sInsAfter (a : ℕ) (p : ℕ × ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | q :: qs => if q.1 = a then q :: p :: qs else q :: sInsAfter a p qs

/-- Splice `p` immediately before the entry with id `a`. -/
def sInsBefore (a : ℕ) (p : ℕ × ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | q :: qs => if q.1 = a then p :: q :: qs else q :: sInsBefore a p qs

/-- The naive two-sided buffer program. -/
def sSpecStep (S : List (ℕ × ℕ)) (o : Op SOp) : List (ℕ × ℕ) :=
  match o.2.2 with
  | .ins el _ a sd =>
      match sd with
      | Side.R => sInsAfter a (o.1, el) S
      | Side.L => sInsBefore a (o.1, el) S
  | .del x => S.filter (fun p => decide (p.1 ≠ x))

def sSpecFold (ρ : List (Op SOp)) : List (ℕ × ℕ) :=
  ρ.foldl sSpecStep [(0, 0)]

theorem sSpecFold_snoc (ρ : List (Op SOp)) (o : Op SOp) :
    sSpecFold (ρ ++ [o]) = sSpecStep (sSpecFold ρ) o := by
  unfold sSpecFold
  rw [List.foldl_append]
  rfl

/-! ## §B  The rooted fold -/

/-- The canonical state seeded with the sentinel. -/
def sRFold (Γ : OrderedPrefixCode) (ρ : List (Op SOp)) : SState :=
  ρ.foldl (sUpdate Γ) [rootRec]

theorem sRFold_snoc (Γ : OrderedPrefixCode) (ρ : List (Op SOp))
    (o : Op SOp) : sRFold Γ (ρ ++ [o]) = sUpdate Γ (sRFold Γ ρ) o := by
  unfold sRFold
  rw [List.foldl_append]
  rfl

/-! ## §C  Sequential honesty -/

/-- Sequential honesty: stamps exceed all previous insert stamps
(Lamport), and every op is applicable at the current (unrooted) fold,
the instance's own §8 issuer guard, specialized to a linear history. -/
def sSeqOK (Γ : OrderedPrefixCode) (ρ : List (Op SOp)) : Prop :=
  ∀ (σ : List (Op SOp)) (o : Op SOp) (τ : List (Op SOp)),
    ρ = σ ++ o :: τ →
    (∀ x ∈ sInsIds σ, x < o.1) ∧ sApplicable o (sFold Γ σ)

theorem sSeqOK_prefix {Γ : OrderedPrefixCode} {ρ : List (Op SOp)}
    {o : Op SOp} (h : sSeqOK Γ (ρ ++ [o])) : sSeqOK Γ ρ := by
  intro σ o' τ heq
  exact h σ o' (τ ++ [o]) (by rw [heq]; simp)

/-! ## §D  Chains for every insert of the history -/

/-- Every insert of a sequentially honest history mints a positive sided
chain's coordinate whose deltas telescope to its (positive) id. -/
theorem s_seq_chains {Γ : OrderedPrefixCode} {ρ : List (Op SOp)}
    (hOK : sSeqOK Γ ρ) :
    ∀ o ∈ ρ, sIsIns o = true →
      ∃ ch, PosSChain ch ∧ ((ch.map Prod.snd).sum = o.1) ∧ 1 ≤ o.1 ∧
        sCoord Γ o = sidedCoordOf Γ ch := by
  induction ρ using List.reverseRecOn with
  | nil =>
      intro o ho
      simp at ho
  | append_singleton ρ o' ih =>
      intro o ho hins
      rcases List.mem_append.mp ho with h | h
      · exact ih (sSeqOK_prefix hOK) o h hins
      · simp at h
        subst h
        obtain ⟨ts, r, op⟩ := o
        cases op with
        | del x => simp [sIsIns] at hins
        | ins el π a sd =>
            have happ := (hOK ρ (ts, r, .ins el π a sd) [] (by simp)).2
            simp only [sApplicable] at happ
            obtain ⟨hat, hcase⟩ := happ
            have hat' : a < ts := hat
            have hts1 : (1:ℕ) ≤ ts :=
              Nat.lt_of_le_of_lt (Nat.zero_le a) hat'
            rcases hcase with ⟨rfl, rfl⟩ | ⟨el', hmem⟩
            · refine ⟨[(sd, ts)], ?_, by simp, hts1, ?_⟩
              · intro e he
                simp at he
                rw [he]
                show 1 ≤ ts
                exact hts1
              · show [] ++ sBlock Γ (sd, ts - 0) = _
                simp [sidedCoordOf]
            · obtain ⟨aop, haρ, hai, hae⟩ :=
                s_fold_rec_sub Γ ρ (a, el', π) hmem
              have hπ : π = sCoord Γ aop :=
                congrArg (fun q : SRec => q.2.2) hae
              have ha1 : aop.1 = a := (congrArg Prod.fst hae).symm
              obtain ⟨cha, hpos, hsum, -, hcoord⟩ :=
                ih (sSeqOK_prefix hOK) aop haρ hai
              refine ⟨cha ++ [(sd, ts - a)], ?_, ?_, hts1, ?_⟩
              · intro e he
                rcases List.mem_append.mp he with h' | h'
                · exact hpos e h'
                · simp at h'
                  rw [h']
                  show 1 ≤ ts - a
                  exact Nat.le_sub_of_add_le (Nat.add_comm 1 a ▸ hat')
              · rw [List.map_append, List.sum_append, hsum, ha1]
                simp
                exact Nat.add_sub_cancel' (Nat.le_of_lt hat')
              · show π ++ sBlock Γ (sd, ts - a) = _
                rw [sidedCoordOf_append, hπ, hcoord]
                simp [sidedCoordOf]

/-! ## §D′  Well-formedness from sequential honesty -/

theorem sInsIds_lt_of_seqOK {Γ : OrderedPrefixCode} {ρ : List (Op SOp)}
    {o : Op SOp} (hOK : sSeqOK Γ (ρ ++ [o])) :
    ∀ x ∈ sInsIds ρ, x < o.1 :=
  (hOK ρ o [] (by simp)).1

theorem sWf_of_seqOK {Γ : OrderedPrefixCode} {ρ : List (Op SOp)}
    (hOK : sSeqOK Γ ρ) : SWf Γ ρ := by
  constructor
  case ins_nodup =>
      induction ρ using List.reverseRecOn with
      | nil => simp [sInsIds]
      | append_singleton ρ o ih =>
          rw [sInsIds_append, List.nodup_append]
          refine ⟨ih (sSeqOK_prefix hOK), ?_, ?_⟩
          · cases o' : o.2.2 <;> simp [sInsIds, sIsIns, o']
          · intro a ha b hb
            have hlt := sInsIds_lt_of_seqOK hOK a ha
            have hb1 : b = o.1 := by
              simp only [sInsIds, List.mem_map, List.mem_filter] at hb
              obtain ⟨o', ⟨ho', -⟩, rfl⟩ := hb
              simp at ho'
              rw [ho']
            omega
  case del_late =>
      intro σ o τ heq hins hdel
      obtain ⟨d, hd, hddel⟩ := mem_sDels.mp hdel
      obtain ⟨σ₁, σ₂, rfl⟩ := List.append_of_mem hd
      have happ := (hOK σ₁ d (σ₂ ++ o :: τ) (by rw [heq]; simp)).2
      obtain ⟨ts, rr, dop2⟩ := d
      cases dop2 with
      | ins el π a sd => simp at hddel
      | del x =>
          simp only [sApplicable] at happ
          simp only at hddel
          injection hddel with hx
          subst hx
          obtain ⟨rec, hrec, hrx⟩ := List.mem_map.mp happ
          obtain ⟨iop, hiρ, hii, hie⟩ := s_fold_rec_sub Γ σ₁ rec hrec
          have hix : iop.1 = o.1 → False := by
            intro hcontra
            have hmem : o.1 ∈ sInsIds (σ₁ ++ (ts, rr, SOp.del o.1) :: σ₂) := by
              rw [show σ₁ ++ (ts, rr, SOp.del o.1) :: σ₂ =
                  (σ₁ ++ [(ts, rr, SOp.del o.1)]) ++ σ₂ from by simp,
                sInsIds_append, sInsIds_append]
              exact List.mem_append_left _ (List.mem_append_left _
                (mem_sInsIds.mpr ⟨iop, hiρ, hii, hcontra⟩))
            have := (hOK (σ₁ ++ (ts, rr, SOp.del o.1) :: σ₂) o τ
              (by simp [heq])).1 o.1 hmem
            omega
          apply hix
          rw [hie] at hrx
          exact hrx
  case keys_inj =>
      intro o₁ h₁ o₂ h₂ hi₁ hi₂ hne hkey
      obtain ⟨ch₁, hp₁, hs₁, -, hc₁⟩ := s_seq_chains hOK o₁ h₁ hi₁
      obtain ⟨ch₂, hp₂, hs₂, -, hc₂⟩ := s_seq_chains hOK o₂ h₂ hi₂
      rw [hc₁, hc₂] at hkey
      have hco := sKey_inj hkey
      have hch := sidedCoordOf_inj Γ hp₁ hp₂ hco
      rw [← hs₁, ← hs₂, hch] at hne
      exact hne rfl

/-! ## §E  Rooted-fold structure -/

/-- Chain package for a live record of the unrooted fold. -/
theorem s_fold_chain {Γ : OrderedPrefixCode} {ρ : List (Op SOp)}
    (hOK : sSeqOK Γ ρ) {rec : SRec} (hrec : rec ∈ sFold Γ ρ) :
    ∃ ch, PosSChain ch ∧ ((ch.map Prod.snd).sum = rec.1) ∧
      rec.2.2 = sidedCoordOf Γ ch := by
  obtain ⟨iop, hiρ, hii, hie⟩ := s_fold_rec_sub Γ ρ rec hrec
  obtain ⟨ch, h1, h2, -, h4⟩ := s_seq_chains hOK iop hiρ hii
  have e1 : rec.1 = iop.1 := by rw [hie]; rfl
  have e2 : rec.2.2 = sCoord Γ iop := by rw [hie]; rfl
  exact ⟨ch, h1, by rw [e1]; exact h2, by rw [e2]; exact h4⟩

theorem s_fold_id_pos {Γ : OrderedPrefixCode} {ρ : List (Op SOp)}
    (hOK : sSeqOK Γ ρ) {rec : SRec} (hrec : rec ∈ sFold Γ ρ) :
    1 ≤ rec.1 := by
  obtain ⟨iop, hiρ, hii, hie⟩ := s_fold_rec_sub Γ ρ rec hrec
  obtain ⟨-, -, -, h3, -⟩ := s_seq_chains hOK iop hiρ hii
  have e1 : rec.1 = iop.1 := by rw [hie]; rfl
  rw [e1]
  exact h3

/-- **The rooted fold is the unrooted fold plus the sentinel**, the
membership bridge. -/
theorem sr_fold_iff {Γ : OrderedPrefixCode} {ρ : List (Op SOp)}
    (hOK : sSeqOK Γ ρ) :
    ∀ r : SRec, r ∈ sRFold Γ ρ ↔ r = rootRec ∨ r ∈ sFold Γ ρ := by
  induction ρ using List.reverseRecOn with
  | nil =>
      intro r
      show r ∈ [rootRec] ↔ _
      rw [show sFold Γ [] = [] from rfl]
      simp
  | append_singleton ρ o ih =>
      intro r
      have hOK' := sSeqOK_prefix hOK
      have IH := ih hOK'
      rw [sRFold_snoc, sFold_snoc]
      obtain ⟨ts, rr, op⟩ := o
      cases op with
      | ins el π a sd =>
          have happ := (hOK ρ (ts, rr, .ins el π a sd) [] (by simp)).2
          simp only [sApplicable] at happ
          have hat : a < ts := happ.1
          have hts1 : (1:ℕ) ≤ ts :=
            Nat.lt_of_le_of_lt (Nat.zero_le a) hat
          have hfreshU : ts ∉ sIds (sFold Γ ρ) :=
            s_fold_guard_free (sWf_of_seqOK hOK) (by simp [sIsIns])
          have hfreshR : ts ∉ sIds (sRFold Γ ρ) := by
            intro hmem
            obtain ⟨rec, hrec, hr1⟩ := List.mem_map.mp hmem
            rcases (IH rec).mp hrec with rfl | hrec'
            · have h0 : (0:ℕ) = ts := hr1
              rw [← h0] at hts1
              exact absurd hts1 (by decide)
            · exact hfreshU (List.mem_map.mpr ⟨rec, hrec', hr1⟩)
          show r ∈ sUpdate Γ (sRFold Γ ρ) (ts, rr, .ins el π a sd) ↔
            r = rootRec ∨ r ∈ sUpdate Γ (sFold Γ ρ) (ts, rr, .ins el π a sd)
          simp only [sUpdate]
          rw [if_neg hfreshR, if_neg hfreshU, mem_sInsert, mem_sInsert, IH r]
          tauto
      | del x =>
          have happ := (hOK ρ (ts, rr, .del x) [] (by simp)).2
          simp only [sApplicable] at happ
          have hx0 : x ≠ 0 := by
            intro h0
            obtain ⟨rec, hrec, hr1⟩ := List.mem_map.mp happ
            have h1 := s_fold_id_pos hOK' hrec
            rw [hr1, h0] at h1
            exact absurd h1 (by decide)
          show r ∈ sUpdate Γ (sRFold Γ ρ) (ts, rr, .del x) ↔
            r = rootRec ∨ r ∈ sUpdate Γ (sFold Γ ρ) (ts, rr, .del x)
          simp only [sUpdate]
          constructor
          · intro hr
            have hm := List.mem_of_mem_filter hr
            have hxne := List.of_mem_filter hr
            simp only [decide_eq_true_eq] at hxne
            rcases (IH r).mp hm with rfl | hm'
            · exact Or.inl rfl
            · exact Or.inr (List.mem_filter.mpr ⟨hm', by simpa using hxne⟩)
          · intro hr
            rcases hr with rfl | hr'
            · refine List.mem_filter.mpr
                ⟨(IH rootRec).mpr (Or.inl rfl), ?_⟩
              show decide (rootRec.1 ≠ x) = true
              simp only [rootRec, decide_eq_true_eq]
              exact fun h => hx0 h.symm
            · have hm := List.mem_of_mem_filter hr'
              have hxne := List.of_mem_filter hr'
              exact List.mem_filter.mpr ⟨(IH r).mpr (Or.inr hm), hxne⟩

/-- Chain package on the rooted fold: the sentinel carries the empty
chain. -/
theorem sr_fold_chain {Γ : OrderedPrefixCode} {ρ : List (Op SOp)}
    (hOK : sSeqOK Γ ρ) {rec : SRec} (hrec : rec ∈ sRFold Γ ρ) :
    ∃ ch, PosSChain ch ∧ ((ch.map Prod.snd).sum = rec.1) ∧
      rec.2.2 = sidedCoordOf Γ ch := by
  rcases (sr_fold_iff hOK rec).mp hrec with rfl | h
  · exact ⟨[], by intro e he; simp at he, rfl, rfl⟩
  · exact s_fold_chain hOK h

/-- Rooted ids sit below a fresh op's stamp. -/
theorem sr_fold_id_lt {Γ : OrderedPrefixCode} {ρ : List (Op SOp)}
    {o : Op SOp} (hOK : sSeqOK Γ (ρ ++ [o])) (hts1 : 1 ≤ o.1)
    {rec : SRec} (hrec : rec ∈ sRFold Γ ρ) : rec.1 < o.1 := by
  rcases (sr_fold_iff (sSeqOK_prefix hOK) rec).mp hrec with rfl | hrec'
  · show (0:ℕ) < o.1
    exact hts1
  · obtain ⟨iop, hiρ, hii, hie⟩ := s_fold_rec_sub Γ ρ rec hrec'
    have h1 := sInsIds_lt_of_seqOK hOK iop.1
      (mem_sInsIds.mpr ⟨iop, hiρ, hii, rfl⟩)
    have e1 : rec.1 = iop.1 := by rw [hie]; rfl
    rw [e1]
    exact h1

theorem sr_fold_sorted {Γ : OrderedPrefixCode} {ρ : List (Op SOp)}
    (hOK : sSeqOK Γ ρ) : SSorted (sRFold Γ ρ) := by
  induction ρ using List.reverseRecOn with
  | nil => exact List.pairwise_singleton _ _
  | append_singleton ρ o ih =>
      have hOK' := sSeqOK_prefix hOK
      rw [sRFold_snoc]
      obtain ⟨ts, rr, op⟩ := o
      cases op with
      | del x => exact List.Pairwise.filter _ (ih hOK')
      | ins el π a sd =>
          apply sUpdate_sorted (ih hOK')
          intro x hx hkey
          obtain ⟨chx, hpx, hsx, hcx⟩ := sr_fold_chain hOK' hx
          obtain ⟨cho, hpo, hso, hts1, hco⟩ := s_seq_chains hOK
            (ts, rr, .ins el π a sd)
            (List.mem_append_right _ (by simp)) (by simp [sIsIns])
          have hxlt : x.1 < ts := sr_fold_id_lt hOK
            (show (1:ℕ) ≤ ts from hts1) hx
          rw [hcx, hco] at hkey
          have hch := sidedCoordOf_inj Γ hpx hpo (sKey_inj hkey)
          rw [hch, hso] at hsx
          have hsx' : ts = x.1 := hsx
          rw [hsx'] at hxlt
          exact absurd hxlt (Nat.lt_irrefl _)

theorem sr_fold_fst_inj {Γ : OrderedPrefixCode} {ρ : List (Op SOp)}
    (hOK : sSeqOK Γ ρ) :
    ∀ r ∈ sRFold Γ ρ, ∀ r' ∈ sRFold Γ ρ, r.1 = r'.1 → r = r' := by
  intro r hr r' hr' hfst
  rcases (sr_fold_iff hOK r).mp hr with rfl | h
  · rcases (sr_fold_iff hOK r').mp hr' with rfl | h'
    · rfl
    · exfalso
      have := s_fold_id_pos hOK h'
      have h0 : (0:ℕ) = r'.1 := hfst
      omega
  · rcases (sr_fold_iff hOK r').mp hr' with rfl | h'
    · exfalso
      have := s_fold_id_pos hOK h
      have h0 : r.1 = (0:ℕ) := hfst
      omega
    · obtain ⟨o, ho, hi, hrec⟩ := s_fold_rec_sub Γ ρ r h
      obtain ⟨o', ho', hi', hrec'⟩ := s_fold_rec_sub Γ ρ r' h'
      have h1 : o.1 = o'.1 := by
        have e1 : r.1 = o.1 := by rw [hrec]; rfl
        have e2 : r'.1 = o'.1 := by rw [hrec']; rfl
        rw [← e1, ← e2, hfst]
      have : o = o' := by
        have hinj := List.inj_on_of_nodup_map
          (f := Prod.fst) (l := ρ.filter (fun o => sIsIns o))
          (sWf_of_seqOK hOK).ins_nodup
        exact hinj (List.mem_filter.mpr ⟨ho, hi⟩)
          (List.mem_filter.mpr ⟨ho', hi'⟩) h1
      rw [hrec, hrec', this]

/-! ## §F  The two sided adjacency lemmas (the heart) -/

/-- **R-adjacency**: appending a fresh R entry whose delta beats every
existing R-continuation of the anchor changes no display verdict against
the anchor, the newcomer sits immediately after it. -/
theorem schainBefore_snocR_iff {ca cr : SChain} {δ : ℕ}
    (hne : cr ≠ ca)
    (hmax : ∀ d rest, cr = ca ++ (Side.R, d) :: rest → d < δ) :
    schainBefore cr (ca ++ [(Side.R, δ)]) ↔ schainBefore cr ca := by
  constructor
  · intro h
    rcases schainBefore_inv h with ⟨d, rest, heq⟩ | ⟨d, rest, heq⟩ |
      ⟨q, e1, e2, t1, t2, hlt, hu, hv⟩
    · -- cr extends the newcomer on the L side: refuted by freshness
      exfalso
      have := hmax δ ((Side.L, d) :: rest) (by rw [heq]; simp)
      omega
    · -- ca ++ [(R,δ)] = cr ++ (R,d) :: rest
      rcases List.eq_nil_or_concat rest with rfl | ⟨rest', lst, rfl⟩
      · have hinj := List.append_inj' heq rfl
        exact absurd hinj.1.symm hne
      · simp only [List.concat_eq_append] at heq
        rw [show cr ++ (Side.R, d) :: (rest' ++ [lst])
            = (cr ++ (Side.R, d) :: rest') ++ [lst] from by simp] at heq
        obtain ⟨hca, -⟩ := List.append_inj' heq rfl
        rw [hca]
        exact schainBefore.extR cr d rest'
    · rcases List.eq_nil_or_concat t2 with rfl | ⟨t2', lst, rfl⟩
      · -- the divergence is at the snoc position
        have h2 : q ++ [e2] = ca ++ [(Side.R, δ)] := hv.symm
        obtain ⟨rfl, he⟩ := List.append_inj' h2 rfl
        injection he with he1
        subst he1
        obtain ⟨s1, d1⟩ := e1
        cases s1 with
        | R =>
            exfalso
            have hd := hmax d1 t1 hu
            have hδd : δ < d1 := hlt
            omega
        | L =>
            rw [hu]
            exact schainBefore.extL q d1 t1
      · simp only [List.concat_eq_append] at hv
        rw [show q ++ e2 :: (t2' ++ [lst]) = (q ++ e2 :: t2') ++ [lst]
            from by simp] at hv
        obtain ⟨hca, -⟩ := List.append_inj' hv rfl
        rw [hu, hca]
        exact schainBefore.diverge q e1 e2 t1 t2' hlt
  · intro h
    rcases schainBefore_inv h with ⟨d, rest, heq⟩ | ⟨d, rest, heq⟩ |
      ⟨q, e1, e2, t1, t2, hlt, hu, hv⟩
    · rw [heq, show ca ++ [(Side.R, δ)] = ca ++ (Side.R, δ) :: []
        from rfl]
      exact schainBefore.diverge ca (Side.L, d) (Side.R, δ) rest []
        trivial
    · rw [heq, List.append_assoc]
      exact schainBefore.extR cr d (rest ++ [(Side.R, δ)])
    · rw [hu, hv, List.append_assoc]
      exact schainBefore.diverge q e1 e2 t1 (t2 ++ [(Side.R, δ)]) hlt

/-- **L-adjacency**: appending a fresh L entry whose delta beats every
existing L-continuation of the anchor changes no display verdict against
the anchor, the newcomer sits immediately before it (the L band is
mirrored: the newest L-child hugs the node). -/
theorem schainBefore_snocL_iff {ca cr : SChain} {δ : ℕ}
    (hne : cr ≠ ca)
    (hmax : ∀ d rest, cr = ca ++ (Side.L, d) :: rest → d < δ) :
    schainBefore (ca ++ [(Side.L, δ)]) cr ↔ schainBefore ca cr := by
  constructor
  · intro h
    rcases schainBefore_inv h with ⟨d, rest, heq⟩ | ⟨d, rest, heq⟩ |
      ⟨q, e1, e2, t1, t2, hlt, hu, hv⟩
    · -- ca ++ [(L,δ)] = cr ++ (L,d) :: rest
      rcases List.eq_nil_or_concat rest with rfl | ⟨rest', lst, rfl⟩
      · have hinj := List.append_inj' heq rfl
        exact absurd hinj.1.symm hne
      · simp only [List.concat_eq_append] at heq
        rw [show cr ++ (Side.L, d) :: (rest' ++ [lst])
            = (cr ++ (Side.L, d) :: rest') ++ [lst] from by simp] at heq
        obtain ⟨hca, -⟩ := List.append_inj' heq rfl
        rw [hca]
        exact schainBefore.extL cr d rest'
    · -- cr extends the newcomer on the R side: refuted by freshness
      exfalso
      have := hmax δ ((Side.R, d) :: rest) (by rw [heq]; simp)
      omega
    · rcases List.eq_nil_or_concat t1 with rfl | ⟨t1', lst, rfl⟩
      · have h2 : q ++ [e1] = ca ++ [(Side.L, δ)] := hu.symm
        obtain ⟨rfl, he⟩ := List.append_inj' h2 rfl
        injection he with he1
        subst he1
        obtain ⟨s2, d2⟩ := e2
        cases s2 with
        | R =>
            rw [hv]
            exact schainBefore.extR q d2 t2
        | L =>
            exfalso
            have hd := hmax d2 t2 hv
            have hδd : δ < d2 := hlt
            omega
      · simp only [List.concat_eq_append] at hu
        rw [show q ++ e1 :: (t1' ++ [lst]) = (q ++ e1 :: t1') ++ [lst]
            from by simp] at hu
        obtain ⟨hca, -⟩ := List.append_inj' hu rfl
        rw [hv, hca]
        exact schainBefore.diverge q e1 e2 t1' t2 hlt
  · intro h
    rcases schainBefore_inv h with ⟨d, rest, heq⟩ | ⟨d, rest, heq⟩ |
      ⟨q, e1, e2, t1, t2, hlt, hu, hv⟩
    · rw [heq, List.append_assoc]
      exact schainBefore.extL cr d (rest ++ [(Side.L, δ)])
    · rw [heq, show ca ++ [(Side.L, δ)] = ca ++ (Side.L, δ) :: []
        from rfl]
      exact schainBefore.diverge ca (Side.L, δ) (Side.R, d) [] rest
        trivial
    · rw [hu, hv, List.append_assoc]
      exact schainBefore.diverge q e1 e2 (t1 ++ [(Side.L, δ)]) t2 hlt

#print axioms schainBefore_snocR_iff
#print axioms schainBefore_snocL_iff

/-! ## §G  Placement: sorted insert = splice at the anchor -/

theorem sInsert_all_lt {nr : SRec} : ∀ {s : SState},
    (∀ y ∈ s, keyLt (sKey y.2.2) (sKey nr.2.2) = true) →
    sInsert nr s = nr :: s
  | [], _ => rfl
  | x :: xs, h => by
      unfold sInsert
      rw [if_pos (h x List.mem_cons_self)]

/-- **R-placement**: when the newcomer's key sits exactly between the
anchor's and everything after it, the sorted insert IS the
splice-after-anchor, under projection. -/
theorem sInsert_map_insAfter {a : ℕ} {nr : SRec} :
    ∀ {s : SState} {ar : SRec}, SSorted s → ar ∈ s → ar.1 = a →
    (∀ r ∈ s, ∀ r' ∈ s, r.1 = r'.1 → r = r') →
    (∀ r ∈ s, sKey r.2.2 ≠ sKey nr.2.2) →
    (∀ r ∈ s, (keyLt (sKey nr.2.2) (sKey r.2.2) = true ↔
      (r = ar ∨ keyLt (sKey ar.2.2) (sKey r.2.2) = true))) →
    (sInsert nr s).map sProj = sInsAfter a (sProj nr) (s.map sProj) := by
  intro s
  induction s with
  | nil =>
      intro ar _ har
      exact absurd har (by simp)
  | cons x xs ih =>
      intro ar hsort har hara hinj hkeyne hiff
      by_cases hx : keyLt (sKey x.2.2) (sKey nr.2.2) = true
      · exfalso
        have hnx : ¬ (keyLt (sKey nr.2.2) (sKey x.2.2) = true) := by
          rw [keyLt_asymm hx]
          exact fun h => Bool.noConfusion h
        have hnor : ¬ (x = ar ∨ keyLt (sKey ar.2.2) (sKey x.2.2) = true) :=
          fun h => hnx ((hiff x List.mem_cons_self).mpr h)
        rcases List.mem_cons.mp har with heq | harx
        · exact hnor (Or.inl heq.symm)
        · exact hnor (Or.inr ((List.pairwise_cons.mp hsort).1 ar harx))
      · have hstep : sInsert nr (x :: xs) = x :: sInsert nr xs := by
          show (if keyLt (sKey x.2.2) (sKey nr.2.2) = true
            then nr :: x :: xs else x :: sInsert nr xs)
            = x :: sInsert nr xs
          rw [if_neg hx]
        rw [hstep]
        have hxk : keyLt (sKey nr.2.2) (sKey x.2.2) = true := by
          rcases keyLt_total (hkeyne x List.mem_cons_self) with h | h
          · exact absurd h hx
          · exact h
        rcases (hiff x List.mem_cons_self).mp hxk with heq | hax
        · have hall : ∀ y ∈ xs,
              keyLt (sKey y.2.2) (sKey nr.2.2) = true := by
            intro y hy
            have hyx := (List.pairwise_cons.mp hsort).1 y hy
            have hyne : y ≠ x := by
              rintro rfl
              rw [keyLt_irrefl] at hyx
              exact Bool.noConfusion hyx
            have hrfalse :
                ¬ (y = ar ∨ keyLt (sKey ar.2.2) (sKey y.2.2) = true) := by
              rintro (rfl | hcontra)
              · exact hyne heq.symm
              · rw [← heq, keyLt_asymm hyx] at hcontra
                exact Bool.noConfusion hcontra
            have hnn : ¬ (keyLt (sKey nr.2.2) (sKey y.2.2) = true) :=
              fun h => hrfalse ((hiff y (List.mem_cons_of_mem _ hy)).mp h)
            rcases keyLt_total
              (hkeyne y (List.mem_cons_of_mem _ hy)) with h | h
            · exact h
            · exact absurd h hnn
          rw [sInsert_all_lt hall, List.map_cons]
          show sProj x :: sProj nr :: xs.map sProj =
            if (sProj x).1 = a then sProj x :: sProj nr :: xs.map sProj
            else sProj x :: sInsAfter a (sProj nr) (xs.map sProj)
          rw [if_pos (show (sProj x).1 = a from by
            show x.1 = a
            rw [heq, hara])]
        · have hxa : x.1 ≠ a := by
            intro hcontra
            have hxar : x = ar :=
              hinj x List.mem_cons_self ar har (by rw [hcontra, hara])
            rw [hxar, keyLt_irrefl] at hax
            exact Bool.noConfusion hax
          have harx : ar ∈ xs := by
            rcases List.mem_cons.mp har with heq2 | h
            · exact absurd (show x.1 = a from by rw [← heq2]; exact hara)
                hxa
            · exact h
          rw [List.map_cons, List.map_cons]
          show sProj x :: (sInsert nr xs).map sProj =
            if (sProj x).1 = a then
              sProj x :: sProj nr :: xs.map sProj
            else sProj x :: sInsAfter a (sProj nr) (xs.map sProj)
          rw [if_neg (show ¬ (sProj x).1 = a from hxa)]
          rw [ih (List.pairwise_cons.mp hsort).2 harx hara
            (fun r hr r' hr' => hinj r (List.mem_cons_of_mem _ hr)
              r' (List.mem_cons_of_mem _ hr'))
            (fun r hr => hkeyne r (List.mem_cons_of_mem _ hr))
            (fun r hr => hiff r (List.mem_cons_of_mem _ hr))]

/-- **L-placement**: when everything displaying after the newcomer is
exactly the anchor and what follows it, the sorted insert IS the
splice-before-anchor, under projection. -/
theorem sInsert_map_insBefore {a : ℕ} {nr : SRec} :
    ∀ {s : SState} {ar : SRec}, SSorted s → ar ∈ s → ar.1 = a →
    (∀ r ∈ s, ∀ r' ∈ s, r.1 = r'.1 → r = r') →
    (∀ r ∈ s, (keyLt (sKey r.2.2) (sKey nr.2.2) = true ↔
      (r = ar ∨ keyLt (sKey r.2.2) (sKey ar.2.2) = true))) →
    (sInsert nr s).map sProj = sInsBefore a (sProj nr) (s.map sProj) := by
  intro s
  induction s with
  | nil =>
      intro ar _ har
      exact absurd har (by simp)
  | cons x xs ih =>
      intro ar hsort har hara hinj hiff
      by_cases hx : keyLt (sKey x.2.2) (sKey nr.2.2) = true
      · -- the head displays after the newcomer: it must be the anchor
        have hxar : x = ar := by
          rcases (hiff x List.mem_cons_self).mp hx with h | h
          · exact h
          · exfalso
            rcases List.mem_cons.mp har with heq | harx
            · rw [← heq, keyLt_irrefl] at h
              exact Bool.noConfusion h
            · have hhead := (List.pairwise_cons.mp hsort).1 ar harx
              rw [keyLt_asymm hhead] at h
              exact Bool.noConfusion h
        have hstep : sInsert nr (x :: xs) = nr :: x :: xs := by
          show (if keyLt (sKey x.2.2) (sKey nr.2.2) = true
            then nr :: x :: xs else x :: sInsert nr xs)
            = nr :: x :: xs
          rw [if_pos hx]
        rw [hstep]
        show sProj nr :: sProj x :: xs.map sProj =
          if (sProj x).1 = a then sProj nr :: sProj x :: xs.map sProj
          else sProj x :: sInsBefore a (sProj nr) (xs.map sProj)
        rw [if_pos (show (sProj x).1 = a from by
          show x.1 = a
          rw [hxar, hara])]
      · have hxne : x ≠ ar :=
          fun heq => hx ((hiff x List.mem_cons_self).mpr (Or.inl heq))
        have harx : ar ∈ xs := by
          rcases List.mem_cons.mp har with heq2 | h
          · exact absurd heq2.symm hxne
          · exact h
        have hxa : x.1 ≠ a := by
          intro hcontra
          exact hxne (hinj x List.mem_cons_self ar
            (List.mem_cons_of_mem _ harx) (by rw [hcontra, hara]))
        have hstep : sInsert nr (x :: xs) = x :: sInsert nr xs := by
          show (if keyLt (sKey x.2.2) (sKey nr.2.2) = true
            then nr :: x :: xs else x :: sInsert nr xs)
            = x :: sInsert nr xs
          rw [if_neg hx]
        rw [hstep, List.map_cons, List.map_cons]
        show sProj x :: (sInsert nr xs).map sProj =
          if (sProj x).1 = a then
            sProj nr :: sProj x :: xs.map sProj
          else sProj x :: sInsBefore a (sProj nr) (xs.map sProj)
        rw [if_neg (show ¬ (sProj x).1 = a from hxa)]
        rw [ih (List.pairwise_cons.mp hsort).2 harx hara
          (fun r hr r' hr' => hinj r (List.mem_cons_of_mem _ hr)
            r' (List.mem_cons_of_mem _ hr'))
          (fun r hr => hiff r (List.mem_cons_of_mem _ hr))]

/-! ## §H  Deletion commutes with projection -/

theorem map_sProj_filter (s : SState) (x : ℕ) :
    (s.filter (fun r => decide (r.1 ≠ x))).map sProj =
      (s.map sProj).filter (fun p => decide (p.1 ≠ x)) := by
  induction s with
  | nil => rfl
  | cons r rs ih =>
      simp only [ne_eq, decide_not] at ih
      by_cases h : r.1 = x
      · simp [h, sProj, ih]
      · simp [h, sProj, ih]

/-! ## §I  The capstone -/

/-- **The sided embedded-chain RGA, sequentially = the naive two-sided
buffer.** Under the datatype's own sequential discipline the rooted
canonical state IS the buffer program, record for record: an R insert
splices immediately after its anchor, an L insert immediately before it
(the two adjacency lemmas), a delete filters. -/
theorem sided_seq_sound {Γ : OrderedPrefixCode} {ρ : List (Op SOp)}
    (hOK : sSeqOK Γ ρ) :
    (sRFold Γ ρ).map sProj = sSpecFold ρ := by
  induction ρ using List.reverseRecOn with
  | nil => rfl
  | append_singleton ρ o ih =>
      have hOK' := sSeqOK_prefix hOK
      have IH := ih hOK'
      rw [sRFold_snoc, sSpecFold_snoc]
      obtain ⟨ts, rr, op⟩ := o
      cases op with
      | del x =>
          show ((sRFold Γ ρ).filter (fun r => decide (r.1 ≠ x))).map sProj
            = _
          rw [map_sProj_filter, IH]
          rfl
      | ins el π a sd =>
          have happ := (hOK ρ (ts, rr, .ins el π a sd) [] (by simp)).2
          simp only [sApplicable] at happ
          obtain ⟨hat, hcase⟩ := happ
          have hat' : a < ts := hat
          have hts1 : (1:ℕ) ≤ ts :=
            Nat.lt_of_le_of_lt (Nat.zero_le a) hat'
          have hsort := sr_fold_sorted hOK'
          have hinj := sr_fold_fst_inj hOK'
          have hfresh : (ts, rr, SOp.ins el π a sd).1
              ∉ sIds (sRFold Γ ρ) := by
            intro hmem
            obtain ⟨rec, hrec, hr1⟩ := List.mem_map.mp hmem
            have h1 : rec.1 < ts := sr_fold_id_lt hOK hts1 hrec
            rw [hr1] at h1
            exact absurd h1 (Nat.lt_irrefl _)
          -- the anchor package: the sentinel serves the root anchor
          obtain ⟨ar, cha, harm, hara, har2, hpa, hsa⟩ :
              ∃ (ar : SRec) (cha : SChain), ar ∈ sRFold Γ ρ ∧ ar.1 = a ∧
                ar.2.2 = π ∧ PosSChain cha ∧
                ((cha.map Prod.snd).sum = a ∧
                  π = sidedCoordOf Γ cha) := by
            rcases hcase with ⟨rfl, rfl⟩ | ⟨el', hmem⟩
            · exact ⟨rootRec, [],
                (sr_fold_iff hOK' rootRec).mpr (Or.inl rfl),
                rfl, rfl, by intro e he; simp at he, rfl, rfl⟩
            · obtain ⟨ch, hp, hs, hc⟩ := s_fold_chain hOK' hmem
              exact ⟨(a, el', π), ch,
                (sr_fold_iff hOK' _).mpr (Or.inr hmem), rfl, rfl, hp,
                hs, hc⟩
          obtain ⟨hsa, hπeq⟩ := hsa
          have harc : ar.2.2 = sidedCoordOf Γ cha := by rw [har2, hπeq]
          have hδpos : 1 ≤ ts - a :=
            Nat.le_sub_of_add_le (Nat.add_comm 1 a ▸ hat')
          have hcoordnew : π ++ sBlock Γ (sd, ts - a)
              = sidedCoordOf Γ (cha ++ [(sd, ts - a)]) := by
            rw [sidedCoordOf_append, hπeq]
            simp [sidedCoordOf]
          have hpos_new : PosSChain (cha ++ [(sd, ts - a)]) := by
            intro e he
            rcases List.mem_append.mp he with h | h
            · exact hpa e h
            · simp at h
              rw [h]
              exact hδpos
          have hsum_new : ((cha ++ [(sd, ts - a)]).map Prod.snd).sum
              = ts := by
            rw [List.map_append, List.sum_append, hsa]
            simp
            exact Nat.add_sub_cancel' (Nat.le_of_lt hat')
          have hcane : cha ≠ cha ++ [(sd, ts - a)] := by
            intro hcontra
            have := congrArg List.length hcontra
            simp at this
          have hkeyne : ∀ rec ∈ sRFold Γ ρ, sKey rec.2.2 ≠
              sKey (((ts : ℕ), el, π ++ sBlock Γ (sd, ts - a))
                : SRec).2.2 := by
            intro rec hrec hcontra
            obtain ⟨chr, hpr, hsr, hcr⟩ := sr_fold_chain hOK' hrec
            have hrlt : rec.1 < ts := sr_fold_id_lt hOK hts1 hrec
            rw [hcr, show (((ts : ℕ), el, π ++ sBlock Γ (sd, ts - a))
                : SRec).2.2 = sidedCoordOf Γ (cha ++ [(sd, ts - a)])
                from hcoordnew] at hcontra
            have h1 := sidedCoordOf_inj Γ hpr hpos_new
              (sKey_inj hcontra)
            rw [h1, hsum_new] at hsr
            rw [hsr] at hrlt
            exact absurd hrlt (Nat.lt_irrefl _)
          show (sUpdate Γ (sRFold Γ ρ) (ts, rr, SOp.ins el π a sd)).map
            sProj = _
          simp only [sUpdate]
          rw [if_neg hfresh]
          -- per-record facts for the divergence analysis
          have hrecfacts : ∀ rec ∈ sRFold Γ ρ, rec ≠ ar →
              ∃ chr, PosSChain chr ∧ rec.2.2 = sidedCoordOf Γ chr ∧
                chr ≠ cha ∧ chr ≠ cha ++ [(sd, ts - a)] ∧
                (∀ sd' d rest, chr = cha ++ (sd', d) :: rest →
                  d < ts - a) := by
            intro rec hrec hreq
            obtain ⟨chr, hpr, hsr, hcr⟩ := sr_fold_chain hOK' hrec
            have hrlt : rec.1 < ts := sr_fold_id_lt hOK hts1 hrec
            have hra : rec.1 ≠ a := by
              intro hcontra
              exact hreq (hinj rec hrec ar harm (by rw [hcontra, hara]))
            refine ⟨chr, hpr, hcr, ?_, ?_, ?_⟩
            · intro hcontra
              apply hra
              rw [← hsr, hcontra, hsa]
            · intro hcontra
              rw [hcontra, hsum_new] at hsr
              rw [hsr] at hrlt
              exact absurd hrlt (Nat.lt_irrefl _)
            · intro sd' d rest hcontra
              have h2 := congrArg (fun l => (l.map Prod.snd).sum) hcontra
              simp only [List.map_append, List.sum_append, List.map_cons,
                List.sum_cons] at h2
              rw [hsa, hsr] at h2
              have h3 : a + d ≤ rec.1 := by
                rw [h2]
                omega
              have h4 : a + d < ts := Nat.lt_of_le_of_lt h3 hrlt
              exact Nat.lt_sub_of_add_lt (by rw [Nat.add_comm]; exact h4)
          cases sd with
          | R =>
              have hiff : ∀ rec ∈ sRFold Γ ρ,
                  (keyLt (sKey (((ts : ℕ), el,
                      π ++ sBlock Γ (Side.R, ts - a)) : SRec).2.2)
                    (sKey rec.2.2) = true ↔
                    (rec = ar ∨ keyLt (sKey ar.2.2)
                      (sKey rec.2.2) = true)) := by
                intro rec hrec
                by_cases hreq : rec = ar
                · subst hreq
                  constructor
                  · intro _
                    exact Or.inl rfl
                  · intro _
                    rw [show (((ts : ℕ), el,
                        π ++ sBlock Γ (Side.R, ts - a)) : SRec).2.2
                        = sidedCoordOf Γ (cha ++ [(Side.R, ts - a)])
                        from hcoordnew, harc]
                    exact (sdisplay_iff_schainBefore Γ hpa hpos_new
                      hcane).mpr (schainBefore.extR cha (ts - a) [])
                · obtain ⟨chr, hpr, hcr, hchne, hchne2, hmax⟩ :=
                    hrecfacts rec hrec hreq
                  rw [show (((ts : ℕ), el,
                      π ++ sBlock Γ (Side.R, ts - a)) : SRec).2.2
                      = sidedCoordOf Γ (cha ++ [(Side.R, ts - a)])
                      from hcoordnew, harc,
                    show rec.2.2 = sidedCoordOf Γ chr from hcr,
                    sdisplay_iff_schainBefore Γ hpr hpos_new hchne2,
                    or_iff_right hreq,
                    sdisplay_iff_schainBefore Γ hpr hpa hchne]
                  exact schainBefore_snocR_iff hchne
                    (fun d rest h => hmax Side.R d rest h)
              rw [sInsert_map_insAfter hsort harm hara hinj hkeyne hiff,
                IH]
              rfl
          | L =>
              have hiff : ∀ rec ∈ sRFold Γ ρ,
                  (keyLt (sKey rec.2.2)
                    (sKey (((ts : ℕ), el,
                      π ++ sBlock Γ (Side.L, ts - a)) : SRec).2.2)
                      = true ↔
                    (rec = ar ∨ keyLt (sKey rec.2.2)
                      (sKey ar.2.2) = true)) := by
                intro rec hrec
                by_cases hreq : rec = ar
                · subst hreq
                  constructor
                  · intro _
                    exact Or.inl rfl
                  · intro _
                    rw [show (((ts : ℕ), el,
                        π ++ sBlock Γ (Side.L, ts - a)) : SRec).2.2
                        = sidedCoordOf Γ (cha ++ [(Side.L, ts - a)])
                        from hcoordnew, harc]
                    exact (sdisplay_iff_schainBefore Γ hpos_new hpa
                      (Ne.symm hcane)).mpr
                      (schainBefore.extL cha (ts - a) [])
                · obtain ⟨chr, hpr, hcr, hchne, hchne2, hmax⟩ :=
                    hrecfacts rec hrec hreq
                  rw [show (((ts : ℕ), el,
                      π ++ sBlock Γ (Side.L, ts - a)) : SRec).2.2
                      = sidedCoordOf Γ (cha ++ [(Side.L, ts - a)])
                      from hcoordnew, harc,
                    show rec.2.2 = sidedCoordOf Γ chr from hcr,
                    sdisplay_iff_schainBefore Γ hpos_new hpr
                      (Ne.symm hchne2),
                    or_iff_right hreq,
                    sdisplay_iff_schainBefore Γ hpa hpr (Ne.symm hchne)]
                  exact schainBefore_snocL_iff hchne
                    (fun d rest h => hmax Side.L d rest h)
              rw [sInsert_map_insBefore hsort harm hara hinj hiff, IH]
              rfl

#print axioms sided_seq_sound

/-- The read corollary: dropping the sentinel on both sides, the
unrooted read IS the buffer program's read. -/
theorem sided_seq_read {Γ : OrderedPrefixCode} {ρ : List (Op SOp)}
    (hOK : sSeqOK Γ ρ) :
    (sFold Γ ρ).map sProj
      = (sSpecFold ρ).filter (fun p => decide (p.1 ≠ 0)) := by
  rw [← sided_seq_sound hOK, ← map_sProj_filter]
  congr 1
  apply ssorted_ext (s_fold_sorted Γ (sWf_of_seqOK hOK))
    (List.Pairwise.filter _ (sr_fold_sorted hOK))
  intro r
  rw [List.mem_filter]
  constructor
  · intro h
    refine ⟨(sr_fold_iff hOK r).mpr (Or.inr h), ?_⟩
    have h1 := s_fold_id_pos hOK h
    simp only [decide_eq_true_eq]
    intro h0
    rw [h0] at h1
    exact absurd h1 (by decide)
  · rintro ⟨hm, hne⟩
    rcases (sr_fold_iff hOK r).mp hm with rfl | h
    · simp [rootRec] at hne
    · exact h

#print axioms sided_seq_read



end Sal.MRDTs.Instances.SidedEmbedRGA

