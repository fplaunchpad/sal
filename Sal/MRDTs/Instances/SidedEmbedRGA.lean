import Sal.MRDTs.Metatheory.Correctness
import Sal.MRDTs.Instances.RGAKernel.SidedChainLex
import Sal.MRDTs.Instances.RGAKernel.BinaryCode

namespace Sal.MRDTs.Instances.SidedEmbedRGA

open Sal.MRDTs.Foundation
open Sal.EmbedRGA (OrderedPrefixCode keyLt sKey sBlock Side
  unaryCode binaryCode)

/-! ## §1  The datatype -/

inductive SOp : Type where
  | ins (e : ℕ) (π : List ℕ) (a : ℕ) (sd : Side)
      -- element, symbol-coordinate prefix, anchor, side
  | del (x : ℕ)
deriving DecidableEq

/-- A record: `(id, element, absolute sided symbol coordinate)`. -/
abbrev SRec : Type := ℕ × ℕ × List ℕ

/-- State: the document, records strictly descending by `sKey`. Canonical
single-list form (sortedness is the `Inv`-grade invariant, established by
fold-canonicity in §3, not baked into the type). -/
abbrev SState : Type := List SRec

def sIds (s : SState) : List ℕ := s.map Prod.fst

/-- The coordinate an insert writes, a function of the op alone: the
carried prefix + the entry's sided block (`sBlock` composes the band and
the per-band code, complemented on L). -/
def sCoord (Γ : OrderedPrefixCode) (o : Op SOp) : List ℕ :=
  match o.2.2 with
  | .ins _ π a sd => π ++ sBlock Γ (sd, o.1 - a)
  | .del _        => []

/-- Sorted insertion, descending by key: the newcomer goes before the first
record with a strictly smaller key. -/
def sInsert (r : SRec) : SState → SState
  | [] => [r]
  | x :: xs =>
      if keyLt (sKey x.2.2) (sKey r.2.2) then r :: x :: xs
      else x :: sInsert r xs

/-- Insert places the record at its sorted position (idempotent on a present
id); delete removes the record wherever it sits. Strictness about *which*
target lives in the honesty layer, not in the effect. -/
def sUpdate (Γ : OrderedPrefixCode) (s : SState) (o : Op SOp) : SState :=
  match o.2.2 with
  | .ins e π a sd =>
      if o.1 ∈ sIds s then s
      else sInsert (o.1, e, π ++ sBlock Γ (sd, o.1 - a)) s
  | .del x => s.filter (fun r => decide (r.1 ≠ x))

/-- Merge of two sorted lists, descending by key (ties cannot occur between
distinct ids on chain-generated states, `sidedCoordOf_inj`). -/
def sMerge2 : SState → SState → SState
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
      if keyLt (sKey y.2.2) (sKey x.2.2) then x :: sMerge2 xs (y :: ys)
      else y :: sMerge2 (x :: xs) ys
termination_by xs ys => xs.length + ys.length

/-- Ternary merge: OR-set survival (values immutable, so each survivor's
record is read off whichever input holds it), re-canonicalized by the sorted
2-merge. Branch `a` contributes its survivors (shared with `b`, or new since
`l`); branch `b` contributes its own news not already contributed. -/
def sMergeL (l a b : SState) : SState :=
  sMerge2
    (a.filter (fun r => decide (r.1 ∈ sIds b ∨ r.1 ∉ sIds l)))
    (b.filter (fun r => decide (r.1 ∉ sIds l ∧ r.1 ∉ sIds a)))

/-- The sided embedded-chain RGA, parametric in the code (one `Γ` covers
both bands, the L band is `Γ` complemented, inside `sBlock`). The side is
datatype-blind: `Inv`/`applicable` are trivially true, and side *selection*
(all-R = published RGA, Fugue = non-interleaving) is a generation policy
of the honesty layer. -/
def S (Γ : OrderedPrefixCode) : MRDTSig where
  State := SState
  dec_state := inferInstance
  init := []
  AppOp := SOp
  dec_op := inferInstance
  Query := Unit
  Value := List ℕ
  update := sUpdate Γ
  merge := fun a b => sMergeL [] a b
  query := fun s _ => s.map (fun r => r.2.1)
  mergeL := sMergeL
  merge_init_slice := fun _ _ => rfl

theorem S_core_update (Γ : OrderedPrefixCode) (s : SState) (o : Op SOp) :
    (S Γ).toCRDTSig.update s o = sUpdate Γ s o := rfl

theorem S_rc_either (Γ : OrderedPrefixCode) (o₁ o₂ : Op SOp) :
    (S Γ).toCRDTSig.replayOrder o₁ o₂ = RcRes.Either := rfl

/-! ## §1½  First list algebra -/

theorem mem_sIds_sInsert {r : SRec} {t : ℕ} : ∀ {s : SState},
    t ∈ sIds (sInsert r s) ↔ t ∈ sIds s ∨ t = r.1
  | [] => by simp [sInsert, sIds]
  | x :: xs => by
      by_cases h : keyLt (sKey x.2.2) (sKey r.2.2) = true
      · simp only [sInsert, if_pos h, sIds, List.map_cons, List.mem_cons]
        tauto
      · simp only [sInsert, if_neg h, sIds, List.map_cons, List.mem_cons]
        have ih := @mem_sIds_sInsert r t xs
        simp only [sIds] at ih
        rw [ih]
        tauto

theorem mem_sIds_update_del {Γ : OrderedPrefixCode} {s : SState} {ts r x t : ℕ} :
    t ∈ sIds (sUpdate Γ s (ts, r, .del x)) ↔ t ∈ sIds s ∧ t ≠ x := by
  simp only [sUpdate, sIds, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hm := List.mem_of_mem_filter hp
    have hx := List.of_mem_filter hp
    simp at hx
    exact ⟨⟨p, hm, rfl⟩, hx⟩
  · rintro ⟨⟨p, hp, rfl⟩, hne⟩
    exact ⟨p, List.mem_filter.mpr ⟨hp, by simpa using hne⟩, rfl⟩

/-! ## §2  Sortedness and canonical-form extensionality

The state is canonical because it is strictly sorted: strictly-sorted lists
with the same members are EQUAL (`ssorted_ext`). Everything the fold and the
merge produce stays sorted, so fold-canonicity (§3) reduces to a membership
characterization. -/

open Sal.EmbedRGA (keyLt_trans keyLt_asymm keyLt_total keyLt_irrefl)

/-- Strictly descending by key, the canonical form. -/
def SSorted (s : SState) : Prop :=
  s.Pairwise (fun r r' => keyLt (sKey r'.2.2) (sKey r.2.2) = true)

theorem mem_sInsert {r x : SRec} : ∀ {s : SState},
    x ∈ sInsert r s ↔ x ∈ s ∨ x = r
  | [] => by simp [sInsert]
  | y :: ys => by
      by_cases h : keyLt (sKey y.2.2) (sKey r.2.2) = true
      · simp only [sInsert, if_pos h, List.mem_cons]
        tauto
      · simp only [sInsert, if_neg h, List.mem_cons]
        rw [mem_sInsert (s := ys)]
        tauto

theorem sInsert_sorted {r : SRec} : ∀ {s : SState}, SSorted s →
    (∀ x ∈ s, sKey x.2.2 ≠ sKey r.2.2) → SSorted (sInsert r s)
  | [], _, _ => List.pairwise_singleton _ _
  | y :: ys, hs, hne => by
      rcases List.pairwise_cons.mp hs with ⟨hy, hys⟩
      by_cases h : keyLt (sKey y.2.2) (sKey r.2.2) = true
      · rw [show sInsert r (y :: ys) = r :: y :: ys from by
          simp [sInsert, h]]
        refine List.pairwise_cons.mpr ⟨?_, hs⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz'
        · exact h
        · exact keyLt_trans (hy z hz') h
      · rw [show sInsert r (y :: ys) = y :: sInsert r ys from by
          simp [sInsert, h]]
        refine List.pairwise_cons.mpr ⟨?_, ?_⟩
        · intro z hz
          rcases mem_sInsert.mp hz with hz' | rfl
          · exact hy z hz'
          · rcases keyLt_total (hne y List.mem_cons_self) with h' | h'
            · exact absurd h' (by simpa using h)
            · exact h'
        · exact sInsert_sorted hys
            (fun x hx => hne x (List.mem_cons_of_mem _ hx))

theorem sUpdate_sorted {Γ : OrderedPrefixCode} {s : SState} {o : Op SOp}
    (hs : SSorted s)
    (hne : ∀ x ∈ s, sKey x.2.2 ≠ sKey (sCoord Γ o)) :
    SSorted (sUpdate Γ s o) := by
  obtain ⟨ts, r, op⟩ := o
  cases op with
  | del x => exact List.Pairwise.filter _ hs
  | ins e π a sd =>
      simp only [sUpdate]
      by_cases hmem : ts ∈ sIds s
      · rw [if_pos hmem]; exact hs
      · rw [if_neg hmem]
        exact sInsert_sorted hs (by
          intro x hx
          have := hne x hx
          simpa [sCoord] using this)

/-- **Canonical-form extensionality**: strictly-sorted lists with the same
members are equal. This is why the sorted list is a canonical state: any two
routes to the same record set produce the identical list. -/
theorem ssorted_ext : ∀ {s s' : SState}, SSorted s → SSorted s' →
    (∀ x, x ∈ s ↔ x ∈ s') → s = s'
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
            rw [keyLt_asymm h1] at h2
            exact Bool.noConfusion h2
      subst hxy
      have htails : ∀ z, z ∈ xs ↔ z ∈ ys := by
        intro z
        constructor
        · intro hz
          rcases List.mem_cons.mp ((hmem z).mp (List.mem_cons_of_mem _ hz))
            with rfl | h
          · exact absurd (hx z hz) (by rw [keyLt_irrefl]; simp)
          · exact h
        · intro hz
          rcases List.mem_cons.mp ((hmem z).mpr (List.mem_cons_of_mem _ hz))
            with rfl | h
          · exact absurd (hy z hz) (by rw [keyLt_irrefl]; simp)
          · exact h
      rw [ssorted_ext hxs hys htails]

/-! ## §2½  The sorted 2-merge -/

theorem mem_sMerge2 {x : SRec} : ∀ (as bs : SState),
    x ∈ sMerge2 as bs ↔ x ∈ as ∨ x ∈ bs := by
  intro as bs
  induction as, bs using sMerge2.induct with
  | case1 ys => simp [sMerge2]
  | case2 xs => cases xs <;> simp [sMerge2]
  | case3 a as' b bs' h ih =>
      rw [show sMerge2 (a :: as') (b :: bs') = a :: sMerge2 as' (b :: bs')
        from by rw [sMerge2]; simp [h]]
      simp only [List.mem_cons, ih]
      tauto
  | case4 a as' b bs' h ih =>
      rw [show sMerge2 (a :: as') (b :: bs') = b :: sMerge2 (a :: as') bs'
        from by rw [sMerge2]; simp [h]]
      simp only [List.mem_cons, ih]
      tauto

theorem sMerge2_sorted : ∀ {as bs : SState}, SSorted as → SSorted bs →
    (∀ a ∈ as, ∀ b ∈ bs, sKey a.2.2 ≠ sKey b.2.2) →
    SSorted (sMerge2 as bs) := by
  intro as bs has hbs hne
  induction as, bs using sMerge2.induct with
  | case1 ys => simpa [sMerge2] using hbs
  | case2 xs => cases xs <;> simpa [sMerge2] using has
  | case3 a as' b bs' h ih =>
      rw [show sMerge2 (a :: as') (b :: bs') = a :: sMerge2 as' (b :: bs')
        from by rw [sMerge2]; simp [h]]
      rcases List.pairwise_cons.mp has with ⟨ha, has'⟩
      refine List.pairwise_cons.mpr ⟨?_, ih has' hbs
        (fun x hx => hne x (List.mem_cons_of_mem _ hx))⟩
      intro z hz
      rcases (mem_sMerge2 as' (b :: bs')).mp hz with hz' | hz'
      · exact ha z hz'
      · rcases List.mem_cons.mp hz' with rfl | hz''
        · exact h
        · rcases List.pairwise_cons.mp hbs with ⟨hb, -⟩
          exact keyLt_trans (hb z hz'') h
  | case4 a as' b bs' h ih =>
      rw [show sMerge2 (a :: as') (b :: bs') = b :: sMerge2 (a :: as') bs'
        from by rw [sMerge2]; simp [h]]
      rcases List.pairwise_cons.mp hbs with ⟨hb, hbs'⟩
      have hab : keyLt (sKey a.2.2) (sKey b.2.2) = true := by
        rcases keyLt_total (Ne.symm (hne a List.mem_cons_self b
          List.mem_cons_self)) with h' | h'
        · exact absurd h' (by simpa using h)
        · exact h'
      refine List.pairwise_cons.mpr ⟨?_, ih has hbs'
        (fun x hx y hy => hne x hx y (List.mem_cons_of_mem _ hy))⟩
      intro z hz
      rcases (mem_sMerge2 (a :: as') bs').mp hz with hz' | hz'
      · rcases List.mem_cons.mp hz' with rfl | hz''
        · exact hab
        · rcases List.pairwise_cons.mp has with ⟨ha, -⟩
          exact keyLt_trans (ha z hz'') hab
      · exact hb z hz'

/-- The merge of canonical inputs is canonical (sorted), given no key ties,
supplied on chain-generated states by unique decodability
(`sidedCoordOf_inj`). -/
theorem sMergeL_sorted {l a b : SState}
    (ha : SSorted a) (hb : SSorted b)
    (hdisj : ∀ x ∈ a, ∀ y ∈ b, sKey x.2.2 = sKey y.2.2 → x = y) :
    SSorted (sMergeL l a b) := by
  apply sMerge2_sorted (List.Pairwise.filter _ ha) (List.Pairwise.filter _ hb)
  intro x hx y hy hkey
  have hxa := List.mem_of_mem_filter hx
  have hyb := List.mem_of_mem_filter hy
  have hxy : x = y := hdisj x hxa y hyb hkey
  subst hxy
  have h2 := List.of_mem_filter hy
  simp at h2
  exact h2.2 (List.mem_map.mpr ⟨x, hxa, rfl⟩)

/-! ## §3  Well-formed enumerations and fold-canonicity

`s_fold_canon`: any two well-formed enumerations of one event set fold to
the **same** state, the sided form of "state is a function of the event
set", by `ssorted_ext` + a fold membership characterization. The side rides
along inertly: it is consumed by `sCoord` at record-creation time and never
consulted again, which is why every proof below is the one-sided proof with
`sKey`/`sCoord` substituted. -/

def sFold (Γ : OrderedPrefixCode) (ρ : List (Op SOp)) : SState :=
  applySeq (S Γ).toCRDTSig (S Γ).init ρ

theorem sFold_snoc (Γ : OrderedPrefixCode) (ρ : List (Op SOp)) (e : Op SOp) :
    sFold Γ (ρ ++ [e]) = sUpdate Γ (sFold Γ ρ) e := by
  unfold sFold applySeq
  rw [List.foldl_append]
  rfl

def sIsIns (o : Op SOp) : Bool :=
  match o.2.2 with
  | .ins _ _ _ _ => true
  | .del _ => false

/-- The record an insert writes. -/
def sRecOf (Γ : OrderedPrefixCode) (o : Op SOp) : SRec :=
  (o.1, (match o.2.2 with | .ins e _ _ _ => e | .del _ => 0), sCoord Γ o)

def sInsIds (ρ : List (Op SOp)) : List ℕ :=
  (ρ.filter (fun o => sIsIns o)).map Prod.fst

def sDels (ρ : List (Op SOp)) : List ℕ :=
  ρ.filterMap (fun o => match o.2.2 with
    | .del x => some x | .ins _ _ _ _ => none)

theorem mem_sInsIds {ρ : List (Op SOp)} {t : ℕ} :
    t ∈ sInsIds ρ ↔ ∃ o ∈ ρ, sIsIns o = true ∧ o.1 = t := by
  simp only [sInsIds, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨o, ⟨hm, hi⟩, rfl⟩
    exact ⟨o, hm, hi, rfl⟩
  · rintro ⟨o, hm, hi, rfl⟩
    exact ⟨o, ⟨hm, hi⟩, rfl⟩

theorem mem_sDels {ρ : List (Op SOp)} {x : ℕ} :
    x ∈ sDels ρ ↔ ∃ o ∈ ρ, o.2.2 = SOp.del x := by
  simp only [sDels, List.mem_filterMap]
  constructor
  · rintro ⟨o, hm, hsome⟩
    refine ⟨o, hm, ?_⟩
    cases hop : o.2.2 with
    | ins e π a sd => rw [hop] at hsome; simp at hsome
    | del y => rw [hop] at hsome; simp at hsome; rw [hsome]
  · rintro ⟨o, hm, hdel⟩
    exact ⟨o, hm, by rw [hdel]⟩

theorem sInsIds_append (ρ σ : List (Op SOp)) :
    sInsIds (ρ ++ σ) = sInsIds ρ ++ sInsIds σ := by
  simp [sInsIds, List.filter_append]

theorem sDels_append (ρ σ : List (Op SOp)) :
    sDels (ρ ++ σ) = sDels ρ ++ sDels σ := by
  simp [sDels, List.filterMap_append]

/-- Well-formed enumerations: insert ids are unique, nothing is deleted
before its insert, and distinct inserts mint distinct keys (supplied on
honest histories by sided chain-generation + unique decodability,
`sidedCoordOf_inj`). -/
structure SWf (Γ : OrderedPrefixCode) (ρ : List (Op SOp)) : Prop where
  ins_nodup : (sInsIds ρ).Nodup
  del_late : ∀ σ o τ, ρ = σ ++ o :: τ → sIsIns o = true → o.1 ∉ sDels σ
  keys_inj : ∀ o₁ ∈ ρ, ∀ o₂ ∈ ρ, sIsIns o₁ = true → sIsIns o₂ = true →
      o₁.1 ≠ o₂.1 → sKey (sCoord Γ o₁) ≠ sKey (sCoord Γ o₂)

theorem SWf.prefix {Γ : OrderedPrefixCode} {ρ : List (Op SOp)} {e : Op SOp}
    (h : SWf Γ (ρ ++ [e])) : SWf Γ ρ where
  ins_nodup := by
    have := h.ins_nodup
    rw [sInsIds_append] at this
    exact this.of_append_left
  del_late := fun σ o τ heq hins => by
    refine h.del_late σ o (τ ++ [e]) ?_ hins
    rw [heq]
    simp
  keys_inj := fun o₁ h₁ o₂ h₂ => h.keys_inj o₁ (List.mem_append_left _ h₁)
    o₂ (List.mem_append_left _ h₂)

/-- Record provenance, unconditioned: everything in a fold was written by
some insert of the enumeration. -/
theorem s_fold_rec_sub (Γ : OrderedPrefixCode) : ∀ (ρ : List (Op SOp))
    (r : SRec), r ∈ sFold Γ ρ → ∃ o ∈ ρ, sIsIns o = true ∧ r = sRecOf Γ o := by
  intro ρ
  induction ρ using List.reverseRecOn with
  | nil =>
      intro r hr
      exact absurd hr (by simp [sFold, applySeq, S])
  | append_singleton ρ e ih =>
      intro r hr
      rw [sFold_snoc] at hr
      obtain ⟨ts, rr, op⟩ := e
      cases op with
      | ins el π a sd =>
          simp only [sUpdate] at hr
          by_cases hmem : ts ∈ sIds (sFold Γ ρ)
          · rw [if_pos hmem] at hr
            obtain ⟨o, hm, hi, hrec⟩ := ih r hr
            exact ⟨o, List.mem_append_left _ hm, hi, hrec⟩
          · rw [if_neg hmem] at hr
            rcases mem_sInsert.mp hr with hr' | rfl
            · obtain ⟨o, hm, hi, hrec⟩ := ih r hr'
              exact ⟨o, List.mem_append_left _ hm, hi, hrec⟩
            · exact ⟨(ts, rr, .ins el π a sd),
                List.mem_append_right _ (by simp),
                by simp [sIsIns], by simp [sRecOf, sCoord]⟩
      | del x =>
          simp only [sUpdate] at hr
          obtain ⟨o, hm, hi, hrec⟩ := ih r (List.mem_of_mem_filter hr)
          exact ⟨o, List.mem_append_left _ hm, hi, hrec⟩

/-- Under well-formedness the insert guard never fires: a fresh insert's id
is not in the fold of its past. -/
theorem s_fold_guard_free {Γ : OrderedPrefixCode} {ρ : List (Op SOp)}
    {e : Op SOp} (hwf : SWf Γ (ρ ++ [e])) (hins : sIsIns e = true) :
    e.1 ∉ sIds (sFold Γ ρ) := by
  intro hmem
  obtain ⟨r, hr, hr1⟩ := List.mem_map.mp hmem
  obtain ⟨o, hm, hi, hrec⟩ := s_fold_rec_sub Γ ρ r hr
  have ho1 : o.1 = e.1 := by rw [hrec] at hr1; exact hr1
  have h1 : e.1 ∈ sInsIds ρ := mem_sInsIds.mpr ⟨o, hm, hi, ho1⟩
  have := hwf.ins_nodup
  rw [sInsIds_append] at this
  rcases List.nodup_append.mp this with ⟨-, -, hdisj⟩
  have h2 : e.1 ∈ sInsIds [e] := by
    simp [sInsIds, hins]
  exact (hdisj e.1 h1 e.1 h2) rfl

/-- Folds of well-formed enumerations are canonical (sorted). -/
theorem s_fold_sorted (Γ : OrderedPrefixCode) : ∀ {ρ : List (Op SOp)},
    SWf Γ ρ → SSorted (sFold Γ ρ) := by
  intro ρ
  induction ρ using List.reverseRecOn with
  | nil =>
      intro _
      rw [show sFold Γ [] = [] from rfl]
      exact List.Pairwise.nil
  | append_singleton ρ e ih =>
      intro hwf
      have hsorted := ih hwf.prefix
      rw [sFold_snoc]
      obtain ⟨ts, rr, op⟩ := e
      cases op with
      | del x => exact List.Pairwise.filter _ hsorted
      | ins el π a sd =>
          simp only [sUpdate]
          by_cases hmem : ts ∈ sIds (sFold Γ ρ)
          · rw [if_pos hmem]; exact hsorted
          · rw [if_neg hmem]
            apply sInsert_sorted hsorted
            intro x hx
            obtain ⟨o, hm, hi, hrec⟩ := s_fold_rec_sub Γ ρ x hx
            have hx1 : x.1 = o.1 := by rw [hrec]; rfl
            have hne : o.1 ≠ ts := by
              intro heq
              exact hmem (List.mem_map.mpr ⟨x, hx, by rw [hx1, heq]⟩)
            have hkey := hwf.keys_inj o (List.mem_append_left _ hm)
              (ts, rr, .ins el π a sd) (List.mem_append_right _ (by simp))
              hi (by simp [sIsIns]) hne
            rw [hrec]
            show sKey (sCoord Γ o) ≠ sKey (π ++ sBlock Γ (sd, ts - a))
            simpa [sCoord] using hkey

/-- **The fold membership characterization**: under well-formedness a record
is in the fold iff its insert is in the enumeration and its id is never
deleted, an ORDER-FREE description. -/
theorem s_fold_mem (Γ : OrderedPrefixCode) : ∀ {ρ : List (Op SOp)},
    SWf Γ ρ → ∀ (r : SRec),
    (r ∈ sFold Γ ρ ↔
      (∃ o ∈ ρ, sIsIns o = true ∧ r = sRecOf Γ o) ∧ r.1 ∉ sDels ρ) := by
  intro ρ
  induction ρ using List.reverseRecOn with
  | nil =>
      intro _ r
      simp [show sFold Γ [] = [] from rfl]
  | append_singleton ρ e ih =>
      intro hwf r
      have IH := ih hwf.prefix
      rw [sFold_snoc]
      obtain ⟨ts, rr, op⟩ := e
      cases op with
      | ins el π a sd =>
          simp only [sUpdate]
          rw [if_neg (s_fold_guard_free hwf (by simp [sIsIns]))]
          have hdels : sDels (ρ ++ [(ts, rr, SOp.ins el π a sd)]) = sDels ρ := by
            rw [sDels_append]
            simp [sDels]
          rw [hdels, mem_sInsert]
          constructor
          · rintro (hr | rfl)
            · obtain ⟨⟨o, hm, hi, hrec⟩, hnd⟩ := (IH r).mp hr
              exact ⟨⟨o, List.mem_append_left _ hm, hi, hrec⟩, hnd⟩
            · refine ⟨⟨(ts, rr, .ins el π a sd),
                List.mem_append_right _ (by simp),
                by simp [sIsIns], by simp [sRecOf, sCoord]⟩, ?_⟩
              show ts ∉ sDels ρ
              exact hwf.del_late ρ (ts, rr, .ins el π a sd) [] rfl
                (by simp [sIsIns])
          · rintro ⟨⟨o, hm, hi, hrec⟩, hnd⟩
            rcases List.mem_append.mp hm with hm' | hm'
            · exact Or.inl ((IH r).mpr ⟨⟨o, hm', hi, hrec⟩, hnd⟩)
            · right
              have : o = (ts, rr, .ins el π a sd) := List.mem_singleton.mp hm'
              rw [hrec, this]
              simp [sRecOf, sCoord]
      | del x =>
          simp only [sUpdate]
          have hdels : sDels (ρ ++ [(ts, rr, SOp.del x)])
              = sDels ρ ++ [x] := by
            rw [sDels_append]
            simp [sDels]
          rw [hdels]
          constructor
          · intro hr
            have hm := List.mem_of_mem_filter hr
            have hx := List.of_mem_filter hr
            simp only [decide_eq_true_eq] at hx
            obtain ⟨⟨o, hmo, hi, hrec⟩, hnd⟩ := (IH r).mp hm
            refine ⟨⟨o, List.mem_append_left _ hmo, hi, hrec⟩, ?_⟩
            simp only [List.mem_append, List.mem_singleton]
            rintro (h | h)
            · exact hnd h
            · exact hx h
          · rintro ⟨⟨o, hm, hi, hrec⟩, hnd⟩
            simp only [List.mem_append, List.mem_singleton] at hnd
            push_neg at hnd
            have hm' : o ∈ ρ := by
              rcases List.mem_append.mp hm with h | h
              · exact h
              · have : o = (ts, rr, .del x) := List.mem_singleton.mp h
                rw [this] at hi
                simp [sIsIns] at hi
            refine List.mem_filter.mpr
              ⟨(IH r).mpr ⟨⟨o, hm', hi, hrec⟩, hnd.1⟩, by
                simpa using hnd.2⟩

/-- **Fold-canonicity**, sided: well-formed enumerations of one event set
fold to the SAME state. The state is a function of the event set, the
property the queue-route Join hook cannot live without, and the reason the
side can be a policy: the datatype's canonical state never depends on
enumeration order, whichever sides the ops carry. -/
theorem s_fold_canon (Γ : OrderedPrefixCode) {ρ ρ' : List (Op SOp)}
    (hwf : SWf Γ ρ) (hwf' : SWf Γ ρ')
    (hmem : ∀ o, o ∈ ρ ↔ o ∈ ρ') :
    sFold Γ ρ = sFold Γ ρ' := by
  apply ssorted_ext (s_fold_sorted Γ hwf) (s_fold_sorted Γ hwf')
  intro r
  rw [s_fold_mem Γ hwf r, s_fold_mem Γ hwf' r]
  constructor
  · rintro ⟨⟨o, hm, hi, hrec⟩, hnd⟩
    refine ⟨⟨o, (hmem o).mp hm, hi, hrec⟩, fun hx => hnd ?_⟩
    obtain ⟨o', hm', hdel⟩ := mem_sDels.mp hx
    exact mem_sDels.mpr ⟨o', (hmem o').mpr hm', hdel⟩
  · rintro ⟨⟨o, hm, hi, hrec⟩, hnd⟩
    refine ⟨⟨o, (hmem o).mpr hm, hi, hrec⟩, fun hx => hnd ?_⟩
    obtain ⟨o', hm', hdel⟩ := mem_sDels.mp hx
    exact mem_sDels.mpr ⟨o', (hmem o').mp hm', hdel⟩

/-! ## §5  Honest histories, well-formedness of enumerations

`SHonestCore` is the sided analogue of the embed instance's honesty: every
delete names an id its issuer had observed (a `vis`-prior insert), and
inserts are chain-generated, the mint is a positive sided birth chain's
coordinate whose timestamp components telescope to the id. The side is
part of the minted entry, not a separate obligation: whichever side the
generation policy picks, the chain is a chain. Its three consequences are
exactly `SWf`'s three fields. -/

open Sal.EmbedRGA (SChain PosSChain sidedCoordOf sidedCoordOf_inj
  sidedCoordOf_append)

/-- The marker makes `sKey` trivially injective. -/
theorem sKey_inj {c1 c2 : List ℕ} (h : sKey c1 = sKey c2) : c1 = c2 := by
  have h' : c1 ++ [3] = c2 ++ [3] := h
  exact (List.append_inj' h' rfl).1

/-- The one non-commuting shape: an insert and the delete of its id.
Witnessed at the empty state. -/
theorem s_ins_del_not_comm (Γ : OrderedPrefixCode) (ts r el : ℕ)
    (π : List ℕ) (a : ℕ) (sd : Side) (ts' r' : ℕ) :
    ¬ (S Γ).toCRDTSig.commutes (ts, r, SOp.ins el π a sd) (ts', r', SOp.del ts) := by
  intro h
  have h0 := h []
  rw [S_core_update, S_core_update, S_core_update, S_core_update] at h0
  simp only [sUpdate, sIds, sInsert, List.map_nil, List.not_mem_nil,
    if_false, List.filter_nil] at h0
  simp at h0

/-- Honest histories. -/
structure SHonestCore (Γ : OrderedPrefixCode)
    (C : Sal.MRDTs.Foundation.Configuration (S Γ).toCRDTSig) : Prop where
  /-- Every delete's target was inserted `vis`-before it. -/
  del_has_ins : ∀ e ∈ C.events, ∀ x : ℕ, e.2.2 = SOp.del x →
    ∃ a ∈ C.events, C.vis a e ∧ a.1 = x ∧ sIsIns a = true
  /-- Inserts are chain-generated: each mint is the coordinate of a positive
  sided birth chain whose timestamp components telescope to the id (so
  chains are injective on ids for free). -/
  chain_gen : ∃ chainOf : ℕ → SChain,
    ∀ o ∈ C.events, sIsIns o = true →
      PosSChain (chainOf o.1) ∧
      sCoord Γ o = sidedCoordOf Γ (chainOf o.1) ∧
      ((chainOf o.1).map Prod.snd).sum = o.1

/-- Honesty + backward closure: a delete's insert lies in the same closed
event set, `vis`-before it. -/
theorem s_del_ins_mem {Γ : OrderedPrefixCode}
    {C : Sal.MRDTs.Foundation.Configuration (S Γ).toCRDTSig}
    (hHon : SHonestCore Γ C) {ev : Set (Op SOp)}
    (hin : ∀ a ∈ ev, a ∈ C.events)
    (hcl : ∀ a b, C.vis a b → ¬ (S Γ).toCRDTSig.commutes a b → b ∈ ev → a ∈ ev) :
    ∀ d ∈ ev, ∀ x : ℕ, d.2.2 = SOp.del x →
      ∃ a ∈ ev, sIsIns a = true ∧ a.1 = x ∧ C.vis a d := by
  intro d hd x hdel
  obtain ⟨a, haev, hvis, hax, hains⟩ := hHon.del_has_ins d (hin d hd) x hdel
  have hncomm : ¬ (S Γ).toCRDTSig.commutes a d := by
    obtain ⟨a1, a2, aop⟩ := a
    obtain ⟨d1, d2, dop⟩ := d
    simp only at hdel hax
    subst hdel
    cases aop with
    | del y => simp [sIsIns] at hains
    | ins el π anc sd =>
        subst hax
        exact s_ins_del_not_comm Γ a1 a2 el π anc sd d1 d2
  exact ⟨a, hcl a d hvis hncomm hd, hains, hax, hvis⟩

/-- **A `loOn`-respecting enumeration of a closed honest set is
well-formed**, the bridge from the configuration layer to `SWf`, one
honesty ingredient per field: timestamp uniqueness gives `ins_nodup`,
delete-after-insert visibility gives `del_late`, chain generation +
sided unique decodability give `keys_inj`. -/
theorem s_wf_of_enum {Γ : OrderedPrefixCode}
    {C : Sal.MRDTs.Foundation.Configuration (S Γ).toCRDTSig}
    (hHon : SHonestCore Γ C) {ev : Set (Op SOp)} {ρ : List (Op SOp)}
    (hin : ∀ a ∈ ev, a ∈ C.events)
    (hcl : ∀ a b, C.vis a b → ¬ (S Γ).toCRDTSig.commutes a b → b ∈ ev → a ∈ ev)
    (hperm : listPermOf ρ ev)
    (hresp : respects ρ (loOn C ev)) : SWf Γ ρ where
  ins_nodup := by
    apply List.Nodup.map_on ?_ (hperm.1.filter _)
    intro o₁ h₁ o₂ h₂ hfst
    exact C.ts_unique
      (hin _ ((hperm.2 _).mp (List.mem_of_mem_filter h₁)))
      (hin _ ((hperm.2 _).mp (List.mem_of_mem_filter h₂))) hfst
  del_late := by
    intro σ o τ heq hins hdel
    obtain ⟨d, hdσ, hddel⟩ := mem_sDels.mp hdel
    have hdρ : d ∈ ρ := by
      rw [heq]; exact List.mem_append_left _ hdσ
    have hoρ : o ∈ ρ := by
      rw [heq]; exact List.mem_append_right _ List.mem_cons_self
    obtain ⟨a, haev, hains, hax, hvis⟩ :=
      s_del_ins_mem hHon hin hcl d ((hperm.2 d).mp hdρ) o.1 hddel
    have hao : a = o :=
      C.ts_unique (hin a haev) (hin o ((hperm.2 o).mp hoρ)) hax
    subst hao
    unfold respects at hresp
    rw [heq] at hresp
    have hcross := (List.pairwise_append.mp hresp).2.2 d hdσ a
      List.mem_cons_self
    apply hcross
    rw [loOn_iff_of_rc_either (S_rc_either Γ)]
    refine ⟨hvis, ?_⟩
    obtain ⟨a1, a2, aop⟩ := a
    obtain ⟨d1, d2, dop⟩ := d
    simp only at hddel
    subst hddel
    cases aop with
    | del y => simp [sIsIns] at hins
    | ins el π anc sd =>
        exact s_ins_del_not_comm Γ a1 a2 el π anc sd d1 d2
  keys_inj := by
    obtain ⟨chainOf, hch⟩ := hHon.chain_gen
    intro o₁ h₁ o₂ h₂ hi₁ hi₂ hne hkey
    obtain ⟨hp₁, hc₁, hs₁⟩ := hch o₁ (hin _ ((hperm.2 _).mp h₁)) hi₁
    obtain ⟨hp₂, hc₂, hs₂⟩ := hch o₂ (hin _ ((hperm.2 _).mp h₂)) hi₂
    apply hne
    have hc : sidedCoordOf Γ (chainOf o₁.1) = sidedCoordOf Γ (chainOf o₂.1) := by
      rw [← hc₁, ← hc₂]
      exact sKey_inj hkey
    have hchain := sidedCoordOf_inj Γ hp₁ hp₂ hc
    calc o₁.1 = ((chainOf o₁.1).map Prod.snd).sum := hs₁.symm
      _ = ((chainOf o₂.1).map Prod.snd).sum := by rw [hchain]
      _ = o₂.1 := hs₂

/-! ## §6a  The survival algebra

The record-level membership of the ternary merge, characterized order-free
against the union event set, the mathematical core of the Join. §6b turns
it into `JoinLemma3At` by exhibiting the witness enumeration. -/

theorem s_fold_id_mem (Γ : OrderedPrefixCode) {ρ : List (Op SOp)}
    (hwf : SWf Γ ρ) (t : ℕ) :
    t ∈ sIds (sFold Γ ρ) ↔
      (∃ o ∈ ρ, sIsIns o = true ∧ o.1 = t) ∧ t ∉ sDels ρ := by
  constructor
  · intro h
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
    obtain ⟨⟨o, hm, hi, hrec⟩, hnd⟩ := (s_fold_mem Γ hwf r).mp hr
    exact ⟨⟨o, hm, hi, by rw [hrec]; rfl⟩, hnd⟩
  · rintro ⟨⟨o, hm, hi, rfl⟩, hnd⟩
    have hr : sRecOf Γ o ∈ sFold Γ ρ :=
      (s_fold_mem Γ hwf _).mpr ⟨⟨o, hm, hi, rfl⟩, hnd⟩
    exact List.mem_map.mpr ⟨sRecOf Γ o, hr, rfl⟩

/-- Distinct honest inserts mint distinct keys (the standalone form of
`s_wf_of_enum`'s third discharge, for use at the merge site). -/
theorem s_keys_inj_events {Γ : OrderedPrefixCode}
    {C : Sal.MRDTs.Foundation.Configuration (S Γ).toCRDTSig}
    (hHon : SHonestCore Γ C) :
    ∀ o₁ ∈ C.events, ∀ o₂ ∈ C.events, sIsIns o₁ = true → sIsIns o₂ = true →
      o₁.1 ≠ o₂.1 → sKey (sCoord Γ o₁) ≠ sKey (sCoord Γ o₂) := by
  obtain ⟨chainOf, hch⟩ := hHon.chain_gen
  intro o₁ h₁ o₂ h₂ hi₁ hi₂ hne hkey
  obtain ⟨hp₁, hc₁, hs₁⟩ := hch o₁ h₁ hi₁
  obtain ⟨hp₂, hc₂, hs₂⟩ := hch o₂ h₂ hi₂
  apply hne
  have hc : sidedCoordOf Γ (chainOf o₁.1) = sidedCoordOf Γ (chainOf o₂.1) := by
    rw [← hc₁, ← hc₂]
    exact sKey_inj hkey
  have hchain := sidedCoordOf_inj Γ hp₁ hp₂ hc
  calc o₁.1 = ((chainOf o₁.1).map Prod.snd).sum := hs₁.symm
    _ = ((chainOf o₂.1).map Prod.snd).sum := by rw [hchain]
    _ = o₂.1 := hs₂

/-- **The merge membership characterization.** At a join site (three
canonical enumerations over an honest configuration), a record is in the
ternary merge iff its insert is somewhere in the union and its id is deleted
nowhere in the union, the union's order-free membership. OR-set survival,
with honesty closing the one subtle corner (a branch-2 delete of a
branch-1 survivor forces the insert into the LCA). -/
theorem s_mergeL_mem {Γ : OrderedPrefixCode}
    {C : Sal.MRDTs.Foundation.Configuration (S Γ).toCRDTSig}
    (hHon : SHonestCore Γ C) {ev₁ ev₂ : Set (Op SOp)}
    {ρ₀ ρ₁ ρ₂ : List (Op SOp)}
    (hin₁ : ∀ a ∈ ev₁, a ∈ C.events) (hin₂ : ∀ a ∈ ev₂, a ∈ C.events)
    (hcl₁ : ∀ a b, C.vis a b → ¬ (S Γ).toCRDTSig.commutes a b → b ∈ ev₁ → a ∈ ev₁)
    (hcl₂ : ∀ a b, C.vis a b → ¬ (S Γ).toCRDTSig.commutes a b → b ∈ ev₂ → a ∈ ev₂)
    (hp₀ : listPermOf ρ₀ (ev₁ ∩ ev₂)) (hp₁ : listPermOf ρ₁ ev₁)
    (hp₂ : listPermOf ρ₂ ev₂)
    (hwf₀ : SWf Γ ρ₀) (hwf₁ : SWf Γ ρ₁) (hwf₂ : SWf Γ ρ₂) (r : SRec) :
    r ∈ sMergeL (sFold Γ ρ₀) (sFold Γ ρ₁) (sFold Γ ρ₂) ↔
      (∃ o, (o ∈ ev₁ ∨ o ∈ ev₂) ∧ sIsIns o = true ∧ r = sRecOf Γ o) ∧
      (∀ d, (d ∈ ev₁ ∨ d ∈ ev₂) → d.2.2 ≠ SOp.del r.1) := by
  classical
  set s₀ := sFold Γ ρ₀
  set s₁ := sFold Γ ρ₁
  set s₂ := sFold Γ ρ₂
  have hdels : ∀ {ρ : List (Op SOp)} {ev : Set (Op SOp)}, listPermOf ρ ev →
      ∀ {t : ℕ}, t ∈ sDels ρ ↔ ∃ d ∈ ev, d.2.2 = SOp.del t := by
    intro ρ ev hp t
    rw [mem_sDels]
    constructor
    · rintro ⟨d, hm, hdel⟩
      exact ⟨d, (hp.2 d).mp hm, hdel⟩
    · rintro ⟨d, hm, hdel⟩
      exact ⟨d, (hp.2 d).mpr hm, hdel⟩
  rw [show sMergeL s₀ s₁ s₂ = sMerge2
    (s₁.filter (fun x => decide (x.1 ∈ sIds s₂ ∨ x.1 ∉ sIds s₀)))
    (s₂.filter (fun x => decide (x.1 ∉ sIds s₀ ∧ x.1 ∉ sIds s₁))) from rfl,
    mem_sMerge2]
  constructor
  · rintro (hr | hr)
    · -- branch-1 survivor
      have hm := List.mem_of_mem_filter hr
      have hcond := List.of_mem_filter hr
      simp only [decide_eq_true_eq] at hcond
      obtain ⟨⟨o, hoρ, hi, hrec⟩, hnd₁⟩ := (s_fold_mem Γ hwf₁ r).mp hm
      refine ⟨⟨o, Or.inl ((hp₁.2 o).mp hoρ), hi, hrec⟩, ?_⟩
      rintro d (hd | hd) hdel
      · exact hnd₁ ((hdels hp₁).mpr ⟨d, hd, hdel⟩)
      · rcases hcond with hin2 | hout0
        · have := ((s_fold_id_mem Γ hwf₂ r.1).mp hin2).2
          exact this ((hdels hp₂).mpr ⟨d, hd, hdel⟩)
        · -- honest corner: the deleter's insert lands in the LCA
          obtain ⟨a, haev₂, hains, hax, -⟩ :=
            s_del_ins_mem hHon hin₂ hcl₂ d hd r.1 hdel
          have hao : a = o := by
            apply C.ts_unique (hin₂ a haev₂)
              (hin₁ o ((hp₁.2 o).mp hoρ))
            rw [hax, hrec]; rfl
          have ho₀ : o ∈ ev₁ ∩ ev₂ :=
            ⟨(hp₁.2 o).mp hoρ, hao ▸ haev₂⟩
          apply hout0
          rw [s_fold_id_mem Γ hwf₀]
          refine ⟨⟨o, (hp₀.2 o).mpr ho₀, hi, by rw [hrec]; rfl⟩, ?_⟩
          intro hdel0
          obtain ⟨d', hd', hdel'⟩ := (hdels hp₀).mp hdel0
          exact hnd₁ ((hdels hp₁).mpr ⟨d', hd'.1, hdel'⟩)
    · -- branch-2 news
      have hm := List.mem_of_mem_filter hr
      have hcond := List.of_mem_filter hr
      simp only [decide_eq_true_eq] at hcond
      obtain ⟨⟨o, hoρ, hi, hrec⟩, hnd₂⟩ := (s_fold_mem Γ hwf₂ r).mp hm
      refine ⟨⟨o, Or.inr ((hp₂.2 o).mp hoρ), hi, hrec⟩, ?_⟩
      rintro d (hd | hd) hdel
      · -- a branch-1 delete would force the insert into the LCA,
        -- contradicting r.1 ∉ ids s₀
        obtain ⟨a, haev₁, hains, hax, -⟩ :=
          s_del_ins_mem hHon hin₁ hcl₁ d hd r.1 hdel
        have hao : a = o := by
          apply C.ts_unique (hin₁ a haev₁)
            (hin₂ o ((hp₂.2 o).mp hoρ))
          rw [hax, hrec]; rfl
        have ho₀ : o ∈ ev₁ ∩ ev₂ :=
          ⟨hao ▸ haev₁, (hp₂.2 o).mp hoρ⟩
        apply hcond.1
        rw [s_fold_id_mem Γ hwf₀]
        refine ⟨⟨o, (hp₀.2 o).mpr ho₀, hi, by rw [hrec]; rfl⟩, ?_⟩
        intro hdel0
        obtain ⟨d', hd', hdel'⟩ := (hdels hp₀).mp hdel0
        exact hnd₂ ((hdels hp₂).mpr ⟨d', hd'.2, hdel'⟩)
      · exact hnd₂ ((hdels hp₂).mpr ⟨d, hd, hdel⟩)
  · rintro ⟨⟨o, hor, hi, hrec⟩, hnd⟩
    by_cases ho₁ : o ∈ ev₁
    · -- route through branch 1
      left
      refine List.mem_filter.mpr ⟨?_, ?_⟩
      · rw [s_fold_mem Γ hwf₁]
        refine ⟨⟨o, (hp₁.2 o).mpr ho₁, hi, hrec⟩, ?_⟩
        intro hdel1
        obtain ⟨d, hd, hdel⟩ := (hdels hp₁).mp hdel1
        exact hnd d (Or.inl hd) hdel
      · simp only [decide_eq_true_eq]
        by_cases h0 : r.1 ∈ sIds s₀
        · left
          obtain ⟨⟨o', ho'ρ, hi', ho'1⟩, -⟩ := (s_fold_id_mem Γ hwf₀ r.1).mp h0
          have ho'₀ := (hp₀.2 o').mp ho'ρ
          rw [s_fold_id_mem Γ hwf₂]
          refine ⟨⟨o', (hp₂.2 o').mpr ho'₀.2, hi', ho'1⟩, ?_⟩
          intro hdel2
          obtain ⟨d, hd, hdel⟩ := (hdels hp₂).mp hdel2
          exact hnd d (Or.inr hd) hdel
        · exact Or.inr h0
    · -- o ∈ ev₂ only: route through branch 2
      have ho₂ : o ∈ ev₂ := by
        rcases hor with h | h
        · exact absurd h ho₁
        · exact h
      right
      refine List.mem_filter.mpr ⟨?_, ?_⟩
      · rw [s_fold_mem Γ hwf₂]
        refine ⟨⟨o, (hp₂.2 o).mpr ho₂, hi, hrec⟩, ?_⟩
        intro hdel2
        obtain ⟨d, hd, hdel⟩ := (hdels hp₂).mp hdel2
        exact hnd d (Or.inr hd) hdel
      · simp only [decide_eq_true_eq]
        have hnot : ∀ {ρ : List (Op SOp)} {ev : Set (Op SOp)},
            listPermOf ρ ev → SWf Γ ρ → (∀ a ∈ ev, a ∈ C.events) →
            (∀ a ∈ ev, a ∈ ev₁) → r.1 ∉ sIds (sFold Γ ρ) := by
          intro ρ ev hp hwf hin hsub hmem
          obtain ⟨⟨o', ho'ρ, hi', ho'1⟩, -⟩ := (s_fold_id_mem Γ hwf r.1).mp hmem
          have ho'ev := (hp.2 o').mp ho'ρ
          have : o' = o := by
            apply C.ts_unique (hin o' ho'ev) (hin₂ o ho₂)
            rw [ho'1, hrec]; rfl
          exact ho₁ (this ▸ hsub o' ho'ev)
        exact ⟨hnot hp₀ hwf₀ (fun a ha => hin₁ a ha.1) (fun a ha => ha.1),
               hnot hp₁ hwf₁ hin₁ (fun a ha => ha)⟩

/-! ## §6b  The Join: the merge is its own linearization witness

Witness enumeration for the union: the LCA's enumeration, then branch one's
delta (in branch order), then branch two's news. Its `respects` obligation
falls to CLOSURE, a `loOn`-later event sitting in an earlier block would
have been pulled into the earlier event set, and `loOn` is event-set
independent under `rc = Either`, so within-block orders transfer verbatim. -/

open LabeledTS in
theorem s_join_at {Γ : OrderedPrefixCode}
    {C : Sal.MRDTs.Foundation.Configuration (S Γ).toCRDTSig}
    (hHon : SHonestCore Γ C) : JoinLemma3At (S Γ) C := by
  intro ev₁ ev₂ s₀ s₁ s₂ _htr _hir hin₁ hin₂ hcl₁ hcl₂ h₀ h₁ h₂
  classical
  obtain ⟨ρ₀, hp₀, hr₀, hf₀⟩ := h₀
  obtain ⟨ρ₁, hp₁, hr₁, hf₁⟩ := h₁
  obtain ⟨ρ₂, hp₂, hr₂, hf₂⟩ := h₂
  set ev₀ := ev₁ ∩ ev₂ with hev₀
  have hin₀ : ∀ a ∈ ev₀, a ∈ C.events := fun a ha => hin₁ a ha.1
  have hcl₀ : ∀ a b, C.vis a b → ¬ (S Γ).toCRDTSig.commutes a b →
      b ∈ ev₀ → a ∈ ev₀ :=
    fun a b hv hc hb => ⟨hcl₁ a b hv hc hb.1, hcl₂ a b hv hc hb.2⟩
  have hinU : ∀ a ∈ ev₁ ∪ ev₂, a ∈ C.events := by
    rintro a (ha | ha)
    · exact hin₁ a ha
    · exact hin₂ a ha
  have hclU : ∀ a b, C.vis a b → ¬ (S Γ).toCRDTSig.commutes a b →
      b ∈ ev₁ ∪ ev₂ → a ∈ ev₁ ∪ ev₂ := by
    rintro a b hv hc (hb | hb)
    · exact Or.inl (hcl₁ a b hv hc hb)
    · exact Or.inr (hcl₂ a b hv hc hb)
  have hwf₀ := s_wf_of_enum hHon hin₀ hcl₀ hp₀ hr₀
  have hwf₁ := s_wf_of_enum hHon hin₁ hcl₁ hp₁ hr₁
  have hwf₂ := s_wf_of_enum hHon hin₂ hcl₂ hp₂ hr₂
  -- loOn is event-set independent under rc = Either
  have hloOn : ∀ (ev ev' : Set (Op SOp)) (x y : Op SOp),
      loOn C ev x y → loOn C ev' x y := by
    intro ev ev' x y h
    rw [loOn_iff_of_rc_either (S_rc_either Γ)] at h ⊢
    exact h
  -- the witness enumeration
  set δ₁ := ρ₁.filter (fun o => decide (o ∉ ev₀)) with hδ₁
  set δ₂ := ρ₂.filter (fun o => decide (o ∉ ev₁)) with hδ₂
  set ρᵤ := ρ₀ ++ (δ₁ ++ δ₂) with hρᵤ
  have hmemδ₁ : ∀ {o}, o ∈ δ₁ ↔ o ∈ ρ₁ ∧ o ∉ ev₀ := by
    intro o
    rw [hδ₁]
    simp [List.mem_filter]
  have hmemδ₂ : ∀ {o}, o ∈ δ₂ ↔ o ∈ ρ₂ ∧ o ∉ ev₁ := by
    intro o
    rw [hδ₂]
    simp [List.mem_filter]
  -- membership: ρᵤ enumerates the union
  have hmemU : ∀ o, o ∈ ρᵤ ↔ o ∈ ev₁ ∪ ev₂ := by
    intro o
    rw [hρᵤ]
    simp only [List.mem_append]
    constructor
    · rintro (h | h | h)
      · exact Or.inl ((hp₀.2 o).mp h).1
      · exact Or.inl ((hp₁.2 o).mp (hmemδ₁.mp h).1)
      · exact Or.inr ((hp₂.2 o).mp (hmemδ₂.mp h).1)
    · rintro (h | h)
      · by_cases h0 : o ∈ ev₀
        · exact Or.inl ((hp₀.2 o).mpr h0)
        · exact Or.inr (Or.inl (hmemδ₁.mpr ⟨(hp₁.2 o).mpr h, h0⟩))
      · by_cases h1 : o ∈ ev₁
        · by_cases h0 : o ∈ ev₀
          · exact Or.inl ((hp₀.2 o).mpr h0)
          · exact Or.inr (Or.inl (hmemδ₁.mpr ⟨(hp₁.2 o).mpr h1, h0⟩))
        · exact Or.inr (Or.inr (hmemδ₂.mpr ⟨(hp₂.2 o).mpr h, h1⟩))
  -- nodup: blocks are nodup and pairwise set-separated
  have hndU : ρᵤ.Nodup := by
    rw [hρᵤ]
    rw [List.nodup_append]
    refine ⟨hp₀.1, ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hp₁.1.filter _, hp₂.1.filter _, ?_⟩
      intro a ha b hb hab
      subst hab
      exact (hmemδ₂.mp hb).2 ((hp₁.2 a).mp (hmemδ₁.mp ha).1)
    · intro a ha b hb hab
      subst hab
      have ha0 : a ∈ ev₀ := (hp₀.2 a).mp ha
      rcases List.mem_append.mp hb with h | h
      · exact (hmemδ₁.mp h).2 ha0
      · exact (hmemδ₂.mp h).2 ha0.1
  have hpU : listPermOf ρᵤ (ev₁ ∪ ev₂) := ⟨hndU, hmemU⟩
  -- respects: within-blocks by transfer, cross-blocks by closure
  have hrU : respects ρᵤ (loOn C (ev₁ ∪ ev₂)) := by
    rw [hρᵤ]
    unfold respects at hr₀ hr₁ hr₂ ⊢
    rw [List.pairwise_append]
    refine ⟨hr₀.imp (fun h hl => h (hloOn _ _ _ _ hl)), ?_, ?_⟩
    · rw [List.pairwise_append]
      refine ⟨(hr₁.sublist List.filter_sublist).imp
          (fun h hl => h (hloOn _ _ _ _ hl)),
        (hr₂.sublist List.filter_sublist).imp
          (fun h hl => h (hloOn _ _ _ _ hl)), ?_⟩
      -- cross δ₁ × δ₂: a loOn-later δ₂ event before a δ₁ event would be in ev₁
      intro a ha b hb hl
      rw [loOn_iff_of_rc_either (S_rc_either Γ)] at hl
      have hb1 : b ∈ ev₁ := hcl₁ b a hl.1 hl.2 ((hp₁.2 a).mp (hmemδ₁.mp ha).1)
      exact (hmemδ₂.mp hb).2 hb1
    · -- cross ρ₀ × deltas: a loOn-later delta event before an LCA event
      -- would be in ev₀
      intro a ha b hb hl
      rw [loOn_iff_of_rc_either (S_rc_either Γ)] at hl
      have ha0 : a ∈ ev₀ := (hp₀.2 a).mp ha
      have hb0 : b ∈ ev₀ := hcl₀ b a hl.1 hl.2 ha0
      rcases List.mem_append.mp hb with h | h
      · exact (hmemδ₁.mp h).2 hb0
      · exact (hmemδ₂.mp h).2 hb0.1
  have hwfU : SWf Γ ρᵤ := s_wf_of_enum hHon hinU hclU hpU hrU
  -- the fold of the witness IS the merge, by canonical-form extensionality
  refine ⟨ρᵤ, hpU, hrU, ?_⟩
  show sFold Γ ρᵤ = (S Γ).mergeL s₀ s₁ s₂
  rw [← hf₀, ← hf₁, ← hf₂]
  show sFold Γ ρᵤ = sMergeL (sFold Γ ρ₀) (sFold Γ ρ₁) (sFold Γ ρ₂)
  -- cross-key-injectivity feeding the merge's sortedness
  have hdisj : ∀ x ∈ sFold Γ ρ₁, ∀ y ∈ sFold Γ ρ₂,
      sKey x.2.2 = sKey y.2.2 → x = y := by
    intro x hx y hy hkey
    obtain ⟨o₁, hm₁, hi₁, hrec₁⟩ := s_fold_rec_sub Γ ρ₁ x hx
    obtain ⟨o₂, hm₂, hi₂, hrec₂⟩ := s_fold_rec_sub Γ ρ₂ y hy
    have he₁ : o₁ ∈ C.events := hin₁ o₁ ((hp₁.2 o₁).mp hm₁)
    have he₂ : o₂ ∈ C.events := hin₂ o₂ ((hp₂.2 o₂).mp hm₂)
    have hkey' : sKey (sCoord Γ o₁) = sKey (sCoord Γ o₂) := by
      rw [hrec₁, hrec₂] at hkey
      exact hkey
    have hids : o₁.1 = o₂.1 := by
      by_contra hne
      exact s_keys_inj_events hHon o₁ he₁ o₂ he₂ hi₁ hi₂ hne hkey'
    have : o₁ = o₂ := C.ts_unique he₁ he₂ hids
    rw [hrec₁, hrec₂, this]
  apply ssorted_ext (s_fold_sorted Γ hwfU)
    (sMergeL_sorted (s_fold_sorted Γ hwf₁) (s_fold_sorted Γ hwf₂) hdisj)
  intro r
  rw [s_fold_mem Γ hwfU r,
      s_mergeL_mem hHon hin₁ hin₂ hcl₁ hcl₂ hp₀ hp₁ hp₂ hwf₀ hwf₁ hwf₂ r]
  constructor
  · rintro ⟨⟨o, hm, hi, hrec⟩, hnd⟩
    have hor : o ∈ ev₁ ∨ o ∈ ev₂ := by
      rcases (hmemU o).mp hm with h | h
      · exact Or.inl h
      · exact Or.inr h
    refine ⟨⟨o, hor, hi, hrec⟩, ?_⟩
    intro d hd hdel
    apply hnd
    apply mem_sDels.mpr
    refine ⟨d, (hmemU d).mpr ?_, hdel⟩
    rcases hd with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro ⟨⟨o, hor, hi, hrec⟩, hnd⟩
    have hmU : o ∈ ev₁ ∪ ev₂ := by
      rcases hor with h | h
      · exact Or.inl h
      · exact Or.inr h
    refine ⟨⟨o, (hmemU o).mpr hmU, hi, hrec⟩, ?_⟩
    intro hdel
    obtain ⟨d, hd, hdel'⟩ := mem_sDels.mp hdel
    rcases (hmemU d).mp hd with h | h
    · exact hnd d (Or.inl h) hdel'
    · exact hnd d (Or.inr h) hdel'



/-- Honest histories at the ternary configuration: every delete names an id
its issuer had observed (a `vis`-prior insert), and inserts are
chain-generated. The sided embed's `HonestDelivery`. -/
def SHonest (Γ : OrderedPrefixCode) (C : Configuration (S Γ)) : Prop :=
  (∀ e ∈ C.events, ∀ x : ℕ, e.2.2 = SOp.del x →
    ∃ a ∈ C.events, C.vis a e ∧ a.1 = x ∧ sIsIns a = true) ∧
  (∃ chainOf : ℕ → SChain, ∀ o ∈ C.events, sIsIns o = true →
    PosSChain (chainOf o.1) ∧ sCoord Γ o = sidedCoordOf Γ (chainOf o.1) ∧
    ((chainOf o.1).map Prod.snd).sum = o.1)

theorem sHonest_core {Γ : OrderedPrefixCode} {C : Configuration (S Γ)}
    (h : SHonest Γ C) : SHonestCore Γ (Configuration.core C) where
  del_has_ins := by
    intro e he x hx
    rw [Configuration.core_events] at he
    obtain ⟨a, ha, hv, hax, hai⟩ := h.1 e he x hx
    refine ⟨a, ?_, hv, hax, hai⟩
    rw [Configuration.core_events]
    exact ha
  chain_gen := by
    obtain ⟨chainOf, hch⟩ := h.2
    refine ⟨chainOf, fun o ho hi => hch o ?_ hi⟩
    rw [Configuration.core_events] at ho
    exact ho
/-! ## §8  The generation discipline: `applicable` implies honesty

What a well-behaved replica checks before issuing an op at the state it
sees. Both `SHonest` components are consequences: the delete half exactly as
the queue (fold provenance is unconditioned), the chain half by building the
global chain assignment by strong induction on ids, anchors have smaller
timestamps, and the anchor's record in ANY fold of the issuer's past is
op-determined, so the carried prefix is forced to be the anchor's chain's
coordinate. The side rides into the minted entry untouched: the guard
constrains the anchor, never the side, which is the honesty-layer face of
"side selection is a generation policy". -/

/-- The issuer-side guard: an insert's anchor is live with EXACTLY the
carried prefix as its stored coordinate and a smaller stamp (Lamport); a
delete's target is live. The side is unconstrained. -/
def sApplicable (o : Op SOp) (s : SState) : Prop :=
  match o with
  | (t, _, .ins _ π a _) => a < t ∧ ((a = 0 ∧ π = []) ∨ ∃ el, (a, el, π) ∈ s)
  | (_, _, .del x)       => x ∈ sIds s

/-- Per-id chain existence: every insert's coordinate is a positive sided
chain's coordinate with telescoping timestamp sum. Strong induction on the
id. -/
theorem s_chain_exists {Γ : OrderedPrefixCode} (C : Configuration (S Γ))
    (hApp : ∀ e ∈ C.events, ∃ π : List (Op SOp),
      listPermOf π {e' ∈ C.events | C.vis e' e} ∧
      sApplicable e (sFold Γ π)) :
    ∀ t : ℕ, ∃ ch : SChain, PosSChain ch ∧ (ch.map Prod.snd).sum = t ∧
      ∀ o ∈ C.events, sIsIns o = true → o.1 = t →
        sCoord Γ o = sidedCoordOf Γ ch := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    classical
    by_cases hex : ∃ o ∈ C.events, sIsIns o = true ∧ o.1 = t
    · obtain ⟨o, ho, hoi, hot⟩ := hex
      obtain ⟨ts, r, op⟩ := o
      cases op with
      | del x => simp [sIsIns] at hoi
      | ins el π a sd =>
          simp only at hot
          subst hot
          obtain ⟨πe, hπe, happ⟩ := hApp _ ho
          simp only [sApplicable] at happ
          obtain ⟨hat, hcase⟩ := happ
          rcases hcase with ⟨ha0, hπ0⟩ | ⟨el', hmem⟩
          · subst ha0
            subst hπ0
            refine ⟨[(sd, ts)], ?_, by simp, ?_⟩
            · intro d hd
              simp at hd
              rw [hd]
              show 1 ≤ ts
              exact hat
            · intro o' ho' hoi' hot'
              have ho'eq : o' = (ts, r, SOp.ins el [] 0 sd) :=
                (Configuration.core C).ts_unique ho' ho hot'
              rw [ho'eq]
              simp [sCoord, sidedCoordOf]
          · obtain ⟨aop, haπ, hai, hae⟩ := s_fold_rec_sub Γ πe (a, el', π) hmem
            have haev := (hπe.2 aop).mp haπ
            have ha1 : aop.1 = a := congrArg Prod.fst hae.symm
            have hπval : π = sCoord Γ aop :=
              congrArg (fun p : SRec => p.2.2) hae
            obtain ⟨ch, hpos, hsum, hcoord⟩ := ih a hat
            refine ⟨ch ++ [(sd, ts - a)], ?_, ?_, ?_⟩
            · intro d hd
              rcases List.mem_append.mp hd with h | h
              · exact hpos d h
              · simp at h
                rw [h]
                show 1 ≤ ts - a
                exact Nat.le_sub_of_add_le (Nat.add_comm 1 a ▸ hat)
            · rw [List.map_append, List.sum_append]
              simp
              omega
            · intro o' ho' hoi' hot'
              have ho'eq : o' = (ts, r, SOp.ins el π a sd) :=
                (Configuration.core C).ts_unique ho' ho hot'
              rw [ho'eq]
              show π ++ sBlock Γ (sd, ts - a) = sidedCoordOf Γ (ch ++ [(sd, ts - a)])
              rw [sidedCoordOf_append, hπval, hcoord aop haev.1 hai ha1]
              simp [sidedCoordOf]
    · push_neg at hex
      cases t with
      | zero =>
          exact ⟨[], by intro d hd; simp at hd, rfl,
            fun o ho hi h1 => absurd h1 (hex o ho hi)⟩
      | succ n =>
          refine ⟨[(Side.R, n + 1)], ?_, by simp,
            fun o ho hi h1 => absurd h1 (hex o ho hi)⟩
          intro d hd
          simp at hd
          rw [hd]
          show 1 ≤ n + 1
          omega

/-- **The `applicable` discipline discharges honesty.** If every op was
applicable at SOME fold of its issuer's causal past, the issuer's own
materialized state is such a fold, then the history is honest: a delete's
target can only have entered that fold through a `vis`-prior insert, and the
carried prefixes are forced to be sided birth-chain coordinates. -/
theorem sHonest_of_applicable {Γ : OrderedPrefixCode} (C : Configuration (S Γ))
    (hApp : ∀ e ∈ C.events, ∃ π : List (Op SOp),
      listPermOf π {e' ∈ C.events | C.vis e' e} ∧
      sApplicable e (sFold Γ π)) :
    SHonest Γ C := by
  constructor
  · -- delete half: fold provenance
    intro e he x hx
    obtain ⟨π, hπ, happ⟩ := hApp e he
    obtain ⟨ts, r, op⟩ := e
    simp only at hx
    subst hx
    simp only [sApplicable] at happ
    obtain ⟨rec, hrec, hrec1⟩ := List.mem_map.mp happ
    obtain ⟨a, ha, hai, hae⟩ := s_fold_rec_sub Γ π rec hrec
    have haev := (hπ.2 a).mp ha
    have hax : a.1 = x := by
      rw [hae] at hrec1
      exact hrec1
    exact ⟨a, haev.1, haev.2, hax, hai⟩
  · -- chain half: the global assignment, by choice over per-id existence
    classical
    refine ⟨fun t => Classical.choose (s_chain_exists C hApp t), ?_⟩
    intro o ho hi
    obtain ⟨hpos, hsum, hcoord⟩ :=
      Classical.choose_spec (s_chain_exists C hApp o.1)
    exact ⟨hpos, hcoord o ho hi rfl, hsum⟩



def generation (Γ : OrderedPrefixCode) : Issuance (S Γ) where
  CanIssue := sApplicable

theorem sHonest_of_mint {Γ : OrderedPrefixCode} {C : Configuration (S Γ)}
    (h : MintHonest (S Γ) sApplicable C) : SHonest Γ C :=
  sHonest_of_applicable C (fun e he => by
    obtain ⟨π, hp, _hr, hg⟩ := h e he
    exact ⟨π, hp, hg⟩)

theorem convergence (Γ : OrderedPrefixCode) :
    ConvergenceCertificate (S Γ) (generation Γ) where
  soundV := fun h => (isRALinearizable_iff_join _ _).mpr
    (ra_of_mintCertifiedV
      (fun C hH => s_join_at (sHonest_core (sHonest_of_mint hH))) h)


end Sal.MRDTs.Instances.SidedEmbedRGA
