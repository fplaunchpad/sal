import Sal.ConditionedMRDTs.MRDT_Instances.Peritext_Embed.PeritextEmbed_MarksGC

/-!
# O4 — the A3 guarded pair-drop

An `(add m, remove r)` pair with EQUAL boundary tuples (ids and sides) and
`m.mid < r.mid` resolves to the same covered interval forever, and `r` beats
`m` on every covered character, so dropping both records (and, downstream,
their retention roots) looks render-neutral.  The naive settledness guard is
NOT enough; `a3_guarded_drop` proves render preservation under the full
guard, and the two SPOT FAIL companions pin each clause's necessity:

* **(alpha)** settledness / declared in-flights: a concurrent same-mtype mark
  with mid below `r.mid` (delivered late) is resurrected by the drop —
  `alpha_undeclared_flip`; the `hothers` clause (which ranges over declared
  in-flight marks too) refuses it.
* **(beta)**: a character id strictly inside `(m.mid, r.mid)` is grabbed by
  the add's end-growth (`id > m.mid`) but NOT by the remove's (`id < r.mid`
  fails its newer-run test), so the pair is not render-neutral even though
  its boundaries are identical — `beta_growth_window_flip`; the `hwindow`
  clause refuses it.  Checking the settled + declared ids at the cut
  suffices: beyond-cut mints are Lamport-fresh (above `r.mid`), so they
  satisfy `hwindow` automatically.

The theorem is stated over the FINAL delivered document and mark list; the
cut-time guards of the harness (`a3_pairs`: removal settled, no same-mtype
mark below `r.mid` among settled or declared, no settled-or-declared id in
the window) plus beyond-cut Lamport freshness are exactly what make the
final-form hypotheses `hothers`/`hwindow` true.  Only `r.op = remove` is
load-bearing for the verdict (`m` never wins in the pair's presence); the
`m.op = add` hypothesis documents the pair shape.

A root freed by this drop between two GC epochs is the rank-reclaim shape
`naive_composition_collides` (`EmbedRGA_MultiEpoch.lean`) pins; the two-epoch
capstone `marksGC_render_congr_twoEpoch` already carries the
surviving-domain composite that fix requires.
-/

namespace Sal.ConditionedMRDTs.PeritextEmbed.MarksGC

open Sal.Emulation
open Sal.ConditionedMRDTs.PeritextEmbed.MarkDoc
open Sal.EmbedRGA (unaryCode)

set_option linter.unusedSectionVars false

deriving instance DecidableEq for Sal.ConditionedMRDTs.PeritextEmbed.MarkDoc.MarkD

/-! ## §1  The LWW fold, characterized -/

/-- `foldl winner` from a seeded accumulator returns a member (or the seed)
whose `mid` dominates everything folded over. -/
theorem foldl_winner_acc :
    ∀ (l : List MarkD) (a : MarkD),
      ∃ w, l.foldl winner (some a) = some w ∧ (w = a ∨ w ∈ l) ∧ a.mid ≤ w.mid ∧
        ∀ o ∈ l, o.mid ≤ w.mid
  | [], a => ⟨a, rfl, Or.inl rfl, Nat.le_refl _,
      fun o ho => absurd ho List.not_mem_nil⟩
  | x :: l, a => by
      rw [List.foldl_cons]
      by_cases h : a.mid < x.mid
      · have hwin : winner (some a) x = some x := by simp [winner, h]
        rw [hwin]
        obtain ⟨w, hfold, hmem, hle, hall⟩ := foldl_winner_acc l x
        refine ⟨w, hfold, ?_, Nat.le_trans (Nat.le_of_lt h) hle, ?_⟩
        · rcases hmem with rfl | hm
          · exact Or.inr List.mem_cons_self
          · exact Or.inr (List.mem_cons_of_mem _ hm)
        · intro o ho
          rcases List.mem_cons.mp ho with rfl | ho'
          · exact hle
          · exact hall o ho'
      · have hwin : winner (some a) x = some a := by simp [winner, h]
        rw [hwin]
        obtain ⟨w, hfold, hmem, hle, hall⟩ := foldl_winner_acc l a
        refine ⟨w, hfold, ?_, hle, ?_⟩
        · rcases hmem with rfl | hm
          · exact Or.inl rfl
          · exact Or.inr (List.mem_cons_of_mem _ hm)
        · intro o ho
          rcases List.mem_cons.mp ho with rfl | ho'
          · exact Nat.le_trans (Nat.le_of_not_lt h) hle
          · exact hall o ho'

/-- The LWW fold on a candidate list: empty ↦ `none`, else a member with the
maximal `mid`. -/
theorem foldl_winner_spec (l : List MarkD) :
    (l = [] ∧ l.foldl winner none = none) ∨
    ∃ w, l.foldl winner none = some w ∧ w ∈ l ∧ ∀ o ∈ l, o.mid ≤ w.mid := by
  cases l with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons x l =>
      right
      rw [List.foldl_cons]
      rw [show winner none x = some x from rfl]
      obtain ⟨w, hfold, hmem, hle, hall⟩ := foldl_winner_acc l x
      refine ⟨w, hfold, ?_, ?_⟩
      · rcases hmem with rfl | hm
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ hm
      · intro o ho
        rcases List.mem_cons.mp ho with rfl | ho'
        · exact hle
        · exact hall o ho'

/-- Distinct marks carry distinct mids (Lamport), so `mid` is injective on
the mark list. -/
theorem mid_inj {marks : List MarkD} (hnodup : (marks.map MarkD.mid).Nodup)
    {a b : MarkD} (ha : a ∈ marks) (hb : b ∈ marks) (h : a.mid = b.mid) :
    a = b :=
  List.inj_on_of_nodup_map hnodup ha hb h

/-! ## §2  The pair resolves to ONE interval (the window guard at work) -/

theorem skipRight_window (live : List ℕ) (mm rm : ℕ)
    (hw : ∀ c ∈ live, decide (mm < c) = decide (rm < c)) (j : ℕ) :
    skipRight live mm j = skipRight live rm j := by
  unfold skipRight
  rw [takeWhile_congr_mem _ _ _ (fun c hc =>
    hw c ((List.drop_sublist _ _).subset hc))]

theorem skipLeft_window (live : List ℕ) (mm rm : ℕ)
    (hw : ∀ c ∈ live, decide (mm < c) = decide (rm < c)) (i : ℕ) :
    skipLeft live mm i = skipLeft live rm i := by
  unfold skipLeft
  rw [takeWhile_congr_mem _ _ _ (fun c hc =>
    hw c ((List.take_sublist _ _).subset (List.mem_reverse.mp hc)))]

theorem startIncl_pair (d : DocD) (m r : MarkD)
    (hsid : r.start_id = m.start_id) (hss : r.startSide = m.startSide)
    (hw : ∀ c ∈ d.liveIds, decide (m.mid < c) = decide (r.mid < c)) :
    startIncl d r = startIncl d m := by
  rw [startIncl_factor, startIncl_factor]
  have hres : startResolved d r = startResolved d m := by
    unfold startResolved
    rw [hsid, hss]
  rw [hres]
  cases hX : startResolved d m with
  | none =>
      unfold startFinish
      rw [hss]
  | some a =>
      unfold startFinish
      rw [hss]
      cases hSide : m.startSide with
      | before => rfl
      | after =>
          show some ((idxOf d.liveIds a + 1)
              + skipRight d.liveIds r.mid (idxOf d.liveIds a + 1))
            = some ((idxOf d.liveIds a + 1)
              + skipRight d.liveIds m.mid (idxOf d.liveIds a + 1))
          rw [skipRight_window d.liveIds r.mid m.mid
            (fun c hc => (hw c hc).symm)]

theorem endExcl_pair (d : DocD) (m r : MarkD)
    (heid : r.end_id = m.end_id) (hes : r.endSide = m.endSide)
    (hw : ∀ c ∈ d.liveIds, decide (m.mid < c) = decide (r.mid < c)) :
    endExcl d r = endExcl d m := by
  rw [endExcl_factor, endExcl_factor]
  have hres : endResolved d r = endResolved d m := by
    unfold endResolved
    rw [heid, hes]
  rw [hres]
  cases hX : endResolved d m with
  | none =>
      unfold endFinish
      rw [hes]
  | some a =>
      unfold endFinish
      rw [hes]
      cases hSide : m.endSide with
      | after =>
          show some ((idxOf d.liveIds a + 1)
              + skipRight d.liveIds r.mid (idxOf d.liveIds a + 1))
            = some ((idxOf d.liveIds a + 1)
              + skipRight d.liveIds m.mid (idxOf d.liveIds a + 1))
          rw [skipRight_window d.liveIds r.mid m.mid
            (fun c hc => (hw c hc).symm)]
      | before =>
          show some (idxOf d.liveIds a - skipLeft d.liveIds r.mid (idxOf d.liveIds a))
            = some (idxOf d.liveIds a - skipLeft d.liveIds m.mid (idxOf d.liveIds a))
          rw [skipLeft_window d.liveIds r.mid m.mid
            (fun c hc => (hw c hc).symm)]

/-- Equal boundary tuples + the window guard ⟹ the pair covers the same
positions, at every render position, forever. -/
theorem markCoversPos_pair (d : DocD) (m r : MarkD)
    (hsid : r.start_id = m.start_id) (heid : r.end_id = m.end_id)
    (hss : r.startSide = m.startSide) (hes : r.endSide = m.endSide)
    (hw : ∀ c ∈ d.liveIds, decide (m.mid < c) = decide (r.mid < c)) (k : ℕ) :
    markCoversPos d r k = markCoversPos d m k := by
  unfold markCoversPos
  rw [startIncl_pair d m r hsid hss hw, endExcl_pair d m r heid hes hw]

/-! ## §3  O4 — the guarded drop preserves the render -/

/-- The per-position core: under the guards, dropping the pair never changes
a character's verdict.  Either some OTHER same-mtype mark covers the
position — then it has mid above `r.mid` (guard iii + declared in-flights +
freshness) and wins on both sides — or the pair's members are the only
covering candidates, the winner is `r` (LWW inside the pair), and a winning
`remove` renders exactly like no mark at all. -/
theorem fmtAt_drop_pair (d : DocD) (marks : List MarkD) (m r : MarkD) (mt : MType)
    (hm : m ∈ marks) (hr : r ∈ marks)
    (hopr : r.op = MarkOp.remove)
    (hty : r.mtype = m.mtype) (hlt : m.mid < r.mid)
    (hsid : r.start_id = m.start_id) (heid : r.end_id = m.end_id)
    (hss : r.startSide = m.startSide) (hes : r.endSide = m.endSide)
    (hnodup : (marks.map MarkD.mid).Nodup)
    (hothers : ∀ o ∈ marks, o.mtype = m.mtype → o.mid ≠ m.mid → o.mid ≠ r.mid →
      r.mid < o.mid)
    (hwindow : ∀ c ∈ d.birthIds, c ≤ m.mid ∨ r.mid < c) (k : ℕ) :
    fmtAt (markCoversPos d)
        (marks.filter (fun o => !(o.mid == m.mid || o.mid == r.mid))) mt k
      = fmtAt (markCoversPos d) marks mt k := by
  -- the window guard makes the pair's newer-run tests agree on every live id
  have hw : ∀ c ∈ d.liveIds, decide (m.mid < c) = decide (r.mid < c) := by
    intro c hc
    rcases hwindow c (List.mem_of_mem_filter hc) with h | h
    · have h1 : ¬ m.mid < c := Nat.not_lt.mpr h
      have h2 : ¬ r.mid < c := Nat.not_lt.mpr (Nat.le_trans h (Nat.le_of_lt hlt))
      simp [h1, h2]
    · have h1 : m.mid < c := Nat.lt_trans hlt h
      simp [h1, h]
  have hcov : markCoversPos d r k = markCoversPos d m k :=
    markCoversPos_pair d m r hsid heid hss hes hw k
  have hpairmem : ∀ o ∈ marks, (o.mid == m.mid || o.mid == r.mid) = true →
      o = m ∨ o = r := by
    intro o ho hpo
    have h' : o.mid = m.mid ∨ o.mid = r.mid := by simpa using hpo
    rcases h' with h | h
    · exact Or.inl (mid_inj hnodup ho hm h)
    · exact Or.inr (mid_inj hnodup ho hr h)
  -- the two candidate lists differ exactly by the pair members
  have hcand : (marks.filter (fun o => !(o.mid == m.mid || o.mid == r.mid))).filter
        (fun o => decide (o.mtype = mt) && markCoversPos d o k)
      = (marks.filter (fun o => decide (o.mtype = mt) && markCoversPos d o k)).filter
          (fun o => !(o.mid == m.mid || o.mid == r.mid)) := by
    rw [filter_and, filter_and]
    exact List.filter_congr (fun o _ => Bool.and_comm _ _)
  have hPrPm : (decide (r.mtype = mt) && markCoversPos d r k)
      = (decide (m.mtype = mt) && markCoversPos d m k) := by
    rw [hty, hcov]
  by_cases hPm : (decide (m.mtype = mt) && markCoversPos d m k) = true
  · -- the pair genuinely covers: analyze both winners
    have hPr : (decide (r.mtype = mt) && markCoversPos d r k) = true := by
      rw [hPrPm]
      exact hPm
    have hrW : r ∈ marks.filter (fun o => decide (o.mtype = mt) && markCoversPos d o k) :=
      List.mem_filter.mpr ⟨hr, hPr⟩
    have hmtEq : m.mtype = mt := by
      have h' := hPm
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
      exact h'.1
    unfold fmtAt bestCover
    rw [hcand]
    rcases foldl_winner_spec ((marks.filter
        (fun o => decide (o.mtype = mt) && markCoversPos d o k)).filter
        (fun o => !(o.mid == m.mid || o.mid == r.mid))) with
      ⟨hOnil, hOfold⟩ | ⟨wO, hOfold, hOmem, hOmax⟩
    · -- no non-pair candidate: with-pair winner is r, a remove: both sides false
      rw [hOfold]
      rcases foldl_winner_spec (marks.filter
          (fun o => decide (o.mtype = mt) && markCoversPos d o k)) with
        ⟨hWnil, _⟩ | ⟨wW, hWfold, hWmem, hWmax⟩
      · rw [hWnil] at hrW
        exact absurd hrW List.not_mem_nil
      · rw [hWfold]
        have hallpair : ∀ o ∈ marks.filter
            (fun o => decide (o.mtype = mt) && markCoversPos d o k),
            (o.mid == m.mid || o.mid == r.mid) = true := by
          intro o ho
          cases hb : (o.mid == m.mid || o.mid == r.mid) with
          | true => rfl
          | false =>
              have : o ∈ (marks.filter
                  (fun o => decide (o.mtype = mt) && markCoversPos d o k)).filter
                  (fun o => !(o.mid == m.mid || o.mid == r.mid)) :=
                List.mem_filter.mpr ⟨ho, by rw [hb]; rfl⟩
              rw [hOnil] at this
              exact absurd this List.not_mem_nil
        have hwWr : wW = r := by
          rcases hpairmem wW (List.mem_of_mem_filter hWmem) (hallpair wW hWmem) with
            rfl | rfl
          · exact absurd (hWmax r hrW) (Nat.not_le.mpr hlt)
          · rfl
        rw [hwWr]
        show false = decide (r.op = MarkOp.add)
        rw [hopr]
        decide
    · -- a non-pair candidate exists: the winners coincide
      have hwOW : wO ∈ marks.filter
          (fun o => decide (o.mtype = mt) && markCoversPos d o k) :=
        List.mem_of_mem_filter hOmem
      have hwOmarks : wO ∈ marks := List.mem_of_mem_filter hwOW
      have hwOP := (List.mem_filter.mp hwOW).2
      have hwOnp : (!(wO.mid == m.mid || wO.mid == r.mid)) = true :=
        (List.mem_filter.mp hOmem).2
      have hwOty : wO.mtype = m.mtype := by
        have h' := hwOP
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
        rw [h'.1]
        exact hmtEq.symm
      have hwOne : wO.mid ≠ m.mid ∧ wO.mid ≠ r.mid := by
        constructor
        · intro hEq
          have : (wO.mid == m.mid || wO.mid == r.mid) = true := by
            rw [hEq]
            simp
          rw [this] at hwOnp
          exact Bool.noConfusion hwOnp
        · intro hEq
          have : (wO.mid == m.mid || wO.mid == r.mid) = true := by
            rw [hEq]
            simp
          rw [this] at hwOnp
          exact Bool.noConfusion hwOnp
      have hrlt : r.mid < wO.mid := hothers wO hwOmarks hwOty hwOne.1 hwOne.2
      rcases foldl_winner_spec (marks.filter
          (fun o => decide (o.mtype = mt) && markCoversPos d o k)) with
        ⟨hWnil, _⟩ | ⟨wW, hWfold, hWmem, hWmax⟩
      · rw [hWnil] at hrW
        exact absurd hrW List.not_mem_nil
      · rw [hOfold, hWfold]
        have hwWgt : r.mid < wW.mid := Nat.lt_of_lt_of_le hrlt (hWmax wO hwOW)
        have hwWnp : (!(wW.mid == m.mid || wW.mid == r.mid)) = true := by
          cases hb : (wW.mid == m.mid || wW.mid == r.mid) with
          | false => rfl
          | true =>
              rcases hpairmem wW (List.mem_of_mem_filter hWmem) hb with rfl | rfl
              · exact absurd hwWgt (Nat.lt_asymm hlt)
              · exact absurd hwWgt (Nat.lt_irrefl _)
        have hwWO : wW ∈ (marks.filter
            (fun o => decide (o.mtype = mt) && markCoversPos d o k)).filter
            (fun o => !(o.mid == m.mid || o.mid == r.mid)) :=
          List.mem_filter.mpr ⟨hWmem, hwWnp⟩
        have heq : wO = wW := mid_inj hnodup hwOmarks (List.mem_of_mem_filter hWmem)
          (Nat.le_antisymm (hWmax wO hwOW) (hOmax wW hwWO))
        rw [heq]
  · -- the pair covers nothing at k (or wrong type): the candidate lists agree
    have hPmf : (decide (m.mtype = mt) && markCoversPos d m k) = false := by
      cases h : (decide (m.mtype = mt) && markCoversPos d m k) with
      | true => exact absurd h hPm
      | false => rfl
    have hPrf : (decide (r.mtype = mt) && markCoversPos d r k) = false := by
      rw [hPrPm]
      exact hPmf
    unfold fmtAt bestCover
    rw [hcand]
    have hnopair : ∀ o ∈ marks.filter
        (fun o => decide (o.mtype = mt) && markCoversPos d o k),
        (!(o.mid == m.mid || o.mid == r.mid)) = true := by
      intro o ho
      have hom : o ∈ marks := List.mem_of_mem_filter ho
      have hoP := (List.mem_filter.mp ho).2
      cases hb : (o.mid == m.mid || o.mid == r.mid) with
      | false => rfl
      | true =>
          rcases hpairmem o hom hb with rfl | rfl
          · rw [hPmf] at hoP
            exact Bool.noConfusion hoP
          · rw [hPrf] at hoP
            exact Bool.noConfusion hoP
    rw [List.filter_eq_self.mpr hnopair]

/-- **O4 (the A3 guarded drop).**  Removing an `(add, remove)` pair with
equal boundary tuples and `r.mid > m.mid` preserves `renderMarksDoc` under
the three guards, stated over the final delivered document and mark list:

* removal settled + declared in-flights included: `hothers` ranges over the
  FULL final list, so a settled cut may check settled marks plus declared
  in-flight marks and rely on Lamport freshness for everything else;
* no other same-mtype mark with mid below `r.mid` (`hothers`);
* no id strictly inside `(m.mid, r.mid)` (`hwindow`; beyond-cut mints are
  fresh, above `r.mid`, so checking settled + declared ids at the cut
  suffices).

Dropping the pair frees its boundary anchors for the NEXT cut's keep-set
(they stop being mark anchors); `gamma_root_freed` pins the freed root. -/
theorem a3_guarded_drop (d : DocD) (marks : List MarkD) (m r : MarkD) (mt : MType)
    (hm : m ∈ marks) (hr : r ∈ marks)
    (hopm : m.op = MarkOp.add) (hopr : r.op = MarkOp.remove)
    (hty : r.mtype = m.mtype) (hlt : m.mid < r.mid)
    (hsid : r.start_id = m.start_id) (heid : r.end_id = m.end_id)
    (hss : r.startSide = m.startSide) (hes : r.endSide = m.endSide)
    (hnodup : (marks.map MarkD.mid).Nodup)
    (hothers : ∀ o ∈ marks, o.mtype = m.mtype → o.mid ≠ m.mid → o.mid ≠ r.mid →
      r.mid < o.mid)
    (hwindow : ∀ c ∈ d.birthIds, c ≤ m.mid ∨ r.mid < c) :
    renderMarksDoc d (marks.filter (fun o => !(o.mid == m.mid || o.mid == r.mid))) mt
      = renderMarksDoc d marks mt := by
  unfold renderMarksDoc renderFlagWith
  refine mapIdx_congr_mem _ _ _ (fun k c _ => ?_)
  rw [fmtAt_drop_pair d marks m r mt hm hr hopr hty hlt hsid heid hss hes
    hnodup hothers hwindow k]

/-! ## §4  SPOTs, hand-derived, PASS + FAIL shaped -/

namespace SPOT_A3

/-! ### (gamma) the guarded positive, with a genuinely freed retention root

`A` = 1, `B` = 2 (child of `A`, DEAD), beyond-cut `x` = 10 under `A`; add
bold `[A..B]` mid 3, remove bold `[A..B]` mid 4, same sides.  Window `(3,4)`
empty, no other bold mark: the guard fires.  Twin (hand): birth `A x B`,
live `A x`; both marks' dead end `B` rehomes left to `x`; both cover
`{A, x}`; remove (mid 4) wins everywhere: ALL PLAIN.  Dropped: no marks:
ALL PLAIN.  Identical — and `B`'s record stops being a retention root, so
the next cut drops it (plain H-A would retain it forever). -/

def dGamTwin : DocD :=
  { shadow := buildShadow unaryCode [(1, 65, 0), (2, 66, 1), (10, 120, 1)],
    deleted := [2] }

def addG : MarkD :=
  { mid := 3, mtype := MType.bold, op := MarkOp.add, start_id := 1, end_id := 2 }
def remG : MarkD :=
  { mid := 4, mtype := MType.bold, op := MarkOp.remove, start_id := 1, end_id := 2 }

theorem gamma_filter :
    [addG, remG].filter (fun o => !(o.mid == addG.mid || o.mid == remG.mid))
      = [] := by native_decide

/-- PASS: with the pair, everything is plain (the remove wins on the whole
rehomed span, growth included); with the pair dropped, everything is plain
trivially. -/
theorem gamma_renders :
    renderMarksDoc dGamTwin [addG, remG] MType.bold = [(65, false), (120, false)] ∧
    renderMarksDoc dGamTwin [] MType.bold = [(65, false), (120, false)] := by
  native_decide

/-- **PASS, fired through the theorem**: `a3_guarded_drop` discharges on the
concrete pair — settled removal, no other bold mark, empty growth window. -/
theorem gamma_via_theorem :
    renderMarksDoc dGamTwin [] MType.bold
      = renderMarksDoc dGamTwin [addG, remG] MType.bold := by
  have h := a3_guarded_drop dGamTwin [addG, remG] addG remG MType.bold
    (by simp) (by simp) rfl rfl rfl (by decide) rfl rfl rfl rfl
    (by native_decide)
    (by
      intro o ho h1 h2 h3
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl
      · exact absurd rfl h2
      · exact absurd rfl h3)
    (by native_decide)
  rw [gamma_filter] at h
  exact h

/-- PASS (the payoff): after the pair-drop, `B` is no retention root; the
next cut's keep-set drops its record and the render still matches the twin
with both marks present. -/
def dGamSubj : DocD :=
  { shadow := dGamTwin.shadow.filter (fun r => r.1 != 2), deleted := [2] }

theorem gamma_root_freed :
    renderMarksDoc dGamSubj [] MType.bold
      = renderMarksDoc dGamTwin [addG, remG] MType.bold ∧
    (2 ∉ dGamSubj.birthIds) ∧ (2 ∈ dGamTwin.birthIds) := by native_decide

/-! ### (gamma₂) the guarded positive with a surviving rival mark

Same doc; a third bold mark `big` (mid 20, `[A..x]`) stays: the drop must
leave ITS verdict intact (the winners-coincide branch of the proof). -/

def bigG : MarkD :=
  { mid := 20, mtype := MType.bold, op := MarkOp.add, start_id := 1, end_id := 10 }

theorem gamma2_filter :
    [addG, remG, bigG].filter (fun o => !(o.mid == addG.mid || o.mid == remG.mid))
      = [bigG] := by native_decide

theorem gamma2_via_theorem :
    renderMarksDoc dGamTwin [bigG] MType.bold
      = renderMarksDoc dGamTwin [addG, remG, bigG] MType.bold := by
  have h := a3_guarded_drop dGamTwin [addG, remG, bigG] addG remG MType.bold
    (by simp) (by simp) rfl rfl rfl (by decide) rfl rfl rfl rfl
    (by native_decide)
    (by
      intro o ho h1 h2 h3
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl
      · exact absurd rfl h2
      · exact absurd rfl h3
      · decide)
    (by native_decide)
  rw [gamma2_filter] at h
  exact h

/-- PASS: the rival `big` (mid 20 > 4) formats `{A, x}` with or without the
pair — dropping the pair never resurrects or suppresses it. -/
theorem gamma2_renders :
    renderMarksDoc dGamTwin [addG, remG, bigG] MType.bold
      = [(65, true), (120, true)] ∧
    renderMarksDoc dGamTwin [bigG] MType.bold = [(65, true), (120, true)] := by
  native_decide

/-! ### (beta) FAIL — the growth window

`A` = 1, `B` = 2 (child of `A`), `w` = 4 (child of `B`, LIVE, settled); add
bold `[A..B]` mid 3, remove bold `[A..B]` mid 5 — identical boundaries, both
anchors LIVE, removal settled.  Hand: the add's end-growth grabs `w`
(`4 > 3`) but the remove's does NOT (`4 < 5` fails its newer-run test), so
`w` is BOLD with the pair present and PLAIN after an unguarded drop — the
pair is NOT render-neutral even though its boundary tuples are equal.  The
window guard `hwindow` refuses: `w`'s id 4 sits strictly inside `(3, 5)`. -/

def dBeta : DocD :=
  { shadow := buildShadow unaryCode [(1, 65, 0), (2, 66, 1), (4, 119, 2)],
    deleted := [] }

def addB : MarkD :=
  { mid := 3, mtype := MType.bold, op := MarkOp.add, start_id := 1, end_id := 2 }
def remB : MarkD :=
  { mid := 5, mtype := MType.bold, op := MarkOp.remove, start_id := 1, end_id := 2 }

/-- **FAIL (beta)**: the unguarded drop FLIPS `w` from bold to plain. -/
theorem beta_growth_window_flip :
    renderMarksDoc dBeta [addB, remB] MType.bold
      = [(65, false), (66, false), (119, true)] ∧
    renderMarksDoc dBeta [] MType.bold
      = [(65, false), (66, false), (119, false)] ∧
    renderMarksDoc dBeta [] MType.bold
      ≠ renderMarksDoc dBeta [addB, remB] MType.bold := by native_decide

/-- The window guard refuses beta: `w`'s id sits strictly inside
`(m.mid, r.mid)`, so `a3_guarded_drop`'s `hwindow` hypothesis is FALSE on
this document — the flip is the guard clause's necessity witness. -/
theorem beta_guard_refuses :
    ¬ (∀ c ∈ dBeta.birthIds, c ≤ addB.mid ∨ remB.mid < c) := by native_decide

/-! ### (alpha) FAIL — settledness / declared in-flights

`A` = 1, `B` = 2; add bold mid 3, remove bold mid 6, and a concurrent
same-mtype add mid 4 in flight at the drop, delivered after it.  Hand: with
the pair present the remove (mid 6) beats both adds: ALL PLAIN; with the
pair dropped the straggler add (mid 4) is unopposed: `{A, B}` BOLD.  FLIP.
The `hothers` clause — which ranges over declared in-flight marks — sees
mid 4 below 6 and refuses. -/

def dAlpha : DocD :=
  { shadow := buildShadow unaryCode [(1, 65, 0), (2, 66, 1)], deleted := [] }

def addA : MarkD :=
  { mid := 3, mtype := MType.bold, op := MarkOp.add, start_id := 1, end_id := 2 }
def remA : MarkD :=
  { mid := 6, mtype := MType.bold, op := MarkOp.remove, start_id := 1, end_id := 2 }
def stragA : MarkD :=
  { mid := 4, mtype := MType.bold, op := MarkOp.add, start_id := 1, end_id := 2 }

/-- **FAIL (alpha)**: dropping the pair while ignoring the declared
in-flight add resurrects it — `{A, B}` flips to bold. -/
theorem alpha_undeclared_flip :
    renderMarksDoc dAlpha [addA, remA, stragA] MType.bold
      = [(65, false), (66, false)] ∧
    renderMarksDoc dAlpha [stragA] MType.bold = [(65, true), (66, true)] ∧
    renderMarksDoc dAlpha [stragA] MType.bold
      ≠ renderMarksDoc dAlpha [addA, remA, stragA] MType.bold := by native_decide

/-- The declared-in-flight clause refuses alpha: the straggler is a
same-mtype mark with mid below the remove's, so `hothers` is FALSE on the
final list. -/
theorem alpha_guard_refuses :
    ¬ (∀ o ∈ [addA, remA, stragA], o.mtype = addA.mtype → o.mid ≠ addA.mid →
        o.mid ≠ remA.mid → remA.mid < o.mid) := by native_decide

end SPOT_A3

/-! ## §5  Axiom audit -/

#print axioms foldl_winner_spec
#print axioms markCoversPos_pair
#print axioms fmtAt_drop_pair
#print axioms a3_guarded_drop
#print axioms SPOT_A3.gamma_via_theorem
#print axioms SPOT_A3.gamma2_via_theorem
#print axioms SPOT_A3.gamma_root_freed
#print axioms SPOT_A3.beta_growth_window_flip
#print axioms SPOT_A3.beta_guard_refuses
#print axioms SPOT_A3.alpha_undeclared_flip
#print axioms SPOT_A3.alpha_guard_refuses

end Sal.ConditionedMRDTs.PeritextEmbed.MarksGC
