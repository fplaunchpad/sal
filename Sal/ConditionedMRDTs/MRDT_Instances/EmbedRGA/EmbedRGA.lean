import Sal.ConditionedMRDTs.Metatheory.HonestReach
import Sal.MRDTs.RGA_Embed.RGA_Embed_ChainLex
import Sal.MRDTs.RGA_Embed.Embed_Code_Binary

/-!
# The embedded-chain RGA as a conditioned MRDT instance — §1, the datatype

Route decision (recorded): the **mergeable-queue route**, not the RGA_TF
55-file chain. The queue's `JoinLemma3At` hook requires canonical states to
be *unique per event set* (`Shesha_Join_Refuted` shows the hook is false
without it; the queue was immune because its canonical states are unique).
The embedded-chain RGA has exactly that property — coordinates are birth
constants and the display is their sort, so the state is a function of the
event set (design doc Thm 4; `q_fold_canon`'s analogue) — which is why this
instance exists at all.

The framework needs `DecidableEq State`, so the instance state is the
**canonical sorted association list** — the document itself, records
`(id, element, coordinate)` strictly descending by key — rather than the
function-based map of `Sal/MRDTs/RGA_Embed/RGA_Embed_MRDT.lean`. The two
present the same datatype; the kernel theorems (commutation, stability,
chain-lex) live on the map model, and the fold-canonicity theorem of this
file's later sections is what makes the list state canonical.

Sections mirror `MRDT_Instances/MergeableQueue/MergeableQueue.lean`:
§1 datatype (this file's content) · §2 event helpers + canonical list ·
§3 well-formed enumerations + fold = canon · §5 honest histories ·
§6 the Join (the merge is its own linearization witness) · §7 capstone via
`HonestReach` · §8 `applicable` discharges honesty. See `PLAN.md`.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode keyLt keyLe key unaryCode binaryCode)

/-! ## §1  The datatype -/

inductive EOp : Type where
  | ins (e : ℕ) (π : List Bool) (a : ℕ)   -- element, coordinate prefix, anchor
  | del (x : ℕ)
deriving DecidableEq

/-- A record: `(id, element, absolute coordinate)`. -/
abbrev ERec : Type := ℕ × ℕ × List Bool

/-- State: the document — records strictly descending by key. Canonical
single-list form (sortedness is the `Inv`-grade invariant, established by
fold-canonicity in §3, not baked into the type). -/
abbrev EState : Type := List ERec

def eIds (s : EState) : List ℕ := s.map Prod.fst

/-- The coordinate an insert writes — a function of the op alone (the carried
prefix + the delta codeword; design doc §3: the prefix is for the proof). -/
def eCoord (Γ : OrderedPrefixCode) (o : Op EOp) : List Bool :=
  match o.2.2 with
  | .ins _ π a => π ++ Γ.enc (o.1 - a)
  | .del _     => []

/-- Sorted insertion, descending by key: the newcomer goes before the first
record with a strictly smaller key. -/
def eInsert (r : ERec) : EState → EState
  | [] => [r]
  | x :: xs =>
      if keyLt (key x.2.2) (key r.2.2) then r :: x :: xs
      else x :: eInsert r xs

/-- Insert places the record at its sorted position (idempotent on a present
id); delete removes the record wherever it sits. Strictness about *which*
target lives in the honesty layer (§8), not in the effect. -/
def eUpdate (Γ : OrderedPrefixCode) (s : EState) (o : Op EOp) : EState :=
  match o.2.2 with
  | .ins e π a =>
      if o.1 ∈ eIds s then s
      else eInsert (o.1, e, π ++ Γ.enc (o.1 - a)) s
  | .del x => s.filter (fun r => decide (r.1 ≠ x))

/-- Merge of two sorted lists, descending by key (ties cannot occur between
distinct ids on chain-generated states — `coordOf_inj`). -/
def eMerge2 : EState → EState → EState
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
      if keyLt (key y.2.2) (key x.2.2) then x :: eMerge2 xs (y :: ys)
      else y :: eMerge2 (x :: xs) ys
termination_by xs ys => xs.length + ys.length

/-- Ternary merge: OR-set survival (values immutable, so each survivor's
record is read off whichever input holds it), re-canonicalized by the sorted
2-merge. Branch `a` contributes its survivors (shared with `b`, or new since
`l`); branch `b` contributes its own news not already contributed. -/
def eMergeL (l a b : EState) : EState :=
  eMerge2
    (a.filter (fun r => decide (r.1 ∈ eIds b ∨ r.1 ∉ eIds l)))
    (b.filter (fun r => decide (r.1 ∉ eIds l ∧ r.1 ∉ eIds a)))

/-- The embedded-chain RGA, parametric in the code (instantiate at
`binaryCode` for the entropy-optimal artifact, `unaryCode` for hand
computation). `Inv`/`applicable` are trivially true — as in the queue, the
honesty discipline lives in the configuration layer (§5/§8), not the
signature. -/
def E (Γ : OrderedPrefixCode) : ConditionedMRDTSig where
  State := EState
  dec_state := inferInstance
  init := []
  AppOp := EOp
  dec_op := inferInstance
  Query := Unit
  Value := List ℕ
  update := eUpdate Γ
  merge := fun a b => eMergeL [] a b
  query := fun s _ => s.map (fun r => r.2.1)
  rc := fun _ _ => RcRes.Either
  mergeL := eMergeL
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem E_core_update (Γ : OrderedPrefixCode) (s : EState) (o : Op EOp) :
    (E Γ).toCRDTSig.update s o = eUpdate Γ s o := rfl

theorem E_rc_either (Γ : OrderedPrefixCode) (o₁ o₂ : Op EOp) :
    (E Γ).toCRDTSig.rc o₁ o₂ = RcRes.Either := rfl

/-! ## §1½  First list algebra -/

theorem mem_eIds_eInsert {r : ERec} {t : ℕ} : ∀ {s : EState},
    t ∈ eIds (eInsert r s) ↔ t ∈ eIds s ∨ t = r.1
  | [] => by simp [eInsert, eIds]
  | x :: xs => by
      by_cases h : keyLt (key x.2.2) (key r.2.2) = true
      · simp only [eInsert, if_pos h, eIds, List.map_cons, List.mem_cons]
        tauto
      · simp only [eInsert, if_neg h, eIds, List.map_cons, List.mem_cons]
        have ih := @mem_eIds_eInsert r t xs
        simp only [eIds] at ih
        rw [ih]
        tauto

theorem mem_eIds_update_del {Γ : OrderedPrefixCode} {s : EState} {ts r x t : ℕ} :
    t ∈ eIds (eUpdate Γ s (ts, r, .del x)) ↔ t ∈ eIds s ∧ t ≠ x := by
  simp only [eUpdate, eIds, List.mem_map]
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
with the same members are EQUAL (`esorted_ext`). Everything the fold and the
merge produce stays sorted, so fold-canonicity (§3) reduces to a membership
characterization. -/

open Sal.EmbedRGA (keyLt_trans keyLt_asymm keyLt_total keyLt_irrefl)

/-- Strictly descending by key — the canonical form. -/
def ESorted (s : EState) : Prop :=
  s.Pairwise (fun r r' => keyLt (key r'.2.2) (key r.2.2) = true)

theorem mem_eInsert {r x : ERec} : ∀ {s : EState},
    x ∈ eInsert r s ↔ x ∈ s ∨ x = r
  | [] => by simp [eInsert]
  | y :: ys => by
      by_cases h : keyLt (key y.2.2) (key r.2.2) = true
      · simp only [eInsert, if_pos h, List.mem_cons]
        tauto
      · simp only [eInsert, if_neg h, List.mem_cons]
        rw [mem_eInsert (s := ys)]
        tauto

theorem eInsert_sorted {r : ERec} : ∀ {s : EState}, ESorted s →
    (∀ x ∈ s, key x.2.2 ≠ key r.2.2) → ESorted (eInsert r s)
  | [], _, _ => List.pairwise_singleton _ _
  | y :: ys, hs, hne => by
      rcases List.pairwise_cons.mp hs with ⟨hy, hys⟩
      by_cases h : keyLt (key y.2.2) (key r.2.2) = true
      · rw [show eInsert r (y :: ys) = r :: y :: ys from by
          simp [eInsert, h]]
        refine List.pairwise_cons.mpr ⟨?_, hs⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz'
        · exact h
        · exact keyLt_trans (hy z hz') h
      · rw [show eInsert r (y :: ys) = y :: eInsert r ys from by
          simp [eInsert, h]]
        refine List.pairwise_cons.mpr ⟨?_, ?_⟩
        · intro z hz
          rcases mem_eInsert.mp hz with hz' | rfl
          · exact hy z hz'
          · rcases keyLt_total (hne y List.mem_cons_self) with h' | h'
            · exact absurd h' (by simpa using h)
            · exact h'
        · exact eInsert_sorted hys
            (fun x hx => hne x (List.mem_cons_of_mem _ hx))

theorem eUpdate_sorted {Γ : OrderedPrefixCode} {s : EState} {o : Op EOp}
    (hs : ESorted s)
    (hne : ∀ x ∈ s, key x.2.2 ≠ key (eCoord Γ o)) :
    ESorted (eUpdate Γ s o) := by
  obtain ⟨ts, r, op⟩ := o
  cases op with
  | del x => exact List.Pairwise.filter _ hs
  | ins e π a =>
      simp only [eUpdate]
      by_cases hmem : ts ∈ eIds s
      · rw [if_pos hmem]; exact hs
      · rw [if_neg hmem]
        exact eInsert_sorted hs (by
          intro x hx
          have := hne x hx
          simpa [eCoord] using this)

/-- **Canonical-form extensionality**: strictly-sorted lists with the same
members are equal. This is why the sorted list is a canonical state: any two
routes to the same record set produce the identical list. -/
theorem esorted_ext : ∀ {s s' : EState}, ESorted s → ESorted s' →
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
      rw [esorted_ext hxs hys htails]

/-! ## §2½  The sorted 2-merge -/

theorem mem_eMerge2 {x : ERec} : ∀ (as bs : EState),
    x ∈ eMerge2 as bs ↔ x ∈ as ∨ x ∈ bs := by
  intro as bs
  induction as, bs using eMerge2.induct with
  | case1 ys => simp [eMerge2]
  | case2 xs => cases xs <;> simp [eMerge2]
  | case3 a as' b bs' h ih =>
      rw [show eMerge2 (a :: as') (b :: bs') = a :: eMerge2 as' (b :: bs')
        from by rw [eMerge2]; simp [h]]
      simp only [List.mem_cons, ih]
      tauto
  | case4 a as' b bs' h ih =>
      rw [show eMerge2 (a :: as') (b :: bs') = b :: eMerge2 (a :: as') bs'
        from by rw [eMerge2]; simp [h]]
      simp only [List.mem_cons, ih]
      tauto

theorem eMerge2_sorted : ∀ {as bs : EState}, ESorted as → ESorted bs →
    (∀ a ∈ as, ∀ b ∈ bs, key a.2.2 ≠ key b.2.2) →
    ESorted (eMerge2 as bs) := by
  intro as bs has hbs hne
  induction as, bs using eMerge2.induct with
  | case1 ys => simpa [eMerge2] using hbs
  | case2 xs => cases xs <;> simpa [eMerge2] using has
  | case3 a as' b bs' h ih =>
      rw [show eMerge2 (a :: as') (b :: bs') = a :: eMerge2 as' (b :: bs')
        from by rw [eMerge2]; simp [h]]
      rcases List.pairwise_cons.mp has with ⟨ha, has'⟩
      refine List.pairwise_cons.mpr ⟨?_, ih has' hbs
        (fun x hx => hne x (List.mem_cons_of_mem _ hx))⟩
      intro z hz
      rcases (mem_eMerge2 as' (b :: bs')).mp hz with hz' | hz'
      · exact ha z hz'
      · rcases List.mem_cons.mp hz' with rfl | hz''
        · exact h
        · rcases List.pairwise_cons.mp hbs with ⟨hb, -⟩
          exact keyLt_trans (hb z hz'') h
  | case4 a as' b bs' h ih =>
      rw [show eMerge2 (a :: as') (b :: bs') = b :: eMerge2 (a :: as') bs'
        from by rw [eMerge2]; simp [h]]
      rcases List.pairwise_cons.mp hbs with ⟨hb, hbs'⟩
      have hab : keyLt (key a.2.2) (key b.2.2) = true := by
        rcases keyLt_total (Ne.symm (hne a List.mem_cons_self b
          List.mem_cons_self)) with h' | h'
        · exact absurd h' (by simpa using h)
        · exact h'
      refine List.pairwise_cons.mpr ⟨?_, ih has hbs'
        (fun x hx y hy => hne x hx y (List.mem_cons_of_mem _ hy))⟩
      intro z hz
      rcases (mem_eMerge2 (a :: as') bs').mp hz with hz' | hz'
      · rcases List.mem_cons.mp hz' with rfl | hz''
        · exact hab
        · rcases List.pairwise_cons.mp has with ⟨ha, -⟩
          exact keyLt_trans (ha z hz'') hab
      · exact hb z hz'

/-- The merge of canonical inputs is canonical (sorted), given no key ties —
supplied on chain-generated states by unique decodability. -/
theorem eMergeL_sorted {l a b : EState}
    (ha : ESorted a) (hb : ESorted b)
    (hdisj : ∀ x ∈ a, ∀ y ∈ b, key x.2.2 = key y.2.2 → x = y) :
    ESorted (eMergeL l a b) := by
  apply eMerge2_sorted (List.Pairwise.filter _ ha) (List.Pairwise.filter _ hb)
  intro x hx y hy hkey
  have hxa := List.mem_of_mem_filter hx
  have hyb := List.mem_of_mem_filter hy
  have hxy : x = y := hdisj x hxa y hyb hkey
  subst hxy
  have h2 := List.of_mem_filter hy
  simp at h2
  exact h2.2 (List.mem_map.mpr ⟨x, hxa, rfl⟩)

/-! ## §3  Well-formed enumerations and fold-canonicity

`e_fold_canon`: any two well-formed enumerations of one event set fold to
the **same** state — the mechanized "state is a function of the event set"
(design doc Thm 4), by `esorted_ext` + a fold membership characterization.
No explicit canonical-list formula is needed. -/

def eFold (Γ : OrderedPrefixCode) (ρ : List (Op EOp)) : EState :=
  applySeq (E Γ).toCRDTSig (E Γ).init ρ

theorem eFold_snoc (Γ : OrderedPrefixCode) (ρ : List (Op EOp)) (e : Op EOp) :
    eFold Γ (ρ ++ [e]) = eUpdate Γ (eFold Γ ρ) e := by
  unfold eFold applySeq
  rw [List.foldl_append]
  rfl

def eIsIns (o : Op EOp) : Bool :=
  match o.2.2 with
  | .ins _ _ _ => true
  | .del _ => false

/-- The record an insert writes. -/
def eRecOf (Γ : OrderedPrefixCode) (o : Op EOp) : ERec :=
  (o.1, (match o.2.2 with | .ins e _ _ => e | .del _ => 0), eCoord Γ o)

def eInsIds (ρ : List (Op EOp)) : List ℕ :=
  (ρ.filter (fun o => eIsIns o)).map Prod.fst

def eDels (ρ : List (Op EOp)) : List ℕ :=
  ρ.filterMap (fun o => match o.2.2 with | .del x => some x | .ins _ _ _ => none)

theorem mem_eInsIds {ρ : List (Op EOp)} {t : ℕ} :
    t ∈ eInsIds ρ ↔ ∃ o ∈ ρ, eIsIns o = true ∧ o.1 = t := by
  simp only [eInsIds, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨o, ⟨hm, hi⟩, rfl⟩
    exact ⟨o, hm, hi, rfl⟩
  · rintro ⟨o, hm, hi, rfl⟩
    exact ⟨o, ⟨hm, hi⟩, rfl⟩

theorem mem_eDels {ρ : List (Op EOp)} {x : ℕ} :
    x ∈ eDels ρ ↔ ∃ o ∈ ρ, o.2.2 = EOp.del x := by
  simp only [eDels, List.mem_filterMap]
  constructor
  · rintro ⟨o, hm, hsome⟩
    refine ⟨o, hm, ?_⟩
    cases hop : o.2.2 with
    | ins e π a => rw [hop] at hsome; simp at hsome
    | del y => rw [hop] at hsome; simp at hsome; rw [hsome]
  · rintro ⟨o, hm, hdel⟩
    exact ⟨o, hm, by rw [hdel]⟩

theorem eInsIds_append (ρ σ : List (Op EOp)) :
    eInsIds (ρ ++ σ) = eInsIds ρ ++ eInsIds σ := by
  simp [eInsIds, List.filter_append]

theorem eDels_append (ρ σ : List (Op EOp)) :
    eDels (ρ ++ σ) = eDels ρ ++ eDels σ := by
  simp [eDels, List.filterMap_append]

/-- Well-formed enumerations: insert ids are unique, nothing is deleted
before its insert, and distinct inserts mint distinct keys (supplied on
honest histories by chain-generation + unique decodability — §5). -/
structure EWf (Γ : OrderedPrefixCode) (ρ : List (Op EOp)) : Prop where
  ins_nodup : (eInsIds ρ).Nodup
  del_late : ∀ σ o τ, ρ = σ ++ o :: τ → eIsIns o = true → o.1 ∉ eDels σ
  keys_inj : ∀ o₁ ∈ ρ, ∀ o₂ ∈ ρ, eIsIns o₁ = true → eIsIns o₂ = true →
      o₁.1 ≠ o₂.1 → key (eCoord Γ o₁) ≠ key (eCoord Γ o₂)

theorem EWf.prefix {Γ : OrderedPrefixCode} {ρ : List (Op EOp)} {e : Op EOp}
    (h : EWf Γ (ρ ++ [e])) : EWf Γ ρ where
  ins_nodup := by
    have := h.ins_nodup
    rw [eInsIds_append] at this
    exact this.of_append_left
  del_late := fun σ o τ heq hins => by
    refine h.del_late σ o (τ ++ [e]) ?_ hins
    rw [heq]
    simp
  keys_inj := fun o₁ h₁ o₂ h₂ => h.keys_inj o₁ (List.mem_append_left _ h₁)
    o₂ (List.mem_append_left _ h₂)

/-- Record provenance, unconditioned: everything in a fold was written by
some insert of the enumeration. -/
theorem e_fold_rec_sub (Γ : OrderedPrefixCode) : ∀ (ρ : List (Op EOp))
    (r : ERec), r ∈ eFold Γ ρ → ∃ o ∈ ρ, eIsIns o = true ∧ r = eRecOf Γ o := by
  intro ρ
  induction ρ using List.reverseRecOn with
  | nil =>
      intro r hr
      exact absurd hr (by simp [eFold, applySeq, E])
  | append_singleton ρ e ih =>
      intro r hr
      rw [eFold_snoc] at hr
      obtain ⟨ts, rr, op⟩ := e
      cases op with
      | ins el π a =>
          simp only [eUpdate] at hr
          by_cases hmem : ts ∈ eIds (eFold Γ ρ)
          · rw [if_pos hmem] at hr
            obtain ⟨o, hm, hi, hrec⟩ := ih r hr
            exact ⟨o, List.mem_append_left _ hm, hi, hrec⟩
          · rw [if_neg hmem] at hr
            rcases mem_eInsert.mp hr with hr' | rfl
            · obtain ⟨o, hm, hi, hrec⟩ := ih r hr'
              exact ⟨o, List.mem_append_left _ hm, hi, hrec⟩
            · exact ⟨(ts, rr, .ins el π a),
                List.mem_append_right _ (by simp),
                by simp [eIsIns], by simp [eRecOf, eCoord]⟩
      | del x =>
          simp only [eUpdate] at hr
          obtain ⟨o, hm, hi, hrec⟩ := ih r (List.mem_of_mem_filter hr)
          exact ⟨o, List.mem_append_left _ hm, hi, hrec⟩

/-- Under well-formedness the insert guard never fires: a fresh insert's id
is not in the fold of its past. -/
theorem e_fold_guard_free {Γ : OrderedPrefixCode} {ρ : List (Op EOp)}
    {e : Op EOp} (hwf : EWf Γ (ρ ++ [e])) (hins : eIsIns e = true) :
    e.1 ∉ eIds (eFold Γ ρ) := by
  intro hmem
  obtain ⟨r, hr, hr1⟩ := List.mem_map.mp hmem
  obtain ⟨o, hm, hi, hrec⟩ := e_fold_rec_sub Γ ρ r hr
  have ho1 : o.1 = e.1 := by rw [hrec] at hr1; exact hr1
  have h1 : e.1 ∈ eInsIds ρ := mem_eInsIds.mpr ⟨o, hm, hi, ho1⟩
  have := hwf.ins_nodup
  rw [eInsIds_append] at this
  rcases List.nodup_append.mp this with ⟨-, -, hdisj⟩
  have h2 : e.1 ∈ eInsIds [e] := by
    simp [eInsIds, hins]
  exact (hdisj e.1 h1 e.1 h2) rfl

/-- Folds of well-formed enumerations are canonical (sorted). -/
theorem e_fold_sorted (Γ : OrderedPrefixCode) : ∀ {ρ : List (Op EOp)},
    EWf Γ ρ → ESorted (eFold Γ ρ) := by
  intro ρ
  induction ρ using List.reverseRecOn with
  | nil =>
      intro _
      rw [show eFold Γ [] = [] from rfl]
      exact List.Pairwise.nil
  | append_singleton ρ e ih =>
      intro hwf
      have hsorted := ih hwf.prefix
      rw [eFold_snoc]
      obtain ⟨ts, rr, op⟩ := e
      cases op with
      | del x => exact List.Pairwise.filter _ hsorted
      | ins el π a =>
          simp only [eUpdate]
          by_cases hmem : ts ∈ eIds (eFold Γ ρ)
          · rw [if_pos hmem]; exact hsorted
          · rw [if_neg hmem]
            apply eInsert_sorted hsorted
            intro x hx
            obtain ⟨o, hm, hi, hrec⟩ := e_fold_rec_sub Γ ρ x hx
            have hx1 : x.1 = o.1 := by rw [hrec]; rfl
            have hne : o.1 ≠ ts := by
              intro heq
              exact hmem (List.mem_map.mpr ⟨x, hx, by rw [hx1, heq]⟩)
            have hkey := hwf.keys_inj o (List.mem_append_left _ hm)
              (ts, rr, .ins el π a) (List.mem_append_right _ (by simp))
              hi (by simp [eIsIns]) hne
            rw [hrec]
            show key (eCoord Γ o) ≠ key (π ++ Γ.enc (ts - a))
            simpa [eCoord] using hkey

/-- **The fold membership characterization**: under well-formedness a record
is in the fold iff its insert is in the enumeration and its id is never
deleted — an ORDER-FREE description. -/
theorem e_fold_mem (Γ : OrderedPrefixCode) : ∀ {ρ : List (Op EOp)},
    EWf Γ ρ → ∀ (r : ERec),
    (r ∈ eFold Γ ρ ↔
      (∃ o ∈ ρ, eIsIns o = true ∧ r = eRecOf Γ o) ∧ r.1 ∉ eDels ρ) := by
  intro ρ
  induction ρ using List.reverseRecOn with
  | nil =>
      intro _ r
      simp [show eFold Γ [] = [] from rfl]
  | append_singleton ρ e ih =>
      intro hwf r
      have IH := ih hwf.prefix
      rw [eFold_snoc]
      obtain ⟨ts, rr, op⟩ := e
      cases op with
      | ins el π a =>
          simp only [eUpdate]
          rw [if_neg (e_fold_guard_free hwf (by simp [eIsIns]))]
          have hdels : eDels (ρ ++ [(ts, rr, EOp.ins el π a)]) = eDels ρ := by
            rw [eDels_append]
            simp [eDels]
          rw [hdels, mem_eInsert]
          constructor
          · rintro (hr | rfl)
            · obtain ⟨⟨o, hm, hi, hrec⟩, hnd⟩ := (IH r).mp hr
              exact ⟨⟨o, List.mem_append_left _ hm, hi, hrec⟩, hnd⟩
            · refine ⟨⟨(ts, rr, .ins el π a),
                List.mem_append_right _ (by simp),
                by simp [eIsIns], by simp [eRecOf, eCoord]⟩, ?_⟩
              show ts ∉ eDels ρ
              exact hwf.del_late ρ (ts, rr, .ins el π a) [] rfl
                (by simp [eIsIns])
          · rintro ⟨⟨o, hm, hi, hrec⟩, hnd⟩
            rcases List.mem_append.mp hm with hm' | hm'
            · exact Or.inl ((IH r).mpr ⟨⟨o, hm', hi, hrec⟩, hnd⟩)
            · right
              have : o = (ts, rr, .ins el π a) := List.mem_singleton.mp hm'
              rw [hrec, this]
              simp [eRecOf, eCoord]
      | del x =>
          simp only [eUpdate]
          have hdels : eDels (ρ ++ [(ts, rr, EOp.del x)])
              = eDels ρ ++ [x] := by
            rw [eDels_append]
            simp [eDels]
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
                simp [eIsIns] at hi
            refine List.mem_filter.mpr
              ⟨(IH r).mpr ⟨⟨o, hm', hi, hrec⟩, hnd.1⟩, by
                simpa using hnd.2⟩

/-- **Fold-canonicity** (design doc Thm 4, mechanized): well-formed
enumerations of one event set fold to the SAME state. The state is a
function of the event set — the property `Shesha_Join_Refuted` shows the
join hook cannot live without, and the reason this instance exists. -/
theorem e_fold_canon (Γ : OrderedPrefixCode) {ρ ρ' : List (Op EOp)}
    (hwf : EWf Γ ρ) (hwf' : EWf Γ ρ')
    (hmem : ∀ o, o ∈ ρ ↔ o ∈ ρ') :
    eFold Γ ρ = eFold Γ ρ' := by
  apply esorted_ext (e_fold_sorted Γ hwf) (e_fold_sorted Γ hwf')
  intro r
  rw [e_fold_mem Γ hwf r, e_fold_mem Γ hwf' r]
  constructor
  · rintro ⟨⟨o, hm, hi, hrec⟩, hnd⟩
    refine ⟨⟨o, (hmem o).mp hm, hi, hrec⟩, fun hx => hnd ?_⟩
    obtain ⟨o', hm', hdel⟩ := mem_eDels.mp hx
    exact mem_eDels.mpr ⟨o', (hmem o').mpr hm', hdel⟩
  · rintro ⟨⟨o, hm, hi, hrec⟩, hnd⟩
    refine ⟨⟨o, (hmem o).mpr hm, hi, hrec⟩, fun hx => hnd ?_⟩
    obtain ⟨o', hm', hdel⟩ := mem_eDels.mp hx
    exact mem_eDels.mpr ⟨o', (hmem o').mp hm', hdel⟩

/-! ## §5  Honest histories, well-formedness of enumerations

`EHonestCore` is the embed analogue of the queue's honesty: every delete
names an id its issuer had observed (a `vis`-prior insert), and inserts are
chain-generated (the mint is a positive birth chain's coordinate whose
deltas telescope to the id — what an honest replica's `accurate` generation
produces, §8). Its three consequences are exactly `EWf`'s three fields. -/

open Sal.EmbedRGA (PosChain coordOf coordOf_inj key_inj)

/-- The one non-commuting shape: an insert and the delete of its id.
Witnessed at the empty state. -/
theorem e_ins_del_not_comm (Γ : OrderedPrefixCode) (ts r el : ℕ)
    (π : List Bool) (a : ℕ) (ts' r' : ℕ) :
    ¬ (E Γ).toCRDTSig.commutes (ts, r, EOp.ins el π a) (ts', r', EOp.del ts) := by
  intro h
  have h0 := h []
  rw [E_core_update, E_core_update, E_core_update, E_core_update] at h0
  simp only [eUpdate, eIds, eInsert, List.map_nil, List.not_mem_nil,
    if_false, List.filter_nil] at h0
  simp at h0

/-- Honest histories. -/
structure EHonestCore (Γ : OrderedPrefixCode)
    (C : Sal.Emulation.Configuration (E Γ).toCRDTSig) : Prop where
  /-- Every delete's target was inserted `vis`-before it. -/
  del_has_ins : ∀ e ∈ C.events, ∀ x : ℕ, e.2.2 = EOp.del x →
    ∃ a ∈ C.events, C.vis a e ∧ a.1 = x ∧ eIsIns a = true
  /-- Inserts are chain-generated: each mint is the coordinate of a positive
  birth chain whose deltas telescope to the id (so chains are injective on
  ids for free). -/
  chain_gen : ∃ chainOf : ℕ → List ℕ,
    ∀ o ∈ C.events, eIsIns o = true →
      PosChain (chainOf o.1) ∧
      eCoord Γ o = coordOf Γ (chainOf o.1) ∧
      (chainOf o.1).sum = o.1

/-- Honesty + backward closure: a delete's insert lies in the same closed
event set, `vis`-before it. -/
theorem e_del_ins_mem {Γ : OrderedPrefixCode}
    {C : Sal.Emulation.Configuration (E Γ).toCRDTSig}
    (hHon : EHonestCore Γ C) {ev : Set (Op EOp)}
    (hin : ∀ a ∈ ev, a ∈ C.events)
    (hcl : ∀ a b, C.vis a b → ¬ (E Γ).toCRDTSig.commutes a b → b ∈ ev → a ∈ ev) :
    ∀ d ∈ ev, ∀ x : ℕ, d.2.2 = EOp.del x →
      ∃ a ∈ ev, eIsIns a = true ∧ a.1 = x ∧ C.vis a d := by
  intro d hd x hdel
  obtain ⟨a, haev, hvis, hax, hains⟩ := hHon.del_has_ins d (hin d hd) x hdel
  have hncomm : ¬ (E Γ).toCRDTSig.commutes a d := by
    obtain ⟨a1, a2, aop⟩ := a
    obtain ⟨d1, d2, dop⟩ := d
    simp only at hdel hax
    subst hdel
    cases aop with
    | del y => simp [eIsIns] at hains
    | ins el π anc =>
        subst hax
        exact e_ins_del_not_comm Γ a1 a2 el π anc d1 d2
  exact ⟨a, hcl a d hvis hncomm hd, hains, hax, hvis⟩

/-- **A `loOn`-respecting enumeration of a closed honest set is
well-formed** — the bridge from the configuration layer to `EWf`, one
honesty ingredient per field: timestamp uniqueness gives `ins_nodup`,
delete-after-insert visibility gives `del_late`, chain generation +
unique decodability give `keys_inj`. -/
theorem e_wf_of_enum {Γ : OrderedPrefixCode}
    {C : Sal.Emulation.Configuration (E Γ).toCRDTSig}
    (hHon : EHonestCore Γ C) {ev : Set (Op EOp)} {ρ : List (Op EOp)}
    (hin : ∀ a ∈ ev, a ∈ C.events)
    (hcl : ∀ a b, C.vis a b → ¬ (E Γ).toCRDTSig.commutes a b → b ∈ ev → a ∈ ev)
    (hperm : listPermOf ρ ev)
    (hresp : respects ρ (loOn C ev)) : EWf Γ ρ where
  ins_nodup := by
    apply List.Nodup.map_on ?_ (hperm.1.filter _)
    intro o₁ h₁ o₂ h₂ hfst
    exact C.ts_unique
      (hin _ ((hperm.2 _).mp (List.mem_of_mem_filter h₁)))
      (hin _ ((hperm.2 _).mp (List.mem_of_mem_filter h₂))) hfst
  del_late := by
    intro σ o τ heq hins hdel
    obtain ⟨d, hdσ, hddel⟩ := mem_eDels.mp hdel
    have hdρ : d ∈ ρ := by
      rw [heq]; exact List.mem_append_left _ hdσ
    have hoρ : o ∈ ρ := by
      rw [heq]; exact List.mem_append_right _ List.mem_cons_self
    obtain ⟨a, haev, hains, hax, hvis⟩ :=
      e_del_ins_mem hHon hin hcl d ((hperm.2 d).mp hdρ) o.1 hddel
    have hao : a = o :=
      C.ts_unique (hin a haev) (hin o ((hperm.2 o).mp hoρ)) hax
    subst hao
    unfold respects at hresp
    rw [heq] at hresp
    have hcross := (List.pairwise_append.mp hresp).2.2 d hdσ a
      List.mem_cons_self
    apply hcross
    rw [loOn_iff_of_rc_either (E_rc_either Γ)]
    refine ⟨hvis, ?_⟩
    obtain ⟨a1, a2, aop⟩ := a
    obtain ⟨d1, d2, dop⟩ := d
    simp only at hddel
    subst hddel
    cases aop with
    | del y => simp [eIsIns] at hins
    | ins el π anc =>
        exact e_ins_del_not_comm Γ a1 a2 el π anc d1 d2
  keys_inj := by
    obtain ⟨chainOf, hch⟩ := hHon.chain_gen
    intro o₁ h₁ o₂ h₂ hi₁ hi₂ hne hkey
    obtain ⟨hp₁, hc₁, hs₁⟩ := hch o₁ (hin _ ((hperm.2 _).mp h₁)) hi₁
    obtain ⟨hp₂, hc₂, hs₂⟩ := hch o₂ (hin _ ((hperm.2 _).mp h₂)) hi₂
    apply hne
    have hc : coordOf Γ (chainOf o₁.1) = coordOf Γ (chainOf o₂.1) := by
      rw [← hc₁, ← hc₂]
      exact key_inj hkey
    have hchain := coordOf_inj Γ hp₁ hp₂ hc
    calc o₁.1 = (chainOf o₁.1).sum := hs₁.symm
      _ = (chainOf o₂.1).sum := by rw [hchain]
      _ = o₂.1 := hs₂

end Sal.ConditionedMRDTs
