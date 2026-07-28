import Sal.ConditionedMRDTs.Metatheory.HonestReach
import Sal.ConditionedMRDTs.Metatheory.GenHonest
import Sal.MRDTs.RGA_Embed.RGA_Embed_ChainLex
import Sal.MRDTs.RGA_Embed.Embed_Code_Binary

/-!
# The embedded-chain RGA as a conditioned MRDT instance: §1, the datatype

This instance is built as a **mergeable queue**, not via the RGA_TF 55-file
chain. The queue's `JoinLemma3At` hook requires canonical states to be
*unique per event set* (`Shesha_Join_Refuted` shows the hook is false
without it; the queue was immune because its canonical states are unique).
The embedded-chain RGA has exactly that property, coordinates are birth
constants and the display is their sort, so the state is a function of the
event set (`sal-mrdts.tex` Thm 4; `q_fold_canon`'s analogue), which is why
this instance exists at all.

The framework needs `DecidableEq State`, so the instance state is the
**canonical sorted association list**, the document itself, records
`(id, element, coordinate)` strictly descending by key, rather than the
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

set_option linter.unusedSectionVars false

/-! ## §1  The datatype

The element payload is a parameter `α` (default `ℕ`, so every existing
consumer reads unchanged): the datatype carries elements blindly, exactly
like the rehoming model's `concrete_st (α := ℕ)`. `Inhabited α` supplies
the don't-care element of a delete's `eRecOf` (never read: provenance is
insert-only). The fused Peritext instantiates at `α := PeritextElt`. -/

inductive EOp (α : Type := ℕ) : Type where
  | ins (e : α) (π : List Bool) (a : ℕ)   -- element, coordinate prefix, anchor
  | del (x : ℕ)
deriving DecidableEq

/-- A record: `(id, element, absolute coordinate)`. -/
abbrev ERec (α : Type := ℕ) : Type := ℕ × α × List Bool

/-- State: the document, records strictly descending by key. Canonical
single-list form (sortedness is the `Inv`-grade invariant, established by
fold-canonicity in §3, not baked into the type). -/
abbrev EState (α : Type := ℕ) : Type := List (ERec α)

variable {α : Type} [DecidableEq α] [Inhabited α]

def eIds (s : EState α) : List ℕ := s.map Prod.fst

/-- The coordinate an insert writes, a function of the op alone (the carried
prefix + the delta codeword; `sal-mrdts.tex` §3: the prefix is for the proof). -/
def eCoord (Γ : OrderedPrefixCode) (o : Op (EOp α)) : List Bool :=
  match o.2.2 with
  | .ins _ π a => π ++ Γ.enc (o.1 - a)
  | .del _     => []

/-- Sorted insertion, descending by key: the newcomer goes before the first
record with a strictly smaller key. -/
def eInsert (r : ERec α) : EState α → EState α
  | [] => [r]
  | x :: xs =>
      if keyLt (key x.2.2) (key r.2.2) then r :: x :: xs
      else x :: eInsert r xs

/-- Insert places the record at its sorted position (idempotent on a present
id); delete removes the record wherever it sits. Strictness about *which*
target lives in the honesty layer (§8), not in the effect. -/
def eUpdate (Γ : OrderedPrefixCode) (s : EState α) (o : Op (EOp α)) : EState α :=
  match o.2.2 with
  | .ins e π a =>
      if o.1 ∈ eIds s then s
      else eInsert (o.1, e, π ++ Γ.enc (o.1 - a)) s
  | .del x => s.filter (fun r => decide (r.1 ≠ x))

/-- Merge of two sorted lists, descending by key (ties cannot occur between
distinct ids on chain-generated states, `coordOf_inj`). -/
def eMerge2 : EState α → EState α → EState α
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
def eMergeL (l a b : EState α) : EState α :=
  eMerge2
    (a.filter (fun r => decide (r.1 ∈ eIds b ∨ r.1 ∉ eIds l)))
    (b.filter (fun r => decide (r.1 ∉ eIds l ∧ r.1 ∉ eIds a)))

/-- The embedded-chain RGA, parametric in the code (instantiate at
`binaryCode` for the entropy-optimal artifact, `unaryCode` for hand
computation). `Inv`/`applicable` are trivially true, as in the queue, the
honesty discipline lives in the configuration layer (§5/§8), not the
signature. -/
def E (Γ : OrderedPrefixCode) (α : Type := ℕ)
    [DecidableEq α] [Inhabited α] : ConditionedMRDTSig where
  State := EState α
  dec_state := inferInstance
  init := []
  AppOp := EOp α
  dec_op := inferInstance
  Query := Unit
  Value := List α
  update := eUpdate Γ
  merge := fun a b => eMergeL [] a b
  query := fun s _ => s.map (fun r => r.2.1)
  rc := fun _ _ => RcRes.Either
  mergeL := eMergeL
  merge_init_slice := fun _ _ => rfl
  Inv := fun _ => True
  applicable := fun _ _ => True

theorem E_core_update (Γ : OrderedPrefixCode) (s : EState α) (o : Op (EOp α)) :
    (E Γ α).toCRDTSig.update s o = eUpdate Γ s o := rfl

theorem E_rc_either (Γ : OrderedPrefixCode) (o₁ o₂ : Op (EOp α)) :
    (E Γ α).toCRDTSig.rc o₁ o₂ = RcRes.Either := rfl

/-! ## §1½  First list algebra -/

theorem mem_eIds_eInsert {r : ERec α} {t : ℕ} : ∀ {s : EState α},
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

theorem mem_eIds_update_del {Γ : OrderedPrefixCode} {s : EState α} {ts r x t : ℕ} :
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

/-- Strictly descending by key, the canonical form. -/
def ESorted (s : EState α) : Prop :=
  s.Pairwise (fun r r' => keyLt (key r'.2.2) (key r.2.2) = true)

theorem mem_eInsert {r x : ERec α} : ∀ {s : EState α},
    x ∈ eInsert r s ↔ x ∈ s ∨ x = r
  | [] => by simp [eInsert]
  | y :: ys => by
      by_cases h : keyLt (key y.2.2) (key r.2.2) = true
      · simp only [eInsert, if_pos h, List.mem_cons]
        tauto
      · simp only [eInsert, if_neg h, List.mem_cons]
        rw [mem_eInsert (s := ys)]
        tauto

theorem eInsert_sorted {r : ERec α} : ∀ {s : EState α}, ESorted s →
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

theorem eUpdate_sorted {Γ : OrderedPrefixCode} {s : EState α} {o : Op (EOp α)}
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
theorem esorted_ext : ∀ {s s' : EState α}, ESorted s → ESorted s' →
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

theorem mem_eMerge2 {x : ERec α} : ∀ (as bs : EState α),
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

theorem eMerge2_sorted : ∀ {as bs : EState α}, ESorted as → ESorted bs →
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

/-- The merge of canonical inputs is canonical (sorted), given no key ties,
supplied on chain-generated states by unique decodability. -/
theorem eMergeL_sorted {l a b : EState α}
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
the **same** state, the mechanized "state is a function of the event set"
(`sal-mrdts.tex` Thm 4), by `esorted_ext` + a fold membership
characterization. No explicit canonical-list formula is needed. -/

def eFold (Γ : OrderedPrefixCode) (ρ : List (Op (EOp α))) : EState α :=
  applySeq (E Γ α).toCRDTSig (E Γ α).init ρ

theorem eFold_snoc (Γ : OrderedPrefixCode) (ρ : List (Op (EOp α))) (e : Op (EOp α)) :
    eFold Γ (ρ ++ [e]) = eUpdate Γ (eFold Γ ρ) e := by
  unfold eFold applySeq
  rw [List.foldl_append]
  rfl

def eIsIns (o : Op (EOp α)) : Bool :=
  match o.2.2 with
  | .ins _ _ _ => true
  | .del _ => false

/-- The record an insert writes. -/
def eRecOf (Γ : OrderedPrefixCode) (o : Op (EOp α)) : ERec α :=
  (o.1, (match o.2.2 with | .ins e _ _ => e | .del _ => default), eCoord Γ o)

def eInsIds (ρ : List (Op (EOp α))) : List ℕ :=
  (ρ.filter (fun o => eIsIns o)).map Prod.fst

def eDels (ρ : List (Op (EOp α))) : List ℕ :=
  ρ.filterMap (fun o => match o.2.2 with | .del x => some x | .ins _ _ _ => none)

theorem mem_eInsIds {ρ : List (Op (EOp α))} {t : ℕ} :
    t ∈ eInsIds ρ ↔ ∃ o ∈ ρ, eIsIns o = true ∧ o.1 = t := by
  simp only [eInsIds, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨o, ⟨hm, hi⟩, rfl⟩
    exact ⟨o, hm, hi, rfl⟩
  · rintro ⟨o, hm, hi, rfl⟩
    exact ⟨o, ⟨hm, hi⟩, rfl⟩

theorem mem_eDels {ρ : List (Op (EOp α))} {x : ℕ} :
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

theorem eInsIds_append (ρ σ : List (Op (EOp α))) :
    eInsIds (ρ ++ σ) = eInsIds ρ ++ eInsIds σ := by
  simp [eInsIds, List.filter_append]

theorem eDels_append (ρ σ : List (Op (EOp α))) :
    eDels (ρ ++ σ) = eDels ρ ++ eDels σ := by
  simp [eDels, List.filterMap_append]

/-- Well-formed enumerations: insert ids are unique, nothing is deleted
before its insert, and distinct inserts mint distinct keys (supplied on
honest histories by chain-generation + unique decodability, §5). -/
structure EWf (Γ : OrderedPrefixCode) (ρ : List (Op (EOp α))) : Prop where
  ins_nodup : (eInsIds ρ).Nodup
  del_late : ∀ σ o τ, ρ = σ ++ o :: τ → eIsIns o = true → o.1 ∉ eDels σ
  keys_inj : ∀ o₁ ∈ ρ, ∀ o₂ ∈ ρ, eIsIns o₁ = true → eIsIns o₂ = true →
      o₁.1 ≠ o₂.1 → key (eCoord Γ o₁) ≠ key (eCoord Γ o₂)

theorem EWf.prefix {Γ : OrderedPrefixCode} {ρ : List (Op (EOp α))} {e : Op (EOp α)}
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
theorem e_fold_rec_sub (Γ : OrderedPrefixCode) : ∀ (ρ : List (Op (EOp α)))
    (r : ERec α), r ∈ eFold Γ ρ → ∃ o ∈ ρ, eIsIns o = true ∧ r = eRecOf Γ o := by
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
theorem e_fold_guard_free {Γ : OrderedPrefixCode} {ρ : List (Op (EOp α))}
    {e : Op (EOp α)} (hwf : EWf Γ (ρ ++ [e])) (hins : eIsIns e = true) :
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
theorem e_fold_sorted (Γ : OrderedPrefixCode) : ∀ {ρ : List (Op (EOp α))},
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
deleted, an ORDER-FREE description. -/
theorem e_fold_mem (Γ : OrderedPrefixCode) : ∀ {ρ : List (Op (EOp α))},
    EWf Γ ρ → ∀ (r : ERec α),
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

/-- **Fold-canonicity** (`sal-mrdts.tex` Thm 4, mechanized): well-formed
enumerations of one event set fold to the SAME state. The state is a
function of the event set, the property `Shesha_Join_Refuted` shows the
join hook cannot live without, and the reason this instance exists. -/
theorem e_fold_canon (Γ : OrderedPrefixCode) {ρ ρ' : List (Op (EOp α))}
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
deltas telescope to the id, what an honest replica's `accurate` generation
produces, §8). Its three consequences are exactly `EWf`'s three fields. -/

open Sal.EmbedRGA (PosChain coordOf coordOf_inj coordOf_append key_inj)

/-- The one non-commuting shape: an insert and the delete of its id.
Witnessed at the empty state. -/
theorem e_ins_del_not_comm (Γ : OrderedPrefixCode) (ts r : ℕ) (el : α)
    (π : List Bool) (a : ℕ) (ts' r' : ℕ) :
    ¬ (E Γ α).toCRDTSig.commutes (ts, r, EOp.ins el π a) (ts', r', EOp.del ts) := by
  intro h
  have h0 := h []
  rw [E_core_update, E_core_update, E_core_update, E_core_update] at h0
  simp only [eUpdate, eIds, eInsert, List.map_nil, List.not_mem_nil,
    if_false, List.filter_nil] at h0
  simp at h0

/-- Honest histories. -/
structure EHonestCore (Γ : OrderedPrefixCode)
    (C : Sal.Emulation.Configuration (E Γ α).toCRDTSig) : Prop where
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
    {C : Sal.Emulation.Configuration (E Γ α).toCRDTSig}
    (hHon : EHonestCore Γ C) {ev : Set (Op (EOp α))}
    (hin : ∀ a ∈ ev, a ∈ C.events)
    (hcl : ∀ a b, C.vis a b → ¬ (E Γ α).toCRDTSig.commutes a b → b ∈ ev → a ∈ ev) :
    ∀ d ∈ ev, ∀ x : ℕ, d.2.2 = EOp.del x →
      ∃ a ∈ ev, eIsIns a = true ∧ a.1 = x ∧ C.vis a d := by
  intro d hd x hdel
  obtain ⟨a, haev, hvis, hax, hains⟩ := hHon.del_has_ins d (hin d hd) x hdel
  have hncomm : ¬ (E Γ α).toCRDTSig.commutes a d := by
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
well-formed**, the bridge from the configuration layer to `EWf`, one
honesty ingredient per field: timestamp uniqueness gives `ins_nodup`,
delete-after-insert visibility gives `del_late`, chain generation +
unique decodability give `keys_inj`. -/
theorem e_wf_of_enum {Γ : OrderedPrefixCode}
    {C : Sal.Emulation.Configuration (E Γ α).toCRDTSig}
    (hHon : EHonestCore Γ C) {ev : Set (Op (EOp α))} {ρ : List (Op (EOp α))}
    (hin : ∀ a ∈ ev, a ∈ C.events)
    (hcl : ∀ a b, C.vis a b → ¬ (E Γ α).toCRDTSig.commutes a b → b ∈ ev → a ∈ ev)
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

/-! ## §6a  The survival algebra

The record-level membership of the ternary merge, characterized order-free
against the union event set, the mathematical core of the Join. §6b turns
it into `JoinLemma3At` by exhibiting the witness enumeration. -/

theorem e_fold_id_mem (Γ : OrderedPrefixCode) {ρ : List (Op (EOp α))}
    (hwf : EWf Γ ρ) (t : ℕ) :
    t ∈ eIds (eFold Γ ρ) ↔
      (∃ o ∈ ρ, eIsIns o = true ∧ o.1 = t) ∧ t ∉ eDels ρ := by
  constructor
  · intro h
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
    obtain ⟨⟨o, hm, hi, hrec⟩, hnd⟩ := (e_fold_mem Γ hwf r).mp hr
    exact ⟨⟨o, hm, hi, by rw [hrec]; rfl⟩, hnd⟩
  · rintro ⟨⟨o, hm, hi, rfl⟩, hnd⟩
    have hr : eRecOf Γ o ∈ eFold Γ ρ :=
      (e_fold_mem Γ hwf _).mpr ⟨⟨o, hm, hi, rfl⟩, hnd⟩
    exact List.mem_map.mpr ⟨eRecOf Γ o, hr, rfl⟩

/-- Distinct honest inserts mint distinct keys (the standalone form of
`e_wf_of_enum`'s third discharge, for use at the merge site). -/
theorem e_keys_inj_events {Γ : OrderedPrefixCode}
    {C : Sal.Emulation.Configuration (E Γ α).toCRDTSig}
    (hHon : EHonestCore Γ C) :
    ∀ o₁ ∈ C.events, ∀ o₂ ∈ C.events, eIsIns o₁ = true → eIsIns o₂ = true →
      o₁.1 ≠ o₂.1 → key (eCoord Γ o₁) ≠ key (eCoord Γ o₂) := by
  obtain ⟨chainOf, hch⟩ := hHon.chain_gen
  intro o₁ h₁ o₂ h₂ hi₁ hi₂ hne hkey
  obtain ⟨hp₁, hc₁, hs₁⟩ := hch o₁ h₁ hi₁
  obtain ⟨hp₂, hc₂, hs₂⟩ := hch o₂ h₂ hi₂
  apply hne
  have hc : coordOf Γ (chainOf o₁.1) = coordOf Γ (chainOf o₂.1) := by
    rw [← hc₁, ← hc₂]
    exact key_inj hkey
  have hchain := coordOf_inj Γ hp₁ hp₂ hc
  calc o₁.1 = (chainOf o₁.1).sum := hs₁.symm
    _ = (chainOf o₂.1).sum := by rw [hchain]
    _ = o₂.1 := hs₂

/-- **The merge membership characterization.** At a join site (three
canonical enumerations over an honest configuration), a record is in the
ternary merge iff its insert is somewhere in the union and its id is deleted
nowhere in the union, the union's order-free membership. OR-set survival,
with honesty closing the one subtle corner (a branch-2 delete of a
branch-1 survivor forces the insert into the LCA). -/
theorem e_mergeL_mem {Γ : OrderedPrefixCode}
    {C : Sal.Emulation.Configuration (E Γ α).toCRDTSig}
    (hHon : EHonestCore Γ C) {ev₁ ev₂ : Set (Op (EOp α))}
    {ρ₀ ρ₁ ρ₂ : List (Op (EOp α))}
    (hin₁ : ∀ a ∈ ev₁, a ∈ C.events) (hin₂ : ∀ a ∈ ev₂, a ∈ C.events)
    (hcl₁ : ∀ a b, C.vis a b → ¬ (E Γ α).toCRDTSig.commutes a b → b ∈ ev₁ → a ∈ ev₁)
    (hcl₂ : ∀ a b, C.vis a b → ¬ (E Γ α).toCRDTSig.commutes a b → b ∈ ev₂ → a ∈ ev₂)
    (hp₀ : listPermOf ρ₀ (ev₁ ∩ ev₂)) (hp₁ : listPermOf ρ₁ ev₁)
    (hp₂ : listPermOf ρ₂ ev₂)
    (hwf₀ : EWf Γ ρ₀) (hwf₁ : EWf Γ ρ₁) (hwf₂ : EWf Γ ρ₂) (r : ERec α) :
    r ∈ eMergeL (eFold Γ ρ₀) (eFold Γ ρ₁) (eFold Γ ρ₂) ↔
      (∃ o, (o ∈ ev₁ ∨ o ∈ ev₂) ∧ eIsIns o = true ∧ r = eRecOf Γ o) ∧
      (∀ d, (d ∈ ev₁ ∨ d ∈ ev₂) → d.2.2 ≠ EOp.del r.1) := by
  classical
  set s₀ := eFold Γ ρ₀
  set s₁ := eFold Γ ρ₁
  set s₂ := eFold Γ ρ₂
  have hdels : ∀ {ρ : List (Op (EOp α))} {ev : Set (Op (EOp α))}, listPermOf ρ ev →
      ∀ {t : ℕ}, t ∈ eDels ρ ↔ ∃ d ∈ ev, d.2.2 = EOp.del t := by
    intro ρ ev hp t
    rw [mem_eDels]
    constructor
    · rintro ⟨d, hm, hdel⟩
      exact ⟨d, (hp.2 d).mp hm, hdel⟩
    · rintro ⟨d, hm, hdel⟩
      exact ⟨d, (hp.2 d).mpr hm, hdel⟩
  rw [show eMergeL s₀ s₁ s₂ = eMerge2
    (s₁.filter (fun x => decide (x.1 ∈ eIds s₂ ∨ x.1 ∉ eIds s₀)))
    (s₂.filter (fun x => decide (x.1 ∉ eIds s₀ ∧ x.1 ∉ eIds s₁))) from rfl,
    mem_eMerge2]
  constructor
  · rintro (hr | hr)
    · -- branch-1 survivor
      have hm := List.mem_of_mem_filter hr
      have hcond := List.of_mem_filter hr
      simp only [decide_eq_true_eq] at hcond
      obtain ⟨⟨o, hoρ, hi, hrec⟩, hnd₁⟩ := (e_fold_mem Γ hwf₁ r).mp hm
      refine ⟨⟨o, Or.inl ((hp₁.2 o).mp hoρ), hi, hrec⟩, ?_⟩
      rintro d (hd | hd) hdel
      · exact hnd₁ ((hdels hp₁).mpr ⟨d, hd, hdel⟩)
      · rcases hcond with hin2 | hout0
        · have := ((e_fold_id_mem Γ hwf₂ r.1).mp hin2).2
          exact this ((hdels hp₂).mpr ⟨d, hd, hdel⟩)
        · -- honest corner: the deleter's insert lands in the LCA
          obtain ⟨a, haev₂, hains, hax, -⟩ :=
            e_del_ins_mem hHon hin₂ hcl₂ d hd r.1 hdel
          have hao : a = o := by
            apply C.ts_unique (hin₂ a haev₂)
              (hin₁ o ((hp₁.2 o).mp hoρ))
            rw [hax, hrec]; rfl
          have ho₀ : o ∈ ev₁ ∩ ev₂ :=
            ⟨(hp₁.2 o).mp hoρ, hao ▸ haev₂⟩
          apply hout0
          rw [e_fold_id_mem Γ hwf₀]
          refine ⟨⟨o, (hp₀.2 o).mpr ho₀, hi, by rw [hrec]; rfl⟩, ?_⟩
          intro hdel0
          obtain ⟨d', hd', hdel'⟩ := (hdels hp₀).mp hdel0
          exact hnd₁ ((hdels hp₁).mpr ⟨d', hd'.1, hdel'⟩)
    · -- branch-2 news
      have hm := List.mem_of_mem_filter hr
      have hcond := List.of_mem_filter hr
      simp only [decide_eq_true_eq] at hcond
      obtain ⟨⟨o, hoρ, hi, hrec⟩, hnd₂⟩ := (e_fold_mem Γ hwf₂ r).mp hm
      refine ⟨⟨o, Or.inr ((hp₂.2 o).mp hoρ), hi, hrec⟩, ?_⟩
      rintro d (hd | hd) hdel
      · -- a branch-1 delete would force the insert into the LCA,
        -- contradicting r.1 ∉ ids s₀
        obtain ⟨a, haev₁, hains, hax, -⟩ :=
          e_del_ins_mem hHon hin₁ hcl₁ d hd r.1 hdel
        have hao : a = o := by
          apply C.ts_unique (hin₁ a haev₁)
            (hin₂ o ((hp₂.2 o).mp hoρ))
          rw [hax, hrec]; rfl
        have ho₀ : o ∈ ev₁ ∩ ev₂ :=
          ⟨hao ▸ haev₁, (hp₂.2 o).mp hoρ⟩
        apply hcond.1
        rw [e_fold_id_mem Γ hwf₀]
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
      · rw [e_fold_mem Γ hwf₁]
        refine ⟨⟨o, (hp₁.2 o).mpr ho₁, hi, hrec⟩, ?_⟩
        intro hdel1
        obtain ⟨d, hd, hdel⟩ := (hdels hp₁).mp hdel1
        exact hnd d (Or.inl hd) hdel
      · simp only [decide_eq_true_eq]
        by_cases h0 : r.1 ∈ eIds s₀
        · left
          obtain ⟨⟨o', ho'ρ, hi', ho'1⟩, -⟩ := (e_fold_id_mem Γ hwf₀ r.1).mp h0
          have ho'₀ := (hp₀.2 o').mp ho'ρ
          rw [e_fold_id_mem Γ hwf₂]
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
      · rw [e_fold_mem Γ hwf₂]
        refine ⟨⟨o, (hp₂.2 o).mpr ho₂, hi, hrec⟩, ?_⟩
        intro hdel2
        obtain ⟨d, hd, hdel⟩ := (hdels hp₂).mp hdel2
        exact hnd d (Or.inr hd) hdel
      · simp only [decide_eq_true_eq]
        have hnot : ∀ {ρ : List (Op (EOp α))} {ev : Set (Op (EOp α))},
            listPermOf ρ ev → EWf Γ ρ → (∀ a ∈ ev, a ∈ C.events) →
            (∀ a ∈ ev, a ∈ ev₁) → r.1 ∉ eIds (eFold Γ ρ) := by
          intro ρ ev hp hwf hin hsub hmem
          obtain ⟨⟨o', ho'ρ, hi', ho'1⟩, -⟩ := (e_fold_id_mem Γ hwf r.1).mp hmem
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
theorem e_join_at {Γ : OrderedPrefixCode}
    {C : Sal.Emulation.Configuration (E Γ α).toCRDTSig}
    (hHon : EHonestCore Γ C) : JoinLemma3At (E Γ α) C := by
  intro ev₁ ev₂ s₀ s₁ s₂ _htr _hir hin₁ hin₂ hcl₁ hcl₂ h₀ h₁ h₂
  classical
  obtain ⟨ρ₀, hp₀, hr₀, hf₀⟩ := h₀
  obtain ⟨ρ₁, hp₁, hr₁, hf₁⟩ := h₁
  obtain ⟨ρ₂, hp₂, hr₂, hf₂⟩ := h₂
  set ev₀ := ev₁ ∩ ev₂ with hev₀
  have hin₀ : ∀ a ∈ ev₀, a ∈ C.events := fun a ha => hin₁ a ha.1
  have hcl₀ : ∀ a b, C.vis a b → ¬ (E Γ α).toCRDTSig.commutes a b →
      b ∈ ev₀ → a ∈ ev₀ :=
    fun a b hv hc hb => ⟨hcl₁ a b hv hc hb.1, hcl₂ a b hv hc hb.2⟩
  have hinU : ∀ a ∈ ev₁ ∪ ev₂, a ∈ C.events := by
    rintro a (ha | ha)
    · exact hin₁ a ha
    · exact hin₂ a ha
  have hclU : ∀ a b, C.vis a b → ¬ (E Γ α).toCRDTSig.commutes a b →
      b ∈ ev₁ ∪ ev₂ → a ∈ ev₁ ∪ ev₂ := by
    rintro a b hv hc (hb | hb)
    · exact Or.inl (hcl₁ a b hv hc hb)
    · exact Or.inr (hcl₂ a b hv hc hb)
  have hwf₀ := e_wf_of_enum hHon hin₀ hcl₀ hp₀ hr₀
  have hwf₁ := e_wf_of_enum hHon hin₁ hcl₁ hp₁ hr₁
  have hwf₂ := e_wf_of_enum hHon hin₂ hcl₂ hp₂ hr₂
  -- loOn is event-set independent under rc = Either
  have hloOn : ∀ (ev ev' : Set (Op (EOp α))) (x y : Op (EOp α)),
      loOn C ev x y → loOn C ev' x y := by
    intro ev ev' x y h
    rw [loOn_iff_of_rc_either (E_rc_either Γ)] at h ⊢
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
      rw [loOn_iff_of_rc_either (E_rc_either Γ)] at hl
      have hb1 : b ∈ ev₁ := hcl₁ b a hl.1 hl.2 ((hp₁.2 a).mp (hmemδ₁.mp ha).1)
      exact (hmemδ₂.mp hb).2 hb1
    · -- cross ρ₀ × deltas: a loOn-later delta event before an LCA event
      -- would be in ev₀
      intro a ha b hb hl
      rw [loOn_iff_of_rc_either (E_rc_either Γ)] at hl
      have ha0 : a ∈ ev₀ := (hp₀.2 a).mp ha
      have hb0 : b ∈ ev₀ := hcl₀ b a hl.1 hl.2 ha0
      rcases List.mem_append.mp hb with h | h
      · exact (hmemδ₁.mp h).2 hb0
      · exact (hmemδ₂.mp h).2 hb0.1
  have hwfU : EWf Γ ρᵤ := e_wf_of_enum hHon hinU hclU hpU hrU
  -- the fold of the witness IS the merge, by canonical-form extensionality
  refine ⟨ρᵤ, hpU, hrU, ?_⟩
  show eFold Γ ρᵤ = (E Γ α).mergeL s₀ s₁ s₂
  rw [← hf₀, ← hf₁, ← hf₂]
  show eFold Γ ρᵤ = eMergeL (eFold Γ ρ₀) (eFold Γ ρ₁) (eFold Γ ρ₂)
  -- cross-key-injectivity feeding the merge's sortedness
  have hdisj : ∀ x ∈ eFold Γ ρ₁, ∀ y ∈ eFold Γ ρ₂,
      key x.2.2 = key y.2.2 → x = y := by
    intro x hx y hy hkey
    obtain ⟨o₁, hm₁, hi₁, hrec₁⟩ := e_fold_rec_sub Γ ρ₁ x hx
    obtain ⟨o₂, hm₂, hi₂, hrec₂⟩ := e_fold_rec_sub Γ ρ₂ y hy
    have he₁ : o₁ ∈ C.events := hin₁ o₁ ((hp₁.2 o₁).mp hm₁)
    have he₂ : o₂ ∈ C.events := hin₂ o₂ ((hp₂.2 o₂).mp hm₂)
    have hkey' : key (eCoord Γ o₁) = key (eCoord Γ o₂) := by
      rw [hrec₁, hrec₂] at hkey
      exact hkey
    have hids : o₁.1 = o₂.1 := by
      by_contra hne
      exact e_keys_inj_events hHon o₁ he₁ o₂ he₂ hi₁ hi₂ hne hkey'
    have : o₁ = o₂ := C.ts_unique he₁ he₂ hids
    rw [hrec₁, hrec₂, this]
  apply esorted_ext (e_fold_sorted Γ hwfU)
    (eMergeL_sorted (e_fold_sorted Γ hwf₁) (e_fold_sorted Γ hwf₂) hdisj)
  intro r
  rw [e_fold_mem Γ hwfU r,
      e_mergeL_mem hHon hin₁ hin₂ hcl₁ hcl₂ hp₀ hp₁ hp₂ hwf₀ hwf₁ hwf₂ r]
  constructor
  · rintro ⟨⟨o, hm, hi, hrec⟩, hnd⟩
    have hor : o ∈ ev₁ ∨ o ∈ ev₂ := by
      rcases (hmemU o).mp hm with h | h
      · exact Or.inl h
      · exact Or.inr h
    refine ⟨⟨o, hor, hi, hrec⟩, ?_⟩
    intro d hd hdel
    apply hnd
    apply mem_eDels.mpr
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
    obtain ⟨d, hd, hdel'⟩ := mem_eDels.mp hdel
    rcases (hmemU d).mp hd with h | h
    · exact hnd d (Or.inl h) hdel'
    · exact hnd d (Or.inr h) hdel'

/-! ## §7  Honest reachability and the capstone -/

/-- Honest histories at the ternary configuration: every delete names an id
its issuer had observed (a `vis`-prior insert), and inserts are
chain-generated. The embedded-chain RGA's `HonestDelivery`. -/
def EHonest (Γ : OrderedPrefixCode) (C : Configuration (E Γ α)) : Prop :=
  (∀ e ∈ C.events, ∀ x : ℕ, e.2.2 = EOp.del x →
    ∃ a ∈ C.events, C.vis a e ∧ a.1 = x ∧ eIsIns a = true) ∧
  (∃ chainOf : ℕ → List ℕ, ∀ o ∈ C.events, eIsIns o = true →
    PosChain (chainOf o.1) ∧ eCoord Γ o = coordOf Γ (chainOf o.1) ∧
    (chainOf o.1).sum = o.1)

theorem eHonest_core {Γ : OrderedPrefixCode} {C : Configuration (E Γ α)}
    (h : EHonest Γ C) : EHonestCore Γ (Configuration.core C) where
  del_has_ins := by
    intro e he x hx
    rw [core_events] at he
    obtain ⟨a, ha, hv, hax, hai⟩ := h.1 e he x hx
    refine ⟨a, ?_, hv, hax, hai⟩
    rw [core_events]
    exact ha
  chain_gen := by
    obtain ⟨chainOf, hch⟩ := h.2
    refine ⟨chainOf, fun o ho hi => hch o ?_ hi⟩
    rw [core_events] at ho
    exact ho

/-- **Honest reachability**: LTS reachability where every step is taken from
a configuration with an honest history, instantiating the generic
`HonestReach`, exactly as the mergeable queue does. -/
def EReach (Γ : OrderedPrefixCode) : Configuration (E Γ α) → Prop :=
  HonestReach (E Γ α) (EHonest Γ) trivial

theorem e_goodConfig3 {Γ : OrderedPrefixCode} {C : Configuration (E Γ α)}
    (hReach : EReach Γ C) : GoodConfig3 C :=
  goodConfig3_of_honest_reach (fun _ hHon => e_join_at (eHonest_core hHon))
    hReach

/-- **The embedded-chain RGA is RA-linearizable, per version, at every
honestly reachable configuration**: every version the store registers is the
fold of a linearization of its event set that respects delivery order.
Parametric in the code, instantiate `Γ := binaryCode` for the
entropy-optimal artifact. -/
theorem embed_ra_linearizable3 {Γ : OrderedPrefixCode}
    {C : Configuration (E Γ α)} (hReach : EReach Γ C) :
    IsRALinearizable3 C :=
  isRALinearizable3_of_good (e_goodConfig3 hReach)

#print axioms embed_ra_linearizable3

/-! ## §8  The generation discipline: `applicable` implies honesty

What a well-behaved replica checks before issuing an op at the state it
sees. Both `EHonest` components are consequences: the delete half exactly as
the queue (fold provenance is unconditioned), the chain half by building the
global chain assignment by strong induction on ids, anchors have smaller
timestamps, and the anchor's record in ANY fold of the issuer's past is
op-determined, so the carried prefix is forced to be the anchor's chain's
coordinate. -/

/-- The issuer-side guard: an insert's anchor is live with EXACTLY the
carried prefix as its stored coordinate and a smaller stamp (Lamport); a
delete's target is live. -/
def eApplicable (o : Op (EOp α)) (s : EState α) : Prop :=
  match o with
  | (t, _, .ins _ π a) => a < t ∧ ((a = 0 ∧ π = []) ∨ ∃ el, (a, el, π) ∈ s)
  | (_, _, .del x)     => x ∈ eIds s

/-- Per-id chain existence: every insert's coordinate is a positive chain's
coordinate with telescoping sum. Strong induction on the id. -/
theorem e_chain_exists {Γ : OrderedPrefixCode} (C : Configuration (E Γ α))
    (hApp : ∀ e ∈ C.events, ∃ π : List (Op (EOp α)),
      listPermOf π {e' ∈ C.events | C.vis e' e} ∧
      eApplicable e (eFold Γ π)) :
    ∀ t : ℕ, ∃ ch : List ℕ, PosChain ch ∧ ch.sum = t ∧
      ∀ o ∈ C.events, eIsIns o = true → o.1 = t →
        eCoord Γ o = coordOf Γ ch := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    classical
    by_cases hex : ∃ o ∈ C.events, eIsIns o = true ∧ o.1 = t
    · obtain ⟨o, ho, hoi, hot⟩ := hex
      obtain ⟨ts, r, op⟩ := o
      cases op with
      | del x => simp [eIsIns] at hoi
      | ins el π a =>
          simp only at hot
          subst hot
          obtain ⟨πe, hπe, happ⟩ := hApp _ ho
          simp only [eApplicable] at happ
          obtain ⟨hat, hcase⟩ := happ
          rcases hcase with ⟨ha0, hπ0⟩ | ⟨el', hmem⟩
          · subst ha0
            subst hπ0
            refine ⟨[ts], ?_, by simp, ?_⟩
            · intro d hd
              simp at hd
              omega
            · intro o' ho' hoi' hot'
              have ho'eq : o' = (ts, r, EOp.ins el [] 0) :=
                (Configuration.core C).ts_unique ho' ho hot'
              rw [ho'eq]
              simp [eCoord, coordOf]
          · obtain ⟨aop, haπ, hai, hae⟩ := e_fold_rec_sub Γ πe (a, el', π) hmem
            have haev := (hπe.2 aop).mp haπ
            have ha1 : aop.1 = a := congrArg Prod.fst hae.symm
            have hπval : π = eCoord Γ aop :=
              congrArg (fun p : ERec α => p.2.2) hae
            obtain ⟨ch, hpos, hsum, hcoord⟩ := ih a hat
            refine ⟨ch ++ [ts - a], ?_, ?_, ?_⟩
            · intro d hd
              rcases List.mem_append.mp hd with h | h
              · exact hpos d h
              · simp at h
                omega
            · rw [List.sum_append]
              simp
              omega
            · intro o' ho' hoi' hot'
              have ho'eq : o' = (ts, r, EOp.ins el π a) :=
                (Configuration.core C).ts_unique ho' ho hot'
              rw [ho'eq]
              show π ++ Γ.enc (ts - a) = coordOf Γ (ch ++ [ts - a])
              rw [coordOf_append, hπval, hcoord aop haev.1 hai ha1]
              simp [coordOf]
    · push_neg at hex
      cases t with
      | zero =>
          exact ⟨[], by intro d hd; simp at hd, rfl,
            fun o ho hi h1 => absurd h1 (hex o ho hi)⟩
      | succ n =>
          refine ⟨[n + 1], ?_, by simp, fun o ho hi h1 => absurd h1 (hex o ho hi)⟩
          intro d hd
          simp at hd
          omega

/-- **The `applicable` discipline discharges honesty.** If every op was
applicable at SOME fold of its issuer's causal past, the issuer's own
materialized state is such a fold, then the history is honest: a delete's
target can only have entered that fold through a `vis`-prior insert, and the
carried prefixes are forced to be birth-chain coordinates. The embed
analogue of the queue's §8 and of the RGA's applicable-delivery layer. -/
theorem eHonest_of_applicable {Γ : OrderedPrefixCode} (C : Configuration (E Γ α))
    (hApp : ∀ e ∈ C.events, ∃ π : List (Op (EOp α)),
      listPermOf π {e' ∈ C.events | C.vis e' e} ∧
      eApplicable e (eFold Γ π)) :
    EHonest Γ C := by
  constructor
  · -- delete half: fold provenance
    intro e he x hx
    obtain ⟨π, hπ, happ⟩ := hApp e he
    obtain ⟨ts, r, op⟩ := e
    simp only at hx
    subst hx
    simp only [eApplicable] at happ
    obtain ⟨rec, hrec, hrec1⟩ := List.mem_map.mp happ
    obtain ⟨a, ha, hai, hae⟩ := e_fold_rec_sub Γ π rec hrec
    have haev := (hπ.2 a).mp ha
    have hax : a.1 = x := by
      rw [hae] at hrec1
      exact hrec1
    exact ⟨a, haev.1, haev.2, hax, hai⟩
  · -- chain half: the global assignment, by choice over per-id existence
    classical
    refine ⟨fun t => Classical.choose (e_chain_exists C hApp t), ?_⟩
    intro o ho hi
    obtain ⟨hpos, hsum, hcoord⟩ :=
      Classical.choose_spec (e_chain_exists C hApp o.1)
    exact ⟨hpos, hcoord o ho hi rfl, hsum⟩

/-- The honesty contract from the generic honesty shape at
`P := eApplicable`: `GenHonest` + causal-past enumerability supply exactly
`eHonest_of_applicable`'s hypothesis. -/
theorem eHonest_of_genHonest {Γ : OrderedPrefixCode} (C : Configuration (E Γ α))
    (hEnum : CausalPastEnumerable (E Γ α) C)
    (hApp : GenHonest (E Γ α) eApplicable C) : EHonest Γ C :=
  eHonest_of_applicable C
    (fun e he => (hEnum e he).imp (fun π hπ => ⟨hπ, hApp e he π hπ⟩))

#print axioms eHonest_of_applicable
#print axioms eHonest_of_genHonest

/-! ## §9  Intent theorems at the instance

The instance state IS the document (a sorted list), so the display-stability
contract becomes sublist preservation, three short lemmas. A delete never
reorders survivors (the clause the proved flat RGA violates); an insert
never reorders the existing document; a merge displays each branch's
survivors in that branch's own order. No co-displayed pair ever flips. -/

/-- **Delete-order preservation**: deletion displays exactly the survivors,
in unchanged order. -/
theorem eUpdate_del_sublist (Γ : OrderedPrefixCode) (s : EState α)
    (ts r x : ℕ) :
    List.Sublist (eUpdate Γ s (ts, r, .del x)) s :=
  List.filter_sublist

theorem eInsert_sublist (r : ERec α) : ∀ (s : EState α), List.Sublist s (eInsert r s)
  | [] => List.nil_sublist _
  | x :: xs => by
      by_cases h : keyLt (key x.2.2) (key r.2.2) = true
      · rw [show eInsert r (x :: xs) = r :: x :: xs from by simp [eInsert, h]]
        exact List.Sublist.cons r (List.Sublist.refl _)
      · rw [show eInsert r (x :: xs) = x :: eInsert r xs from by
          simp [eInsert, h]]
        exact List.Sublist.cons₂ x (eInsert_sublist r xs)

/-- **Step stability**: an insert never reorders the existing document. -/
theorem eUpdate_ins_sublist (Γ : OrderedPrefixCode) (s : EState α)
    (ts r : ℕ) (el : α) (π : List Bool) (a : ℕ) :
    List.Sublist s (eUpdate Γ s (ts, r, .ins el π a)) := by
  simp only [eUpdate]
  by_cases h : ts ∈ eIds s
  · rw [if_pos h]
  · rw [if_neg h]
    exact eInsert_sublist _ s

theorem eMerge2_sublist_left : ∀ (as bs : EState α), List.Sublist as (eMerge2 as bs) := by
  intro as bs
  induction as, bs using eMerge2.induct with
  | case1 ys => exact List.nil_sublist _
  | case2 xs => cases xs <;> simp [eMerge2]
  | case3 a as' b bs' h ih =>
      rw [show eMerge2 (a :: as') (b :: bs') = a :: eMerge2 as' (b :: bs')
        from by rw [eMerge2]; simp [h]]
      exact List.Sublist.cons₂ a ih
  | case4 a as' b bs' h ih =>
      rw [show eMerge2 (a :: as') (b :: bs') = b :: eMerge2 (a :: as') bs'
        from by rw [eMerge2]; simp [h]]
      exact List.Sublist.cons b ih

theorem eMerge2_sublist_right : ∀ (as bs : EState α), List.Sublist bs (eMerge2 as bs) := by
  intro as bs
  induction as, bs using eMerge2.induct with
  | case1 ys =>
      rw [show eMerge2 [] ys = ys from by rw [eMerge2]]
  | case2 xs => cases xs <;> simp [eMerge2]
  | case3 a as' b bs' h ih =>
      rw [show eMerge2 (a :: as') (b :: bs') = a :: eMerge2 as' (b :: bs')
        from by rw [eMerge2]; simp [h]]
      exact List.Sublist.cons a ih
  | case4 a as' b bs' h ih =>
      rw [show eMerge2 (a :: as') (b :: bs') = b :: eMerge2 (a :: as') bs'
        from by rw [eMerge2]; simp [h]]
      exact List.Sublist.cons₂ b ih

/-- **Merge stability (S4 at the instance)**: the merge displays branch
`a`'s survivors, those shared with `b` or new since the LCA, as a sublist
of `a`'s own document: in `a`'s order, never reordered. Symmetrically for
`b`'s news via `eMerge2_sublist_right`. -/
theorem eMergeL_stable_left (l a b : EState α) :
    List.Sublist (a.filter (fun r => decide (r.1 ∈ eIds b ∨ r.1 ∉ eIds l)))
      (eMergeL l a b) :=
  eMerge2_sublist_left _ _

theorem eMergeL_stable_right (l a b : EState α) :
    List.Sublist (b.filter (fun r => decide (r.1 ∉ eIds l ∧ r.1 ∉ eIds a)))
      (eMergeL l a b) :=
  eMerge2_sublist_right _ _

#print axioms eUpdate_del_sublist
#print axioms eMergeL_stable_left

end Sal.ConditionedMRDTs
