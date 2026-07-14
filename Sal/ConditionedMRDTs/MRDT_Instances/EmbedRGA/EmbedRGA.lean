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

end Sal.ConditionedMRDTs
