import LeanProofs.Implementations.EnableWinsFlag.Laws
import LeanProofs.Soundness.LinearExtension

/-!
# The flag core: clause 1

What a canonical state is, the issuance guard, and the join lemma

The join lemma is proved directly, as for the OR-set and for the same reason:
the arbitrary-state VCs rule out the VC route.

A canonical state of an event set `E` is read off `E` in two pieces.

* **The counter of row `r`** is the number of `winning` events in `E` issued
  by `r`. Counters never decrease and no event reads them, so this is
  immediate and order-free.
* **The bit of row `r`** records survivorship, exactly as the OR-set records
  liveness: it is set when some `winning` at `r` in `E` is observed by no
  `reset` in `E`, or when the initial bit was set and `E` holds no `reset`
  at all.

The merge then has to reproduce both. The counter is inclusion-exclusion.
The bit is a four-way case analysis in which the counter comparison
`a.1 > l.1` plays the part that `(a \ l)` plays in the OR-set: it says the
branch holds a `winning` the ancestor did not.
-/

namespace LeanProofs.Implementations.EnableWinsFlag

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.Interface

/-- The replay order of Section 4: `rc`, lifted to events. -/
noncomputable local instance rcOrder :
    EventOrder D.toMRDTSig.toUpdateSig :=
  Interface.rcOrder D

@[simp] theorem replayBefore_iff (a b : D.Event) :
    D.toMRDTSig.toUpdateSig.replayBefore a b
      ↔ a.op = AppOp.reset ∧ b.op = AppOp.winning := by
  refine Iff.trans ?_ (rcBefore_iff a.op b.op)
  exact @OperationPolicy.lift_replayOrder_iff D.toMRDTSig.toUpdateSig
    (Interface.policy D) a b

/-- A `reset` and a `winning` are exactly the pairs `loOn` can order. -/
theorem replayBefore_or_iff (a b : D.Event) :
    (D.toMRDTSig.toUpdateSig.replayBefore a b
        ∨ D.toMRDTSig.toUpdateSig.replayBefore b a)
      ↔ (a.op = AppOp.reset ∧ b.op = AppOp.winning)
        ∨ (b.op = AppOp.reset ∧ a.op = AppOp.winning) := by
  simp only [replayBefore_iff]

/-! ## Counters -/

/-- The number of `winning` events issued by `r`. -/
def winCount (r : Replica) (pi : List (Event)) : Nat :=
  pi.countP (fun e => decide (e.op = AppOp.winning ∧ e.rep = r))

@[simp] theorem winCount_nil (r : Replica) : winCount r [] = 0 := rfl

theorem winCount_cons (r : Replica) (e : Event) (pi : List (Event)) :
    winCount r (e :: pi) =
      winCount r pi + if e.op = AppOp.winning ∧ e.rep = r then 1 else 0 := by
  by_cases h : e.op = AppOp.winning ∧ e.rep = r <;>
    simp [winCount, List.countP_cons, h]

/-- Replaying a list adds one to row `r` for each `winning` it issued. -/
theorem foldl_counter (s : St) (pi : List (Event)) (r : Replica) :
    ((pi.foldl step s) r).1 = (s r).1 + (winCount r pi : Int) := by
  induction pi generalizing s with
  | nil => simp
  | cons e pi ih =>
      rw [List.foldl_cons, ih, winCount_cons]
      cases he : e.op with
      | winning =>
          simp only [step, he]
          by_cases hr : r = e.rep
          · simp [hr]; omega
          · have hr' : ¬ (e.rep = r) := Ne.symm hr
            simp [hr, hr']
      | reset =>
          simp only [step, he]
          simp [he]

/-! ## Bits

The bit of row `r` is set exactly when the list holds a `winning` at `r` with
no `reset` after it, or holds no `reset` at all and started set. -/

/-- No event in the list is a `reset`. -/
def NoReset (pi : List (Event)) : Prop := ∀ e ∈ pi, e.op ≠ AppOp.reset

@[simp] theorem noReset_nil : NoReset [] := by simp [NoReset]

theorem noReset_append_singleton {pi : List (Event)} {e : Event} :
    NoReset (pi ++ [e]) ↔ NoReset pi ∧ e.op ≠ AppOp.reset := by
  constructor
  · exact fun h => ⟨fun a ha => h a (by simp [ha]), h e (by simp)⟩
  · rintro ⟨h, he⟩ a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact h a ha
    · rw [List.mem_singleton.mp ha]; exact he

/-- Splitting a list that ends in `e`: either the marked element is `e`
itself, or the split lies entirely inside the prefix. -/
theorem append_singleton_split {α : Type} {pi pre post : List α} {w e : α}
    (h : pi ++ [e] = pre ++ w :: post) :
    (w = e ∧ pi = pre)
      ∨ (∃ post', post = post' ++ [e] ∧ pi = pre ++ w :: post') := by
  cases post using List.reverseRecOn with
  | nil =>
      obtain ⟨hpre, hw⟩ := List.append_inj' (h : pi ++ [e] = pre ++ [w]) rfl
      have hew : e = w := by simpa using hw
      exact Or.inl ⟨hew.symm, hpre⟩
  | append_singleton post' x =>
      have h' : pi ++ [e] = (pre ++ w :: post') ++ [x] := by rw [h]; simp
      obtain ⟨hpi, hx⟩ := List.append_inj' h' rfl
      have hex : e = x := by simpa using hx
      exact Or.inr ⟨post', by rw [hex], hpi⟩

/-- The list-level reading of the bit. -/
theorem foldl_bit_iff (s : St) (pi : List (Event)) (r : Replica) :
    ((pi.foldl step s) r).2 = true ↔
      (∃ pre w post, pi = pre ++ w :: post ∧ w.op = AppOp.winning ∧ w.rep = r
        ∧ NoReset post)
      ∨ ((s r).2 = true ∧ NoReset pi) := by
  induction pi using List.reverseRecOn with
  | nil =>
      constructor
      · exact fun h => Or.inr ⟨h, noReset_nil⟩
      · rintro (⟨pre, w, post, hs, -, -, -⟩ | ⟨h, -⟩)
        · exact absurd hs.symm (by simp)
        · exact h
  | append_singleton pi e ih =>
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      cases he : e.op with
      | winning =>
          simp only [step, he]
          by_cases hr : r = e.rep
          · subst hr
            simp only [if_pos rfl]
            constructor
            · exact fun _ => Or.inl ⟨pi, e, [], rfl, he, rfl, noReset_nil⟩
            · exact fun _ => rfl
          · simp only [if_neg hr]
            rw [ih]
            constructor
            · rintro (⟨pre, w, post, hs, hw, hwr, hn⟩ | ⟨h, hn⟩)
              · exact Or.inl ⟨pre, w, post ++ [e], by rw [hs]; simp, hw, hwr,
                  noReset_append_singleton.mpr ⟨hn, by rw [he]; simp⟩⟩
              · exact Or.inr ⟨h, noReset_append_singleton.mpr ⟨hn, by rw [he]; simp⟩⟩
            · rintro (⟨pre, w, post, hs, hw, hwr, hn⟩ | ⟨h, hn⟩)
              · rcases append_singleton_split hs with ⟨hwe, -⟩ | ⟨post', hpost, hpi⟩
                · exact absurd (hwe ▸ hwr) (Ne.symm hr)
                · exact Or.inl ⟨pre, w, post', hpi, hw, hwr,
                    (noReset_append_singleton.mp (hpost ▸ hn)).1⟩
              · exact Or.inr ⟨h, (noReset_append_singleton.mp hn).1⟩
      | reset =>
          simp only [step, he]
          constructor
          · exact fun h => absurd h (by simp)
          · rintro (⟨pre, w, post, hs, hw, hwr, hn⟩ | ⟨-, hn⟩)
            · exfalso
              rcases append_singleton_split hs with ⟨hwe, -⟩ | ⟨post', hpost, -⟩
              · exact absurd (hwe ▸ hw) (by rw [he]; simp)
              · exact absurd he (hn e (by rw [hpost]; simp))
            · exact absurd he (hn e (by simp))

/-! ## Liveness

The bit of row `r` is set exactly when some `winning` at `r` survives, which
is the OR-set's liveness predicate with `reset` in the role of `remove`. -/

variable {C : Configuration D.toMRDTSig}

/-- No `reset` of `E` observes `a`. -/
def Survives (C : Configuration D.toMRDTSig)
    (E : Set (Event)) (a : Event) : Prop :=
  ¬ ∃ rho ∈ E, rho.op = AppOp.reset ∧ C.vis a rho

/-- Row `r` is live in `E`: some `winning` at `r` survives, or the initial
bit was set and `E` holds no `reset` at all. -/
def Live (C : Configuration D.toMRDTSig)
    (E : Set (Event)) (flag : Bool) (r : Replica) : Prop :=
  (∃ w ∈ E, w.op = AppOp.winning ∧ w.rep = r ∧ Survives C E w)
    ∨ (flag = true ∧ ¬ ∃ rho ∈ E, rho.op = AppOp.reset)

theorem survives_union {E₁ E₂ : Set (Event)} {a : Event} :
    Survives C (E₁ ∪ E₂) a ↔ Survives C E₁ a
      ∧ Survives C E₂ a := by
  constructor
  · exact fun h => ⟨fun ⟨p, hp, hr, hv⟩ => h ⟨p, Or.inl hp, hr, hv⟩,
      fun ⟨p, hp, hr, hv⟩ => h ⟨p, Or.inr hp, hr, hv⟩⟩
  · rintro ⟨h₁, h₂⟩ ⟨p, hp | hp, hr, hv⟩
    · exact h₁ ⟨p, hp, hr, hv⟩
    · exact h₂ ⟨p, hp, hr, hv⟩

theorem survives_subset {E F : Set (Event)} {a : Event} (hsub : E ⊆ F)
    (h : Survives C F a) :
    Survives C E a :=
  fun ⟨p, hp, hr, hv⟩ => h ⟨p, hsub hp, hr, hv⟩

/-- A `winning` and a `reset` never commute. -/
theorem not_commutes_winning_reset {a b : Event} (ha : a.op = AppOp.winning)
    (hb : b.op = AppOp.reset) :
    ¬ D.toMRDTSig.toUpdateSig.commutes a b :=
  fun hc => not_commutes_reset_winning
    b a hb ha (commutes_symm hc)

/-- A `winning` a branch does not contain is observed by no `reset` of that
branch: causal closure would otherwise force it in. This is where the
closure premises of `JoinAt` are used. -/
theorem survives_of_not_mem {E : Set (Event)} {w : Event}
    (hclosed : ∀ a b, C.vis a b →
      ¬ D.toMRDTSig.toUpdateSig.commutes a b → b ∈ E → a ∈ E)
    (hw : w.op = AppOp.winning) (hnm : w ∉ E) : Survives C E w := by
  rintro ⟨rho, hrho, hres, hvis⟩
  exact hnm (hclosed w rho hvis (not_commutes_winning_reset hw hres) hrho)

/-- Survival passes to later `winning` events of the same replica: a `reset`
observing the later one observes the earlier one too. -/
theorem survives_mono {E : Set (Event)} {w w' : Event}
    (htr : ∀ {a b c : Event}, C.vis a b → C.vis b c → C.vis a c)
    (hvis : C.vis w w')
    (h : Survives C E w) :
    Survives C E w' :=
  fun ⟨rho, hrho, hres, hv⟩ => h ⟨rho, hrho, hres, htr hvis hv⟩

/-- `vis` is total on the events of one replica. -/
theorem vis_total {a b : Event} (ha : a ∈ C.events) (hb : b ∈ C.events)
    (hne : a ≠ b) (hrep : a.rep = b.rep) : C.vis a b ∨ C.vis b a := by
  obtain ⟨p, s, hL, hs⟩ := ha
  obtain ⟨p', s', hL', hs'⟩ := hb
  exact C.vis_total_same_replica hL hs hL' hs' hne hrep

/-! ### Edges and list positions -/

theorem not_edge_to_prefix {R : Event → Event → Prop}
    {pre post : List (Event)} {a r : Event}
    (hr : respects (pre ++ a :: post) R) (hm : r ∈ pre) : ¬ R a r :=
  (List.pairwise_append.mp hr).2.2 r hm a (by simp)

theorem not_edge_from_suffix {R : Event → Event → Prop}
    {pre post : List (Event)} {a r : Event}
    (hr : respects (pre ++ a :: post) R) (hm : r ∈ post) : ¬ R r a :=
  (List.pairwise_cons.mp (List.pairwise_append.mp hr).2.1).1 r hm

/-- **The bit of a canonical state is liveness.** Every replay of `E` that
respects `lo^C_E` agrees, so the bit depends on the event set alone. -/
theorem run_bit_iff_live {E : Set (Event)} {pi : List (Event)}
    (hp : listPermOf pi E) (hr : respects pi (loOn C.replayContext E)) (r : Replica) :
    ((pi.foldl step (fun _ => (0, false))) r).2 = true
      ↔ Live C E false r := by
  rw [foldl_bit_iff]
  constructor
  · rintro (⟨pre, w, post, hs, hw, hwr, hn⟩ | ⟨hb, hn⟩)
    · subst pi
      refine Or.inl ⟨w, (hp.2 w).mp (by simp), hw, hwr, ?_⟩
      rintro ⟨rho, hrho, hres, hvis⟩
      have hm : rho ∈ pre ++ w :: post := (hp.2 rho).mpr hrho
      rcases List.mem_append.mp hm with hm | hm
      · exact not_edge_to_prefix hr hm
          (Or.inl ⟨hvis, Or.inr ((replayBefore_iff rho w).mpr ⟨hres, hw⟩)⟩)
      · rcases List.mem_cons.mp hm with heq | hm
        · rw [heq, hw] at hres; cases hres
        · exact hn rho hm hres
    · exact Or.inr ⟨hb, fun ⟨rho, hrho, hres⟩ => hn rho ((hp.2 rho).mpr hrho) hres⟩
  · rintro (⟨w, hwe, hw, hwr, hsv⟩ | ⟨hb, hno⟩)
    · obtain ⟨pre, post, hs⟩ := List.append_of_mem ((hp.2 w).mpr hwe)
      refine Or.inl ⟨pre, w, post, hs, hw, hwr, ?_⟩
      subst pi
      intro rho hm hres
      refine not_edge_from_suffix hr hm ?_
      have hre : rho ∈ E := (hp.2 rho).mp (by simp [hm])
      have hrc : D.toMRDTSig.toUpdateSig.replayBefore rho w :=
        (replayBefore_iff rho w).mpr ⟨hres, hw⟩
      by_cases hvw : C.vis rho w
      · exact Or.inl ⟨hvw, Or.inl hrc⟩
      · refine Or.inr ⟨hvw, ?_, hrc, ?_⟩
        · exact fun hv => hsv ⟨rho, hre, hres, hv⟩
        · rintro ⟨c, hce, hvc, hc | hc⟩
          · obtain ⟨hwres, -⟩ := (replayBefore_iff w c).mp hc
            rw [hw] at hwres; cases hwres
          · obtain ⟨hcres, -⟩ := (replayBefore_iff c w).mp hc
            exact hsv ⟨c, hce, hcres, hvc⟩
    · exact Or.inr ⟨hb, fun rho hm hres => hno ⟨rho, (hp.2 rho).mp hm, hres⟩⟩

/-! ### How liveness behaves under union

These four lemmas are the whole content of the bit half of the merge. -/

/-- A row live in the union is live in one of the branches. -/
theorem live_of_live_union {E₁ E₂ : Set (Event)} {flag : Bool} {r : Replica}
    (h : Live C (E₁ ∪ E₂) flag r) : Live C E₁ flag r ∨ Live C E₂ flag r := by
  rcases h with ⟨w, hwe, hw, hwr, hsv⟩ | ⟨hb, hno⟩
  · obtain ⟨hs₁, hs₂⟩ := survives_union.mp hsv
    rcases hwe with hwe | hwe
    · exact Or.inl (Or.inl ⟨w, hwe, hw, hwr, hs₁⟩)
    · exact Or.inr (Or.inl ⟨w, hwe, hw, hwr, hs₂⟩)
  · exact Or.inl (Or.inr ⟨hb, fun ⟨rho, hrho, hres⟩ => hno ⟨rho, Or.inl hrho, hres⟩⟩)

/-- A row live in both branches is live in the union. The two surviving
`winning` events are issued by the same replica, so `vis` compares them, and
the later one survives both branches. -/
theorem live_union_of_both {E₁ E₂ : Set (Event)} {flag : Bool} {r : Replica}
    (htr : ∀ {a b c : Event}, C.vis a b → C.vis b c → C.vis a c)
    (hsub₁ : ∀ a ∈ E₁, a ∈ C.events) (hsub₂ : ∀ a ∈ E₂, a ∈ C.events)
    (h₁ : Live C E₁ flag r) (h₂ : Live C E₂ flag r) : Live C (E₁ ∪ E₂) flag r := by
  rcases h₁ with ⟨w₁, hw₁e, hw₁, hw₁r, hs₁⟩ | ⟨hb₁, hno₁⟩
  · rcases h₂ with ⟨w₂, hw₂e, hw₂, hw₂r, hs₂⟩ | ⟨hb₂, hno₂⟩
    · by_cases heq : w₁ = w₂
      · subst heq
        exact Or.inl ⟨w₁, Or.inl hw₁e, hw₁, hw₁r, survives_union.mpr ⟨hs₁, hs₂⟩⟩
      · rcases vis_total (hsub₁ w₁ hw₁e) (hsub₂ w₂ hw₂e) heq (hw₁r.trans hw₂r.symm)
          with hv | hv
        · exact Or.inl ⟨w₂, Or.inr hw₂e, hw₂, hw₂r,
            survives_union.mpr ⟨survives_mono htr hv hs₁, hs₂⟩⟩
        · exact Or.inl ⟨w₁, Or.inl hw₁e, hw₁, hw₁r,
            survives_union.mpr ⟨hs₁, survives_mono htr hv hs₂⟩⟩
    · exact Or.inl ⟨w₁, Or.inl hw₁e, hw₁, hw₁r, survives_union.mpr
        ⟨hs₁, fun ⟨rho, hrho, hres, _⟩ => hno₂ ⟨rho, hrho, hres⟩⟩⟩
  · rcases h₂ with ⟨w₂, hw₂e, hw₂, hw₂r, hs₂⟩ | ⟨hb₂, hno₂⟩
    · exact Or.inl ⟨w₂, Or.inr hw₂e, hw₂, hw₂r, survives_union.mpr
        ⟨fun ⟨rho, hrho, hres, _⟩ => hno₁ ⟨rho, hrho, hres⟩, hs₂⟩⟩
    · refine Or.inr ⟨hb₁, ?_⟩
      rintro ⟨rho, hrho | hrho, hres⟩
      · exact hno₁ ⟨rho, hrho, hres⟩
      · exact hno₂ ⟨rho, hrho, hres⟩

/-- A branch that is live and holds a `winning` the other branch does not
makes the union live. -/
theorem live_union_of_fresh {E₁ E₂ : Set (Event)} {flag : Bool} {r : Replica}
    (htr : ∀ {a b c : Event}, C.vis a b → C.vis b c → C.vis a c)
    (hsub₁ : ∀ a ∈ E₁, a ∈ C.events)
    (hclosed₂ : ∀ a b, C.vis a b →
      ¬ D.toMRDTSig.toUpdateSig.commutes a b → b ∈ E₂ → a ∈ E₂)
    (h₁ : Live C E₁ flag r)
    {w : Event} (hwe : w ∈ E₁) (hnm : w ∉ E₂)
    (hw : w.op = AppOp.winning) (hwr : w.rep = r) : Live C (E₁ ∪ E₂) flag r := by
  have hw₂ : Survives C E₂ w := survives_of_not_mem hclosed₂ hw hnm
  rcases h₁ with ⟨w₁, hw₁e, hw₁, hw₁r, hs₁⟩ | ⟨-, hno₁⟩
  · by_cases heq : w = w₁
    · subst heq
      exact Or.inl ⟨w, Or.inl hwe, hw, hwr, survives_union.mpr ⟨hs₁, hw₂⟩⟩
    · rcases vis_total (hsub₁ w hwe) (hsub₁ w₁ hw₁e) heq (hwr.trans hw₁r.symm) with hv | hv
      · exact Or.inl ⟨w₁, Or.inl hw₁e, hw₁, hw₁r,
          survives_union.mpr ⟨hs₁, survives_mono htr hv hw₂⟩⟩
      · exact Or.inl ⟨w, Or.inl hwe, hw, hwr,
          survives_union.mpr ⟨survives_mono htr hv hs₁, hw₂⟩⟩
  · exact Or.inl ⟨w, Or.inl hwe, hw, hwr, survives_union.mpr
      ⟨fun ⟨rho, hrho, hres, _⟩ => hno₁ ⟨rho, hrho, hres⟩, hw₂⟩⟩

/-- If the union is live but one branch is not, the other branch holds a
`winning` the first does not. -/
theorem fresh_of_live_union {E₁ E₂ : Set (Event)} {flag : Bool} {r : Replica}
    (h : Live C (E₁ ∪ E₂) flag r) (hn₂ : ¬ Live C E₂ flag r) :
    ∃ w ∈ E₁, w ∉ E₂ ∧ w.op = AppOp.winning ∧ w.rep = r := by
  rcases h with ⟨w, hwe, hw, hwr, hsv⟩ | ⟨hb, hno⟩
  · obtain ⟨hs₁, hs₂⟩ := survives_union.mp hsv
    rcases hwe with hwe | hwe
    · refine ⟨w, hwe, ?_, hw, hwr⟩
      exact fun hm => hn₂ (Or.inl ⟨w, hm, hw, hwr, hs₂⟩)
    · exact absurd (Or.inl ⟨w, hwe, hw, hwr, hs₂⟩) hn₂
  · exact absurd (Or.inr ⟨hb, fun ⟨rho, hrho, hres⟩ => hno ⟨rho, Or.inr hrho, hres⟩⟩) hn₂

/-! ## Counting the `winning` events

The counter half of the merge is inclusion-exclusion, and the comparison
`a.1 > l.1` that the bit half consults says the branch holds a `winning` the
ancestor did not. Both are read off one finite set. -/

/-- The `winning` events of `r` in an enumeration. -/
def winOf (r : Replica) (pi : List (Event)) : Finset (Event) :=
  pi.toFinset.filter (fun e => e.op = AppOp.winning ∧ e.rep = r)

theorem mem_winOf_set {r : Replica} {pi : List (Event)} {E : Set (Event)}
    (hp : listPermOf pi E) {e : Event} :
    e ∈ winOf r pi ↔ e ∈ E ∧ e.op = AppOp.winning ∧ e.rep = r := by
  rw [winOf, Finset.mem_filter, List.mem_toFinset, hp.2 e]

theorem card_winOf {r : Replica} {pi : List (Event)} (h : pi.Nodup) :
    (winOf r pi).card = winCount r pi := by
  have hfilter : winOf r pi
      = (pi.filter (fun e => decide (e.op = AppOp.winning ∧ e.rep = r))).toFinset := by
    ext e
    simp [winOf, List.mem_toFinset, List.mem_filter]
  rw [hfilter, List.toFinset_card_of_nodup (h.filter _), winCount,
    List.countP_eq_length_filter]

/-- The counters obey inclusion-exclusion, which is the counter half of the
merge equation. -/
theorem count_union_inter {E₁ E₂ : Set (Event)}
    {pi₀ pi₁ pi₂ piU : List (Event)}
    (hp₀ : listPermOf pi₀ (E₁ ∩ E₂)) (hp₁ : listPermOf pi₁ E₁)
    (hp₂ : listPermOf pi₂ E₂) (hpU : listPermOf piU (E₁ ∪ E₂)) (r : Replica) :
    winCount r piU + winCount r pi₀ = winCount r pi₁ + winCount r pi₂ := by
  have hU : winOf r pi₁ ∪ winOf r pi₂ = winOf r piU := by
    ext e
    simp only [Finset.mem_union, mem_winOf_set hp₁, mem_winOf_set hp₂,
      mem_winOf_set hpU, Set.mem_union]
    constructor
    · rintro (⟨h, hw⟩ | ⟨h, hw⟩)
      · exact ⟨Or.inl h, hw⟩
      · exact ⟨Or.inr h, hw⟩
    · rintro ⟨h | h, hw⟩
      · exact Or.inl ⟨h, hw⟩
      · exact Or.inr ⟨h, hw⟩
  have hI : winOf r pi₁ ∩ winOf r pi₂ = winOf r pi₀ := by
    ext e
    simp only [Finset.mem_inter, mem_winOf_set hp₁, mem_winOf_set hp₂,
      mem_winOf_set hp₀, Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨h1, hw⟩, ⟨h2, -⟩⟩
      exact ⟨⟨h1, h2⟩, hw⟩
    · rintro ⟨⟨h1, h2⟩, hw⟩
      exact ⟨⟨h1, hw⟩, ⟨h2, hw⟩⟩
  rw [← card_winOf hpU.1, ← card_winOf hp₀.1, ← card_winOf hp₁.1,
    ← card_winOf hp₂.1, ← hU, ← hI]
  exact Finset.card_union_add_card_inter _ _

/-- A branch's counter exceeds the ancestor's exactly when the branch holds a
`winning` the other branch does not. -/
theorem count_lt_iff {E₁ E₂ : Set (Event)} {pi₀ pi₁ : List (Event)}
    (hp₀ : listPermOf pi₀ (E₁ ∩ E₂)) (hp₁ : listPermOf pi₁ E₁) (r : Replica) :
    winCount r pi₀ < winCount r pi₁
      ↔ ∃ w ∈ E₁, w ∉ E₂ ∧ w.op = AppOp.winning ∧ w.rep = r := by
  have hsub : winOf r pi₀ ⊆ winOf r pi₁ := by
    intro e he
    rw [mem_winOf_set hp₀] at he
    exact (mem_winOf_set hp₁).mpr ⟨he.1.1, he.2⟩
  rw [← card_winOf hp₀.1, ← card_winOf hp₁.1]
  constructor
  · intro hlt
    by_contra hcon
    have hsub2 : winOf r pi₁ ⊆ winOf r pi₀ := by
      intro e he
      rw [mem_winOf_set hp₁] at he
      refine (mem_winOf_set hp₀).mpr ⟨⟨he.1, ?_⟩, he.2⟩
      by_contra hm
      exact hcon ⟨e, he.1, hm, he.2.1, he.2.2⟩
    have := Finset.card_le_card hsub2
    omega
  · rintro ⟨w, hw₁, hw₂, hww, hwr⟩
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨w, ?_, ?_⟩)
    · exact (mem_winOf_set hp₁).mpr ⟨hw₁, hww, hwr⟩
    · intro hm
      rw [mem_winOf_set hp₀] at hm
      exact hw₂ hm.1.2

/-! ## The join lemma -/

/-- **The join lemma**, proved directly. Merging canonical states of the
branches yields a canonical state of the union of their event sets. The
counter half is inclusion-exclusion; the bit half is the four-way case
analysis of `mergeFlag`, in which the counter comparison stands for "this
branch holds a `winning` the ancestor did not". -/
theorem joinLemma : Interface.JoinConfig D := by
  intro C E₁ E₂ s₀ s₁ s₂ htr hir hsub₁ hsub₂ hclosed₁ hclosed₂ hs₀ hs₁ hs₂
  obtain ⟨pi₀, hp₀, hr₀, hf₀⟩ := id hs₀
  obtain ⟨pi₁, hp₁, hr₁, hf₁⟩ := id hs₁
  obtain ⟨pi₂, hp₂, hr₂, hf₂⟩ := id hs₂
  have hsubU : ∀ a ∈ E₁ ∪ E₂, a ∈ C.replayContext.events :=
    fun a ha => ha.elim (hsub₁ a) (hsub₂ a)
  obtain ⟨sU, hsU⟩ := isCanonicalState_exists_of_replayLaws
    (Metatheory.replayLaws laws rc_non_comm cond_comm)
    htr hir
    (listPermOf_union (D := D.toMRDTSig.toUpdateSig) hp₁ hp₂) hsubU
  obtain ⟨piU, hpU, hrU, hfU⟩ := id hsU
  have hcount : ∀ (pi : List (Event)) (s : St),
      applySeq D.toMRDTSig.toUpdateSig
        D.toMRDTSig.init pi = s →
      ∀ r, (s r).1 = (winCount r pi : Int) := by
    intro pi s hfs r
    rw [← hfs]
    simpa using foldl_counter (fun _ => ((0 : Int), false)) pi r
  have hbit : ∀ (pi : List (Event)) (s : St) (E : Set (Event)),
      listPermOf pi E → respects pi (loOn C.replayContext E) →
      applySeq D.toMRDTSig.toUpdateSig
        D.toMRDTSig.init pi = s →
      ∀ r, ((s r).2 = true ↔ Live C E false r) := by
    intro pi s E hp hr hfs r
    rw [← hfs]
    exact run_bit_iff_live hp hr r
  have heq : D.toMRDTSig.merge s₀ s₁ s₂ = sU := by
    funext r
    have hc₀ := hcount pi₀ s₀ hf₀ r
    have hc₁ := hcount pi₁ s₁ hf₁ r
    have hc₂ := hcount pi₂ s₂ hf₂ r
    have hcU := hcount piU sU hfU r
    have hb₀ := hbit pi₀ s₀ _ hp₀ hr₀ hf₀ r
    have hb₁ := hbit pi₁ s₁ _ hp₁ hr₁ hf₁ r
    have hb₂ := hbit pi₂ s₂ _ hp₂ hr₂ hf₂ r
    have hbU := hbit piU sU _ hpU hrU hfU r
    have hcounter : (s₁ r).1 + (s₂ r).1 - (s₀ r).1 = (sU r).1 := by
      have := count_union_inter hp₀ hp₁ hp₂ hpU r
      rw [hc₀, hc₁, hc₂, hcU]
      omega
    have hflag : mergeFlag (s₀ r) (s₁ r) (s₂ r) = (sU r).2 := by
      cases hv₁ : (s₁ r).2 with
      | true =>
          cases hv₂ : (s₂ r).2 with
          | true =>
              have := (hbU).mpr (live_union_of_both htr hsub₁ hsub₂
                (hb₁.mp hv₁) (hb₂.mp hv₂))
              simp [mergeFlag, hv₁, hv₂, this]
          | false =>
              have hn₂ : ¬ Live C E₂ false r := by
                intro h
                rw [hb₂.mpr h] at hv₂
                exact Bool.noConfusion hv₂
              simp only [mergeFlag, hv₁, hv₂, Bool.and_false, if_false,
                Bool.not_true, Bool.false_and, Bool.not_false, if_true]
              rw [hc₀, hc₁]
              cases hvU : (sU r).2 with
              | true =>
                  obtain ⟨w, hw₁, hw₂, hww, hwr⟩ :=
                    fresh_of_live_union (hbU.mp hvU) hn₂
                  have : winCount r pi₀ < winCount r pi₁ :=
                    (count_lt_iff hp₀ hp₁ r).mpr ⟨w, hw₁, hw₂, hww, hwr⟩
                  simp
                  omega
              | false =>
                  have hnf : ¬ ∃ w ∈ E₁, w ∉ E₂ ∧ w.op = AppOp.winning ∧ w.rep = r := by
                    rintro ⟨w, hw₁, hw₂, hww, hwr⟩
                    have := hbU.mpr (live_union_of_fresh htr hsub₁ hclosed₂
                      (hb₁.mp hv₁) hw₁ hw₂ hww hwr)
                    rw [this] at hvU
                    exact Bool.noConfusion hvU
                  have hle : ¬ (winCount r pi₀ < winCount r pi₁) :=
                    fun h => hnf ((count_lt_iff hp₀ hp₁ r).mp h)
                  simp
                  omega
      | false =>
          cases hv₂ : (s₂ r).2 with
          | true =>
              have hn₁ : ¬ Live C E₁ false r := by
                intro h
                rw [hb₁.mpr h] at hv₁
                exact Bool.noConfusion hv₁
              simp only [mergeFlag, hv₁, hv₂, Bool.false_and, if_false,
                Bool.not_false, Bool.not_true, Bool.and_false, if_true, if_false]
              rw [hc₀, hc₂]
              cases hvU : (sU r).2 with
              | true =>
                  obtain ⟨w, hw₂, hw₁, hww, hwr⟩ :=
                    fresh_of_live_union (E₁ := E₂) (E₂ := E₁)
                      (by rw [Set.union_comm]; exact hbU.mp hvU) hn₁
                  have : winCount r pi₀ < winCount r pi₂ :=
                    (count_lt_iff (E₂ := E₁) (by rw [Set.inter_comm]; exact hp₀) hp₂ r).mpr
                      ⟨w, hw₂, hw₁, hww, hwr⟩
                  simp
                  omega
              | false =>
                  have hnf : ¬ ∃ w ∈ E₂, w ∉ E₁ ∧ w.op = AppOp.winning ∧ w.rep = r := by
                    rintro ⟨w, hw₂, hw₁, hww, hwr⟩
                    have := hbU.mpr (by
                      rw [Set.union_comm]
                      exact live_union_of_fresh htr hsub₂ hclosed₁
                        (hb₂.mp hv₂) hw₂ hw₁ hww hwr)
                    rw [this] at hvU
                    exact Bool.noConfusion hvU
                  have hle : ¬ (winCount r pi₀ < winCount r pi₂) :=
                    fun h => hnf ((count_lt_iff (E₂ := E₁)
                      (by rw [Set.inter_comm]; exact hp₀) hp₂ r).mp h)
                  simp
                  omega
          | false =>
              have hnU : (sU r).2 = false := by
                cases hvU : (sU r).2 with
                | false => rfl
                | true =>
                    exfalso
                    rcases live_of_live_union (hbU.mp hvU) with h | h
                    · rw [hb₁.mpr h] at hv₁; exact Bool.noConfusion hv₁
                    · rw [hb₂.mpr h] at hv₂; exact Bool.noConfusion hv₂
              simp [mergeFlag, hv₁, hv₂, hnU]
    exact Prod.ext hcounter hflag
  rw [heq]
  exact hsU

/-! ## Issuance -/

/-- Issuance: `G(e, O) <=> true`. The source algorithm puts no side condition
on the events a replica may mint. -/
def issuance : Issuance D.toMRDTSig where
  CanIssue := fun _ _ => True

/-- **What this row supplies for the direct route**: `Laws(D_type)` proved
by hand, and the join lemma. -/
theorem directObligations : DirectObligations D issuance :=
  ⟨laws, payloadDetermined, cond_comm, rc_non_comm, fun C _ => joinLemma C⟩

end LeanProofs.Implementations.EnableWinsFlag
