import Sal.MRDTs.Metatheory.Conditioned.RGA_MergeLinearization
import Sal.MRDTs.Metatheory.Conditioned.RGA_SubchainResolve

/-!
# RGA update convergence via the direct canonical-state characterization

Per `CANONICAL_STATE_DESIGN.md`: two per-event-disciplined folds of the same
event set converge because each fold state is observationally a pure function
of the applied event SET — domain = `survivors F`, per-survivor anchor =
`canonAnc F` (the recorded chain resolved against the survivor set), payload =
recorded element.  No swap oracle, no per-prefix `Faithful`, no `DepComp`: this
file does not even import them.

The inductive engine is `CanonInv F s` — the design's `CanonMatch` strengthened
per survivor with the `LiveChain` carrier from `RGA_SubchainResolve` (the
live-filtered recorded chain is the survivor's genuine current ancestor chain).
The bare equation `anc s k = canonAnc F k` is not by itself inductive: the
`Del`-step rehoming needs the cross-chain coherence that `LiveChain` carries,
and its `resolve`-projection (`liveChain_resolve` + domain match) is exactly
`canonAnc` — so `CanonMatch` is the corollary `canonMatch_of_canonInv`.

The per-event discipline (`CanonStepOK`, at each event's OWN application state)
is the honest weakening of `accurate`+`fresh`: an `Ins` needs only that the
live-filtered entries of its recorded chain hang together (`ChainOK` — true
even after a concurrent delete of its anchor, where full `accurate` fails), a
`Del` only that its path resolves to its target's current stored anchor
(`DelOK`).  `chainOK_of_accurate` / `delOK_of_accurate` show `accurate` implies
them; `LiveChain` preservation is what transports them from generation-time
accuracy.  Crucially the discipline is only ever assumed at each event's own
application point — never at reordered prefixes.
-/

set_option maxHeartbeats 1000000

open Classical

namespace RGACanonConvergence

open RGAMergeLinearization (applySeqR applySeqR_nil applySeqR_cons)

/-! ## §1  Survivors of an applied event set, and the canonical anchor -/

/-- `k` is inserted by some event of `F`. -/
def insertedIn (F : List op_t) (k : ℕ) : Prop :=
  ∃ r e p a, (k, r, .Ins e p a) ∈ F

/-- `k` is the target of some delete of `F`. -/
def deletedIn (F : List op_t) (k : ℕ) : Prop :=
  ∃ t r p, (t, r, .Del p k) ∈ F

/-- Survivors of the applied set `F`: inserted in `F` and not deleted in `F`.
A pure function of `F`'s membership. -/
def survP (F : List op_t) (k : ℕ) : Prop := insertedIn F k ∧ ¬ deletedIn F k

/-- The canonical anchor: the first entry of a recorded ancestor chain that
survives `F` (else the root `0`) — the applied-set analog of the merge's
LCA-climb, and the value `resolve` computes on any state whose domain is
`survivors F`. -/
noncomputable def canonAnc (F : List op_t) : List ℕ → ℕ
  | [] => 0
  | c :: cs => if survP F c then c else canonAnc F cs

/-- **The design's `CanonMatch F s`**: `s` is observationally the canonical
state of the applied set `F` — domain = survivors, and each surviving insert
holds its recorded element and its `canonAnc`. -/
def CanonMatch (F : List op_t) (s : concrete_st) : Prop :=
  (∀ c, contains s c = true ↔ survP F c) ∧
  (∀ t r e p a, (t, r, .Ins e p a) ∈ F → survP F t →
      el s t = e ∧ anc s t = canonAnc F (a :: p))

/-- **The inductive engine**: `CanonMatch` strengthened with the state
invariants (`0` unstored, `wf`) and, per surviving insert, the `LiveChain`
carrier — the live entries of its recorded chain are its genuine current
ancestor chain.  `LiveChain`'s `resolve`-projection is `canonAnc`
(`canonMatch_of_canonInv`), and it is what makes the `Del` step inductive. -/
def CanonInv (F : List op_t) (s : concrete_st) : Prop :=
  contains s 0 = false ∧ wf s ∧
  (∀ c, contains s c = true ↔ survP F c) ∧
  (∀ t r e p a, (t, r, .Ins e p a) ∈ F → survP F t →
      el s t = e ∧ LiveChain s t (a :: p))

/-! ## §2  The per-event generation discipline (at own application only) -/

/-- The live-filtered recorded chain hangs together: if any entry survives,
the survivors form a genuine ancestor path from the first one.  Weaker than
`accurate` (which demands every entry live): it is exactly what generation-time
accuracy transports through concurrent deletes (`LiveChain` preservation), and
it survives the deletion of the chain's own head. -/
def ChainOK (s : concrete_st) (L : List ℕ) : Prop :=
  ∀ c cs, liveSub s L = c :: cs → IsAncPath s c cs

/-- A `Del`'s path names its target's current stored anchor (or the root, in
the degenerate root-delete).  Nothing is required of a delete whose target is
already dead and non-root — it is a no-op on live data. -/
def DelOK (s : concrete_st) (p : List ℕ) (x : ℕ) : Prop :=
  (x = 0 → resolve s p = 0) ∧ (contains s x = true → resolve s p = anc s x)

/-- Per-event discipline at the event's OWN application point (`F` = applied
prefix, `s` = its fold).  For an `Ins`: fresh nonzero id, never previously
deleted (no id reuse across the history), absent from every recorded chain
(monotone allocation), and `ChainOK` for its own chain.  For a `Del`:
`DelOK`. -/
def CanonStepOK (F : List op_t) (s : concrete_st) : op_t → Prop
  | (t, _, .Ins _ p a) =>
      t ≠ 0 ∧ contains s t = false ∧ ¬ deletedIn F t ∧ t ∉ a :: p ∧
      (∀ t' r' e' p' a', (t', r', .Ins e' p' a') ∈ F → t ∉ a' :: p') ∧
      ChainOK s (a :: p)
  | (_, _, .Del p x) => DelOK s p x

/-- The whole enumeration is disciplined: each event satisfies `CanonStepOK`
at its own prefix fold. -/
def CanonFoldOK : List op_t → concrete_st → List op_t → Prop
  | _, _, [] => True
  | F, s, o :: rest => CanonStepOK F s o ∧ CanonFoldOK (F ++ [o]) (do_ s o) rest

/-! ## §3  Membership algebra for `survP` and `canonAnc` -/

theorem insertedIn_append (F : List op_t) (o : op_t) (k : ℕ) :
    insertedIn (F ++ [o]) k ↔
      (insertedIn F k ∨ ∃ r e p a, o = (k, r, .Ins e p a)) := by
  unfold insertedIn
  constructor
  · rintro ⟨r, e, p, a, hm⟩
    rcases List.mem_append.mp hm with h | h
    · exact Or.inl ⟨r, e, p, a, h⟩
    · exact Or.inr ⟨r, e, p, a, (List.mem_singleton.mp h).symm⟩
  · rintro (⟨r, e, p, a, hm⟩ | ⟨r, e, p, a, ho⟩)
    · exact ⟨r, e, p, a, List.mem_append.mpr (Or.inl hm)⟩
    · exact ⟨r, e, p, a, List.mem_append.mpr (Or.inr (by rw [ho]; simp))⟩

theorem deletedIn_append (F : List op_t) (o : op_t) (k : ℕ) :
    deletedIn (F ++ [o]) k ↔
      (deletedIn F k ∨ ∃ t r p, o = (t, r, .Del p k)) := by
  unfold deletedIn
  constructor
  · rintro ⟨t, r, p, hm⟩
    rcases List.mem_append.mp hm with h | h
    · exact Or.inl ⟨t, r, p, h⟩
    · exact Or.inr ⟨t, r, p, (List.mem_singleton.mp h).symm⟩
  · rintro (⟨t, r, p, hm⟩ | ⟨t, r, p, ho⟩)
    · exact ⟨t, r, p, List.mem_append.mpr (Or.inl hm)⟩
    · exact ⟨t, r, p, List.mem_append.mpr (Or.inr (by rw [ho]; simp))⟩

/-- Appending an `Ins t` adds `t` to the inserted set and deletes nothing. -/
theorem survP_append_ins (F : List op_t) (t r e : ℕ) (p : List ℕ) (a : ℕ) (c : ℕ) :
    survP (F ++ [(t, r, .Ins e p a)]) c ↔
      ((insertedIn F c ∨ c = t) ∧ ¬ deletedIn F c) := by
  unfold survP
  rw [insertedIn_append, deletedIn_append]
  constructor
  · rintro ⟨hi | ⟨r', e', p', a', ho⟩, hnd⟩
    · exact ⟨Or.inl hi, fun h => hnd (Or.inl h)⟩
    · injection ho with h1 h2
      exact ⟨Or.inr h1.symm, fun h => hnd (Or.inl h)⟩
  · rintro ⟨hi | rfl, hnd⟩
    · refine ⟨Or.inl hi, ?_⟩
      rintro (h | ⟨t', r', p', ho⟩)
      · exact hnd h
      · exact app_op_t.noConfusion (congrArg (·.2.2) ho)
    · refine ⟨Or.inr ⟨r, e, p, a, rfl⟩, ?_⟩
      rintro (h | ⟨t', r', p', ho⟩)
      · exact hnd h
      · exact app_op_t.noConfusion (congrArg (·.2.2) ho)

/-- Appending a `Del x` removes `x` from the survivors and inserts nothing. -/
theorem survP_append_del (F : List op_t) (t r x : ℕ) (p : List ℕ) (c : ℕ) :
    survP (F ++ [(t, r, .Del p x)]) c ↔ (survP F c ∧ c ≠ x) := by
  unfold survP
  rw [insertedIn_append, deletedIn_append]
  constructor
  · rintro ⟨hi | ⟨r', e', p', a', ho⟩, hnd⟩
    · refine ⟨⟨hi, fun h => hnd (Or.inl h)⟩, ?_⟩
      rintro rfl
      exact hnd (Or.inr ⟨t, r, p, rfl⟩)
    · exact app_op_t.noConfusion (congrArg (·.2.2) ho)
  · rintro ⟨⟨hi, hnd⟩, hcx⟩
    refine ⟨Or.inl hi, ?_⟩
    rintro (h | ⟨t', r', p', ho⟩)
    · exact hnd h
    · injection ho with h1 h2
      injection h2 with h3 h4
      exact hcx (app_op_t.Del.inj h4).2.symm

/-- `survP` depends only on membership. -/
theorem survP_congr (F₁ F₂ : List op_t) (hmem : ∀ o, o ∈ F₁ ↔ o ∈ F₂) (k : ℕ) :
    survP F₁ k ↔ survP F₂ k := by
  unfold survP insertedIn deletedIn
  constructor <;> rintro ⟨⟨r, e, p, a, hi⟩, hnd⟩
  · exact ⟨⟨r, e, p, a, (hmem _).mp hi⟩,
      fun ⟨t', r', p', h⟩ => hnd ⟨t', r', p', (hmem _).mpr h⟩⟩
  · exact ⟨⟨r, e, p, a, (hmem _).mpr hi⟩,
      fun ⟨t', r', p', h⟩ => hnd ⟨t', r', p', (hmem _).mp h⟩⟩

/-- `canonAnc` depends only on membership. -/
theorem canonAnc_congr (F₁ F₂ : List op_t) (hmem : ∀ o, o ∈ F₁ ↔ o ∈ F₂) :
    ∀ L : List ℕ, canonAnc F₁ L = canonAnc F₂ L := by
  intro L
  induction L with
  | nil => rfl
  | cons c cs ih =>
    simp only [canonAnc]
    by_cases h : survP F₁ c
    · rw [if_pos h, if_pos ((survP_congr F₁ F₂ hmem c).mp h)]
    · rw [if_neg h, if_neg (fun h' => h ((survP_congr F₁ F₂ hmem c).mpr h')), ih]

/-! ## §4  `resolve`/`liveSub` helpers and live-guarded chain transport -/

/-- Members of the live sublist are live. -/
theorem liveSub_live (s : concrete_st) (L : List ℕ) (c : ℕ) (hc : c ∈ liveSub s L) :
    contains s c = true :=
  (List.mem_filter.mp hc).2

/-- `resolve` of a chain with no live entry is the root. -/
theorem resolve_of_liveSub_nil (s : concrete_st) (L : List ℕ)
    (h : liveSub s L = []) : resolve s L = 0 := by
  rw [← resolve_liveSub s L, h]; rfl

/-- `resolve` of a chain is the head of its live sublist. -/
theorem resolve_of_liveSub_cons (s : concrete_st) (L : List ℕ) (c : ℕ) (cs : List ℕ)
    (h : liveSub s L = c :: cs) : resolve s L = c := by
  rw [← resolve_liveSub s L, h]
  exact resolve_live_head s c cs (liveSub_live s L c (by rw [h]; simp))

/-- On a state whose domain is the `F`-survivor set, `resolve` computes
`canonAnc F` on every chain. -/
theorem resolve_eq_canonAnc (F : List op_t) (s : concrete_st)
    (hdom : ∀ c, contains s c = true ↔ survP F c) :
    ∀ L : List ℕ, resolve s L = canonAnc F L := by
  intro L
  induction L with
  | nil => rfl
  | cons c cs ih =>
    by_cases h : survP F c
    · have hcc : contains s c = true := (hdom c).mpr h
      simp only [resolve, canonAnc]
      rw [if_pos hcc, if_pos h]
    · have hcc : contains s c = false := by
        cases hb : contains s c with
        | true => exact absurd ((hdom c).mp hb) h
        | false => rfl
      simp only [resolve, canonAnc]
      rw [if_neg (by rw [hcc]; exact Bool.false_ne_true), if_neg h]
      exact ih

/-- Chain transport when `anc`/containment agree on live nodes (the leaf
included).  The `∀ k`-strong `isAncPath_of_eq` does not apply when dead
mapping junk changes (a `Del` of a dead target rewrites dead anchors). -/
theorem isAncPath_congr_live (s s' : concrete_st)
    (Ha : ∀ c, contains s c = true → anc s' c = anc s c)
    (Hc : ∀ c, contains s c = true → contains s' c = true) :
    ∀ (L : List ℕ) (z : ℕ), contains s z = true → IsAncPath s z L →
      IsAncPath s' z L := by
  intro L
  induction L with
  | nil =>
    intro z hz h
    simp only [IsAncPath] at h ⊢
    rw [Ha z hz]; exact h
  | cons p ps ih =>
    intro z hz h
    simp only [IsAncPath] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨(Ha z hz).trans h1, Hc p h2, ih p h2 h3⟩

/-! ## §5  Projection to the design's `CanonMatch`, and its `eq`-plumbing -/

/-- `CanonInv` projects to the design's `CanonMatch`: the surviving insert's
anchor is `resolve` of its recorded chain (`liveChain_resolve`), and `resolve`
against the survivor domain is `canonAnc` (`resolve_eq_canonAnc`). -/
theorem canonMatch_of_canonInv (F : List op_t) (s : concrete_st)
    (h : CanonInv F s) : CanonMatch F s := by
  obtain ⟨h0, hwf, hdom, hins⟩ := h
  refine ⟨hdom, ?_⟩
  intro t r e p a hm hs
  obtain ⟨hel, hlc⟩ := hins t r e p a hm hs
  refine ⟨hel, ?_⟩
  rw [← liveChain_resolve s t (a :: p) hlc]
  exact resolve_eq_canonAnc F s hdom (a :: p)

/-- `CanonMatch` is `eq`-respecting. -/
theorem canonMatch_eq_respecting (F : List op_t) (s s' : concrete_st)
    (h : CanonMatch F s) (he : eq s s') : CanonMatch F s' := by
  obtain ⟨hdom, hanc⟩ := h
  refine ⟨?_, ?_⟩
  · intro c
    rw [← (he c).1]
    exact hdom c
  · intro t r e p a hm hs
    have hks : contains s t = true := (hdom t).mpr hs
    obtain ⟨hel, hanc'⟩ := hanc t r e p a hm hs
    have hsel : sel s t = sel s' t := (he t).2 hks
    constructor
    · show (sel s' t).1 = e
      rw [← hsel]; exact hel
    · show (sel s' t).2 = canonAnc F (a :: p)
      rw [← hsel]; exact hanc'

/-- **Two canonical states of the same event set are observationally equal** —
the per-id extensional glue (the update analog of `eq_merge2_of_branchInv2`'s
per-id reduction): same domain (= survivors), same element and anchor
(= recorded payload and `canonAnc`) on every survivor. -/
theorem eq_of_canonMatch2 (F₁ F₂ : List op_t) (s s' : concrete_st)
    (hmem : ∀ o, o ∈ F₁ ↔ o ∈ F₂)
    (h1 : CanonMatch F₁ s) (h2 : CanonMatch F₂ s') : eq s s' := by
  obtain ⟨hdom1, hanc1⟩ := h1
  obtain ⟨hdom2, hanc2⟩ := h2
  intro k
  have hdiff : contains s k = true ↔ contains s' k = true := by
    rw [hdom1 k, hdom2 k]
    exact survP_congr F₁ F₂ hmem k
  refine ⟨?_, ?_⟩
  · cases hb : contains s k with
    | true => exact (hdiff.mp hb).symm
    | false =>
      cases hb' : contains s' k with
      | true => rw [hdiff.mpr hb'] at hb; exact Bool.noConfusion hb
      | false => rfl
  · intro hk
    have hs1 : survP F₁ k := (hdom1 k).mp hk
    obtain ⟨⟨r, e, p, a, hi1⟩, _⟩ := id hs1
    have hi2 : (k, r, .Ins e p a) ∈ F₂ := (hmem _).mp hi1
    have hs2 : survP F₂ k := (survP_congr F₁ F₂ hmem k).mp hs1
    obtain ⟨hel1, ha1⟩ := hanc1 k r e p a hi1 hs1
    obtain ⟨hel2, ha2⟩ := hanc2 k r e p a hi2 hs2
    show sel s k = sel s' k
    rw [show sel s k = (el s k, anc s k) from rfl,
        show sel s' k = (el s' k, anc s' k) from rfl,
        hel1, hel2, ha1, ha2, canonAnc_congr F₁ F₂ hmem (a :: p)]

/-! ## §6  Base case and the `Ins` step -/

/-- `CanonInv` holds at the empty applied set and the initial state. -/
theorem canonInv_init : CanonInv [] init_st := by
  refine ⟨by simp [init_st], ?_, ?_, ?_⟩
  · intro t ht
    simp [init_st] at ht
  · intro c
    constructor
    · intro hc
      simp [init_st] at hc
    · rintro ⟨⟨r, e, p, a, hm⟩, _⟩
      simp at hm
  · intro t r e p a hm _
    simp at hm

/-- **Step `Ins` (the design's `canonMatch_doIns`).**  A disciplined fresh
insert extends the canonical invariant: the new node's stored anchor is
`resolve` of its recorded chain (= the nearest `F`-survivor), its live-filtered
chain is genuine (`ChainOK`), and every prior survivor's carrier is untouched
(`liveChain_doIns`, reused). -/
theorem canonInv_doIns (F : List op_t) (s : concrete_st) (t r e a : ℕ) (p : List ℕ)
    (hinv : CanonInv F s) (hok : CanonStepOK F s (t, r, .Ins e p a)) :
    CanonInv (F ++ [(t, r, .Ins e p a)]) (do_ s (t, r, .Ins e p a)) := by
  obtain ⟨h0, hwf, hdom, hins⟩ := hinv
  obtain ⟨ht0, htf, htnd, htnp, htnpF, hcok⟩ := hok
  have hdo : do_ s (t, r, .Ins e p a) = upd s t (e, resolve s (a :: p)) := by
    simp only [do_]
  set v := resolve s (a :: p) with hv
  have hvlive : v = 0 ∨ contains s v = true := resolve_zero_or_live s (a :: p)
  -- (a) root sentinel stays absent
  have h0' : contains (do_ s (t, r, .Ins e p a)) 0 = false := by
    rw [hdo, lemma_InDomUpd1, h0, Bool.or_false]
    simp [ht0]
  -- (b) wf preserved: the new anchor is 0-or-live, old nodes untouched
  have hwf' : wf (do_ s (t, r, .Ins e p a)) := by
    rw [hdo]
    intro k hk
    by_cases hkt : k = t
    · have hanck : anc (upd s t (e, v)) k = v := by
        rw [hkt]; simp only [anc]; rw [lemma_SelUpd1]
      rw [hanck]
      rcases hvlive with hv0 | hvl
      · exact Or.inl hv0
      · refine Or.inr ?_
        rw [lemma_InDomUpd1, hvl]; simp only [Bool.or_true]
    · have htk : t ≠ k := fun e' => hkt e'.symm
      have hck : contains s k = true := by
        rw [lemma_InDomUpd1] at hk
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hk
        rcases hk with hh | hh
        · exact absurd hh htk
        · exact hh
      have hanck : anc (upd s t (e, v)) k = anc s k := by
        simp only [anc]
        rw [lemma_SelUpd2 s k t (e, v) (by simp only [bne_iff_ne, ne_eq]; exact htk)]
      rw [hanck]
      rcases hwf k hck with hanc0 | hancl
      · exact Or.inl hanc0
      · refine Or.inr ?_
        rw [lemma_InDomUpd1, hancl]; simp only [Bool.or_true]
  -- (c) domain = survivors of F ++ [Ins t]
  have hdom' : ∀ c, contains (do_ s (t, r, .Ins e p a)) c = true ↔
      survP (F ++ [(t, r, .Ins e p a)]) c := by
    intro c
    rw [hdo, lemma_InDomUpd1, survP_append_ins]
    constructor
    · intro h
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with rfl | hsc
      · exact ⟨Or.inr rfl, htnd⟩
      · obtain ⟨hi, hnd⟩ := (hdom c).mp hsc
        exact ⟨Or.inl hi, hnd⟩
    · rintro ⟨hi | rfl, hnd⟩
      · have hc : contains s c = true := (hdom c).mpr ⟨hi, hnd⟩
        rw [hc, Bool.or_true]
      · simp
  refine ⟨h0', hwf', hdom', ?_⟩
  -- (d) per-survivor payload + LiveChain
  intro t' r' e' p' a' hm hs
  rcases List.mem_append.mp hm with hmF | hmNew
  · -- an old survivor: untouched by the fresh upd
    have ht't : t' ≠ t := by
      intro hEq
      have hsF : survP F t' :=
        ⟨⟨r', e', p', a', hmF⟩, ((survP_append_ins F t r e p a t').mp hs).2⟩
      have hct' : contains s t' = true := (hdom t').mpr hsF
      rw [hEq, htf] at hct'
      exact Bool.noConfusion hct'
    have hsF : survP F t' :=
      ⟨⟨r', e', p', a', hmF⟩, ((survP_append_ins F t r e p a t').mp hs).2⟩
    obtain ⟨hel, hlc⟩ := hins t' r' e' p' a' hmF hsF
    constructor
    · rw [hdo]
      show (sel (upd s t (e, v)) t').1 = e'
      rw [lemma_SelUpd2 s t' t (e, v)
            (by simp only [bne_iff_ne, ne_eq]; exact fun h => ht't h.symm)]
      exact hel
    · exact liveChain_doIns s t' (a' :: p') t r e a p hlc ht0 htf
        (htnpF t' r' e' p' a' hmF)
  · -- the freshly inserted node
    have hEq := List.mem_singleton.mp hmNew
    injection hEq with h1 h2
    injection h2 with h3 h4
    injection h4 with h5 h6 h7
    rw [h1, h5, h6, h7]
    constructor
    · rw [hdo]
      show (sel (upd s t (e, v)) t).1 = e
      rw [lemma_SelUpd1]
    · refine ⟨h0', ?_, ?_⟩
      · rw [hdo, lemma_InDomUpd1]; simp
      · have hanc_t : anc (do_ s (t, r, .Ins e p a)) t = v := by
          rw [hdo]; show (sel (upd s t (e, v)) t).2 = v; rw [lemma_SelUpd1]
        have hlsub : liveSub (do_ s (t, r, .Ins e p a)) (a :: p) = liveSub s (a :: p) := by
          unfold liveSub
          apply List.filter_congr
          intro c hc
          have hct : c ≠ t := fun hEq' => htnp (hEq' ▸ hc)
          rw [hdo]
          show contains (upd s t (e, v)) c = contains s c
          exact lemma_InDomUpd2 s c t (e, v)
            (by simp only [bne_iff_ne, ne_eq]; exact fun h => hct h.symm)
        rw [hlsub]
        cases hls : liveSub s (a :: p) with
        | nil =>
          simp only [IsAncPath]
          rw [hanc_t, hv]
          exact resolve_of_liveSub_nil s (a :: p) hls
        | cons c cs =>
          have hcl : contains s c = true := liveSub_live s (a :: p) c (by rw [hls]; simp)
          have hct : c ≠ t := fun hEq' => by
            rw [hEq', htf] at hcl; exact Bool.noConfusion hcl
          have hres : v = c := by
            rw [hv]; exact resolve_of_liveSub_cons s (a :: p) c cs hls
          simp only [IsAncPath]
          refine ⟨hanc_t.trans hres, ?_, ?_⟩
          · rw [hdo, lemma_InDomUpd1, hcl]; simp
          · have hpath : IsAncPath s c cs := hcok c cs hls
            rw [hdo]
            exact isAncPath_upd s t (e, v) htf cs c hct hpath

/-! ## §7  The `Del` step: rehoming = climbing the reduced survivor set -/

/-- **Step `Del` (the design's `canonMatch_doDel`).**  Deleting `x` removes it
from the survivors and rehomes its children to `resolve s p = anc s x`; each
survivor's live-filtered chain is spliced across `x` — exactly
`isAncPath_surgery` (the single-sided rehoming lemma reused from the
subchain-resolution development).  Degenerate targets (root, already-dead) are
no-ops on live data. -/
theorem canonInv_doDel (F : List op_t) (s : concrete_st) (t r x : ℕ) (p : List ℕ)
    (hinv : CanonInv F s) (hok : CanonStepOK F s (t, r, .Del p x)) :
    CanonInv (F ++ [(t, r, .Del p x)]) (do_ s (t, r, .Del p x)) := by
  obtain ⟨h0, hwf, hdom, hins⟩ := hinv
  have hok' : DelOK s p x := hok
  obtain ⟨hres0, hresx⟩ := hok'
  have hc : ∀ c, contains (do_ s (t, r, .Del p x)) c = (contains s c && (c != x)) :=
    fun c => contains_doDel s t r x p c
  have ha : ∀ c, anc (do_ s (t, r, .Del p x)) c
      = if anc s c = x then resolve s p else anc s c :=
    fun c => anc_doDel s t r x p c
  have hel' : ∀ c, el (do_ s (t, r, .Del p x)) c = el s c :=
    fun c => el_doDel s t r x p c
  set s' := do_ s (t, r, .Del p x) with hs'def
  have hdom' : ∀ c, contains s' c = true ↔ survP (F ++ [(t, r, .Del p x)]) c := by
    intro c
    rw [hc c, survP_append_del, Bool.and_eq_true, bne_iff_ne]
    exact and_congr_left' (hdom c)
  have hmemF : ∀ t' r' e' p' a', (t', r', .Ins e' p' a') ∈ F ++ [(t, r, .Del p x)] →
      (t', r', .Ins e' p' a') ∈ F := by
    intro t' r' e' p' a' hm
    rcases List.mem_append.mp hm with h | h
    · exact h
    · exact absurd (List.mem_singleton.mp h)
        (by intro hEq; exact app_op_t.noConfusion (congrArg (·.2.2) hEq))
  by_cases hx0 : x = 0
  · -- degenerate root delete: resolve s p = 0, nothing live moves
    subst hx0
    have hr0 : resolve s p = 0 := hres0 rfl
    have haeq : ∀ c, anc s' c = anc s c := by
      intro c
      rw [ha c]
      by_cases h : anc s c = 0
      · rw [if_pos h, hr0, h]
      · rw [if_neg h]
    have hceq : ∀ c, contains s' c = contains s c := by
      intro c
      rw [hc c]
      by_cases h : c = 0
      · subst h; rw [h0]; rfl
      · have hb : (c != 0) = true := by simp [h]
        rw [hb, Bool.and_true]
    refine ⟨by rw [hceq 0]; exact h0, ?_, hdom', ?_⟩
    · intro k hk
      rw [hceq k] at hk
      rw [haeq k, hceq (anc s k)]
      exact hwf k hk
    · intro t' r' e' p' a' hm hs
      have hsF : survP F t' := ((survP_append_del F t r 0 p t').mp hs).1
      obtain ⟨hel, hlc⟩ := hins t' r' e' p' a' (hmemF t' r' e' p' a' hm) hsF
      obtain ⟨_, hlt', hpath⟩ := hlc
      refine ⟨(hel' t').trans hel,
        ⟨by rw [hceq 0]; exact h0, by rw [hceq t']; exact hlt', ?_⟩⟩
      have hlsub : liveSub s' (a' :: p') = liveSub s (a' :: p') := by
        unfold liveSub
        exact List.filter_congr (fun c _ => hceq c)
      rw [hlsub]
      exact isAncPath_of_eq s s' haeq (fun c hcc => by rw [hceq c]; exact hcc)
        (liveSub s (a' :: p')) t' hpath
  · by_cases hxl : contains s x = true
    · -- live target: splice every survivor's chain across x
      have hres : resolve s p = anc s x := hresx hxl
      have hxsurv : survP F x := (hdom x).mp hxl
      obtain ⟨⟨rx, ex, px, ax, hmx⟩, _⟩ := id hxsurv
      obtain ⟨_, hlcx⟩ := hins x rx ex px ax hmx hxsurv
      obtain ⟨_, _, hpathx⟩ := hlcx
      have hancx_ne : anc s x ≠ x := by
        intro hEq
        exact hx0 (isAncPath_self s (liveSub s (ax :: px)) x hpathx hEq)
      have hancx_stat : anc s x = 0 ∨ contains s (anc s x) = true := hwf x hxl
      refine ⟨by rw [hc 0, h0]; rfl, ?_, hdom', ?_⟩
      · intro k hk
        rw [hc k, Bool.and_eq_true] at hk
        obtain ⟨hck, hkx⟩ := hk
        rw [ha k]
        by_cases hak : anc s k = x
        · rw [if_pos hak, hres]
          rcases hancx_stat with h | h
          · exact Or.inl h
          · refine Or.inr ?_
            rw [hc (anc s x), h, Bool.true_and, bne_iff_ne]
            exact hancx_ne
        · rw [if_neg hak]
          rcases hwf k hck with h | h
          · exact Or.inl h
          · refine Or.inr ?_
            rw [hc (anc s k), h, Bool.true_and, bne_iff_ne]
            exact hak
      · intro t' r' e' p' a' hm hs
        obtain ⟨hsF, ht'x⟩ := (survP_append_del F t r x p t').mp hs
        obtain ⟨hel, hlc⟩ := hins t' r' e' p' a' (hmemF t' r' e' p' a' hm) hsF
        obtain ⟨_, hlt', hpath⟩ := hlc
        refine ⟨(hel' t').trans hel, ⟨by rw [hc 0, h0]; rfl, ?_, ?_⟩⟩
        · rw [hc t', hlt']
          simp [ht'x]
        · have hfilter : liveSub s' (a' :: p')
              = (liveSub s (a' :: p')).filter (fun c => c != x) := by
            unfold liveSub
            rw [List.filter_filter]
            apply List.filter_congr
            intro c _
            show contains s' c = ((c != x) && contains s c)
            rw [hc c]
            exact Bool.and_comm _ _
          rw [hfilter]
          exact isAncPath_surgery s s' x (resolve s p) hx0 hres hc ha
            (liveSub s (a' :: p')) t' hpath
    · -- dead non-root target: a no-op on live data (wf forbids live anchors at x)
      have hxdead : contains s x = false := by
        cases h : contains s x with
        | true => exact absurd h hxl
        | false => rfl
      have hane : ∀ c, contains s c = true → anc s c ≠ x := by
        intro c hcc hEq
        rcases hwf c hcc with h | h
        · exact hx0 (hEq ▸ h)
        · rw [hEq, hxdead] at h; exact Bool.noConfusion h
      have haeq : ∀ c, contains s c = true → anc s' c = anc s c := by
        intro c hcc
        rw [ha c, if_neg (hane c hcc)]
      have hceq : ∀ c, contains s' c = contains s c := by
        intro c
        rw [hc c]
        by_cases h : c = x
        · subst h; rw [hxdead]; rfl
        · have hb : (c != x) = true := by simp [h]
          rw [hb, Bool.and_true]
      refine ⟨by rw [hceq 0]; exact h0, ?_, hdom', ?_⟩
      · intro k hk
        rw [hceq k] at hk
        rw [haeq k hk, hceq (anc s k)]
        exact hwf k hk
      · intro t' r' e' p' a' hm hs
        have hsF : survP F t' := ((survP_append_del F t r x p t').mp hs).1
        obtain ⟨hel, hlc⟩ := hins t' r' e' p' a' (hmemF t' r' e' p' a' hm) hsF
        obtain ⟨_, hlt', hpath⟩ := hlc
        refine ⟨(hel' t').trans hel,
          ⟨by rw [hceq 0]; exact h0, by rw [hceq t']; exact hlt', ?_⟩⟩
        have hlsub : liveSub s' (a' :: p') = liveSub s (a' :: p') := by
          unfold liveSub
          exact List.filter_congr (fun c _ => hceq c)
        rw [hlsub]
        exact isAncPath_congr_live s s' haeq (fun c hcc => by rw [hceq c]; exact hcc)
          (liveSub s (a' :: p')) t' hlt' hpath

/-! ## §8  Step corollaries at the `CanonMatch` level (the design's names) -/

/-- The design's `canonMatch_doIns`.  Stated over the carrier invariant
`CanonInv` (the bare `anc = canonAnc` equation is not by itself inductive);
the conclusion is the design's `CanonMatch` of the extended set. -/
theorem canonMatch_doIns (F : List op_t) (s : concrete_st) (t r e a : ℕ) (p : List ℕ)
    (hinv : CanonInv F s) (hok : CanonStepOK F s (t, r, .Ins e p a)) :
    CanonMatch (F ++ [(t, r, .Ins e p a)]) (do_ s (t, r, .Ins e p a)) :=
  canonMatch_of_canonInv _ _ (canonInv_doIns F s t r e a p hinv hok)

/-- The design's `canonMatch_doDel`. -/
theorem canonMatch_doDel (F : List op_t) (s : concrete_st) (t r x : ℕ) (p : List ℕ)
    (hinv : CanonInv F s) (hok : CanonStepOK F s (t, r, .Del p x)) :
    CanonMatch (F ++ [(t, r, .Del p x)]) (do_ s (t, r, .Del p x)) :=
  canonMatch_of_canonInv _ _ (canonInv_doDel F s t r x p hinv hok)

/-! ## §9  The fold and the headline -/

/-- **`canon_fold`:** a disciplined enumeration folds to the canonical state
of its applied set — induction along the enumeration, steps by §6/§7.  The
per-event discipline is consumed at each event's OWN application point only;
no claim is ever made about a not-yet-applied event. -/
theorem canon_fold : ∀ (π F : List op_t) (s : concrete_st),
    CanonInv F s → CanonFoldOK F s π → CanonInv (F ++ π) (applySeqR s π) := by
  intro π
  induction π with
  | nil =>
    intro F s h _
    rw [List.append_nil]
    exact h
  | cons o rest ih =>
    intro F s h hok
    have hok' : CanonStepOK F s o ∧ CanonFoldOK (F ++ [o]) (do_ s o) rest := hok
    obtain ⟨hstep, hrest⟩ := hok'
    have h' : CanonInv (F ++ [o]) (do_ s o) := by
      obtain ⟨t, r, op⟩ := o
      cases op with
      | Ins e p a => exact canonInv_doIns F s t r e a p h hstep
      | Del p x => exact canonInv_doDel F s t r x p h hstep
    rw [applySeqR_cons, show F ++ o :: rest = (F ++ [o]) ++ rest by simp]
    exact ih (F ++ [o]) (do_ s o) h' hrest

/-- **HEADLINE — RGA update convergence via the canonical state.**  Two
disciplined enumerations of the same event set fold from `init_st` to
observationally equal states.

Premises: the per-event generation discipline at each event's own application
point (`CanonFoldOK`, along each enumeration) + set-equality of the two
enumerations.  Nothing else: the reachable-state facts `ReachInv` supplied
(`contains 0 = false`, `wf`) are threaded inside `CanonInv`, and the
`loOnA`-respecting/backward-closure conditions of the execution model are what
make `CanonFoldOK` satisfiable, not separate inputs.  NO swap oracle, NO
per-prefix `Faithful`, NO `DepComp` — none are even imported. -/
theorem RGA_update_convergence_canon (π₁ π₂ : List op_t)
    (hmem : ∀ o, o ∈ π₁ ↔ o ∈ π₂)
    (h₁ : CanonFoldOK [] init_st π₁) (h₂ : CanonFoldOK [] init_st π₂) :
    eq (applySeqR init_st π₁) (applySeqR init_st π₂) := by
  have c₁ := canon_fold π₁ [] init_st canonInv_init h₁
  have c₂ := canon_fold π₂ [] init_st canonInv_init h₂
  rw [List.nil_append] at c₁ c₂
  exact eq_of_canonMatch2 π₁ π₂ _ _ hmem
    (canonMatch_of_canonInv π₁ _ c₁) (canonMatch_of_canonInv π₂ _ c₂)

/-! ## §10  The discipline is weaker than `accurate` (documentation lemmas) -/

/-- `accurate` at application implies `ChainOK` there: an accurate chain is
fully live, hence equal to its own live sublist and genuine from its head.
(`ChainOK` moreover survives concurrent deletes of chain entries — including
the anchor itself — where `accurate` fails.) -/
theorem chainOK_of_accurate (s : concrete_st) (t r e a : ℕ) (p : List ℕ)
    (h0 : contains s 0 = false)
    (hacc : accurate (t, r, .Ins e p a) s) : ChainOK s (a :: p) := by
  simp only [accurate, opLeaf, opPath] at hacc
  intro c cs heq
  rcases hacc with ⟨ha0, hp⟩ | ⟨hal, hpath⟩
  · subst ha0; subst hp
    have hnil : liveSub s [0] = [] := by
      unfold liveSub
      rw [List.filter_cons, List.filter_nil, h0]
      simp
    rw [hnil] at heq
    exact absurd heq (by simp)
  · have hall : ∀ y ∈ a :: p, contains s y = true := by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact hal
      · exact isAncPath_mem s a p hpath y hy'
    have hfull : liveSub s (a :: p) = a :: p :=
      List.filter_eq_self.mpr (fun y hy => hall y hy)
    rw [hfull] at heq
    injection heq with h1 h2
    rw [← h1, ← h2]
    exact hpath

/-- `accurate` at application implies `DelOK` there. -/
theorem delOK_of_accurate (s : concrete_st) (t r x : ℕ) (p : List ℕ)
    (h0 : contains s 0 = false)
    (hacc : accurate (t, r, .Del p x) s) : DelOK s p x := by
  simp only [accurate, opLeaf, opPath] at hacc
  rcases hacc with ⟨hx0, hp⟩ | ⟨hxl, hpath⟩
  · subst hp
    refine ⟨fun _ => rfl, ?_⟩
    intro hcx
    rw [hx0, h0] at hcx
    exact Bool.noConfusion hcx
  · refine ⟨?_, fun _ => isAncPath_resolve s x p hpath⟩
    intro hEq
    rw [hEq, h0] at hxl
    exact Bool.noConfusion hxl

/-! ## §11  Axiom audit -/

#print axioms canonInv_doIns
#print axioms canonInv_doDel
#print axioms canonMatch_doIns
#print axioms canonMatch_doDel
#print axioms canon_fold
#print axioms RGA_update_convergence_canon

end RGACanonConvergence
