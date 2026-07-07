import Sal.MRDTs.RGA_Tombstone_Free.RGA_Tombstone_Free_MRDT

/-!
# Key Lemma: a captured live ancestor chain resolves to the current anchor

Let `pre` be the genuine ancestor chain of `x`, captured at a state `s0` where
`x` and every entry of `pre` were live (`IsAncPath s0 x pre`). Then in any
state `s` reachable from `s0` by post-capture steps that (i) never delete `x`,
(ii) use accurate paths on deletes, and (iii) never insert an id occurring in
`pre` (ids are never reused — in the model this follows from monotone
allocation), we have `resolve s pre = anc s x`: the first entry of `pre` live
in `s` is exactly `x`'s current stored anchor.

Mechanization strategy (the paper proof's cases (a)/(b)/(c) are absorbed into
one inductive invariant): `LiveChain s x pre` states that the entries of `pre`
that are live in `s` form the *genuine current* ancestor chain of `x`. It
holds at capture (all entries live), is preserved by every post-capture step
(`Ins` adds only fresh descendants — case (c); `Del` removes an entry
permanently and splices the chain across it — case (b); no other node can
enter the chain — case (a)), and it immediately yields the conclusion, since
`resolve` skips dead entries and `IsAncPath`'s head is the stored anchor.
-/

set_option maxHeartbeats 1000000

/-! ## The invariant -/

/-- The entries of the captured path `pre` still live in `s`, in order. -/
def liveSub (s : concrete_st) (pre : List ℕ) : List ℕ :=
  pre.filter (fun c => contains s c)

/-- Invariant carried from capture to use: the root sentinel is not stored,
`x` is live, and the live entries of `pre` are the genuine current ancestor
chain of `x`. -/
def LiveChain (s : concrete_st) (x : ℕ) (pre : List ℕ) : Prop :=
  contains s 0 = false ∧ contains s x = true ∧ IsAncPath s x (liveSub s pre)

/-! ## From the invariant to the conclusion -/

/-- `resolve` ignores dead candidates: resolving `pre` is resolving its live
sublist. -/
theorem resolve_liveSub (s : concrete_st) :
    ∀ pre : List ℕ, resolve s (liveSub s pre) = resolve s pre := by
  intro pre
  induction pre with
  | nil => rfl
  | cons c rest ih =>
    simp only [liveSub, List.filter_cons] at ih ⊢
    cases hc : contains s c with
    | true =>
      rw [if_pos rfl]
      rw [resolve_live_head s c _ hc, resolve_live_head s c rest hc]
    | false =>
      rw [if_neg (by simp)]
      rw [resolve_dead_head s c rest hc]
      exact ih

/-- The invariant yields the Key Lemma's conclusion: the first live entry of
`pre` is the current stored anchor of `x`. -/
theorem liveChain_resolve (s : concrete_st) (x : ℕ) (pre : List ℕ)
    (h : LiveChain s x pre) : resolve s pre = anc s x := by
  obtain ⟨_, _, hpath⟩ := h
  rw [← resolve_liveSub s pre]
  exact isAncPath_resolve s x (liveSub s pre) hpath

/-! ## The invariant holds at capture -/

/-! ## Preservation: `Ins` (paper case (c))

A fresh insert attaches a new id as a descendant; it touches neither the
containment nor the anchor of any pre-existing node, so the chain is intact.
The one honest extra hypothesis is `t ∉ pre`: ids are never reused, so a fresh
id cannot resurrect a dead entry of the captured path. (In the execution model
this follows from monotone allocation: every entry of `pre` is below `x`'s id
and a fresh id exceeds every id ever seen.) -/

/-- A genuine chain avoiding a fresh key survives an `upd` at that key. -/
theorem isAncPath_upd (s : concrete_st) (t : ℕ) (v : ℕ × ℕ)
    (ht : contains s t = false) :
    ∀ (L : List ℕ) (z : ℕ), z ≠ t → IsAncPath s z L → IsAncPath (upd s t v) z L := by
  intro L
  induction L with
  | nil =>
    intro z hz h
    simp only [IsAncPath] at h ⊢
    have hsel : sel (upd s t v) z = sel s z :=
      lemma_SelUpd2 s z t v (by simp only [bne_iff_ne, ne_eq]; exact fun e => hz e.symm)
    simp only [anc, hsel]
    exact h
  | cons p ps ih =>
    intro z hz h
    simp only [IsAncPath] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    have hsel : sel (upd s t v) z = sel s z :=
      lemma_SelUpd2 s z t v (by simp only [bne_iff_ne, ne_eq]; exact fun e => hz e.symm)
    refine ⟨?_, ?_, ?_⟩
    · simp only [anc, hsel]; exact h1
    · rw [lemma_InDomUpd1, h2]; simp
    · have hpt : p ≠ t := by
        intro e; rw [e, ht] at h2; exact Bool.noConfusion h2
      exact ih p hpt h3

/-- `LiveChain` is preserved by a fresh `Ins` whose id is not a reused id of
the captured path. -/
theorem liveChain_doIns (s : concrete_st) (x : ℕ) (pre : List ℕ)
    (t r e a : ℕ) (pa : List ℕ)
    (h : LiveChain s x pre) (ht0 : t ≠ 0) (htf : contains s t = false)
    (htp : t ∉ pre) :
    LiveChain (do_ s (t, r, .Ins e pa a)) x pre := by
  obtain ⟨h0, hx, hpath⟩ := h
  have hdo : do_ s (t, r, .Ins e pa a) = upd s t (e, resolve s (a :: pa)) := by
    simp only [do_]
  rw [LiveChain, hdo]
  set v := (e, resolve s (a :: pa)) with hv
  have hfilter : liveSub (upd s t v) pre = liveSub s pre := by
    unfold liveSub
    apply List.filter_congr
    intro c hc
    show contains (upd s t v) c = contains s c
    have hct : t ≠ c := fun e' => htp (e' ▸ hc)
    rw [lemma_InDomUpd1]
    simp [hct]
  refine ⟨?_, ?_, ?_⟩
  · rw [lemma_InDomUpd1, h0]
    simp [ht0]
  · rw [lemma_InDomUpd1, hx]; simp
  · rw [hfilter]
    have hxt : x ≠ t := fun e' => by rw [e', htf] at hx; exact Bool.noConfusion hx
    exact isAncPath_upd s t v htf (liveSub s pre) x hxt hpath

/-! ## Preservation: `Del` (paper cases (a) and (b))

Deleting `y ≠ x` with an accurate path removes `y` permanently (tombstone-free
deletion never resurrects — case (b)) and rehomes `y`'s children to `anc s y`,
so the live sublist of `pre` — the chain with `y` filtered out — is again the
genuine chain of `x`; no node outside `pre` can enter it (case (a)). -/

/-- `IsAncPath` sees its leaf only through `anc`. -/
theorem isAncPath_leaf_congr (s : concrete_st) (z w : ℕ) (L : List ℕ)
    (h : anc s z = anc s w) (hw : IsAncPath s w L) : IsAncPath s z L := by
  cases L with
  | nil => simp only [IsAncPath] at hw ⊢; rw [h]; exact hw
  | cons p ps =>
    simp only [IsAncPath] at hw ⊢
    exact ⟨h.trans hw.1, hw.2.1, hw.2.2⟩

/-- A genuine chain transports along pointwise agreement of `anc` and
containment-preservation. -/
theorem isAncPath_of_eq (s s' : concrete_st)
    (Ha : ∀ k, anc s' k = anc s k)
    (Hc : ∀ k, contains s k = true → contains s' k = true) :
    ∀ (L : List ℕ) (z : ℕ), IsAncPath s z L → IsAncPath s' z L := by
  intro L
  induction L with
  | nil =>
    intro z h
    simp only [IsAncPath] at h ⊢
    rw [Ha z]; exact h
  | cons p ps ih =>
    intro z h
    simp only [IsAncPath] at h ⊢
    exact ⟨(Ha z).trans h.1, Hc p h.2.1, ih p h.2.2⟩

/-- **Chain surgery.** If `s'` differs from `s` by removing a non-root `y`
from the domain and rehoming every `y`-anchored node to `R = anc s y`, then
any genuine chain in `s` becomes, in `s'`, the same chain with `y` filtered
out. The delicate case is a chain entry equal to `y`: its predecessor is
rehomed to `anc s y`, which is exactly where the chain continues. -/
theorem isAncPath_surgery (s s' : concrete_st) (y R : ℕ)
    (hy0 : y ≠ 0) (hR : R = anc s y)
    (Hc : ∀ k, contains s' k = (contains s k && (k != y)))
    (Ha : ∀ k, anc s' k = if anc s k = y then R else anc s k) :
    ∀ (L : List ℕ) (z : ℕ), IsAncPath s z L →
      IsAncPath s' z (L.filter (fun c => c != y)) := by
  intro L
  induction L with
  | nil =>
    intro z h
    simp only [IsAncPath] at h
    simp only [List.filter_nil, IsAncPath]
    rw [Ha z, if_neg (by rw [h]; exact fun e => hy0 e.symm)]
    exact h
  | cons p ps ih =>
    intro z h
    simp only [IsAncPath] at h
    obtain ⟨h1, h2, h3⟩ := h
    rw [List.filter_cons]
    by_cases hpy : p = y
    · subst hpy
      rw [if_neg (by simp)]
      -- predecessor `z` is rehomed to `anc s p`, where the chain continues
      have hzz : anc s' z = anc s' p := by
        rw [Ha z, if_pos h1, Ha p]
        by_cases hpp : anc s p = p
        · rw [if_pos hpp]
        · rw [if_neg hpp, hR]
      exact isAncPath_leaf_congr s' z p _ hzz (ih p h3)
    · have hb : (p != y) = true := by simp [hpy]
      rw [if_pos hb]
      simp only [IsAncPath]
      refine ⟨?_, ?_, ?_⟩
      · rw [Ha z, if_neg (by rw [h1]; exact hpy)]
        exact h1
      · rw [Hc p, h2, hb]; rfl
      · exact ih p h3

/-! ## Reachability packaging and the Key Lemma -/
