import Sal.MRDTs.Metatheory.Development.RGA_BubbleWiring

/-!
# `chainFaithful_doDel` — `ChainFaithful` is preserved by an accurate `Del`

The keystone preservation lemma for the tombstone-free RGA's σ-walk threading
(the M2 tail of `RGA_BubbleWiring.lean` §3.4).  Additive: modifies no existing
file.

The proof is the SPLICE argument.  Write `s' = do_ s (Del pre x)`.  An accurate
`Del x` sets `resolve s pre = anc s x`, so `s'` re-links every child `c` of `x`
(`anc s c = x`) to `anc s x` — exactly `x`'s successor in the true chain — while
`x` itself becomes dead.  In `ChainFaithful` terms this splices `x` out of the
live chain, preserving every surviving `anc`-link.

The mechanisation runs a strong (fuel-bounded) induction that OUTPUTS
`ChainFaithful` on the `x`-free list `M.filter (≠x)`, matched level-by-level with
the `s`-recursion on `M`.  The `Del` merges two `s`-levels (the predecessor of `x`
and `x` itself) into one `s'`-level; the induction consumes exactly those two
`s`-levels there, and the final "add the dead `x` back in" step closes the gap
between the `x`-free output and the full list `L`.
-/

set_option maxHeartbeats 1000000

namespace Sal.Metatheory.RGAChainFaithfulDoDel

open Sal.Metatheory.RGABubbleWiring

/-! ## §0  filter algebra -/

/-- Filtering by `≠a` twice is filtering once. -/
theorem flt_idem (a : ℕ) (L : List ℕ) :
    (L.filter (fun c => c != a)).filter (fun c => c != a) = L.filter (fun c => c != a) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro c _; simp

/-- Filtering by `≠a` then `≠b` = by `≠b` then `≠a`. -/
theorem flt_comm (a b : ℕ) (L : List ℕ) :
    (L.filter (fun c => c != a)).filter (fun c => c != b)
      = (L.filter (fun c => c != b)).filter (fun c => c != a) := by
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro c _; exact Bool.and_comm _ _

/-- `flt x (flt v (flt x M)) = flt x (flt v M)` : an inner `flt x` is absorbed. -/
theorem flt_absorb (x v : ℕ) (M : List ℕ) :
    ((M.filter (fun c => c != x)).filter (fun c => c != v)).filter (fun c => c != x)
      = (M.filter (fun c => c != v)).filter (fun c => c != x) := by
  rw [List.filter_filter, List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro c _
  cases hx : (c != x) <;> cases hv : (c != v) <;> simp [hx, hv]

/-! ## §1  small `resolve` facts -/

/-- A live resolve is a member of the candidate list (needs `contains s 0 = false`). -/
theorem resolve_mem_of_live (s : concrete_st) (h0 : contains s 0 = false) :
    ∀ (N : List ℕ), contains s (resolve s N) = true → resolve s N ∈ N := by
  intro N
  induction N with
  | nil => intro h; rw [show resolve s ([] : List ℕ) = 0 from rfl, h0] at h; exact absurd h (by simp)
  | cons c rest ih =>
    intro h
    simp only [resolve] at h ⊢
    by_cases hc : contains s c = true
    · rw [if_pos hc]; exact List.mem_cons_self
    · rw [if_neg hc] at h ⊢; exact List.mem_cons_of_mem _ (ih h)

/-- If every candidate is dead, `resolve = 0`. -/
theorem resolve_all_dead (s : concrete_st) :
    ∀ (N : List ℕ), (∀ c ∈ N, contains s c = false) → resolve s N = 0 := by
  intro N
  induction N with
  | nil => intro _; rfl
  | cons c rest ih =>
    intro h
    have hc : contains s c = false := h c List.mem_cons_self
    rw [resolve_dead_head s c rest hc]
    exact ih (fun d hd => h d (List.mem_cons_of_mem _ hd))

/-- If the resolve of `M` is dead, every candidate is dead. -/
theorem all_dead_of_resolve_dead (s : concrete_st) :
    ∀ (M : List ℕ), contains s (resolve s M) = false → ∀ c ∈ M, contains s c = false := by
  intro M
  induction M with
  | nil => intro _ c hc; simp at hc
  | cons d rest ih =>
    intro h c hc
    by_cases hd : contains s d = true
    · rw [resolve_live_head s d rest hd] at h; rw [hd] at h; exact absurd h (by simp)
    · have hdf : contains s d = false := by cases hh : contains s d with
        | true => exact absurd hh hd
        | false => rfl
      rw [resolve_dead_head s d rest hdf] at h
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact hdf
      · exact ih h c hc'

/-- `x ∈ M` strictly shortens `M.filter (≠x)`. -/
theorem filter_ne_length_lt : ∀ (M : List ℕ) (v : ℕ), v ∈ M →
    (M.filter (fun c => c != v)).length < M.length := by
  intro M v hv
  induction M with
  | nil => simp at hv
  | cons c cs ih =>
    rw [List.filter_cons]
    by_cases hcv : c = v
    · subst hcv
      simp only [bne_self_eq_false, Bool.false_eq_true, if_false, List.length_cons]
      exact Nat.lt_succ_of_le (List.length_filter_le _ _)
    · have hb : (c != v) = true := by simp [hcv]
      rw [if_pos hb]
      have hvcs : v ∈ cs := by
        rcases List.mem_cons.mp hv with rfl | h
        · exact absurd rfl hcv
        · exact h
      simp only [List.length_cons]
      exact Nat.succ_lt_succ (ih hvcs)

/-! ## §2  `ChainFaithfulAux` structural facts -/

/-- On the empty list `ChainFaithfulAux` holds at any fuel (root is never live). -/
theorem aux_nil (s : concrete_st) (h0 : contains s 0 = false) :
    ∀ n, ChainFaithfulAux s n ([] : List ℕ) := by
  intro n
  cases n with
  | zero => exact trivial
  | succ k =>
    intro h
    rw [show resolve s ([] : List ℕ) = 0 from rfl, h0] at h
    exact absurd h (by simp)

/-- Peel one level of `ChainFaithfulAux`, given enough fuel and a live pivot. -/
theorem chain_unfold (s : concrete_st) (h0 : contains s 0 = false)
    (f : Nat) (N : List ℕ) (h : ChainFaithfulAux s f N) (hlen : N.length ≤ f)
    (hlive : contains s (resolve s N) = true) :
    resolve s (N.filter (fun c => c != resolve s N)) = anc s (resolve s N)
      ∧ ChainFaithfulAux s (f - 1) (N.filter (fun c => c != resolve s N)) := by
  have hmem : resolve s N ∈ N := resolve_mem_of_live s h0 N hlive
  have hN1 : 1 ≤ N.length := List.length_pos_of_mem hmem
  have hf1 : 1 ≤ f := le_trans hN1 hlen
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  simp only [ChainFaithfulAux] at h
  have := h hlive
  simpa using this

/-- If two states agree on `contains` everywhere and on `anc` everywhere, they
have the same `ChainFaithfulAux`.  (Used for the degenerate `x = 0` delete, which
leaves the state observationally unchanged.) -/
theorem chainFaithfulAux_congr (s₁ s₂ : concrete_st)
    (hc : ∀ k, contains s₁ k = contains s₂ k) (ha : ∀ k, anc s₁ k = anc s₂ k) :
    ∀ n M, ChainFaithfulAux s₁ n M → ChainFaithfulAux s₂ n M := by
  intro n
  induction n with
  | zero => intro M _; exact trivial
  | succ k ih =>
    intro M h
    have hres : resolve s₁ M = resolve s₂ M := resolve_dom_eq s₁ s₂ M (fun c _ => hc c)
    intro hlive2
    have hlive1 : contains s₁ (resolve s₁ M) = true := by rw [hres, hc]; exact hlive2
    simp only [ChainFaithfulAux] at h
    obtain ⟨heq, hrec⟩ := h hlive1
    have hfilt : (fun c => c != resolve s₁ M) = (fun c => c != resolve s₂ M) := by rw [hres]
    refine ⟨?_, ?_⟩
    · rw [← hres, ← ha (resolve s₁ M)]
      rw [← heq]
      exact resolve_dom_eq s₂ s₁ _ (fun c _ => (hc c).symm)
    · rw [← hres]; exact ih _ hrec

/-! ## §3  the splice induction (main case: `x ≠ 0`, `contains s x = true`) -/

/-- The core strong induction.  With `s' = do_ s (Del pre x)`, `x` live and
`resolve s pre = anc s x`, `ChainFaithfulAux` on `M` transports to
`ChainFaithfulAux` on the `x`-free list `M.filter (≠x)`, matched to the
`s`-recursion.  Fuel `f` bounds `M.length`; the output fuel `nOut` is free
(above `(M.filter (≠x)).length`). -/
theorem core (s : concrete_st) (t r x : ℕ) (pre : List ℕ)
    (h0 : contains s 0 = false) (hxlive : contains s x = true)
    (htgt : resolve s pre = anc s x) :
    ∀ (f : Nat) (M : List ℕ), M.length ≤ f → ChainFaithfulAux s f M →
      ∀ nOut, (M.filter (fun c => c != x)).length ≤ nOut →
        ChainFaithfulAux (do_ s (t, r, .Del pre x)) nOut (M.filter (fun c => c != x)) := by
  set s' := do_ s (t, r, .Del pre x) with hs'
  have hx0 : x ≠ 0 := fun e => by rw [e, h0] at hxlive; exact absurd hxlive (by simp)
  have h0' : contains s' 0 = false := by
    rw [hs', contains_doDel]; rw [h0]; simp
  intro f
  induction f with
  | zero =>
    intro M hMf _ nOut _
    have : M = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hMf)
    subst this; simpa using aux_nil s' h0' nOut
  | succ f₀ ih =>
    intro M hMf hCF nOut hnOut
    by_cases hM : M = []
    · subst hM; simpa using aux_nil s' h0' nOut
    · by_cases hvx : resolve s M = x
      · -- v = x : the deleted node itself is the current climb-target; absorb it.
        have hxlive' : contains s (resolve s M) = true := by rw [hvx]; exact hxlive
        obtain ⟨_, htail⟩ := chain_unfold s h0 (f₀ + 1) M hCF hMf hxlive'
        rw [hvx] at htail
        simp only [Nat.add_sub_cancel] at htail
        have hxM : x ∈ M := by
          have := resolve_mem_of_live s h0 M hxlive'; rwa [hvx] at this
        have hlenlt : (M.filter (fun c => c != x)).length < M.length :=
          filter_ne_length_lt M x hxM
        have key := ih (M.filter (fun c => c != x)) (by omega) htail nOut
          (by rw [flt_idem]; exact hnOut)
        rw [flt_idem] at key
        exact key
      · -- v ≠ x
        by_cases hvlive : contains s (resolve s M) = true
        · -- v live : the splice point.
          have hfx : resolve s (M.filter (fun c => c != x)) = resolve s M :=
            resolve_filter_ne s x M hvx
          have hps : resolve s' (M.filter (fun c => c != x)) = resolve s M := by
            rw [hs', resolve_doDel, flt_idem]; exact hfx
          have hvM : resolve s M ∈ M := resolve_mem_of_live s h0 M hvlive
          have hvmemx : resolve s M ∈ M.filter (fun c => c != x) := by
            rw [List.mem_filter]; exact ⟨hvM, by simp [hvx]⟩
          obtain ⟨hlink, htail⟩ := chain_unfold s h0 (f₀ + 1) M hCF hMf hvlive
          simp only [Nat.add_sub_cancel] at htail
          have hlenlt : (M.filter (fun c => c != resolve s M)).length < M.length :=
            filter_ne_length_lt M (resolve s M) hvM
          have hnout1 : 1 ≤ nOut :=
            le_trans (List.length_pos_of_mem hvmemx) hnOut
          obtain ⟨k, rfl⟩ : ∃ k, nOut = k + 1 := ⟨nOut - 1, by omega⟩
          simp only [ChainFaithfulAux]
          rw [hps]
          intro _
          refine ⟨?_, ?_⟩
          · -- obligation (a)
            rw [hs', resolve_doDel, flt_absorb, anc_doDel, htgt]
            by_cases hav : anc s (resolve s M) = x
            · rw [if_pos hav]
              have hres_fltv : resolve s (M.filter (fun c => c != resolve s M)) = x := by
                rw [hlink, hav]
              have hxlive2 :
                  contains s (resolve s (M.filter (fun c => c != resolve s M))) = true := by
                rw [hres_fltv]; exact hxlive
              obtain ⟨hlink2, _⟩ := chain_unfold s h0 f₀ (M.filter (fun c => c != resolve s M))
                htail (by omega) hxlive2
              rw [hres_fltv] at hlink2
              exact hlink2
            · rw [if_neg hav]
              rw [resolve_filter_ne s x (M.filter (fun c => c != resolve s M))
                (by rw [hlink]; exact hav)]
              exact hlink
          · -- obligation (b)
            rw [flt_comm]
            refine ih (M.filter (fun c => c != resolve s M)) (by omega) htail k ?_
            rw [flt_comm (resolve s M) x M]
            have hlt2 :
                ((M.filter (fun c => c != x)).filter (fun c => c != resolve s M)).length
                  < (M.filter (fun c => c != x)).length :=
              filter_ne_length_lt (M.filter (fun c => c != x)) (resolve s M) hvmemx
            omega
        · -- v not live : vacuous (all candidates dead)
          have hvf : contains s (resolve s M) = false := by
            cases hh : contains s (resolve s M) with
            | true => exact absurd hh hvlive
            | false => rfl
          have hall : ∀ c ∈ M, contains s c = false := all_dead_of_resolve_dead s M hvf
          have hz : resolve s (M.filter (fun c => c != x)) = 0 :=
            resolve_all_dead s _ (fun c hc => hall c (List.mem_of_mem_filter hc))
          have hzs' : resolve s' (M.filter (fun c => c != x)) = 0 := by
            rw [hs', resolve_doDel, flt_idem]; exact hz
          cases nOut with
          | zero => exact trivial
          | succ k =>
            intro hlive'
            rw [hzs', h0'] at hlive'
            exact absurd hlive' (by simp)

/-! ## §4  bridging back to the full list -/

/-- After a `Del x`, a candidate list resolves the same with or without `x`
present (`x` is dead). -/
theorem resolve_s'_filter_x (s : concrete_st) (t r x : ℕ) (pre : List ℕ) (N : List ℕ) :
    resolve (do_ s (t, r, .Del pre x)) N
      = resolve (do_ s (t, r, .Del pre x)) (N.filter (fun c => c != x)) := by
  rw [resolve_doDel, resolve_doDel, flt_idem]

/-- Adding the dead node `x` back into the list preserves `ChainFaithfulAux`
after a `Del x`.  Bridges `core`'s `x`-free output to the full list `L`. -/
theorem addDeadBack (s : concrete_st) (t r x : ℕ) (pre : List ℕ)
    (h0' : contains (do_ s (t, r, .Del pre x)) 0 = false) :
    ∀ n (L : List ℕ), L.length ≤ n →
      ChainFaithfulAux (do_ s (t, r, .Del pre x)) n (L.filter (fun c => c != x)) →
      ChainFaithfulAux (do_ s (t, r, .Del pre x)) n L := by
  intro n
  induction n with
  | zero =>
    intro L hlen _
    have : L = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst this; exact trivial
  | succ k ih =>
    intro L hlen h
    simp only [ChainFaithfulAux] at h ⊢
    rw [← resolve_s'_filter_x s t r x pre L] at h
    intro hlive
    obtain ⟨heq, hrec⟩ := h hlive
    refine ⟨?_, ?_⟩
    · rw [resolve_s'_filter_x s t r x pre
        (L.filter (fun c => c != resolve (do_ s (t, r, .Del pre x)) L)),
        flt_comm (resolve (do_ s (t, r, .Del pre x)) L) x L]
      exact heq
    · have hq : resolve (do_ s (t, r, .Del pre x)) L ∈ L :=
        resolve_mem_of_live (do_ s (t, r, .Del pre x)) h0' L hlive
      have hlt : (L.filter (fun c => c != resolve (do_ s (t, r, .Del pre x)) L)).length
          < L.length := filter_ne_length_lt L _ hq
      refine ih (L.filter (fun c => c != resolve (do_ s (t, r, .Del pre x)) L)) (by omega) ?_
      rw [flt_comm (resolve (do_ s (t, r, .Del pre x)) L) x L]
      exact hrec

/-! ## §5  the keystone lemma -/

/-- **`ChainFaithful` is preserved by an accurate `Del`.**  The M2 tail of
`RGA_BubbleWiring` §3.4: combined with `chainFaithful_doIns` and
`climbFaithful_of_chain`, this discharges the σ-walk `Faithful`-threading
(deliverable 3a) end-to-end. -/
theorem chainFaithful_doDel (s : concrete_st) (t r x : ℕ) (pre L : List ℕ)
    (h0 : contains s 0 = false) (hacc : accurate (t, r, .Del pre x) s)
    (hcf : ChainFaithful s L) :
    ChainFaithful (do_ s (t, r, .Del pre x)) L := by
  simp only [accurate, opLeaf, opPath] at hacc
  unfold ChainFaithful at hcf ⊢
  have h0' : contains (do_ s (t, r, .Del pre x)) 0 = false := by rw [contains_doDel, h0]; simp
  rcases hacc with ⟨hx0, hpnil⟩ | ⟨hxlive, hpath⟩
  · -- degenerate `x = 0` : observationally unchanged
    subst hx0; subst hpnil
    have hcE : ∀ k, contains s k = contains (do_ s (t, r, .Del [] 0)) k := by
      intro k; rw [contains_doDel]
      by_cases hck : contains s k = true
      · rw [hck]; simp [contains_ne_zero s k h0 hck]
      · simp only [Bool.not_eq_true] at hck; rw [hck]; simp
    have haE : ∀ k, anc s k = anc (do_ s (t, r, .Del [] 0)) k := by
      intro k; rw [anc_doDel]
      split
      · next hh => rw [show resolve s ([] : List ℕ) = 0 from rfl]; exact hh
      · rfl
    exact chainFaithfulAux_congr s (do_ s (t, r, .Del [] 0)) hcE haE L.length L hcf
  · -- accurate delete of a live node
    have htgt : resolve s pre = anc s x := isAncPath_resolve s x pre hpath
    have hmain :=
      core s t r x pre h0 hxlive htgt L.length L (le_refl _) hcf L.length
        (List.length_filter_le _ _)
    exact addDeadBack s t r x pre h0' L.length L (le_refl _) hmain

#print axioms chainFaithful_doDel

end Sal.Metatheory.RGAChainFaithfulDoDel
