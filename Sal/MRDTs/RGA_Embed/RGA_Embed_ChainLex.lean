import Sal.MRDTs.RGA_Embed.RGA_Embed_ReadSide

/-!
# Embedded-chain RGA: the chain-lex theorem and the document characterization

The intent layer (design doc §2, Corollary 2): **display order ≡ lexicographic
order on birth chains**. This is where the code's two properties (monotone,
prefix-free) are finally consumed, the stability layer needed neither.

Contents:
* `keyLt` order algebra (irreflexive, asymmetric, transitive, total) and the
  induced `keyLe` facts the sort needs;
* `document` characterization: it is a permutation of the live filter, sorted
  by descending key, and, on states with injective coordinates, pairwise
  `before`;
* birth chains: `coordOf` (concatenation of codewords), **unique
  decodability** (`coordOf_inj`, prefix-free concatenations decode
  uniquely, so distinct chains have distinct coordinates);
* `chainBefore` (the display order on chains: ancestors first, then larger
  delta at the first divergence) and the **chain-lex theorem**
  (`display_iff_chainBefore`): the key comparison of coordinates computes
  exactly `chainBefore`, the RGA order of the birth tree, restricted to
  survivors, realized by one flat comparison of immutable bit strings.
-/

namespace Sal.EmbedRGA

/-! ## `keyLt` is a strict total order -/

theorem keyLt_irrefl (u : List ℕ) : keyLt u u = false := by
  induction u with
  | nil => rfl
  | cons x xs ih => simp [keyLt, ih]

theorem keyLt_asymm : ∀ {u v : List ℕ}, keyLt u v = true → keyLt v u = false
  | [], [], h => by simp [keyLt] at h
  | [], _ :: _, _ => rfl
  | _ :: _, [], h => by simp [keyLt] at h
  | x :: xs, y :: ys, h => by
      simp only [keyLt] at h ⊢
      rcases Nat.lt_trichotomy x y with hxy | rfl | hxy
      · rw [if_neg (by omega : ¬ y < x), if_pos hxy]
      · rw [if_neg (by omega : ¬ x < x)] at h ⊢
        rw [if_neg (by omega : ¬ x < x)] at h ⊢
        exact keyLt_asymm h
      · rw [if_neg (by omega : ¬ x < y), if_pos hxy] at h
        exact Bool.noConfusion h

theorem keyLt_trans : ∀ {u v w : List ℕ},
    keyLt u v = true → keyLt v w = true → keyLt u w = true
  | [], v, w, h1, h2 => by
      cases w with
      | nil =>
          cases v with
          | nil => exact h2
          | cons y ys => simp [keyLt] at h2
      | cons z zs => rfl
  | _ :: _, [], _, h1, _ => by simp [keyLt] at h1
  | _ :: _, _ :: _, [], _, h2 => by simp [keyLt] at h2
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
      simp only [keyLt] at h1 h2 ⊢
      rcases Nat.lt_trichotomy x y with hxy | rfl | hxy
      · rcases Nat.lt_trichotomy y z with hyz | rfl | hyz
        · rw [if_pos (by omega : x < z)]
        · rw [if_pos hxy]
        · rw [if_neg (by omega : ¬ y < z), if_pos hyz] at h2
          exact Bool.noConfusion h2
      · rw [if_neg (by omega : ¬ x < x)] at h1
        rw [if_neg (by omega : ¬ x < x)] at h1
        rcases Nat.lt_trichotomy x z with hxz | rfl | hxz
        · rw [if_pos hxz]
        · rw [if_neg (by omega : ¬ x < x)] at h2 ⊢
          rw [if_neg (by omega : ¬ x < x)] at h2 ⊢
          exact keyLt_trans h1 h2
        · rw [if_neg (by omega : ¬ x < z), if_pos hxz] at h2
          exact Bool.noConfusion h2
      · rw [if_neg (by omega : ¬ x < y), if_pos hxy] at h1
        exact Bool.noConfusion h1

theorem keyLt_total : ∀ {u v : List ℕ}, u ≠ v →
    keyLt u v = true ∨ keyLt v u = true
  | [], [], hne => absurd rfl hne
  | [], _ :: _, _ => Or.inl rfl
  | _ :: _, [], _ => Or.inr rfl
  | x :: xs, y :: ys, hne => by
      rcases Nat.lt_trichotomy x y with hxy | rfl | hxy
      · exact Or.inl (by simp [keyLt, hxy])
      · have hne' : xs ≠ ys := fun h => hne (by rw [h])
        rcases keyLt_total hne' with h | h
        · exact Or.inl (by simp [keyLt, h])
        · exact Or.inr (by simp [keyLt, h])
      · exact Or.inr (by simp [keyLt, hxy])

theorem keyLe_total (u v : List ℕ) : (keyLe u v || keyLe v u) = true := by
  simp only [keyLe, Bool.or_eq_true, Bool.not_eq_true']
  by_cases h : keyLt u v = true
  · exact Or.inl (keyLt_asymm h)
  · exact Or.inr (by simpa using h)

theorem keyLe_trans {u v w : List ℕ}
    (h1 : keyLe u v = true) (h2 : keyLe v w = true) : keyLe u w = true := by
  simp only [keyLe, Bool.not_eq_true'] at h1 h2 ⊢
  by_contra hc
  have hwu : keyLt w u = true := by
    cases h : keyLt w u
    · exact absurd h hc
    · rfl
  rcases eq_or_ne v w with rfl | hne
  · rw [hwu] at h1
    exact Bool.noConfusion h1
  · rcases keyLt_total hne with h | h
    · rw [keyLt_trans h hwu] at h1
      exact Bool.noConfusion h1
    · rw [h] at h2
      exact Bool.noConfusion h2

/-! ## The document is the live filter, sorted; on injective states it is
pairwise `before` -/

variable {α : Type} [DecidableEq α]

omit [DecidableEq α] in
theorem document_perm (s : concrete_st α) (ids : List ℕ) :
    (document s ids).Perm (ids.filter (fun t => contains s t)) :=
  List.mergeSort_perm _ _

omit [DecidableEq α] in
theorem mem_document {s : concrete_st α} {ids : List ℕ} {t : ℕ} :
    t ∈ document s ids ↔ t ∈ ids ∧ contains s t = true := by
  rw [(document_perm s ids).mem_iff, List.mem_filter]

omit [DecidableEq α] in
theorem document_pairwise_le (s : concrete_st α) (ids : List ℕ) :
    (document s ids).Pairwise
      (fun t1 t2 => keyLe (key (pos s t2)) (key (pos s t1)) = true) := by
  apply List.pairwise_mergeSort
  · intro a b c h1 h2
    exact keyLe_trans h2 h1
  · intro a b
    exact keyLe_total _ _

/-- Coordinate injectivity on the live domain, the wf invariant delivered by
unique decodability (`coordOf_inj`) on chain-generated states. -/
@[simp] def distinctCoords (s : concrete_st α) : Prop :=
  ∀ t1 t2, contains s t1 = true → contains s t2 = true →
    pos s t1 = pos s t2 → t1 = t2

omit [DecidableEq α] in
theorem key_inj {c1 c2 : coord} (h : key c1 = key c2) : c1 = c2 := by
  have hmap : c1.map (fun b => if b then 2 else 1) =
              c2.map (fun b => if b then 2 else 1) :=
    List.append_inj_left' h (by simp)
  have hinj : Function.Injective (fun b : Bool => if b then (2 : ℕ) else 1) := by
    intro a b hab
    cases a <;> cases b <;> simp_all
  exact List.map_injective_iff.mpr hinj hmap

omit [DecidableEq α] in
/-- **The document characterization**: on a state with injective coordinates,
the document is pairwise strictly `before`, every displayed pair is a
co-displayed pair in the design sense, ordered by the immutable keys. -/
theorem document_pairwise_before (s : concrete_st α) (ids : List ℕ)
    (hinj : distinctCoords s) (hnd : ids.Nodup) :
    (document s ids).Pairwise (before s) := by
  have hsorted := document_pairwise_le s ids
  have hnodup : (document s ids).Nodup :=
    (document_perm s ids).nodup_iff.mpr (hnd.filter _)
  refine (hsorted.and hnodup).imp_of_mem ?_
  intro a b ha hb hab
  obtain ⟨hle, hne⟩ := hab
  have hca : contains s a = true := (mem_document.mp ha).2
  have hcb : contains s b = true := (mem_document.mp hb).2
  refine ⟨hca, hcb, ?_⟩
  have hkne : key (pos s b) ≠ key (pos s a) := by
    intro h
    exact hne (hinj b a hcb hca (key_inj h)).symm
  rcases keyLt_total hkne with h | h
  · exact h
  · simp only [keyLe, Bool.not_eq_true'] at hle
    rw [h] at hle
    exact Bool.noConfusion hle

/-! ## Birth chains and unique decodability -/

/-- The coordinate of a birth chain: concatenated codewords. -/
def coordOf (Γ : OrderedPrefixCode) : List ℕ → coord
  | [] => []
  | d :: ds => Γ.enc d ++ coordOf Γ ds

/-- All deltas positive (causality: every insert's timestamp exceeds its
anchor's). -/
@[simp] def PosChain (ch : List ℕ) : Prop := ∀ d ∈ ch, 1 ≤ d

theorem enc_ne_nil (Γ : OrderedPrefixCode) {d : ℕ} (hd : 1 ≤ d) :
    Γ.enc d ≠ [] := by
  intro h
  apply Γ.prefixFree hd (show 1 ≤ d + 1 by omega) (by omega)
  rw [h]
  exact List.nil_prefix

theorem coordOf_append (Γ : OrderedPrefixCode) (ch1 ch2 : List ℕ) :
    coordOf Γ (ch1 ++ ch2) = coordOf Γ ch1 ++ coordOf Γ ch2 := by
  induction ch1 with
  | nil => simp [coordOf]
  | cons d ds ih => simp [coordOf, ih]

/-- **Unique decodability**: prefix-free concatenations decode uniquely,
distinct birth chains have distinct coordinates, so coordinates are honest
names and `distinctCoords` holds on chain-generated states. -/
theorem coordOf_inj (Γ : OrderedPrefixCode) :
    ∀ {ch1 ch2 : List ℕ}, PosChain ch1 → PosChain ch2 →
      coordOf Γ ch1 = coordOf Γ ch2 → ch1 = ch2
  | [], [], _, _, _ => rfl
  | [], e :: es, _, h2, h => by
      exfalso
      simp only [coordOf] at h
      have henc : Γ.enc e = [] := by
        cases henc : Γ.enc e with
        | nil => rfl
        | cons b bs => rw [henc] at h; simp at h
      exact enc_ne_nil Γ (h2 e List.mem_cons_self) henc
  | d :: ds, [], h1, _, h => by
      exfalso
      simp only [coordOf] at h
      have henc : Γ.enc d = [] := by
        cases henc : Γ.enc d with
        | nil => rfl
        | cons b bs => rw [henc] at h; simp at h
      exact enc_ne_nil Γ (h1 d List.mem_cons_self) henc
  | d :: ds, e :: es, h1, h2, h => by
      simp only [coordOf] at h
      have hd1 : 1 ≤ d := h1 d List.mem_cons_self
      have he1 : 1 ≤ e := h2 e List.mem_cons_self
      have hde : d = e := by
        by_contra hne
        have p1 : Γ.enc d <+: (Γ.enc d ++ coordOf Γ ds) := List.prefix_append _ _
        have p2 : Γ.enc e <+: (Γ.enc d ++ coordOf Γ ds) := by
          rw [h]; exact List.prefix_append _ _
        rcases Nat.le_total (Γ.enc d).length (Γ.enc e).length with hle | hle
        · exact Γ.prefixFree hd1 he1 hne
            (List.prefix_of_prefix_length_le p1 p2 hle)
        · exact Γ.prefixFree he1 hd1 (Ne.symm hne)
            (List.prefix_of_prefix_length_le p2 p1 hle)
      subst hde
      have htail : coordOf Γ ds = coordOf Γ es := by
        exact List.append_cancel_left h
      rw [List.cons.injEq]
      exact ⟨rfl, coordOf_inj Γ
        (fun x hx => h1 x (List.mem_cons_of_mem _ hx))
        (fun x hx => h2 x (List.mem_cons_of_mem _ hx)) htail⟩

/-! ## The first-difference witness

Monotone + prefix-free forces every comparison of distinct codewords to be
decided at a genuine first differing bit, the `nil` escape of `List.Lex`
never fires. This is the bit-level content of "the ranges fully capture it":
the verdict is IN the strings, at a bounded position. -/

theorem lex_first_diff : ∀ {u v : List Bool},
    bitLt u v → ¬(u <+: v) →
    ∃ p u1 u2, u = p ++ false :: u1 ∧ v = p ++ true :: u2 := by
  intro u v hlex
  induction hlex with
  | nil => intro hnp; exact absurd List.nil_prefix hnp
  | @rel a l₁ b l₂ hab =>
      intro _
      have hb : a = false ∧ b = true := by
        cases a <;> cases b <;> revert hab <;> decide
      exact ⟨[], l₁, l₂, by simp [hb.1], by simp [hb.2]⟩
  | @cons a l₁ l₂ h ih =>
      intro hnp
      have : ¬(l₁ <+: l₂) := fun hp => hnp (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)
      obtain ⟨p, u1, u2, e1, e2⟩ := ih this
      exact ⟨a :: p, u1, u2, by simp [e1], by simp [e2]⟩

theorem enc_first_diff (Γ : OrderedPrefixCode) {d e : ℕ}
    (hd : 1 ≤ d) (he : 1 ≤ e) (hlt : d < e) :
    ∃ p u1 u2, Γ.enc d = p ++ false :: u1 ∧ Γ.enc e = p ++ true :: u2 :=
  lex_first_diff (Γ.mono hd hlt) (Γ.prefixFree hd he (Nat.ne_of_lt hlt))

/-! ## Key plumbing -/

/-- Bit symbol under the terminator embedding. -/
def sym (b : Bool) : ℕ := if b then 2 else 1

theorem key_def (c : coord) : key c = c.map sym ++ [3] := rfl

theorem key_append (c d : coord) : key (c ++ d) = c.map sym ++ key d := by
  simp [key_def, List.map_append, List.append_assoc]

theorem keyLt_append_left (p : List ℕ) (u v : List ℕ) :
    keyLt (p ++ u) (p ++ v) = keyLt u v := by
  induction p with
  | nil => rfl
  | cons x xs ih => simp [keyLt, ih]

/-! ## The chain display order and the chain-lex theorem -/

/-- The display order on birth chains: an ancestor precedes everything in its
subtree; at the first divergence the larger delta (the newer sibling)
precedes. This is the RGA order of the birth tree. -/
inductive chainBefore : List ℕ → List ℕ → Prop where
  | ancestor (ch ext : List ℕ) (hne : ext ≠ []) : chainBefore ch (ch ++ ext)
  | newer (p : List ℕ) (d e : ℕ) (ch1 ch2 : List ℕ) (hlt : e < d) :
      chainBefore (p ++ d :: ch1) (p ++ e :: ch2)

/-- Prepending a common ancestor preserves the chain order. -/
theorem chainBefore_cons (x : ℕ) {ch1 ch2 : List ℕ} (h : chainBefore ch1 ch2) :
    chainBefore (x :: ch1) (x :: ch2) := by
  cases h with
  | ancestor ch ext hne =>
      exact chainBefore.ancestor (x :: ch1) ext hne
  | newer p d e c1 c2 hlt =>
      exact chainBefore.newer (x :: p) d e c1 c2 hlt

/-- Distinct chains are always comparable. -/
theorem chainBefore_total : ∀ {ch1 ch2 : List ℕ}, ch1 ≠ ch2 →
    chainBefore ch1 ch2 ∨ chainBefore ch2 ch1
  | [], [], hne => absurd rfl hne
  | [], e :: es, _ => Or.inl (chainBefore.ancestor [] (e :: es) (by simp))
  | d :: ds, [], _ => Or.inr (chainBefore.ancestor [] (d :: ds) (by simp))
  | d :: ds, e :: es, hne => by
      rcases Nat.lt_trichotomy d e with h | rfl | h
      · exact Or.inr (chainBefore.newer [] e d es ds h)
      · have hne' : ds ≠ es := fun hh => hne (by rw [hh])
        rcases chainBefore_total hne' with hb | hb
        · exact Or.inl (chainBefore_cons d hb)
        · exact Or.inr (chainBefore_cons d hb)
      · exact Or.inl (chainBefore.newer [] d e ds es h)

/-- **Chain order ⟹ key order**: the coordinate comparison realizes the chain
display order. -/
theorem chainBefore_display (Γ : OrderedPrefixCode) {ch1 ch2 : List ℕ}
    (h1 : PosChain ch1) (h2 : PosChain ch2) (hb : chainBefore ch1 ch2) :
    keyLt (key (coordOf Γ ch2)) (key (coordOf Γ ch1)) = true := by
  cases hb with
  | ancestor ch ext hne =>
      rw [coordOf_append, key_append, key_def (coordOf Γ ch1), keyLt_append_left]
      obtain ⟨x, xs, rfl⟩ : ∃ x xs, ext = x :: xs := by
        cases ext with
        | nil => exact absurd rfl hne
        | cons x xs => exact ⟨x, xs, rfl⟩
      have hx : 1 ≤ x := h2 x (List.mem_append_right _ List.mem_cons_self)
      obtain ⟨b, bs, hbs⟩ : ∃ b bs, Γ.enc x = b :: bs := by
        cases henc : Γ.enc x with
        | nil => exact absurd henc (enc_ne_nil Γ hx)
        | cons b bs => exact ⟨b, bs, rfl⟩
      show keyLt (key (coordOf Γ (x :: xs))) [3] = true
      simp only [coordOf, hbs, key_def, List.cons_append, List.map_cons]
      cases b <;> simp [keyLt, sym]
  | newer p d e c1 c2 hlt =>
      rw [coordOf_append, coordOf_append, key_append, key_append,
          keyLt_append_left]
      have hd1 : 1 ≤ d := h1 d (List.mem_append_right _ List.mem_cons_self)
      have he1 : 1 ≤ e := h2 e (List.mem_append_right _ List.mem_cons_self)
      obtain ⟨q, u1, u2, hEe, hEd⟩ := enc_first_diff Γ he1 hd1 hlt
      show keyLt (key (coordOf Γ (e :: c2))) (key (coordOf Γ (d :: c1))) = true
      simp only [coordOf, hEe, hEd, List.append_assoc, List.cons_append]
      rw [key_append, key_append, keyLt_append_left]
      simp [key_def, keyLt, sym]

/-- **The chain-lex theorem** (design doc, Corollary 2): for distinct positive
chains, the display comparison of the coordinates is *exactly* the chain
order. Display order ≡ lexicographic order on birth chains, the RGA order of
the birth tree, computed by one flat comparison of immutable bit strings. -/
theorem display_iff_chainBefore (Γ : OrderedPrefixCode) {ch1 ch2 : List ℕ}
    (h1 : PosChain ch1) (h2 : PosChain ch2) (hne : ch1 ≠ ch2) :
    keyLt (key (coordOf Γ ch2)) (key (coordOf Γ ch1)) = true ↔
    chainBefore ch1 ch2 := by
  constructor
  · intro h
    rcases chainBefore_total hne with hb | hb
    · exact hb
    · have h' := chainBefore_display Γ h2 h1 hb
      rw [keyLt_asymm h'] at h
      exact Bool.noConfusion h
  · exact chainBefore_display Γ h1 h2

/-! ## State-level packaging -/

/-- A state is chain-generated when every live coordinate is the coordinate of
a positive birth chain (the reachability invariant: mints write
`prefix ++ codeword`, folds preserve values, merges copy them). -/
@[simp] def chainState (Γ : OrderedPrefixCode) (s : concrete_st α)
    (chainOf : ℕ → List ℕ) : Prop :=
  ∀ t, contains s t = true →
    PosChain (chainOf t) ∧ pos s t = coordOf Γ (chainOf t)

omit [DecidableEq α] in
/-- On chain-generated states, `before` *is* the chain order. -/
theorem before_iff_chainBefore (Γ : OrderedPrefixCode) (s : concrete_st α)
    (chainOf : ℕ → List ℕ) (hcs : chainState Γ s chainOf) {t1 t2 : ℕ}
    (h1 : contains s t1 = true) (h2 : contains s t2 = true)
    (hne : chainOf t1 ≠ chainOf t2) :
    before s t1 t2 ↔ chainBefore (chainOf t1) (chainOf t2) := by
  obtain ⟨hp1, he1⟩ := hcs t1 h1
  obtain ⟨hp2, he2⟩ := hcs t2 h2
  unfold before
  rw [he1, he2]
  constructor
  · intro ⟨_, _, h⟩
    exact (display_iff_chainBefore Γ hp1 hp2 hne).mp h
  · intro h
    exact ⟨h1, h2, (display_iff_chainBefore Γ hp1 hp2 hne).mpr h⟩

omit [DecidableEq α] in
/-- Chain-generated states have injective coordinates (unique decodability),
hence pairwise-`before` documents. -/
theorem chainState_distinctCoords (Γ : OrderedPrefixCode) (s : concrete_st α)
    (chainOf : ℕ → List ℕ) (hcs : chainState Γ s chainOf)
    (hinj : ∀ t1 t2, contains s t1 = true → contains s t2 = true →
            chainOf t1 = chainOf t2 → t1 = t2) :
    distinctCoords s := by
  intro t1 t2 h1 h2 hpos
  obtain ⟨hp1, he1⟩ := hcs t1 h1
  obtain ⟨hp2, he2⟩ := hcs t2 h2
  apply hinj t1 t2 h1 h2
  apply coordOf_inj Γ hp1 hp2
  rw [← he1, ← he2, hpos]

/-! ## chainState is closed under the transitions

Same shape as the coherence closure: honest inserts extend the global chain
assignment, deletes and merges never touch values, so "every live coordinate
is a positive chain's coordinate" is a reachability invariant. -/

omit [DecidableEq α] in
/-- An accurate insert whose id is assigned the extended chain preserves
`chainState`. (`accurate` supplies both the causality bound `a < t` and the
prefix's truthfulness; `hch` records the birth: `t`'s chain is its anchor's
chain extended by the delta.) -/
theorem chainState_ins (Γ : OrderedPrefixCode) (s : concrete_st α)
    (chainOf : ℕ → List ℕ) (t r : ℕ) (e : α) (π : coord) (a : ℕ)
    (h0 : contains s 0 = false)
    (hcs : chainState Γ s chainOf)
    (hacc : accurate (t, r, .Ins e π a) s)
    (hch : chainOf t = (if a = 0 then [] else chainOf a) ++ [t - a]) :
    chainState Γ (do_ Γ s (t, r, .Ins e π a)) chainOf := by
  simp only [accurate] at hacc
  obtain ⟨hat, hval⟩ := hacc
  intro k hk
  by_cases hkt : k = t
  · subst hkt
    have hπc : π = (if a = 0 then [] else coordOf Γ (chainOf a)) := by
      rcases hval with ⟨ha0, hπ⟩ | ⟨hlive, hπ⟩
      · simp [ha0, hπ]
      · have ha0 : a ≠ 0 := by
          intro hz
          rw [hz] at hlive
          rw [hlive] at h0
          exact Bool.noConfusion h0
        rw [if_neg ha0, hπ, (hcs a hlive).2]
    have hpos_a : PosChain (if a = 0 then [] else chainOf a) := by
      rcases hval with ⟨ha0, -⟩ | ⟨hlive, -⟩
      · simp [ha0]
      · by_cases ha0 : a = 0
        · simp [ha0]
        · rw [if_neg ha0]
          exact (hcs a hlive).1
    constructor
    · rw [hch]
      intro d hd
      rcases List.mem_append.mp hd with hmem | hmem
      · exact hpos_a d hmem
      · have : d = k - a := List.mem_singleton.mp hmem
        omega
    · show (sel (upd s k (e, mint Γ π k a)) k).2 = coordOf Γ (chainOf k)
      rw [lemma_SelUpd1]
      show mint Γ π k a = coordOf Γ (chainOf k)
      rw [hch, coordOf_append, hπc]
      by_cases ha0 : a = 0
      · simp [ha0, coordOf, mint]
      · simp [ha0, coordOf, mint]
  · have hk' : contains s k = true := by
      simp only [do_, upd, contains, mem] at hk
      simp only [contains]
      grind
    obtain ⟨hp, hpos⟩ := hcs k hk'
    refine ⟨hp, ?_⟩
    show (sel (upd s t (e, mint Γ π t a)) k).2 = coordOf Γ (chainOf k)
    rw [lemma_SelUpd2 _ _ _ _ (by simpa using Ne.symm hkt)]
    exact hpos

omit [DecidableEq α] in
/-- Deletion preserves `chainState`: values are never touched. -/
theorem chainState_del (Γ : OrderedPrefixCode) (s : concrete_st α)
    (chainOf : ℕ → List ℕ) (t r x : ℕ)
    (hcs : chainState Γ s chainOf) :
    chainState Γ (do_ Γ s (t, r, .Del x)) chainOf := by
  intro k hk
  have hk' : contains s k = true := by
    simp only [do_, del, contains, domain, mem] at hk
    simp only [contains]
    grind
  exact hcs k hk'

omit [DecidableEq α] in
/-- Merging preserves `chainState`: values are copied from the inputs. -/
theorem chainState_merge (Γ : OrderedPrefixCode) (l a b : concrete_st α)
    (chainOf : ℕ → List ℕ)
    (hl : chainState Γ l chainOf) (ha : chainState Γ a chainOf)
    (hb : chainState Γ b chainOf) :
    chainState Γ (merge l a b) chainOf := by
  intro k hk
  simp only [merge, contains, domain, mem] at hk
  have hsel : sel (merge l a b) k =
      (if contains l k then sel l k else
        if contains a k then sel a k else sel b k) := rfl
  by_cases hkl : contains l k
  · obtain ⟨hp, hpos⟩ := hl k hkl
    exact ⟨hp, by simp only [pos, hsel, if_pos hkl]; exact hpos⟩
  · by_cases hka : contains a k
    · obtain ⟨hp, hpos⟩ := ha k hka
      exact ⟨hp, by simp only [pos, hsel, if_neg hkl, if_pos hka]; exact hpos⟩
    · have hkb : contains b k = true := by
        simp only [contains] at hkl hka ⊢
        grind
      obtain ⟨hp, hpos⟩ := hb k hkb
      exact ⟨hp, by
        simp only [pos, hsel, if_neg hkl, if_neg hka]; exact hpos⟩

/-! ## Non-interleaving: subtree convexity

The g-column guarantee, in its sharpest form: **everything displayed between
two members of a subtree is in the subtree**. A subtree is a coordinate
prefix (the anchor's coordinate); concurrent runs live in disjoint subtrees,
so they cannot interleave. The proof is pure lex-order convexity of
prefix-sets, no property of the code is needed. -/

theorem keyLt_prefix_convex : ∀ {q k1 k2 k3 : List ℕ},
    keyLt k1 k2 = true → keyLt k2 k3 = true →
    q <+: k1 → q <+: k3 → q <+: k2
  | [], _, _, _, _, _, _, _ => List.nil_prefix
  | x :: q', k1, k2, k3, h12, h23, hp1, hp3 => by
      obtain ⟨k1', rfl, hp1'⟩ : ∃ k1', k1 = x :: k1' ∧ q' <+: k1' := by
        cases k1 with
        | nil => exact absurd hp1 (by simp)
        | cons y ys =>
            rcases List.cons_prefix_cons.mp hp1 with ⟨rfl, hp⟩
            exact ⟨ys, rfl, hp⟩
      obtain ⟨k3', rfl, hp3'⟩ : ∃ k3', k3 = x :: k3' ∧ q' <+: k3' := by
        cases k3 with
        | nil => exact absurd hp3 (by simp)
        | cons y ys =>
            rcases List.cons_prefix_cons.mp hp3 with ⟨rfl, hp⟩
            exact ⟨ys, rfl, hp⟩
      cases k2 with
      | nil => simp [keyLt] at h12
      | cons y k2' =>
          simp only [keyLt] at h12 h23
          rcases Nat.lt_trichotomy x y with hxy | rfl | hxy
          · rw [if_neg (by omega : ¬ y < x), if_pos hxy] at h23
            exact Bool.noConfusion h23
          · rw [if_neg (by omega : ¬ x < x)] at h12 h23
            rw [if_neg (by omega : ¬ x < x)] at h12 h23
            exact List.cons_prefix_cons.mpr
              ⟨rfl, keyLt_prefix_convex h12 h23 hp1' hp3'⟩
          · rw [if_neg (by omega : ¬ x < y), if_pos hxy] at h12
            exact Bool.noConfusion h12

theorem map_sym_prefix_reflect : ∀ {c d : coord},
    (c.map sym) <+: (d.map sym) → c <+: d
  | [], _, _ => List.nil_prefix
  | b :: c', d, h => by
      cases d with
      | nil => exact absurd h (by simp)
      | cons b' d' =>
          simp only [List.map_cons] at h
          rcases List.cons_prefix_cons.mp h with ⟨hb, hp⟩
          have : b = b' := by
            cases b <;> cases b' <;> simp [sym] at hb ⊢
          exact this ▸ List.cons_prefix_cons.mpr
            ⟨rfl, map_sym_prefix_reflect hp⟩

/-- A symbol-prefix of a key is a coordinate prefix: the terminator `3` is
outside the symbol alphabet, so the prefix cannot reach past the coordinate. -/
theorem sym_prefix_of_key {c d : coord} (h : (c.map sym) <+: key d) :
    c <+: d := by
  rcases Nat.lt_or_ge d.length c.length with hlt | hle
  · exfalso
    have hlen : c.length ≤ d.length + 1 := by
      have := h.length_le
      simpa [key_def] using this
    have hceq : c.length = d.length + 1 := by omega
    have heq : c.map sym = key d := by
      apply h.eq_of_length
      simp [key_def, hceq]
    have hlast : (c.map sym).getLast? = (key d).getLast? := by rw [heq]
    rw [List.getLast?_map] at hlast
    have hklast : (key d).getLast? = some 3 := by
      rw [key_def]
      exact List.getLast?_concat
    obtain ⟨b, hb⟩ : ∃ b, c.getLast? = some b := by
      cases hc : c.getLast? with
      | none =>
          rw [List.getLast?_eq_none_iff] at hc
          subst hc
          simp at hceq
      | some b => exact ⟨b, rfl⟩
    rw [hb, hklast] at hlast
    have : sym b = 3 := by simpa using hlast
    cases b <;> simp [sym] at this
  · apply map_sym_prefix_reflect
    apply List.prefix_of_prefix_length_le h
      (by rw [key_def]; exact List.prefix_append _ _)
    simpa using hle

omit [DecidableEq α] in
/-- **Non-interleaving (subtree convexity)**: anything displayed between two
members of a subtree is in the subtree. Instantiated at an anchor's
coordinate, this says a concurrently-typed run under one anchor is displayed
contiguously, the litmus g-column, from lex convexity alone. -/
theorem subtree_convex (s : concrete_st α) {c : coord} {t1 t2 t3 : ℕ}
    (h12 : before s t1 t2) (h23 : before s t2 t3)
    (hp1 : c <+: pos s t1) (hp3 : c <+: pos s t3) : c <+: pos s t2 := by
  obtain ⟨-, -, hk12⟩ := h12
  obtain ⟨-, -, hk23⟩ := h23
  have hq1 : (c.map sym) <+: key (pos s t1) := by
    rw [key_def]
    exact (hp1.map sym).trans (List.prefix_append _ _)
  have hq3 : (c.map sym) <+: key (pos s t3) := by
    rw [key_def]
    exact (hp3.map sym).trans (List.prefix_append _ _)
  exact sym_prefix_of_key
    (keyLt_prefix_convex hk23 hk12 hq3 hq1)

end Sal.EmbedRGA
