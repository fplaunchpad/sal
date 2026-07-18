import Sal.ConditionedMRDTs.MRDT_Instances.SidedRGA.SidedRGA_FugueMax
import Sal.MRDTs.RGA_Embed.Sided_Traversal

/-!
# FugueMax forward non-interleaving: the condition-(1) discharge (task #88)

Design: `whiteboard/fugue-maximal-noninterleaving.md` section 9; Python
twin: `whiteboard/litmus/traversal_check.py` (traversal = display and the
loShape invariant, 12 directed cases + 1800 randomized states, clean).

This file discharges the stated def `FugueMaxForwardNonInterleaving`
(Weidner-Kleppmann Definition 4 condition (1), strict reading) at every
replica of every `MaxReach`-reachable configuration, kernel-clean. The
route is the paper's Lemma 7 + Lemma 8(a) layer replayed on chains:

* **§1 The loShape invariant** (Lemma 8(a) in chain form): every minted
  element's chain is its left origin's chain, one R entry, then L entries
  only. R mints carry it via the existing `LinkR`; L mints need the one
  genuinely new clause `SLC`, the all-L successor shape: the
  tombstone-visible successor of an anchor with an R-child extends the
  anchor by one R entry and L entries only (`succ_R_desc_allL`, an argmax
  argument on `succOfM`). `maxReach_inv2` threads `SLC` through inserts,
  deletes, and syncs.

* **§2 The first-after descent** (`lo_child_before`): any minted element
  R-headedly below A has, on its left-origin walk, a minted element with
  recorded left origin exactly A displaying no later. Strong induction on
  chain length; the loShape decompositions of the walk collide with the
  all-L tails at every misalignment.

* **§3 The discharge**: `forwardNIM_of_inv` and
  `fuguemax_forward_ni : FugueMaxForwardNonInterleaving Γ`. Full adapted
  Theorem 9 now reduces to the backward condition alone
  (`fuguemax_theorem9_of_backward`); the backward design state is section
  9.6 of the note.

* **§4 SPOTs**, PASS+FAIL shaped, on the Figure-7 and L19 traces.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode keyLt sKey unaryCode Side
  keyLt_irrefl keyLt_asymm keyLt_trans keyLt_total
  FMEntry FMChain fmδ PosFMChain TagOK fmTagOK TagsOK
  fmCoordOf fmChainBefore fmChainBefore_display
  fmdisplay_iff_fmChainBefore fm_subtree_convex fm_ext_after_is_R)

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## §1  The loShape invariant -/

/-- L-entries-only chains: the tail shape of a left-origin walk step. -/
def AllL (ls : FMChain) : Prop := ∀ e ∈ ls, ∃ d, e = FMEntry.L d

/-- **The strengthened L-mint clause** (the one new invariant clause):
an L mint's parent (= its recorded right origin, the mint-time successor)
extends the recorded left origin by one R entry and L entries only. -/
def SLC (Γ : OrderedPrefixCode) (K : KnowM) (g : MRec) : Prop :=
  ∀ p, g.op = MOp.ins p Side.L →
    ∃ t d ls, mChainOf K p = mChainOf K g.lo ++ FMEntry.R t d :: ls ∧
      AllL ls

/-- Transport under knowledge growth: chain lookups of the parent and the
left origin are stable, so the clause is. -/
theorem slc_transport {Γ : OrderedPrefixCode} {K K' : KnowM} {g : MRec}
    (h : SLC Γ K g) (hlk : LinkL Γ K g)
    (hchain : ∀ y, y = 0 ∨ y ∈ mMintedIds K →
      mChainOf K' y = mChainOf K y) :
    SLC Γ K' g := by
  intro p hop
  obtain ⟨t, d, ls, hdec, hall⟩ := h p hop
  obtain ⟨-, -, h3, -, h5, -⟩ := hlk p hop
  refine ⟨t, d, ls, ?_, hall⟩
  rw [hchain p (Or.inr h3), hchain g.lo h5]
  exact hdec

/-- **The all-L successor shape** (the mint-step engine): the successor
of an anchor with an R-child extends the anchor by one R entry and L
entries only. `succ_R_descendant` gives the decomposition; if the rest
held an R entry, the node just above it (minted by ancestor closure)
would display after the anchor and before the successor, beating the
argmax. -/
theorem succ_R_desc_allL {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) {a n : ℕ}
    (ha : a = 0 ∨ a ∈ mMintedIds K)
    (hR : hasRChildM K a = true)
    (hs : succOfM Γ K a = some n) :
    ∃ t d ls, mChainOf K n = mChainOf K a ++ FMEntry.R t d :: ls ∧
      AllL ls := by
  obtain ⟨t, d, rest, hdec⟩ := succ_R_descendant inv ha hR hs
  refine ⟨t, d, rest, hdec, ?_⟩
  intro e he
  cases e with
  | L d' => exact ⟨d', rfl⟩
  | R t' d' =>
      exfalso
      obtain ⟨u, v, huv⟩ := List.append_of_mem he
      -- the node m just above the offending R entry
      have hm : ∃ pre e0, mChainOf K a ++ FMEntry.R t d :: u
          = pre ++ [e0] := by
        rcases List.eq_nil_or_concat u with rfl | ⟨u', lst, rfl⟩
        · exact ⟨mChainOf K a, FMEntry.R t d, rfl⟩
        · exact ⟨mChainOf K a ++ FMEntry.R t d :: u', lst, by simp⟩
      obtain ⟨pre, e0, hpre_eq⟩ := hm
      have hn : n ∈ mMintedIds K := succOfM_mem hs
      obtain ⟨gn, hnfind, hnK, hnins, hnts⟩ := mRecOfId_of_minted hn
      have hgnchain : mChainOf K n = gn.chain :=
        mChainOf_eq_of_rec hnfind
      have hnfull : gn.chain
          = (mChainOf K a ++ FMEntry.R t d :: u) ++ FMEntry.R t' d' :: v := by
        rw [← hgnchain, hdec, huv]
        simp
      have hprefix : (pre ++ [e0]) <+: gn.chain := by
        rw [hnfull, ← hpre_eq]
        exact ⟨FMEntry.R t' d' :: v, rfl⟩
      obtain ⟨h, hhK, hhins, hhchain⟩ := chain_prefix_minted inv
        gn.chain.length gn hnK hnins (Nat.le_refl _) pre e0 hprefix
      have hm_eq : h.chain = mChainOf K a ++ FMEntry.R t d :: u := by
        rw [hhchain, ← hpre_eq]
      have hhts : h.ts ∈ mMintedIds K :=
        List.mem_map.mpr ⟨h, List.mem_filter.mpr ⟨hhK, hhins⟩, rfl⟩
      have hhchainof : mChainOf K h.ts = h.chain :=
        mChainOf_of_mem inv hhK hhins
      -- wellformedness packages
      have hwa := mChainOf_wfparts inv ha
      have hwn := mChainOf_wfparts inv (Or.inr hn)
      have hwh := mChainOf_wfparts inv (Or.inr hhts)
      -- key facts: a before h, h before n
      have hkey_h : mKey Γ K h.ts = sKey (fmCoordOf Γ h.chain) := by
        unfold mKey
        rw [hhchainof]
      have h_after_a : keyLt (mKey Γ K h.ts) (mKey Γ K a) = true := by
        rw [hkey_h]
        show keyLt (sKey (fmCoordOf Γ h.chain))
          (sKey (fmCoordOf Γ (mChainOf K a))) = true
        apply fmChainBefore_display Γ hwa.1 (hhchainof ▸ hwh.1)
          hwa.2 (hhchainof ▸ hwh.2)
        rw [hm_eq]
        exact fmChainBefore.extR _ _ _ _
      have h_n_before_h : keyLt (mKey Γ K n) (mKey Γ K h.ts) = true := by
        rw [hkey_h]
        show keyLt (sKey (fmCoordOf Γ (mChainOf K n)))
          (sKey (fmCoordOf Γ h.chain)) = true
        apply fmChainBefore_display Γ (hhchainof ▸ hwh.1) hwn.1
          (hhchainof ▸ hwh.2) hwn.2
        rw [hgnchain, hnfull, hm_eq]
        exact fmChainBefore.extR _ _ _ _
      -- h is a successor candidate, so the argmax is not beaten by it
      have hcand : (h.ts, mKey Γ K h.ts) ∈ succCandM Γ K a := by
        unfold succCandM
        by_cases h0 : a = 0
        · rw [if_pos h0]
          exact List.mem_map.mpr ⟨h.ts, hhts, rfl⟩
        · rw [if_neg h0]
          exact List.mem_filter.mpr
            ⟨List.mem_map.mpr ⟨h.ts, hhts, rfl⟩, by simpa using h_after_a⟩
      have hnb := succOfM_max hs hcand
      rw [h_n_before_h] at hnb
      exact Bool.noConfusion hnb

/-- **The supplementary reachability invariant**: every record of every
reachable knowledge satisfies the strengthened L-mint clause. -/
theorem maxReach_inv2 (Γ : OrderedPrefixCode) {G : ℕ → KnowM}
    (h : MaxReach Γ G) : ∀ q, ∀ g ∈ G q, SLC Γ (G q) g := by
  induction h with
  | init =>
      intro q g hg
      exact absurd hg (by simp)
  | @ins G r x i hG hx hfresh hlam ih =>
      have inv := maxReach_inv Γ hG
      have ha : mAnchorAt Γ (G r) i = 0 ∨
          mAnchorAt Γ (G r) i ∈ mMintedIds (G r) := by
        rcases mAnchorAt_cases Γ (G r) i with h0 | hv
        · exact Or.inl h0
        · exact Or.inr (mView_sub_minted Γ (G r) _ hv)
      obtain ⟨hts, hins, -, -, -⟩ :=
        mGenInsAfter_props Γ (inv.each r) r hx hlam ha
      have hpos1 : ∀ h ∈ [mGenInsAt Γ (G r) r x i], 1 ≤ h.ts := by
        intro h hh
        rw [List.mem_singleton] at hh
        subst hh
        rw [show (mGenInsAt Γ (G r) r x i).ts = x from hts]
        exact hx
      have hchain : ∀ y, y = 0 ∨ y ∈ mMintedIds (G r) →
          mChainOf (G r ++ [mGenInsAt Γ (G r) r x i]) y
            = mChainOf (G r) y :=
        fun y hy => mChainOf_append_stable hy (inv.each r).pos hpos1
      intro q g hg
      rcases mem_update_elimM hg with ⟨hq, hg'⟩ | ⟨hq, hg'⟩
      · rw [Function.update_of_ne hq]
        exact ih q g hg'
      · subst hq
        rw [Function.update_self]
        rcases List.mem_append.mp hg' with hgr | hgnew
        · exact slc_transport (ih q g hgr)
            ((inv.each q).linkL g hgr) hchain
        · rw [List.mem_singleton] at hgnew
          subst hgnew
          -- the fresh mint: only the L branch is non-vacuous
          intro p hop
          rcases hsucc : succOfM Γ (G q) (mAnchorAt Γ (G q) i)
            with _ | n
          · rw [show mGenInsAt Γ (G q) q x i
                = mGenInsAfter Γ (G q) q x (mAnchorAt Γ (G q) i)
              from rfl, mGenInsAfter_none hsucc] at hop
            exact Side.noConfusion (by injection hop)
          · cases hRc : hasRChildM (G q) (mAnchorAt Γ (G q) i) with
            | false =>
                rw [show mGenInsAt Γ (G q) q x i
                    = mGenInsAfter Γ (G q) q x (mAnchorAt Γ (G q) i)
                  from rfl, mGenInsAfter_someFalse hsucc hRc] at hop
                exact Side.noConfusion (by injection hop)
            | true =>
                have hrec : mGenInsAt Γ (G q) q x i
                    = { ts := x, rep := q, op := .ins n Side.L,
                        lo := mAnchorAt Γ (G q) i, ro := some n,
                        chain := mChainOf (G q) n ++ [.L (x - n)] } :=
                  mGenInsAfter_someTrue hsucc hRc
                rw [hrec] at hop
                have hpn : p = n := by
                  injection hop with h1 h2
                  exact h1.symm
                subst hpn
                have hn : p ∈ mMintedIds (G q) := succOfM_mem hsucc
                obtain ⟨t, d, ls, hdec, hall⟩ :=
                  succ_R_desc_allL (inv.each q) ha hRc hsucc
                refine ⟨t, d, ls, ?_, hall⟩
                rw [show (mGenInsAt Γ (G q) q x i).lo
                    = mAnchorAt Γ (G q) i from by rw [hrec],
                  hchain p (Or.inr hn), hchain _ ha]
                exact hdec
  | @del G r t i hG ht hfresh ih =>
      have inv := maxReach_inv Γ hG
      have hchain : ∀ y, y = 0 ∨ y ∈ mMintedIds (G r) →
          mChainOf (G r ++ [mGenDelAt Γ (G r) r t i]) y
            = mChainOf (G r) y :=
        fun y _ => mChainOf_snoc_del rfl y
      intro q g hg
      rcases mem_update_elimM hg with ⟨hq, hg'⟩ | ⟨hq, hg'⟩
      · rw [Function.update_of_ne hq]
        exact ih q g hg'
      · subst hq
        rw [Function.update_self]
        rcases List.mem_append.mp hg' with hgr | hgnew
        · exact slc_transport (ih q g hgr)
            ((inv.each q).linkL g hgr) hchain
        · rw [List.mem_singleton] at hgnew
          subst hgnew
          intro p hop
          exfalso
          simp [mGenDelAt] at hop
  | @sync G r r' hG ih =>
      have inv := maxReach_inv Γ hG
      have hposU : ∀ g ∈ syncM (G r) (G r'), 1 ≤ g.ts := by
        intro g hg
        rcases mem_syncM hg with h | h
        · exact (inv.each r).pos g h
        · exact (inv.each r').pos g h
      have hchainL : ∀ y, y = 0 ∨ y ∈ mMintedIds (G r) →
          mChainOf (syncM (G r) (G r')) y = mChainOf (G r) y := by
        intro y hy
        exact mChainOf_append_stable hy (inv.each r).pos
          (fun g hg => (inv.each r').pos g (List.mem_of_mem_filter hg))
      have hchainR : ∀ y, y = 0 ∨ y ∈ mMintedIds (G r') →
          mChainOf (syncM (G r) (G r')) y = mChainOf (G r') y := by
        intro y hy
        rcases hy with rfl | hy
        · rw [mChainOf_zero hposU, mChainOf_zero (inv.each r').pos]
        · exact mChainOf_agree
            (by
              intro g hg g' hg' hi hi' hteq
              rcases mem_syncM hg with h | h
              · exact inv.cross r r' g h g' hg' hi hi' hteq
              · exact inv.cross r' r' g h g' hg' hi hi' hteq)
            (minted_syncM_right hy) hy
      intro q g hg
      rcases mem_update_elimM hg with ⟨hq, hg'⟩ | ⟨hq, hg'⟩
      · rw [Function.update_of_ne hq]
        exact ih q g hg'
      · subst hq
        rw [Function.update_self]
        rcases mem_syncM hg' with hgr | hgr'
        · exact slc_transport (ih q g hgr)
            ((inv.each q).linkL g hgr) hchainL
        · exact slc_transport (ih r' g hgr')
            ((inv.each r').linkL g hgr') hchainR

#print axioms maxReach_inv2

/-! ## §2  loShape and the first-after descent -/

theorem mLoOf_eq {K : KnowM} {x : ℕ} {g : MRec}
    (hfind : mRecOfId K x = some g) : mLoOf K x = g.lo := by
  simp [mLoOf, hfind]

/-- **loShape** (the paper's Lemma 8(a) in chain form): every minted
element's chain is its recorded left origin's chain, one R entry, then L
entries only. -/
theorem loShape_of_inv {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) (inv2 : ∀ g ∈ K, SLC Γ K g)
    {x : ℕ} (hx : x ∈ mMintedIds K) :
    (mLoOf K x = 0 ∨ mLoOf K x ∈ mMintedIds K) ∧
    ∃ t d ls, mChainOf K x
        = mChainOf K (mLoOf K x) ++ FMEntry.R t d :: ls ∧ AllL ls := by
  obtain ⟨g, hfind, hgK, hgins, hgts⟩ := mRecOfId_of_minted hx
  have hlo := mLoOf_eq hfind
  have hcx : mChainOf K x = g.chain := mChainOf_eq_of_rec hfind
  obtain ⟨p, sd, hop⟩ := mIsIns_shape hgins
  cases sd with
  | R =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := inv.linkR g hgK p hop
      refine ⟨by rw [hlo, ← h1]; exact h3,
        tagK Γ K g.ro, g.ts - p, [], ?_, ?_⟩
      · rw [hcx, h4, hlo, ← h1]
      · intro e he
        exact absurd he (by simp)
  | L =>
      obtain ⟨t, d, ls, hdec, hall⟩ := inv2 g hgK p hop
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := inv.linkL g hgK p hop
      refine ⟨by rw [hlo]; exact h5,
        t, d, ls ++ [FMEntry.L (g.ts - p)], ?_, ?_⟩
      · rw [hcx, h4, hdec, hlo]
        simp
      · intro e he
        rcases List.mem_append.mp he with h | h
        · exact hall e h
        · rw [List.mem_singleton] at h
          exact ⟨_, h⟩

/-- **The first-after descent**: any minted `c` sitting R-headedly below
`A` has, on its left-origin walk, a minted element with recorded left
origin exactly `A` displaying no later than `c`. Strong induction on
chain length; the loShape decompositions collide with the all-L tails at
every misalignment. -/
theorem lo_child_before {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) (inv2 : ∀ g ∈ K, SLC Γ K g) :
    ∀ (N c : ℕ), c ∈ mMintedIds K → (mChainOf K c).length ≤ N →
    ∀ A : ℕ, (A = 0 ∨ A ∈ mMintedIds K) →
    (∃ t d ext, mChainOf K c = mChainOf K A ++ FMEntry.R t d :: ext) →
    ∃ D ∈ mMintedIds K, mLoOf K D = A ∧
      (D = c ∨ keyLt (mKey Γ K c) (mKey Γ K D) = true) := by
  intro N
  induction N with
  | zero =>
      intro c hc hlen A hA hext
      exfalso
      obtain ⟨t, d, ext, hext⟩ := hext
      have := congrArg List.length hext
      simp at this
      omega
  | succ N ih =>
      intro c hc hlen A hA hext
      obtain ⟨t, d, ext, hext⟩ := hext
      obtain ⟨hloOr, t', d', ls', hdec, hall⟩ := loShape_of_inv inv inv2 hc
      have p1 : mChainOf K A <+: mChainOf K c :=
        ⟨FMEntry.R t d :: ext, hext.symm⟩
      have p2 : mChainOf K (mLoOf K c) <+: mChainOf K c :=
        ⟨FMEntry.R t' d' :: ls', hdec.symm⟩
      rcases List.prefix_or_prefix_of_prefix p2 p1 with hpre | hpre
      · -- chain(lo c) a prefix of chain(A)
        obtain ⟨u, hu⟩ := hpre
        cases u with
        | nil =>
            -- equal chains: lo c = A, take D = c
            rw [List.append_nil] at hu
            have hAeq : mLoOf K c = A := by
              have s1 := mChainOf_sum inv hloOr
              have s2 := mChainOf_sum inv hA
              rw [hu] at s1
              omega
            exact ⟨c, hc, hAeq, Or.inl rfl⟩
        | cons e u' =>
            -- misalignment: A's R entry lands inside the all-L tail
            exfalso
            have hcc : mChainOf K (mLoOf K c)
                ++ FMEntry.R t' d' :: ls'
                = mChainOf K (mLoOf K c)
                  ++ (e :: u') ++ FMEntry.R t d :: ext := by
              rw [← hdec, hext, ← hu]
            rw [List.append_assoc] at hcc
            have hcc' := List.append_cancel_left hcc
            rw [List.cons_append] at hcc'
            injection hcc' with h1 h2
            have hmem : FMEntry.R t d ∈ ls' := by
              rw [h2]
              exact List.mem_append_right _ List.mem_cons_self
            obtain ⟨dd, hL⟩ := hall _ hmem
            exact FMEntry.noConfusion hL
      · -- chain(A) a prefix of chain(lo c)
        obtain ⟨v, hv⟩ := hpre
        cases v with
        | nil =>
            rw [List.append_nil] at hv
            have hAeq : mLoOf K c = A := by
              have s1 := mChainOf_sum inv hloOr
              have s2 := mChainOf_sum inv hA
              rw [← hv] at s1
              omega
            exact ⟨c, hc, hAeq, Or.inl rfl⟩
        | cons e v' =>
            -- chain(lo c) strictly extends chain(A), R-headedly: recurse
            have hcc : mChainOf K A ++ FMEntry.R t d :: ext
                = mChainOf K A
                  ++ (e :: v') ++ FMEntry.R t' d' :: ls' := by
              rw [← hext, hdec, ← hv]
            rw [List.append_assoc] at hcc
            have hcc' := List.append_cancel_left hcc
            rw [List.cons_append] at hcc'
            injection hcc' with h1 h2
            have hlomint : mLoOf K c ∈ mMintedIds K := by
              rcases hloOr with h0 | h
              · exfalso
                rw [h0, mChainOf_zero inv.pos] at hv
                have := congrArg List.length hv
                simp at this
              · exact h
            have hlolen : (mChainOf K (mLoOf K c)).length ≤ N := by
              have := congrArg List.length hdec
              simp at this
              omega
            obtain ⟨D, hD, hDlo, hor⟩ := ih (mLoOf K c) hlomint hlolen
              A hA ⟨t, d, v', by rw [← hv, ← h1]⟩
            -- lo c displays before c
            have hwl := mChainOf_wfparts inv (Or.inr hlomint)
            have hwc := mChainOf_wfparts inv (Or.inr hc)
            have hbefore : keyLt (mKey Γ K c) (mKey Γ K (mLoOf K c))
                = true := by
              show keyLt (sKey (fmCoordOf Γ (mChainOf K c)))
                (sKey (fmCoordOf Γ (mChainOf K (mLoOf K c)))) = true
              apply fmChainBefore_display Γ hwl.1 hwc.1 hwl.2 hwc.2
              rw [hdec]
              exact fmChainBefore.extR _ _ _ _
            refine ⟨D, hD, hDlo, Or.inr ?_⟩
            rcases hor with rfl | hlt
            · exact hbefore
            · exact keyLt_trans hbefore hlt

#print axioms lo_child_before

/-! ## §3  The forward discharge -/

/-- **Condition (1) from the invariant bundles**: loShape places B in
A's R-subtree; convexity traps any live in-between element there too;
the descent produces an element with left origin A displaying strictly
before B, against B's minimality. -/
theorem forwardNIM_of_inv {Γ : OrderedPrefixCode} {K : KnowM}
    (inv : KInv Γ K) (inv2 : ∀ g ∈ K, SLC Γ K g) :
    ForwardNIM Γ K := by
  intro A hA B hB hliveA hliveB hloB hmin
  obtain ⟨hloOrB, t, d, ls, hdecB, hallB⟩ := loShape_of_inv inv inv2 hB
  rw [hloB] at hdecB
  have hwA := mChainOf_wfparts inv (Or.inr hA)
  have hwB := mChainOf_wfparts inv (Or.inr hB)
  have hAB : mBefore Γ K A B := by
    show keyLt (mKey Γ K B) (mKey Γ K A) = true
    show keyLt (sKey (fmCoordOf Γ (mChainOf K B)))
      (sKey (fmCoordOf Γ (mChainOf K A))) = true
    apply fmChainBefore_display Γ hwA.1 hwB.1 hwA.2 hwB.2
    rw [hdecB]
    exact fmChainBefore.extR _ _ _ _
  refine ⟨hAB, ?_⟩
  rintro c hlivec ⟨hAc, hcB⟩
  have hcm : c ∈ mMintedIds K := mView_sub_minted Γ K c hlivec
  have hwc := mChainOf_wfparts inv (Or.inr hcm)
  -- chain-level order facts
  have hneAc : mChainOf K A ≠ mChainOf K c := by
    intro he
    have hAc' : keyLt (mKey Γ K c) (mKey Γ K A) = true := hAc
    unfold mKey at hAc'
    rw [he, keyLt_irrefl] at hAc'
    exact Bool.noConfusion hAc'
  have hnecB : mChainOf K c ≠ mChainOf K B := by
    intro he
    have hcB' : keyLt (mKey Γ K B) (mKey Γ K c) = true := hcB
    unfold mKey at hcB'
    rw [he, keyLt_irrefl] at hcB'
    exact Bool.noConfusion hcB'
  have hbAc : fmChainBefore (mChainOf K A) (mChainOf K c) :=
    (fmdisplay_iff_fmChainBefore Γ hwA.1 hwc.1 hwA.2 hwc.2 hneAc).mp hAc
  have hbcB : fmChainBefore (mChainOf K c) (mChainOf K B) :=
    (fmdisplay_iff_fmChainBefore Γ hwc.1 hwB.1 hwc.2 hwB.2 hnecB).mp hcB
  -- convexity: c is in A's subtree, R-headedly
  obtain ⟨ec, hec⟩ := fm_subtree_convex (mChainOf K A)
    ⟨[], (List.append_nil _).symm⟩ ⟨FMEntry.R t d :: ls, hdecB⟩ hbAc hbcB
  obtain ⟨t', d', rest', hecR⟩ :=
    fm_ext_after_is_R (p := mChainOf K A) (ext := ec)
      (by rw [← hec]; exact hbAc)
  -- the descent
  obtain ⟨D, hD, hDlo, hor⟩ := lo_child_before inv inv2
    (mChainOf K c).length c hcm (Nat.le_refl _) A (Or.inr hA)
    ⟨t', d', rest', by rw [hec, hecR]⟩
  -- close the cycle against B's minimality
  have hDB : D ≠ B := by
    rintro rfl
    have h0 : keyLt (mKey Γ K D) (mKey Γ K c) = true := hcB
    rcases hor with heq | hlt
    · rw [heq, keyLt_irrefl] at h0
      exact Bool.noConfusion h0
    · have h1 := keyLt_trans hlt h0
      rw [keyLt_irrefl] at h1
      exact Bool.noConfusion h1
  have hmin' : keyLt (mKey Γ K D) (mKey Γ K B) = true := hmin D hD hDlo hDB
  have hcB' : keyLt (mKey Γ K B) (mKey Γ K c) = true := hcB
  have h1 : keyLt (mKey Γ K D) (mKey Γ K c) = true :=
    keyLt_trans hmin' hcB'
  rcases hor with heq | hlt
  · rw [← heq, keyLt_irrefl] at h1
    exact Bool.noConfusion h1
  · have h2 := keyLt_trans h1 hlt
    rw [keyLt_irrefl] at h2
    exact Bool.noConfusion h2

/-- **The condition-(1) gap of Theorem 9 is DISCHARGED**: forward
non-interleaving holds at every replica of every reachable FugueMax
configuration. -/
theorem fuguemax_forward_ni (Γ : OrderedPrefixCode) :
    FugueMaxForwardNonInterleaving Γ := by
  intro G hG r
  exact forwardNIM_of_inv ((maxReach_inv Γ hG).each r)
    (maxReach_inv2 Γ hG r)

#print axioms fuguemax_forward_ni

/-- **Full adapted Theorem 9 now reduces to the backward condition
alone**: conditions (1) and (3) are theorems. The backward design state
is section 9.6 of the note. -/
theorem fuguemax_theorem9_of_backward {Γ : OrderedPrefixCode}
    (h2 : FugueMaxBackwardNonInterleaving Γ) :
    FugueMaxMaximallyNonInterleaving Γ :=
  fuguemax_max_noninterleaving_of_gaps (fuguemax_forward_ni Γ) h2

#print axioms fuguemax_theorem9_of_backward

/-! ## §4  SPOTs (PASS+FAIL, hand-derived, matching traversal_check.py)

The loShape invariant watched concretely on the Figure-7 and L19 traces
of the FugueMax file, and the condition-(1) content (A adjacent to its
display-first left-origin child) read off the displays. -/

namespace TravSPOT

/-- Bool form of "R-headed" for concrete chains. -/
def isRHeadB : FMChain → Bool
  | FMEntry.R _ _ :: _ => true
  | _ => false

/-- Bool form of `AllL` for concrete chains. -/
def allLB (ls : FMChain) : Bool :=
  ls.all fun e => match e with | FMEntry.L _ => true | _ => false

/-- The loShape extension of x over its recorded left origin. -/
def loExt (K : KnowM) (x : ℕ) : FMChain :=
  (mChainOf K x).drop (mChainOf K (mLoOf K x)).length

/-- PASS: on Figure 7, X = 6 and Y = 7 both record left origin A = 3. -/
theorem fig7_lo_6 : mLoOf FugueMaxSPOT.kFig 6 = 3 := by native_decide
theorem fig7_lo_7 : mLoOf FugueMaxSPOT.kFig 7 = 3 := by native_decide

/-- FAIL pin: Y's left origin is NOT its right origin B = 4. -/
theorem fig7_lo_7_not_ro : mLoOf FugueMaxSPOT.kFig 7 ≠ 4 := by
  native_decide

/-- PASS: loShape on Figure 7, entry by entry: X extends A's chain by
one R entry and nothing else; the prefix really is A's chain. -/
theorem fig7_loshape_6 :
    ((mChainOf FugueMaxSPOT.kFig 3).isPrefixOf
        (mChainOf FugueMaxSPOT.kFig 6)
      && isRHeadB (loExt FugueMaxSPOT.kFig 6)
      && allLB ((loExt FugueMaxSPOT.kFig 6).drop 1)) = true := by
  native_decide

/-- PASS: loShape on the L19 backward trace: 10 is an L-mint (child of
1, left origin start), so its extension over start is R then L. -/
theorem l19_loshape_10 :
    (mLoOf FugueMaxSPOT.k19 10 = 0
      ∧ isRHeadB (loExt FugueMaxSPOT.k19 10) = true
      ∧ allLB ((loExt FugueMaxSPOT.k19 10).drop 1) = true) := by
  native_decide

/-- FAIL pin: the extension of 10 is NOT all-R (its tail is the L
entry; the walk-up rule has something to strip). -/
theorem l19_ext_10_not_allR :
    ¬ ((loExt FugueMaxSPOT.k19 10).all
        (fun e => isRHeadB [e]) = true) := by native_decide

/-- PASS: the condition-(1) adjacency on Figure 7: A = 3 and its
display-first left-origin child X = 6 are consecutive in the view. -/
theorem fig7_forward_adjacent :
    (mView unaryCode FugueMaxSPOT.kFig).take 2 = [3, 6] := by
  native_decide

/-- FAIL pin: Y = 7 is not adjacent to A = 3. -/
theorem fig7_not_y_adjacent :
    (mView unaryCode FugueMaxSPOT.kFig).take 2 ≠ [3, 7] := by
  native_decide

end TravSPOT

#print axioms TravSPOT.fig7_loshape_6
#print axioms TravSPOT.fig7_forward_adjacent
