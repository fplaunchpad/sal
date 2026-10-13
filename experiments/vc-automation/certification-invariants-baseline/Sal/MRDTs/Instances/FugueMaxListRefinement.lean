import Sal.MRDTs.Instances.FugueMaxSequential

namespace Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax

open Sal.MRDTs.Foundation
open Sal.EmbedRGA (OrderedPrefixCode Side FMEntry FMChain fmδ fmCoordOf
  sKey keyLt keyLt_irrefl PosFMChain TagsOK fmChainBefore fmChainBefore_display
  fmdisplay_iff_fmChainBefore)

/-- The public buffer contains only identities and values, with a root
sentinel. Deletes are idempotent, and the total-index sentinel delete is a
no-op. Neither coordinates nor birth metadata occur in this state. -/
def listStep (s : List (Nat × Nat)) (g : MRec) : List (Nat × Nat) :=
  match g.op with
  | .ins p .L => sInsBefore p (g.ts, g.ts) s
  | .ins p .R => sInsAfter p (g.ts, g.ts) s
  | .del x => if x = 0 then s else s.filter (fun p => p.1 != x)

def listRun (ops : KnowM) : List (Nat × Nat) := ops.foldl listStep [(0, 0)]

/-! The following coordinates and construction fold are proof-local. They
relate ordinary splices to the implementation, not to another abstract state. -/

def node (Γ : OrderedPrefixCode) (K : KnowM) (x : Nat) : SRec :=
  (x, x, fmCoordOf Γ (mChainOf K x))

theorem node_chain_ne {Γ : OrderedPrefixCode} {K : KnowM} (inv : KInv Γ K)
    {x y : Nat} (hx : x = 0 ∨ x ∈ mMintedIds K) (hy : y = 0 ∨ y ∈ mMintedIds K)
    (hne : x ≠ y) : mChainOf K x ≠ mChainOf K y := by
  intro heq
  apply hne
  rw [← mChainOf_sum inv hx, ← mChainOf_sum inv hy, heq]

theorem node_display {Γ : OrderedPrefixCode} {K : KnowM} (inv : KInv Γ K)
    {x y : Nat} (hx : x = 0 ∨ x ∈ mMintedIds K) (hy : y = 0 ∨ y ∈ mMintedIds K)
    (hne : x ≠ y) :
    keyLt (sKey (node Γ K y).2.2) (sKey (node Γ K x).2.2) = true ↔
      fmChainBefore (mChainOf K x) (mChainOf K y) :=
  fmdisplay_iff_fmChainBefore Γ (mChainOf_wfparts inv hx).1
    (mChainOf_wfparts inv hy).1 (mChainOf_wfparts inv hx).2
    (mChainOf_wfparts inv hy).2 (node_chain_ne inv hx hy hne)

theorem splice_node {Γ : OrderedPrefixCode} {K : KnowM} (inv : KInv Γ K)
    {g : MRec} (hg : g ∈ K) {p : Nat} {sd : Side} (hop : g.op = .ins p sd)
    {s : SState} (hs : SSorted s)
    (hshape : ∀ r ∈ s, r = node Γ K r.1 ∧ (r.1 = 0 ∨ r.1 ∈ mMintedIds K))
    (hanchor : node Γ K p ∈ s)
    (hfresh : ∀ r ∈ s, r.1 ≠ g.ts)
    (horder : ∀ r ∈ s, ¬ chainBuildBefore g.chain (mChainOf K r.1)) :
    (sInsert (node Γ K g.ts) s).map sProj = listStep (s.map sProj) g := by
  have hi : mIsIns g = true := by simp [mIsIns, hop]
  have hgId : g.ts = 0 ∨ g.ts ∈ mMintedIds K :=
    Or.inr (List.mem_map.mpr ⟨g, List.mem_filter.mpr ⟨hg, hi⟩, rfl⟩)
  have hpId : p = 0 ∨ p ∈ mMintedIds K := (hshape _ hanchor).2
  have hchain := mChainOf_of_mem inv hg hi
  have hinj : ∀ r ∈ s, ∀ r' ∈ s, r.1 = r'.1 → r = r' := by
    intro r hr r' hr' heq
    rw [(hshape r hr).1, (hshape r' hr').1, heq]
  have hkeyne : ∀ r ∈ s, sKey r.2.2 ≠ sKey (node Γ K g.ts).2.2 := by
    intro r hr heq
    apply hfresh r hr
    rw [(hshape r hr).1] at heq
    exact mKey_inj inv (hshape r hr).2 hgId heq
  cases sd with
  | R =>
    obtain ⟨_, hlt, _, hlink, _⟩ := inv.linkR g hg p hop
    have hpg : p ≠ g.ts := Nat.ne_of_lt hlt
    have hpgBefore : fmChainBefore (mChainOf K p) (mChainOf K g.ts) := by
      rw [hchain, hlink]
      exact fmChainBefore.extR _ _ _ []
    have hiff : ∀ r ∈ s,
        keyLt (sKey (node Γ K g.ts).2.2) (sKey r.2.2) = true ↔
          (r = node Γ K p ∨ keyLt (sKey (node Γ K p).2.2) (sKey r.2.2) = true) := by
      intro r hr
      have hri := (hshape r hr).2
      by_cases hrp : r.1 = p
      · have heq : r = node Γ K p := by rw [(hshape r hr).1, hrp]
        rw [heq]
        exact iff_of_true ((node_display inv hpId hgId hpg).mpr hpgBefore) (Or.inl rfl)
      · have hne : mChainOf K r.1 ≠ mChainOf K p := node_chain_ne inv hri hpId hrp
        have hng : mChainOf K r.1 ≠ g.chain := by
          rw [← hchain]
          exact node_chain_ne inv hri hgId (hfresh r hr)
        have hadj := fmChainBefore_snocR_iff (tag := tagK Γ K g.ro)
          (δ := g.ts - p) hne (fun t d rest heq =>
            construction_right (hlink ▸ hng) (hlink ▸ horder r hr) heq)
        have heq : r ≠ node Γ K p := fun heq => hrp (congrArg Prod.fst heq)
        rw [or_iff_right heq]
        rw [(hshape r hr).1, node_display inv hri hgId (hfresh r hr),
          node_display inv hri hpId hrp, hchain, hlink]
        exact hadj
    have h := sInsert_map_insAfter hs hanchor rfl hinj hkeyne hiff
    simpa [listStep, hop, node, sProj] using h
  | L =>
    obtain ⟨_, hlt, _, hlink, _⟩ := inv.linkL g hg p hop
    have hgp : g.ts ≠ p := Ne.symm (Nat.ne_of_lt hlt)
    have hgpBefore : fmChainBefore (mChainOf K g.ts) (mChainOf K p) := by
      rw [hchain, hlink]
      exact fmChainBefore.extL _ _ []
    have hiff : ∀ r ∈ s,
        keyLt (sKey r.2.2) (sKey (node Γ K g.ts).2.2) = true ↔
          (r = node Γ K p ∨ keyLt (sKey r.2.2) (sKey (node Γ K p).2.2) = true) := by
      intro r hr
      have hri := (hshape r hr).2
      by_cases hrp : r.1 = p
      · have heq : r = node Γ K p := by rw [(hshape r hr).1, hrp]
        rw [heq]
        exact iff_of_true ((node_display inv hgId hpId hgp).mpr hgpBefore) (Or.inl rfl)
      · have hne : mChainOf K r.1 ≠ mChainOf K p := node_chain_ne inv hri hpId hrp
        have hng : mChainOf K r.1 ≠ g.chain := by
          rw [← hchain]
          exact node_chain_ne inv hri hgId (hfresh r hr)
        have hadj := fmChainBefore_snocL_iff (δ := g.ts - p) hne
          (fun d rest heq => construction_left (hlink ▸ hng) (hlink ▸ horder r hr) heq)
        have heq : r ≠ node Γ K p := fun heq => hrp (congrArg Prod.fst heq)
        rw [or_iff_right heq]
        rw [(hshape r hr).1, node_display inv hgId hri (Ne.symm (hfresh r hr)),
          node_display inv hpId hri (Ne.symm hrp), hchain, hlink]
        exact hadj
    have h := sInsert_map_insBefore hs hanchor rfl hinj hiff
    simpa [listStep, hop, node, sProj] using h

def buildNodes (Γ : OrderedPrefixCode) (K L : KnowM) : SState :=
  L.foldl (fun s g => sInsert (node Γ K g.ts) s) [node Γ K 0]

theorem buildNodes_snoc (Γ : OrderedPrefixCode) (K L : KnowM) (g : MRec) :
    buildNodes Γ K (L ++ [g]) = sInsert (node Γ K g.ts) (buildNodes Γ K L) := by
  simp [buildNodes, List.foldl_append]

theorem buildNodes_mem (Γ : OrderedPrefixCode) (K L : KnowM) (r : SRec) :
    r ∈ buildNodes Γ K L ↔ r = node Γ K 0 ∨ ∃ g ∈ L, r = node Γ K g.ts := by
  induction L using List.reverseRecOn with
  | nil => simp [buildNodes]
  | append_singleton L g ih =>
    rw [buildNodes_snoc, mem_sInsert, ih]
    simp only [List.mem_append, List.mem_singleton]
    aesop

def BirthParents (L : KnowM) : Prop :=
  ∀ pre g post, L = pre ++ g :: post → ∀ p sd, g.op = .ins p sd →
    p = 0 ∨ ∃ b ∈ pre, b.ts = p

theorem birth_parents_of_construction {Γ : OrderedPrefixCode} {K L : KnowM}
    (inv : KInv Γ K) (hp : (mMinted K).Perm L)
    (hr : respects L (fun a b => chainBuildBefore a.chain b.chain)) : BirthParents L := by
  intro pre g post heq p sd hop
  have hgL : g ∈ L := by rw [heq]; simp
  have hgK := List.mem_filter.mp (hp.mem_iff.mpr hgL)
  have hlink : p < g.ts ∧ (p = 0 ∨ p ∈ mMintedIds K) ∧
      (mChainOf K p).length < g.chain.length := by
    cases sd with
    | R =>
      obtain ⟨_, hlt, hm, hc, _⟩ := inv.linkR g hgK.1 p hop
      exact ⟨hlt, hm, by rw [hc]; simp⟩
    | L =>
      obtain ⟨_, hlt, hm, hc, _⟩ := inv.linkL g hgK.1 p hop
      exact ⟨hlt, Or.inr hm, by rw [hc]; simp⟩
  rcases hlink.2.1 with hz | hm
  · exact Or.inl hz
  obtain ⟨b, hbm, hbt⟩ := List.mem_map.mp hm
  have hbK := List.mem_filter.mp hbm
  have hbL := hp.mem_iff.mp hbm
  rw [heq, List.mem_append, List.mem_cons] at hbL
  rcases hbL with hbpre | rfl | hbpost
  · exact Or.inr ⟨b, hbpre, hbt⟩
  · exact False.elim ((Nat.ne_of_lt hlink.1) hbt.symm)
  · have hpw := hr
    rw [heq] at hpw
    have hneg := (List.pairwise_cons.mp (List.pairwise_append.mp hpw).2.1).1 b hbpost
    apply False.elim
    apply hneg
    apply Or.inl
    rw [← mChainOf_of_mem inv hbK.1 hbK.2, hbt]
    exact hlink.2.2

theorem births_refine {Γ : OrderedPrefixCode} {K L : KnowM}
    (inv : KInv Γ K) (hsub : ∀ g ∈ L, g ∈ K ∧ mIsIns g = true)
    (hnd : L.Nodup) (hr : respects L (fun a b => chainBuildBefore a.chain b.chain))
    (hparents : BirthParents L) :
    SSorted (buildNodes Γ K L) ∧ (buildNodes Γ K L).map sProj = listRun L := by
  induction L using List.reverseRecOn with
  | nil => exact ⟨by simp [buildNodes, SSorted], rfl⟩
  | append_singleton L g ih =>
    have hsubL : ∀ b ∈ L, b ∈ K ∧ mIsIns b = true :=
      fun b hb => hsub b (List.mem_append_left _ hb)
    have hg := hsub g (by simp)
    have hparts := List.nodup_append.mp hnd
    have hrparts := List.pairwise_append.mp hr
    have hparL : BirthParents L := by
      intro pre b post heq p sd hop
      exact hparents pre b (post ++ [g]) (by rw [heq]; simp) p sd hop
    obtain ⟨hs, hf⟩ := ih hsubL hparts.1 hrparts.1 hparL
    have hshape : ∀ r ∈ buildNodes Γ K L,
        r = node Γ K r.1 ∧ (r.1 = 0 ∨ r.1 ∈ mMintedIds K) := by
      intro r hr
      rcases (buildNodes_mem Γ K L r).mp hr with rfl | ⟨b, hb, rfl⟩
      · exact ⟨rfl, Or.inl rfl⟩
      · exact ⟨rfl, Or.inr (List.mem_map.mpr
          ⟨b, List.mem_filter.mpr (hsubL b hb), rfl⟩)⟩
    have hfresh : ∀ r ∈ buildNodes Γ K L, r.1 ≠ g.ts := by
      intro r hr ht
      rcases (buildNodes_mem Γ K L r).mp hr with rfl | ⟨b, hb, rfl⟩
      · have := inv.pos g hg.1
        change 0 = g.ts at ht
        omega
      · have hbg := inv.uniq b (hsubL b hb).1 g hg.1 (hsubL b hb).2 hg.2 ht
        exact hparts.2.2 b hb g (by simp) hbg
    have hgId : g.ts = 0 ∨ g.ts ∈ mMintedIds K :=
      Or.inr (List.mem_map.mpr ⟨g, List.mem_filter.mpr hg, rfl⟩)
    have hkeyne : ∀ r ∈ buildNodes Γ K L,
        sKey r.2.2 ≠ sKey (node Γ K g.ts).2.2 := by
      intro r hr heq
      apply hfresh r hr
      rw [(hshape r hr).1] at heq
      exact mKey_inj inv (hshape r hr).2 hgId heq
    have horder : ∀ r ∈ buildNodes Γ K L,
        ¬ chainBuildBefore g.chain (mChainOf K r.1) := by
      intro r hr
      rcases (buildNodes_mem Γ K L r).mp hr with rfl | ⟨b, hb, rfl⟩
      · rw [show (node Γ K 0).1 = 0 from rfl, mChainOf_zero inv.pos]
        intro ho
        have hd := chainBuildBefore_length ho
        have hn := kinv_chain_ne_nil inv g hg.1 hg.2
        simp only [List.length_nil, Nat.le_zero, List.length_eq_zero_iff] at hd
        exact hn hd
      · change ¬ chainBuildBefore g.chain (mChainOf K b.ts)
        rw [mChainOf_of_mem inv (hsubL b hb).1 (hsubL b hb).2]
        exact hrparts.2.2 b hb g (by simp)
    obtain ⟨p, sd, hop⟩ := mIsIns_shape hg.2
    have hanchor : node Γ K p ∈ buildNodes Γ K L := by
      apply (buildNodes_mem Γ K L _).mpr
      rcases hparents L g [] rfl p sd hop with hz | ⟨b, hb, ht⟩
      · exact Or.inl (by rw [hz])
      · exact Or.inr ⟨b, hb, by rw [ht]⟩
    refine ⟨by rw [buildNodes_snoc]; exact sInsert_sorted hs hkeyne, ?_⟩
    rw [buildNodes_snoc, splice_node inv hg.1 hop hs hshape hanchor hfresh horder, hf]
    simp [listRun, List.foldl_append]

def eraseNodes (s : SState) : KnowM → SState
  | [] => s
  | g :: rest => eraseNodes (match g.op with
      | .ins _ _ => s
      | .del x => if x = 0 then s else s.filter (fun r => r.1 != x)) rest

theorem map_projection_filter (s : SState) (keep : Nat → Bool) :
    (s.filter (fun r => keep r.1)).map sProj =
      (s.map sProj).filter (fun p => keep p.1) := by
  induction s with
  | nil => rfl
  | cons r s ih => cases hk : keep r.1 <;> simp [hk, sProj, ih]

theorem eraseNodes_project (s : SState) (D : KnowM)
    (hd : ∀ g ∈ D, mIsIns g = false) :
    (eraseNodes s D).map sProj = D.foldl listStep (s.map sProj) := by
  induction D generalizing s with
  | nil => rfl
  | cons g D ih =>
    have hg := hd g List.mem_cons_self
    have ih' := fun s => ih s (fun g hg => hd g (List.mem_cons_of_mem _ hg))
    cases hop : g.op with
    | ins p sd => simp [mIsIns, hop] at hg
    | del x =>
      by_cases hx : x = 0
      · simp [eraseNodes, listStep, hop, hx, ih']
      · simp only [eraseNodes, hop, if_neg hx, List.foldl_cons, listStep]
        rw [ih', map_projection_filter s (fun n => n != x)]

theorem eraseNodes_mem (s : SState) (D : KnowM) (r : SRec) (hn : r.1 ≠ 0) :
    r ∈ eraseNodes s D ↔ r ∈ s ∧ ∀ d ∈ D, d.op ≠ .del r.1 := by
  induction D generalizing s with
  | nil => simp [eraseNodes]
  | cons g D ih =>
    cases hop : g.op with
    | ins p sd => simp [eraseNodes, hop, ih]
    | del x =>
      by_cases hx : x = 0
      · subst x
        simpa [eraseNodes, hop, hn, Ne.symm hn] using ih s
      · simp only [eraseNodes, hop, if_neg hx, ih, List.mem_filter,
          bne_iff_ne, List.mem_cons, forall_eq_or_imp]
        simp only [ne_eq, MOp.del.injEq]
        tauto

theorem eraseNodes_sorted {s : SState} (hs : SSorted s) (D : KnowM) :
    SSorted (eraseNodes s D) := by
  induction D generalizing s with
  | nil => exact hs
  | cons g D ih =>
    cases hop : g.op with
    | ins p sd => simpa [eraseNodes, hop] using ih hs
    | del x =>
      by_cases hx : x = 0
      · simpa [eraseNodes, hop, hx] using ih hs
      · simpa [eraseNodes, hop, hx] using ih (hs.filter _)

def finalNodes (Γ : OrderedPrefixCode) (K L D : KnowM) : SState :=
  (eraseNodes (buildNodes Γ K L) D).filter (fun r => r.1 != 0)

theorem finalNodes_mem (Γ : OrderedPrefixCode) (K L D : KnowM) (r : SRec) :
    r ∈ finalNodes Γ K L D ↔
      (∃ g ∈ L, r = node Γ K g.ts) ∧ r.1 ≠ 0 ∧ ∀ d ∈ D, d.op ≠ .del r.1 := by
  simp only [finalNodes, List.mem_filter, bne_iff_ne]
  constructor
  · rintro ⟨hr, hn⟩
    obtain ⟨hr, hd⟩ := (eraseNodes_mem _ _ _ hn).mp hr
    rcases (buildNodes_mem Γ K L r).mp hr with rfl | hb
    · exact False.elim (hn rfl)
    · exact ⟨hb, hn, hd⟩
  · rintro ⟨hb, hn, hd⟩
    exact ⟨(eraseNodes_mem _ _ _ hn).mpr
      ⟨(buildNodes_mem Γ K L r).mpr (Or.inr hb), hd⟩, hn⟩

theorem finalNodes_project {Γ : OrderedPrefixCode} {K L D : KnowM}
    (hbirths : (buildNodes Γ K L).map sProj = listRun L)
    (hd : ∀ g ∈ D, mIsIns g = false) :
    (finalNodes Γ K L D).map sProj =
      (listRun (L ++ D)).filter (fun p => p.1 != 0) := by
  rw [finalNodes, map_projection_filter _ (fun n => n != 0),
    eraseNodes_project _ _ hd, hbirths]
  simp [listRun, List.foldl_append]

#print axioms splice_node
#print axioms births_refine

end Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax
