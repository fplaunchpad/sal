import Sal.MRDTs.Instances.FugueMaxIssuer

/-!
# Birth enumeration is not part of FugueMax policy

On coherent births, record lookup and the successor argmax depend on birth
membership, not list order or multiplicity. This permits a finite-set MRDT
representation while retaining an executable list-based issuer.
-/

namespace Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax

open Sal.EmbedRGA (OrderedPrefixCode keyLt keyLt_total)

theorem recOf_eq_of_births {Γ : OrderedPrefixCode} {K L : KnowM}
    (inv : KInv Γ K) (hm : ∀ g, g ∈ mMinted K ↔ g ∈ mMinted L) (x : ℕ) :
    mRecOfId K x = mRecOfId L x := by
  cases hk : mRecOfId K x with
  | none =>
      cases hl : mRecOfId L x with
      | none => rfl
      | some g =>
          have hg := (hm g).mpr (List.mem_of_find?_eq_some hl)
          have hx := List.find?_some hl
          have hn := List.find?_eq_none.mp hk g hg
          simp_all
  | some g =>
      have hg := List.mem_of_find?_eq_some hk
      have hx : g.ts = x := by simpa using List.find?_some hk
      have hL : x ∈ mMintedIds L :=
        List.mem_map.mpr ⟨g, (hm g).mp hg, hx⟩
      obtain ⟨b, hb, hbL, hbi, hbx⟩ := mRecOfId_of_minted hL
      rw [hb]
      congr 1
      have hbK := List.mem_filter.mp ((hm b).mpr (List.mem_filter.mpr ⟨hbL, hbi⟩))
      exact inv.uniq g (List.mem_filter.mp hg).1 b hbK.1
        (List.mem_filter.mp hg).2 hbK.2 (hx.trans hbx.symm)

theorem chain_eq_of_births {Γ : OrderedPrefixCode} {K L : KnowM}
    (inv : KInv Γ K) (hm : ∀ g, g ∈ mMinted K ↔ g ∈ mMinted L) (x : ℕ) :
    mChainOf K x = mChainOf L x := by
  simp [mChainOf, recOf_eq_of_births inv hm]

theorem ids_eq_of_births {K L : KnowM}
    (hm : ∀ g, g ∈ mMinted K ↔ g ∈ mMinted L) (x : ℕ) :
    x ∈ mMintedIds K ↔ x ∈ mMintedIds L := by
  simp only [mMintedIds, List.mem_map, hm]

theorem hasRChild_eq_of_births {K L : KnowM}
    (hm : ∀ g, g ∈ mMinted K ↔ g ∈ mMinted L) (a : ℕ) :
    hasRChildM K a = hasRChildM L a := by
  rw [← hasRChild_minted K, ← hasRChild_minted L]
  apply Bool.eq_iff_iff.mpr
  simp only [hasRChildM_iff, hm]

private theorem maxKey_fold_none (xs : List (ℕ × List ℕ))
    (acc : Option (ℕ × List ℕ)) :
    xs.foldl maxKey acc = none ↔ xs = [] ∧ acc = none := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih]
      cases acc with
      | none => simp [maxKey]
      | some a => by_cases h : keyLt a.2 x.2 <;> simp [maxKey, h]

private theorem successor_none (Γ : OrderedPrefixCode) (K : KnowM) (a : ℕ) :
    succOfM Γ K a = none ↔ succCandM Γ K a = [] := by
  simp [succOfM, maxKey_fold_none]

theorem successor_eq_of_births {Γ : OrderedPrefixCode} {K L : KnowM}
    (inv : KInv Γ K) (hm : ∀ g, g ∈ mMinted K ↔ g ∈ mMinted L) (a : ℕ) :
    succOfM Γ K a = succOfM Γ L a := by
  have hkey : ∀ x, mKey Γ K x = mKey Γ L x := by
    intro x
    simp [mKey, chain_eq_of_births inv hm]
  have hkeys : ∀ p, p ∈ mKeys Γ K ↔ p ∈ mKeys Γ L := by
    intro p
    simp only [mKeys, List.mem_map, hkey, ids_eq_of_births hm]
  have hcand : ∀ p, p ∈ succCandM Γ K a ↔ p ∈ succCandM Γ L a := by
    intro p
    simp only [succCandM, hkey]
    split <;> simp only [List.mem_filter, hkeys]
  cases hk : succOfM Γ K a with
  | none =>
      have he := (successor_none Γ K a).mp hk
      cases hl : succOfM Γ L a with
      | none => rfl
      | some n =>
          have h := (hcand _).mpr (succOfM_pair hl)
          simp [he] at h
  | some n =>
      cases hl : succOfM Γ L a with
      | none =>
          have he := (successor_none Γ L a).mp hl
          have h := (hcand _).mp (succOfM_pair hk)
          simp [he] at h
      | some p =>
          congr 1
          have hn := succOfM_mem hk
          have hp := (ids_eq_of_births hm p).mpr (succOfM_mem hl)
          apply mKey_inj inv (Or.inr hn) (Or.inr hp)
          have hpc : (p, mKey Γ K p) ∈ succCandM Γ K a := by
            rw [hkey p]
            exact (hcand _).mpr (succOfM_pair hl)
          have hnc : (n, mKey Γ L n) ∈ succCandM Γ L a := by
            rw [← hkey n]
            exact (hcand _).mp (succOfM_pair hk)
          have hpn := succOfM_max hk hpc
          have hnp := succOfM_max hl hnc
          rw [← hkey n, ← hkey p] at hnp
          by_contra hne
          rcases keyLt_total hne with h | h <;> simp_all

theorem genAfter_eq_of_births {Γ : OrderedPrefixCode} {K L : KnowM}
    (inv : KInv Γ K) (hm : ∀ g, g ∈ mMinted K ↔ g ∈ mMinted L) (r t a : ℕ) :
    mGenInsAfter Γ K r t a = mGenInsAfter Γ L r t a := by
  simp only [mGenInsAfter, successor_eq_of_births inv hm,
    hasRChild_eq_of_births hm, chain_eq_of_births inv hm]

#print axioms genAfter_eq_of_births

end Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax
