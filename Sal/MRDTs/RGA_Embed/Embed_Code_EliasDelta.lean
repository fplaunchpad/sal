import Sal.MRDTs.RGA_Embed.Embed_Code_Binary

/-!
# The flipped Elias-δ code — the length field entropy-coded

Third inhabitant of `OrderedPrefixCode` (design doc §2; order-coding note
I5). The binary delta code `binEnc` announces its payload length in *unary*
(`1^(L−1) 0`), paying the length bill at `L` bits. But only the value bill
is forced at `log₂ δ` — the length can itself be entropy-coded. This file
applies `binEnc` to the *length field*:

```
dEnc δ = binEnc (size δ) ++ (δ with its leading bit removed)
```

`|dEnc δ| = size δ + 2·size (size δ) − 2 = log₂ δ + O(log log δ)` — the
asymptotic halving of large races. (Iterating the construction on its own
length field gives the Elias-ω ladder; one level is where the constants
stop paying on real traces — see the I1 measurement in the order-coding
note: the tail is thin, so this instance's value is the *theorem*, not
measured savings. `dEnc` wins only from `δ ≥ 32` and loses at
`δ ∈ {2,3} ∪ [8,15]`; both facts kernel-checked below.)

The proofs reuse the binary code's machinery wholesale: `binEnc`'s
monotonicity and prefix-freeness *are* the header algebra here, glued by
one new fact — a strict lexicographic comparison that is not a prefix
relationship survives arbitrary appends on both sides.
-/

namespace Sal.EmbedRGA

/-- Strict-`Lex`-and-not-prefix survives appends: if `u <lex v` by an actual
first-difference (not by running out), the difference persists under any
suffixes. The `nil` constructor of `Lex` is exactly the prefix case the
hypothesis excludes. -/
theorem bitLt_append_of_not_prefix (p q : List Bool) {u v : List Bool}
    (h : bitLt u v) : ¬ (u <+: v) → bitLt (u ++ p) (v ++ q) := by
  induction h with
  | nil => intro hnp; exact absurd List.nil_prefix hnp
  | rel hab => intro _; exact List.Lex.rel hab
  | cons h ih =>
      intro hnp
      exact List.Lex.cons
        (ih fun hpre => hnp (List.cons_prefix_cons.mpr ⟨rfl, hpre⟩))

/-! ## The code -/

/-- The flipped Elias-δ codeword: `binEnc` on the bit-length, then the
payload (`δ` minus its always-1 leading bit, big-endian). -/
def dEnc (d : ℕ) : List Bool :=
  binEnc d.size ++ bitsW (d.size - 1) d

/-- The cost, exactly: `|dEnc δ| = size δ + 2·size (size δ) − 2`
(with `size = ⌊log₂ ·⌋ + 1` on positives: `log₂ δ + 2 log₂ log₂ δ + O(1)`). -/
theorem dEnc_length (d : ℕ) (hd : 1 ≤ d) :
    (dEnc d).length = d.size + 2 * (d.size).size - 2 := by
  have hL : 1 ≤ d.size := Nat.size_pos.mpr (by omega)
  have hS : 1 ≤ (d.size).size := Nat.size_pos.mpr (by omega)
  simp only [dEnc, List.length_append, bitsW_length,
             binEnc_length d.size hL]
  omega

theorem dEnc_mono {d e : ℕ} (hd : 1 ≤ d) (hlt : d < e) :
    bitLt (dEnc d) (dEnc e) := by
  have he : 1 ≤ e := by omega
  have hLd : 1 ≤ d.size := Nat.size_pos.mpr (by omega)
  have hLe : 1 ≤ e.size := Nat.size_pos.mpr (by omega)
  rcases Nat.lt_or_ge d.size e.size with hsz | hge
  · -- distinct length classes: the binEnc headers differ at a real first
    -- difference (they are mutually non-prefix), which appends preserve
    exact bitLt_append_of_not_prefix _ _
      (binEnc_mono hLd hsz)
      (binEnc_prefixFree hLd hLe (by omega))
  · -- same length class: identical headers, payloads compare as numbers
    have heq : d.size = e.size :=
      Nat.le_antisymm (Nat.size_le_size (by omega)) hge
    obtain ⟨hlo_d, hb_d, hm_d⟩ := low_bits d hd
    obtain ⟨hlo_e, hb_e, hm_e⟩ := low_bits e he
    unfold dEnc
    rw [heq]
    apply bitLt_append_left
    rw [bitsW_mod _ d, bitsW_mod _ e]
    rw [heq] at hm_d hb_d hlo_d
    rw [hm_d, hm_e]
    exact bitsW_lt hb_e (by omega)

theorem dEnc_prefixFree {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) (hne : d ≠ e) :
    ¬ (dEnc d <+: dEnc e) := by
  have hLd : 1 ≤ d.size := Nat.size_pos.mpr (by omega)
  have hLe : 1 ≤ e.size := Nat.size_pos.mpr (by omega)
  rcases Nat.lt_trichotomy d.size e.size with hsz | hsz | hsz
  · -- shorter class: a prefix would force header-prefixes-header, refuted
    intro hp
    have hu : binEnc d.size <+: dEnc e :=
      List.IsPrefix.trans (by unfold dEnc; exact List.prefix_append _ _) hp
    have hv : binEnc e.size <+: dEnc e := by
      unfold dEnc; exact List.prefix_append _ _
    have hlen : (binEnc d.size).length ≤ (binEnc e.size).length := by
      rw [binEnc_length _ hLd, binEnc_length _ hLe]
      have hs := Nat.size_le_size (Nat.le_of_lt hsz)
      have h1 : 1 ≤ (d.size).size := Nat.size_pos.mpr (by omega)
      omega
    exact binEnc_prefixFree hLd hLe (by omega)
      (List.prefix_of_prefix_length_le hu hv hlen)
  · -- same class: equal lengths force equality; the payload is injective
    intro hp
    have hlen : (dEnc d).length = (dEnc e).length := by
      rw [dEnc_length d hd, dEnc_length e he, hsz]
    have heq := hp.eq_of_length hlen
    unfold dEnc at heq
    rw [hsz] at heq
    have hpay := List.append_cancel_left heq
    obtain ⟨hlo_d, hb_d, hm_d⟩ := low_bits d hd
    obtain ⟨hlo_e, hb_e, hm_e⟩ := low_bits e he
    rw [hsz] at hm_d hb_d hlo_d
    rw [bitsW_mod _ d, bitsW_mod _ e, hm_d, hm_e] at hpay
    have hde := bitsW_inj hb_d hb_e hpay
    exact hne (by omega)
  · -- longer class is a strictly longer word: cannot prefix a shorter one
    intro hp
    have hlen := hp.length_le
    rw [dEnc_length d hd, dEnc_length e he] at hlen
    have hs := Nat.size_le_size (Nat.le_of_lt hsz)
    have h1 : 1 ≤ (e.size).size := Nat.size_pos.mpr (by omega)
    have h2 : 1 ≤ (d.size).size := Nat.size_pos.mpr (by omega)
    omega

/-- The flipped Elias-δ code, packaged. Drop-in third inhabitant: every
datatype theorem, the capstone included, is parametric in the structure. -/
def eliasDeltaCode : OrderedPrefixCode where
  enc := dEnc
  mono := fun hd hlt => dEnc_mono hd hlt
  prefixFree := fun hd he hne => dEnc_prefixFree hd he hne

/-! ## Cross-validation

Values (`D(1)='0'`, `D(2)='1000'`, `D(3)='1001'`, `D(4)='10100'`,
`D(8)='11000000'`) and the honest cost comparison against `binEnc`: the
δ-flip loses at `δ ∈ {2,3} ∪ [8,15]`, ties at `{4..7} ∪ {16..31}`, and wins
from `δ = 32` — matching the I1 measurement's verdict that on thin-tailed
real traces the two are a wash. -/

example : dEnc 1 = [false] := by decide
example : dEnc 2 = [true, false, false, false] := by decide
example : dEnc 3 = [true, false, false, true] := by decide
example : dEnc 4 = [true, false, true, false, false] := by decide
example : dEnc 8 = [true, true, false, false, false, false, false, false] := by
  decide

example : (dEnc 2).length = 4 ∧ (binEnc 2).length = 3 := by decide
example : (dEnc 8).length = 8 ∧ (binEnc 8).length = 7 := by decide
example : (dEnc 16).length = (binEnc 16).length := by decide
example : (dEnc 32).length = 10 ∧ (binEnc 32).length = 11 := by decide
example : (dEnc 1024).length = 17 ∧ (binEnc 1024).length = 21 := by decide

end Sal.EmbedRGA
