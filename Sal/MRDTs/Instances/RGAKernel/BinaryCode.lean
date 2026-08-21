import Mathlib.Data.Nat.Size
import Sal.MRDTs.Instances.RGAKernel.Code

/-!
# The binary delta code: the entropy-optimal `embed-code` mint

The second inhabitant of `OrderedPrefixCode` (design doc §5,
the executable EmbedRGA encoding):

```
C(δ) = 1^(L−1) ++ 0 ++ (δ with its leading bit removed),   L = bitlength δ
```

`|C(δ)| = 2L − 1 = Θ(log δ)`: sequential typing costs ~4 bits per level and a
race with timestamp gap `g` costs `2·log₂ g + O(1)`, the entropy of the
birth chain, versus the unary code's `Θ(δ)`. Because every datatype theorem
is parametric in the code, nothing downstream changes: this file only
proves the two structure fields (monotone, prefix-free) for `binEnc`.
-/

namespace Sal.EmbedRGA

/-! ## Fixed-width big-endian bit fields -/

/-- `n`'s low `w` bits, most significant first. -/
def bitsW : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, n => n.testBit w :: bitsW w n

theorem bitsW_length (w n : ℕ) : (bitsW w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [bitsW, ih]

theorem bitsW_congr {w n m : ℕ} (h : ∀ i, i < w → n.testBit i = m.testBit i) :
    bitsW w n = bitsW w m := by
  induction w with
  | zero => rfl
  | succ w ih =>
      simp only [bitsW]
      rw [h w (by omega), ih (fun i hi => h i (by omega))]

/-- Only the low `w` bits matter. -/
theorem bitsW_mod (w n : ℕ) : bitsW w n = bitsW w (n % 2 ^ w) := by
  apply bitsW_congr
  intro i hi
  rw [Nat.testBit_mod_two_pow]
  simp [hi]

/-- Under a width bound, the top bit reads as a threshold. -/
theorem testBit_top {w x : ℕ} (hx : x < 2 ^ (w + 1)) :
    x.testBit w = decide (2 ^ w ≤ x) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h2 : 0 < 2 ^ w := Nat.two_pow_pos w
  rcases Nat.lt_or_ge x (2 ^ w) with h | h
  · have : x / 2 ^ w = 0 := Nat.div_eq_of_lt h
    simp [this, Nat.not_le.mpr h]
  · have hlt : x / 2 ^ w < 2 := by
      apply Nat.div_lt_of_lt_mul
      have h2s : (2 : ℕ) ^ (w + 1) = 2 ^ w * 2 := by rw [Nat.pow_succ]
      omega
    have hge : 1 ≤ x / 2 ^ w := Nat.one_le_div_iff h2 |>.mpr h
    have : x / 2 ^ w = 1 := by omega
    simp [this, h]

/-- **Same-width comparison**: below a common width bound, the big-endian bit
field compares exactly like the number. -/
theorem bitsW_lt : ∀ {w n m : ℕ}, m < 2 ^ w → n < m →
    bitLt (bitsW w n) (bitsW w m)
  | 0, n, m, hm, hnm => by omega
  | w + 1, n, m, hm, hnm => by
      have hn : n < 2 ^ (w + 1) := by omega
      have h2 : 0 < 2 ^ w := Nat.two_pow_pos w
      have h2s : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by rw [Nat.pow_succ]; omega
      rw [show bitsW (w+1) n = n.testBit w :: bitsW w n from rfl,
          show bitsW (w+1) m = m.testBit w :: bitsW w m from rfl,
          testBit_top hn, testBit_top hm]
      rcases Nat.lt_or_ge n (2 ^ w) with hnw | hnw
      · rcases Nat.lt_or_ge m (2 ^ w) with hmw | hmw
        · -- both below: heads false, recurse directly
          rw [decide_eq_false (by omega), decide_eq_false (by omega)]
          exact List.Lex.cons (bitsW_lt hmw hnm)
        · -- n below, m above: heads false < true
          rw [decide_eq_false (by omega), decide_eq_true hmw]
          exact List.Lex.rel (by decide)
      · -- n above forces m above (n < m); recurse on the low parts
        have hmw : 2 ^ w ≤ m := by omega
        rw [decide_eq_true hnw, decide_eq_true hmw]
        have hn' : n % 2 ^ w = n - 2 ^ w := by
          rw [Nat.mod_eq_sub_mod hnw, Nat.mod_eq_of_lt (by omega)]
        have hm' : m % 2 ^ w = m - 2 ^ w := by
          rw [Nat.mod_eq_sub_mod hmw, Nat.mod_eq_of_lt (by omega)]
        rw [bitsW_mod w n, bitsW_mod w m]
        exact List.Lex.cons (bitsW_lt (by omega) (by omega))

theorem bitLt_irrefl : ∀ (l : List Bool), ¬ bitLt l l
  | [] => fun h => by cases h
  | b :: bs => fun h => by
      cases h with
      | cons h => exact bitLt_irrefl bs h
      | rel h => exact absurd h (by cases b <;> decide)

theorem bitsW_inj {w n m : ℕ} (hn : n < 2 ^ w) (hm : m < 2 ^ w)
    (h : bitsW w n = bitsW w m) : n = m := by
  rcases Nat.lt_trichotomy n m with hlt | heq | hlt
  · exact absurd (h ▸ bitsW_lt hm hlt) (bitLt_irrefl _)
  · exact heq
  · exact absurd (h ▸ bitsW_lt hn hlt) (bitLt_irrefl _)

/-! ## Header algebra -/

theorem header_lt {m n : ℕ} (h : m < n) (u v : List Bool) :
    bitLt (List.replicate m true ++ false :: u)
          (List.replicate n true ++ false :: v) := by
  induction m generalizing n with
  | zero =>
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simpa [List.replicate_succ] using List.Lex.rel (by decide : false < true)
  | succ m ih =>
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simpa [List.replicate_succ] using List.Lex.cons (ih (by omega))

theorem header_not_prefix : ∀ {m n : ℕ}, m ≠ n → ∀ (u v : List Bool),
    ¬ (List.replicate m true ++ false :: u <+:
       List.replicate n true ++ false :: v)
  | 0, 0, hne, _, _ => absurd rfl hne
  | 0, n + 1, _, u, v => by
      intro hp
      simp [List.replicate_succ] at hp
  | m + 1, 0, _, u, v => by
      intro hp
      simp [List.replicate_succ] at hp
  | m + 1, n + 1, hne, u, v => by
      intro hp
      simp only [List.replicate_succ, List.cons_append] at hp
      rcases List.cons_prefix_cons.mp hp with ⟨-, htail⟩
      exact header_not_prefix (by omega) u v htail

theorem bitLt_append_left (p : List Bool) {u v : List Bool} (h : bitLt u v) :
    bitLt (p ++ u) (p ++ v) := by
  induction p with
  | nil => exact h
  | cons x xs ih => exact List.Lex.cons ih

/-- Comparison through a shared prefix and a shared head bit. -/
theorem bitLt_append_cons (p : List Bool) (x : Bool) {u v : List Bool}
    (h : bitLt u v) : bitLt (p ++ x :: u) (p ++ x :: v) := by
  induction p with
  | nil => exact List.Lex.cons h
  | cons y ys ih => exact List.Lex.cons ih

/-! ## The code -/

/-- The binary delta codeword:
`1^(size δ − 1) ++ 0 ++ (low (size δ − 1) bits of δ, MSB first)`. -/
def binEnc (d : ℕ) : List Bool :=
  List.replicate (d.size - 1) true ++ false :: bitsW (d.size - 1) d

/-- The entropy bound, exactly: `|C(δ)| = 2·bitlength δ − 1`. -/
theorem binEnc_length (d : ℕ) (hd : 1 ≤ d) :
    (binEnc d).length = 2 * d.size - 1 := by
  have hL : 1 ≤ d.size := Nat.size_pos.mpr (by omega)
  simp only [binEnc, List.length_append, List.length_replicate,
             List.length_cons, bitsW_length]
  omega

/-- The payload arithmetic: with `L = size d ≥ 1`, `d`'s low `L−1` bits are
`d − 2^(L−1)`, strictly below `2^(L−1)`. -/
theorem low_bits (d : ℕ) (hd : 1 ≤ d) :
    2 ^ (d.size - 1) ≤ d ∧ d - 2 ^ (d.size - 1) < 2 ^ (d.size - 1) ∧
    d % 2 ^ (d.size - 1) = d - 2 ^ (d.size - 1) := by
  have hL : 1 ≤ d.size := Nat.size_pos.mpr (by omega)
  have hlow : 2 ^ (d.size - 1) ≤ d := Nat.lt_size.mp (by omega)
  have hhigh : d < 2 ^ d.size := Nat.lt_size_self d
  have hsplit : 2 ^ d.size = 2 ^ (d.size - 1) + 2 ^ (d.size - 1) := by
    have hup : d.size - 1 + 1 = d.size := Nat.sub_add_cancel hL
    calc 2 ^ d.size = 2 ^ (d.size - 1 + 1) := by rw [hup]
      _ = 2 ^ (d.size - 1) * 2 := Nat.pow_succ 2 (d.size - 1)
      _ = 2 ^ (d.size - 1) + 2 ^ (d.size - 1) := by omega
  refine ⟨hlow, by omega, ?_⟩
  rw [Nat.mod_eq_sub_mod hlow, Nat.mod_eq_of_lt (by omega)]

theorem binEnc_mono {d e : ℕ} (hd : 1 ≤ d) (hlt : d < e) :
    bitLt (binEnc d) (binEnc e) := by
  have he : 1 ≤ e := by omega
  have hsz : d.size ≤ e.size := Nat.size_le_size (by omega)
  have hLd : 1 ≤ d.size := Nat.size_pos.mpr (by omega)
  rcases Nat.lt_or_ge d.size e.size with hne | hge
  · exact header_lt (by omega) _ _
  · have heq : d.size = e.size := by omega
    obtain ⟨hlo_d, hb_d, hm_d⟩ := low_bits d hd
    obtain ⟨hlo_e, hb_e, hm_e⟩ := low_bits e he
    unfold binEnc
    rw [heq]
    apply bitLt_append_cons
    rw [bitsW_mod _ d, bitsW_mod _ e]
    rw [heq] at hm_d hb_d hlo_d
    rw [hm_d, hm_e]
    exact bitsW_lt hb_e (by omega)

theorem binEnc_prefixFree {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) (hne : d ≠ e) :
    ¬ (binEnc d <+: binEnc e) := by
  rcases eq_or_ne d.size e.size with hsz | hsz
  · intro hp
    have hlen : (binEnc d).length = (binEnc e).length := by
      rw [binEnc_length d hd, binEnc_length e he, hsz]
    have heq := hp.eq_of_length hlen
    unfold binEnc at heq
    rw [hsz] at heq
    have hpair := List.append_cancel_left heq
    injection hpair with _ hpay
    obtain ⟨hlo_d, hb_d, hm_d⟩ := low_bits d hd
    obtain ⟨hlo_e, hb_e, hm_e⟩ := low_bits e he
    rw [hsz] at hm_d hb_d hlo_d
    rw [bitsW_mod _ d, bitsW_mod _ e, hm_d, hm_e] at hpay
    have hde := bitsW_inj hb_d hb_e hpay
    exact hne (by omega)
  · have hLd : 1 ≤ d.size := Nat.size_pos.mpr (by omega)
    have hLe : 1 ≤ e.size := Nat.size_pos.mpr (by omega)
    exact header_not_prefix (by omega) _ _

/-- The entropy-optimal code, packaged. Drop-in replacement for `unaryCode`:
every datatype theorem is parametric in the structure. -/
def binaryCode : OrderedPrefixCode where
  enc := binEnc
  mono := fun hd hlt => binEnc_mono hd hlt
  prefixFree := fun hd he hne => binEnc_prefixFree hd he hne

/-! ## Cross-validation against the Python artifact

`embed_tree.py`'s `C`: `C(1)='0'`, `C(2)='100'`, `C(3)='101'`,
`C(5)='11001'`. -/

example : binEnc 1 = [false] := by decide
example : binEnc 2 = [true, false, false] := by decide
example : binEnc 3 = [true, false, true] := by decide
example : binEnc 5 = [true, true, false, false, true] := by decide

end Sal.EmbedRGA
