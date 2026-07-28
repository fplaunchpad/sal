import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lex
import Mathlib.Order.Basic

/-!
# The coordinate code kernel for the embedded-chain RGA

Design: `Sal/ConditionedMRDTs/sal-mrdts.pdf`, Part II (design and encoding
sections). A node's coordinate is the
concatenation, along its birth chain, of codewords `enc δ` for the timestamp
deltas `δ = t − t_anchor ≥ 1`. Everything the datatype needs from the code is
two properties:

* **monotone**: `d < e → enc d <lex enc e` (newest sits highest), and
* **prefix-free**: distinct codewords are never prefixes of one another
  (distinct mints get disjoint cells; concatenations are uniquely decodable).

The datatype theorems are parametric in the code, so we package the two
properties as `OrderedPrefixCode` and prove the datatype against the
structure. This file provides the structure and its simplest inhabitant, the
**unary code** `enc d = replicate d true ++ [false]`, the Lean twin of the
whiteboard's `embed-tree` mint `I(t) = (1 − 2⁻ᵗ, 1 − ¾·2⁻ᵗ)`. The
entropy-optimal binary delta code (`embed-code`'s
`C(δ) = 1^(L−1) 0 (δ minus its leading bit)`) is a second inhabitant to be
added later; nothing downstream changes when it lands.

Order convention: `List.Lex (· < ·)` on `List Bool` with `false < true`.
Between prefix-free codewords the `nil` case of `Lex` never fires, so this is
exactly the first-difference order.
-/

namespace Sal.EmbedRGA

/-- Strict lexicographic order on bit strings, `false < true`. -/
abbrev bitLt (u v : List Bool) : Prop := List.Lex (· < ·) u v

/-- An order-preserving prefix-free code for positive deltas. `enc d` is only
ever consumed at `1 ≤ d` (causality: an insert's timestamp exceeds its
anchor's), so the properties are conditioned on positivity. -/
structure OrderedPrefixCode where
  enc : ℕ → List Bool
  mono : ∀ {d e : ℕ}, 1 ≤ d → d < e → bitLt (enc d) (enc e)
  prefixFree : ∀ {d e : ℕ}, 1 ≤ d → 1 ≤ e → d ≠ e → ¬ (enc d <+: enc e)

namespace OrderedPrefixCode

/-- Codewords of distinct positive deltas are distinct. -/
theorem enc_injOn (Γ : OrderedPrefixCode) {d e : ℕ}
    (hd : 1 ≤ d) (he : 1 ≤ e) (hne : d ≠ e) : Γ.enc d ≠ Γ.enc e := by
  intro h
  exact Γ.prefixFree hd he hne (h ▸ List.prefix_refl _)

end OrderedPrefixCode

/-! ## The unary instance

`enc d = replicate d true ++ [false]`. One `true` per unit of delta, the
bit-string twin of the unary-exponent mint. Wasteful (`Θ(d)` bits) but its
properties are two short inductions, which makes it the right first
inhabitant: it unblocks the entire datatype development while the binary
code's arithmetic is done separately.
-/

/-- Unary codeword. -/
def unaryEnc (d : ℕ) : List Bool := List.replicate d true ++ [false]

theorem unaryEnc_mono {d e : ℕ} (h : d < e) : bitLt (unaryEnc d) (unaryEnc e) := by
  induction d generalizing e with
  | zero =>
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, (Nat.succ_pred_eq_of_pos h).symm⟩
      simpa [unaryEnc, List.replicate_succ] using
        List.Lex.rel (by decide : (false : Bool) < true)
  | succ d ih =>
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 :=
        ⟨e - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) h)).symm⟩
      have h' : d < e' := Nat.lt_of_succ_lt_succ h
      simpa [unaryEnc, List.replicate_succ] using List.Lex.cons (ih h')

theorem unaryEnc_not_prefix {d e : ℕ} (hne : d ≠ e) :
    ¬ (unaryEnc d <+: unaryEnc e) := by
  induction d generalizing e with
  | zero =>
      cases e with
      | zero => exact absurd rfl hne
      | succ e' =>
          intro hpre
          simp [unaryEnc, List.replicate_succ] at hpre
  | succ d ih =>
      cases e with
      | zero =>
          intro hpre
          simp [unaryEnc, List.replicate_succ] at hpre
      | succ e' =>
          intro hpre
          have hne' : d ≠ e' := fun h => hne (by simp [h])
          have : (true :: (List.replicate d true ++ [false])) <+:
                 (true :: (List.replicate e' true ++ [false])) := by
            simpa [unaryEnc, List.replicate_succ] using hpre
          rcases List.cons_prefix_cons.mp this with ⟨-, htail⟩
          exact ih hne' (by simpa [unaryEnc] using htail)

/-- The unary code, packaged. -/
def unaryCode : OrderedPrefixCode where
  enc := unaryEnc
  mono := fun _ h => unaryEnc_mono h
  prefixFree := fun _ _ hne => unaryEnc_not_prefix hne

end Sal.EmbedRGA
