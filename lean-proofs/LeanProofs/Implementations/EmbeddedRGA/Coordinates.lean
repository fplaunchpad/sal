import LeanProofs_no_spec_non_comm.Implementations.EmbeddedRGA.Scheme

/-!
# Embedded RGA: the unary coordinate scheme

The scheme the Embedded RGA row and Embedded Peritext use: coordinates are
bit strings, the codeword of a clock gap is the unary code `1^d 0`, and the
key reads the bits as `2`/`1` with the terminator `3` appended. There is no
extra datum on an insertion, so `Arg` is `Unit`.

The obligation that costs anything is `cancel`, unique decodability. A
coordinate that is not empty ends in the delimiter `false`, and from that
`enc_append_cancel` recovers both the prefix and the codeword from their
concatenation: a longer codeword could only extend the shorter prefix by a
block of `true`, and no coordinate ends in `true`.

`key_sibling` and `key_descendant` are the two placement facts, that a
larger gap gives a larger key and that the terminator exceeds every bit.
They are what make descending key order the RGA **order**, and the scheme
does not ask for them, because RA-linearizability never does. They are kept
because they are the row's design, and the editor semantics would need
them.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.EmbeddedRGA

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

/-- A coordinate of this scheme: the insertion ancestry, in bits. -/
abbrev Coord := List Bool

/-- `enc`: the unary code, `d` trues then a false. -/
def enc (d : Nat) : Coord := List.replicate d true ++ [false]

/-- `K(c)`: the bits as `2`/`1`, with the terminator `3`. -/
def key (c : Coord) : List Nat := c.map (fun b => if b then 2 else 1) ++ [3]

/-! ## `key` is injective -/

theorem key_inj {c d : Coord} (h : key c = key d) : c = d := by
  have hmap : c.map (fun b => if b then 2 else 1) = d.map (fun b => if b then 2 else 1) :=
    List.append_cancel_right h
  have hinj : Function.Injective (fun b : Bool => if b then 2 else 1) := by decide
  exact List.map_injective_iff.mpr hinj hmap

/-- Distinct coordinates have `lexLt`-comparable keys. -/
theorem key_total {c d : Coord} (h : c ≠ d) :
    lexLt (key c) (key d) = true ∨ lexLt (key d) (key c) = true :=
  lexLt_total (fun hk => h (key_inj hk))

/-! ## The codeword, and why coordinates are uniquely decodable

A coordinate is a concatenation of codewords, so when it is not empty it
ends in the delimiter `false`. That is the whole reason two insertions
cannot carve out the same coordinate: a longer codeword could only extend a
prefix by a block of `true`, which no coordinate ends in. -/

/-- A coordinate never ends in `true`. -/
def CoordWf (c : Coord) : Prop := c.getLast? ≠ some true

theorem coordWf_nil : CoordWf [] := by simp [CoordWf]

theorem enc_length (d : Nat) : (enc d).length = d + 1 := by
  simp [enc]

theorem enc_getLast (d : Nat) : (enc d).getLast? = some false := by
  simp [enc]

theorem coordWf_append (p : Coord) (d : Nat) : CoordWf (p ++ enc d) := by
  simp [CoordWf, enc, List.getLast?_append]

/-- `enc` is injective, by length alone. -/
theorem enc_inj {d e : Nat} (h : enc d = enc e) : d = e := by
  have := congrArg List.length h
  simp only [enc_length] at this
  omega

/-- **Coordinates are uniquely decodable at the last codeword.** A longer
codeword could only extend the shorter prefix by a block of `true`, and no
coordinate ends in `true`. -/
theorem enc_append_cancel {p₁ p₂ : Coord} {d₁ d₂ : Nat}
    (h₁ : CoordWf p₁) (h₂ : CoordWf p₂)
    (h : p₁ ++ enc d₁ = p₂ ++ enc d₂) : p₁ = p₂ ∧ d₁ = d₂ := by
  have main : ∀ (q₁ q₂ : Coord) (e₁ e₂ : Nat), CoordWf q₁ →
      q₁ ++ enc e₁ = q₂ ++ enc e₂ → e₁ < e₂ → False := by
    intro q₁ q₂ e₁ e₂ hw hq hlt
    have hlen : q₂.length + e₂ = q₁.length + e₁ := by
      have := congrArg List.length hq
      simp only [List.length_append, enc_length] at this
      omega
    have hp₁ : q₁ <+: q₁ ++ enc e₁ := List.prefix_append _ _
    have hp₂ : q₂ <+: q₁ ++ enc e₁ := by rw [hq]; exact List.prefix_append _ _
    obtain ⟨r, hr⟩ :=
      List.prefix_of_prefix_length_le hp₂ hp₁ (by omega : q₂.length ≤ q₁.length)
    have hrlen : r.length = e₂ - e₁ := by
      have := congrArg List.length hr
      simp only [List.length_append] at this
      omega
    have hrne : r ≠ [] := by
      intro hnil
      rw [hnil, List.length_nil] at hrlen
      omega
    have hcancel : r ++ List.replicate e₁ true = List.replicate e₂ true := by
      have hq' : q₂ ++ (r ++ enc e₁) = q₂ ++ enc e₂ := by
        rw [← List.append_assoc, hr]; exact hq
      have hre : r ++ enc e₁ = enc e₂ := List.append_cancel_left hq'
      have h2 : (r ++ List.replicate e₁ true) ++ [false]
          = List.replicate e₂ true ++ [false] := by
        simpa only [enc, List.append_assoc] using hre
      exact List.append_cancel_right h2
    have hall : ∀ x ∈ r, x = true := by
      intro x hx
      exact List.eq_of_mem_replicate (hcancel ▸ List.mem_append_left _ hx)
    refine hw ?_
    rw [← hr, List.getLast?_append, List.getLast?_eq_some_getLast hrne,
      hall _ (List.getLast_mem hrne)]
    rfl
  rcases Nat.lt_trichotomy d₁ d₂ with hlt | heq | hgt
  · exact (main p₁ p₂ d₁ d₂ h₁ h hlt).elim
  · subst heq
    exact ⟨List.append_cancel_right h, rfl⟩
  · exact (main p₂ p₁ d₂ d₁ h₂ h.symm hgt).elim

/-! ## Where the keys put a record

The two facts the appendix states about the encoding, which are what make
descending key order the RGA order. They are not about any state.
-/

/-- The key of a concatenation splits at the join. -/
theorem key_append (c w : Coord) :
    key (c ++ w) = c.map (fun b => if b then 2 else 1) ++ key w := by
  simp [key, List.map_append, List.append_assoc]

/-- A common prefix does not affect the comparison. -/
theorem lexLt_append : ∀ pre u v : List Nat,
    lexLt (pre ++ u) (pre ++ v) = lexLt u v := by
  intro pre
  induction pre with
  | nil => intro u v; rfl
  | cons x pre ih =>
    intro u v
    simp only [List.cons_append, lexLt, lt_self_iff_false, if_false]
    exact ih u v

/-- The key of a codeword: `d` twos, then the `1` that closes the codeword,
then the terminator. -/
theorem key_enc (d : Nat) : key (enc d) = List.replicate d 2 ++ [1, 3] := by
  simp [key, enc, List.map_append, List.map_replicate]

theorem lexLt_replicate : ∀ d₁ d₂ : Nat, d₁ < d₂ →
    lexLt (List.replicate d₁ 2 ++ [1, 3]) (List.replicate d₂ 2 ++ [1, 3]) = true := by
  intro d₁
  induction d₁ with
  | zero =>
    intro d₂ h
    obtain ⟨k, rfl⟩ : ∃ k, d₂ = k + 1 := ⟨d₂ - 1, by omega⟩
    simp [List.replicate_succ, lexLt]
  | succ d ih =>
    intro d₂ h
    obtain ⟨k, rfl⟩ : ∃ k, d₂ = k + 1 := ⟨d₂ - 1, by omega⟩
    simp only [List.replicate_succ, List.cons_append, lexLt, lt_self_iff_false, if_false]
    exact ih k (by omega)

/-! ## The two order facts the row is designed around -/

/-- **Newest sibling first.** Two insertions sharing an anchor carry the
same prefix, so the comparison falls through to their codewords, and a
larger delta gives a larger key. The read is descending, so the later
insertion is displayed first. -/
theorem key_sibling {p : Coord} {d₁ d₂ : Nat} (h : d₁ < d₂) :
    lexLt (key (p ++ enc d₁)) (key (p ++ enc d₂)) = true := by
  rw [key_append, key_append, lexLt_append, key_enc, key_enc]
  exact lexLt_replicate d₁ d₂ h

/-- **An ancestor precedes its descendants.** The terminator `3` exceeds
every bit, so extending a coordinate strictly lowers its key. -/
theorem key_descendant {c w : Coord} (h : w ≠ []) :
    lexLt (key (c ++ w)) (key c) = true := by
  rw [key_append, show key c = c.map (fun b => if b then 2 else 1) ++ [3] from rfl,
    lexLt_append]
  obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil h
  cases y <;> simp [key, lexLt]

/-! ## The scheme -/

/-- **The unary coordinate scheme.** `Arg` is `Unit`: an insertion of this
family carries no datum beyond its value, anchor coordinate and anchor. -/
def unaryScheme : Scheme where
  Sym := Bool
  Arg := Unit
  code := fun _ d => enc d
  key := key
  key_inj := key_inj
  Wf := CoordWf
  wf_nil := coordWf_nil
  wf_append := fun p _ d => coordWf_append p d
  code_ne_nil := fun _ d => by simp [enc]
  cancel := fun h₁ h₂ h => by
    obtain ⟨hp, hd⟩ := enc_append_cancel h₁ h₂ h
    exact ⟨hp, rfl, hd⟩

end LeanProofs.NoSpecNonComm.Implementations.EmbeddedRGA
