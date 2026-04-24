# List-form `readRichText` — design sketch

Our current `readRichText` / `readRichText_visible` are per-character
functions:

```lean
readRichText : concrete_st → OpId → Option (ℕ × (ℕ → Bool))
```

The paper (§4.4) presents the rendered document as a **list** of
`{text, format}` spans. A list-form version:

```lean
readRichText_list : concrete_st → List (OpId × ℕ × (ℕ → Bool))
```

would:
1. Traverse the RGA in visible order.
2. Filter out tombstones.
3. For each visible char, emit its opId + codepoint + formatting
   function.
4. Optionally coalesce adjacent chars with identical formatting into
   span records.

## Why this is non-trivial

The framework's `set α := α → Bool` and `map K V := set K × (K → V)`
don't provide enumeration. To produce a `List OpId` of visible
chars, we need to **enumerate** the chars (not just query
membership).

Options:

### Option A — `Finset`-based state refinement

Introduce a `Finset OpId` view of the chars domain alongside the
current map. State becomes `{ chars : map OpId ℕ, chars_finset :
Finset OpId, agreement : chars.domain = chars_finset }`. Enumeration
goes through `chars_finset`.

**Cost:** state-shape change, the 24 VCs need re-verification.

### Option B — Finiteness invariant at the theorem level

Keep the state shape as-is. Add a `Fintype (chars.domain).toFinset`
hypothesis to the `readRichText_list` signature. The theorem only
applies to states with finite carriers, which is every reachable
state in practice.

**Cost:** theorems that consume `readRichText_list` need the
hypothesis propagated. Cleaner but verbose.

### Option C — Specification-level relation, no computable function

Define a Prop-valued `is_rga_traversal s l` characterizing what
it means for `l` to be a visible traversal of `s`. Prove:

- Existence: `∃ l, is_rga_traversal s l` (needs the finite carrier).
- Uniqueness: any two traversals agree.
- Convergence: `eq s₁ s₂ → is_rga_traversal s₁ l ↔ is_rga_traversal s₂ l`.

Downstream code computes the list externally (via the TypeScript
demo's `traverse`) and proves it satisfies `is_rga_traversal`.

**Cost:** no computable Lean function, but all the verification
content is there.

## Recommended approach

**Option C.** It's the minimum change to the existing framework,
doesn't require state-shape refactors, and matches how the
TypeScript demo already consumes the spec (the Lean is the
specification, not the implementation).

## Proposed `is_rga_traversal` spec

```lean
def is_rga_traversal (s : concrete_st) (l : List OpId) : Prop :=
  -- l enumerates exactly the visible chars, each once
  (∀ c, c ∈ l ↔ visible s c = true) ∧
  l.Nodup ∧
  -- l is sorted by visible_lt
  l.Sorted (fun c₁ c₂ => visible_lt s c₁ c₂)
```

With this:

```lean
theorem is_rga_traversal_convergent (s₁ s₂ : concrete_st) :
    eq s₁ s₂ → ∀ l, is_rga_traversal s₁ l ↔ is_rga_traversal s₂ l
```

follows from the congruence lemmas + `List.Sorted` congruence.

A downstream `readRichText_list s l (h : is_rga_traversal s l)
: List (OpId × ℕ × (ℕ → Bool))` produces the list given a caller-
provided traversal.

## Estimated effort

- `is_rga_traversal` + convergence theorem: 1-2 hours.
- Existence (if we want it): 4-8 hours with a finite-carrier
  Fintype-style argument.

Existence alone is optional — consumers can construct the
traversal by any means and prove it matches the spec.
