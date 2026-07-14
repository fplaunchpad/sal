import Sal.MRDTs.RGA_Embed.RGA_Embed_MRDT

/-!
# Embedded-chain RGA — read side: display order, stability theorems, SPOT

The display order is a **sort of immutable keys** (design doc §1: read =
descending coordinates, ancestors first). This file:

* the terminator key (`key`) and the strict display relation (`before`);
* the **stability theorems** — the pairwise-display-stability contract
  ("if a co-displayed pair is flipped, we have failed") as Lean theorems.
  None of them uses any property of the code: they are pure consequences of
  value immutability (`sel` never changes for a surviving id), which is the
  design's whole point. Delete-order preservation is the `Del` case of step
  stability — the theorem the proved flat RGA *refutes* on the same scenario
  (`tombstone_free_violates_delete_order`);
* `document` (the executable read over an explicit id list, repo convention)
  and SPOT scenarios: the flat RGA's reorder witness with the opposite
  verdict, litmus L1, the merge read, and both credential-countermodel
  topologies converging.

Sortedness characterization of `document` (Pairwise/perm lemmas connecting it
to `before`) and the chain-lex theorem need the key-order algebra
(totality/transitivity + prefix-free concatenation) — next layer, `PLAN.md`.
-/

namespace Sal.EmbedRGA

variable {α : Type} [DecidableEq α]

/-! ## The key and the display relation -/

/-- Terminator key: bits map to `{1, 2}` (`false ↦ 1`, `true ↦ 2`) and a
terminator `3` is appended. At the point where an ancestor's coordinate ends,
it offers `3` — larger than any bit symbol — so in the *descending* read an
ancestor sorts strictly before its own descendants, and siblings compare by
their first differing bit. This is the arithmetization of "DFS, children by
descending mint" as one flat comparison. -/
def key (c : coord) : List ℕ := (c.map fun b => if b then 2 else 1) ++ [3]

/-- Strict lexicographic order on key strings (first difference decides). -/
def keyLt : List ℕ → List ℕ → Bool
  | [], []           => false
  | [], _ :: _       => true
  | _ :: _, []       => false
  | x :: xs, y :: ys => if x < y then true else if y < x then false else keyLt xs ys

/-- Non-strict companion (used by the sort). -/
def keyLe (u v : List ℕ) : Bool := !(keyLt v u)

/-- `t1` is displayed strictly before `t2` in `s`: both live, and `t1`'s key
is strictly greater (the read is descending). -/
def before (s : concrete_st α) (t1 t2 : ℕ) : Prop :=
  contains s t1 = true ∧ contains s t2 = true ∧
  keyLt (key (pos s t2)) (key (pos s t1)) = true

/-! ## Value stability — the engine of every display-stability theorem -/

omit [DecidableEq α] in
/-- A surviving id's value is untouched by any op with a fresh timestamp:
`Del` never rewrites values (no rehoming exists), and a fresh `Ins` writes
only its own id. -/
theorem sel_do_stable (Γ : OrderedPrefixCode) (s : concrete_st α) (o : op_t α)
    (k : ℕ) (hf : fresh_ts o s) (hk : contains s k = true) :
    sel (do_ Γ s o) k = sel s k := by
  obtain ⟨t, r, op⟩ := o
  cases op with
  | Del x => rfl
  | Ins e π a =>
      have hkt : k ≠ t := by
        intro h
        subst h
        simp only [fresh_ts] at hf
        rw [hf.2] at hk
        exact Bool.noConfusion hk
      simp only [do_, upd, sel]
      rw [if_neg hkt]

omit [DecidableEq α] in
/-- A surviving id's value is untouched by a merge, seen from branch `a`
(coherence with the LCA is the immutability invariant). -/
theorem sel_merge_stable (l a b : concrete_st α) (k : ℕ)
    (hla : coherent2 l a) (hk : contains a k = true) :
    sel (merge l a b) k = sel a k := by
  simp only [merge, sel]
  by_cases hl : contains l k
  · rw [if_pos hl]
    exact hla k hl hk
  · rw [if_neg hl, if_pos hk]

omit [DecidableEq α] in
/-- Symmetric statement for branch `b`. -/
theorem sel_merge_stable_right (l a b : concrete_st α) (k : ℕ)
    (hlb : coherent2 l b) (hab : coherent2 a b) (hk : contains b k = true) :
    sel (merge l a b) k = sel b k := by
  simp only [merge, sel]
  by_cases hl : contains l k
  · rw [if_pos hl]
    exact hlb k hl hk
  · rw [if_neg hl]
    by_cases ha' : contains a k
    · rw [if_pos ha']
      exact hab k ha' hk
    · rw [if_neg ha']

/-! ## The stability theorems (S2/S4 — the adopted contract) -/

omit [DecidableEq α] in
/-- **Step display stability** (litmus S2). Any op with a fresh timestamp
preserves the display order of every surviving pair. Instantiated at `Del`
(whose `fresh_ts` is trivial) this is **delete-order preservation** — the
sequential-spec clause the proved flat RGA machine-refutably violates. -/
theorem before_do_stable (Γ : OrderedPrefixCode) (s : concrete_st α)
    (o : op_t α) (t1 t2 : ℕ) (hf : fresh_ts o s)
    (hb : before s t1 t2)
    (h1 : contains (do_ Γ s o) t1 = true) (h2 : contains (do_ Γ s o) t2 = true) :
    before (do_ Γ s o) t1 t2 := by
  obtain ⟨hl1, hl2, hlt⟩ := hb
  refine ⟨h1, h2, ?_⟩
  simp only [pos]
  rw [sel_do_stable Γ s o t1 hf hl1, sel_do_stable Γ s o t2 hf hl2]
  exact hlt

omit [DecidableEq α] in
/-- **Pairwise display stability at merges** (litmus S4, branch `a`'s pairs).
A pair co-displayed at a branch and surviving the merge is displayed in the
same order by the merge — the contract "if a co-displayed pair is flipped,
we have failed", from nothing but value immutability. -/
theorem before_merge_stable (l a b : concrete_st α) (t1 t2 : ℕ)
    (hla : coherent2 l a)
    (hb : before a t1 t2)
    (h1 : contains (merge l a b) t1 = true) (h2 : contains (merge l a b) t2 = true) :
    before (merge l a b) t1 t2 := by
  obtain ⟨hl1, hl2, hlt⟩ := hb
  refine ⟨h1, h2, ?_⟩
  simp only [pos]
  rw [sel_merge_stable l a b t1 hla hl1, sel_merge_stable l a b t2 hla hl2]
  exact hlt

omit [DecidableEq α] in
/-- Branch `b`'s pairs, symmetrically. -/
theorem before_merge_stable_right (l a b : concrete_st α) (t1 t2 : ℕ)
    (hlb : coherent2 l b) (hab : coherent2 a b)
    (hb : before b t1 t2)
    (h1 : contains (merge l a b) t1 = true) (h2 : contains (merge l a b) t2 = true) :
    before (merge l a b) t1 t2 := by
  obtain ⟨hl1, hl2, hlt⟩ := hb
  refine ⟨h1, h2, ?_⟩
  simp only [pos]
  rw [sel_merge_stable_right l a b t1 hlb hab hl1,
      sel_merge_stable_right l a b t2 hlb hab hl2]
  exact hlt

/-! ## The executable read and SPOT scenarios

`document s ids` — the display over an explicit id list (repo convention:
the function-based map cannot enumerate its own domain). The concrete
scenarios run the **unary** code; every verdict below is a
`native_decide` computation on the real `do_`/`merge`. -/

/-- The read: live ids sorted by descending key. -/
def document (s : concrete_st α) (ids : List ℕ) : List ℕ :=
  (ids.filter (fun t => contains s t)).mergeSort
    (fun t1 t2 => keyLe (key (pos s t2)) (key (pos s t1)))

/-- Build a state from `(id, element, coordinate)` records. -/
def mkE (recs : List (ℕ × ℕ × coord)) : concrete_st ℕ :=
  recs.foldl (fun s r => upd s r.1 (r.2.1, r.2.2)) (init_st ℕ)

/-- Shorthand: the unary codeword. -/
def u (d : ℕ) : coord := unaryEnc d

/-! ### The flat RGA's reorder witness — opposite verdict here

`Sal/MRDTs/RGA/RGA_Tombstone_Free_SPOT.lean` (`del_can_reorder_survivors`):
state `[(5,100,root), (6,101,root), (8,102,under 5)]` reads `[6,5,8]`; the
flat RGA's delete of `5` re-sorts the rehomed `8` by its own timestamp and
reads `[8,6]` — the `[b,a,c] → [c,b]` anomaly. Here the coordinates are
absolute, deletion touches no value, and the order is preserved. -/

def s_reorder : concrete_st ℕ := mkE [(5, 100, u 5), (6, 101, u 6), (8, 102, u 5 ++ u 3)]

theorem reorder_document_before : document s_reorder [5, 6, 8] = [6, 5, 8] := by
  native_decide

theorem del_preserves_order :
    document (do_ unaryCode s_reorder (11, 1, .Del 5)) [5, 6, 8] = [6, 8] := by
  native_decide

/-! ### Litmus L1 (delete-reorder), built through `do_` from `init` -/

def s_L1 : concrete_st ℕ :=
  do_ unaryCode
    (do_ unaryCode
      (do_ unaryCode (init_st ℕ) (1, 0, .Ins 65 [] 0))
      (2, 0, .Ins 66 [] 0))
    (3, 0, .Ins 67 (u 1) 1)

theorem l1_document : document s_L1 [1, 2, 3] = [2, 1, 3] := by native_decide

theorem l1_delete_order :
    document (do_ unaryCode s_L1 (4, 0, .Del 1)) [1, 2, 3] = [2, 3] := by
  native_decide

/-! ### Merge read and the credential countermodel (design doc §1, §4)

`6` and `10` race the front; `22, 16` typed under `6`; a third party mints
`8` concurrently. Both death-before and death-after topologies read
`[10, 8, 22, 16]` — the shape that kills every timestamp-oblivious variant,
converging here because coordinates are birth constants. -/

def m_lca : concrete_st ℕ := mkE []
def m_A : concrete_st ℕ := mkE [(6, 100, u 6), (22, 102, u 6 ++ u 16), (16, 103, u 6 ++ u 10)]
def m_B : concrete_st ℕ := mkE [(10, 101, u 10)]
def m_RT : concrete_st ℕ := mkE [(8, 104, u 8)]

def m_M1 : concrete_st ℕ := merge m_lca m_A m_B

theorem merge_document : document m_M1 [6, 10, 16, 22] = [10, 6, 22, 16] := by
  native_decide

/-- Topology X: meet `8` while `6` is alive, then delete `6`. -/
def m_X : concrete_st ℕ := do_ unaryCode (merge m_lca m_M1 m_RT) (30, 1, .Del 6)

/-- Topology Y: delete `6` first, then meet `8`. -/
def m_Y : concrete_st ℕ := merge m_lca (do_ unaryCode m_M1 (30, 1, .Del 6)) m_RT

theorem credential_topologies_converge :
    document m_X [6, 8, 10, 16, 22] = [10, 8, 22, 16] ∧
    document m_Y [6, 8, 10, 16, 22] = [10, 8, 22, 16] := by
  constructor <;> native_decide

end Sal.EmbedRGA
