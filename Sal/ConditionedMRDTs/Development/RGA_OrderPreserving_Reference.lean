import Mathlib

/-!
# An order-preserving, tombstone-free sequence CRDT — reference model

**Research probe (Development).** This file is a small, self-contained REFERENCE
MODEL of the "anchor + sibling edge" order-preserving sequence CRDT (KC +
Kartik Nagar), in its *stored-path* form, together with a machine-checked proof
that it fixes the delete-reorder bug of the current tombstone-free RGA.

## The bug being fixed

The tombstone-free RGA reorders survivors on delete. With
`ins(a after 0); ins(b after 0); ins(c after a)` the document reads `[b, a, c]`
(siblings newest-first), and deleting `a` gives `[c, b]` instead of `[b, c]`:
the delete physically splices `a` out and **rehomes** `c` to the root, where `c`
re-sorts by its own key and leapfrogs `b`. This is a *sequential*-spec violation
(one replica, no concurrency), machine-checked as
`RGA_TF_SPOT.tombstone_free_violates_delete_order`
(`Sal/MRDTs/RGA_Rehoming/RGA_Tombstone_Free_SPOT.lean`).

## The fix embodied here

Make each node's position embed its **full ancestry** as an immutable path of
anchor keys from the root. Then:

* `read`  = sort the live nodes by their (immutable) position and project ids;
* `del`   = simply drop the node from the live set — **nothing rehomes, nothing
            re-sorts**, so surviving positions never move.

Because positions are immutable, deleting one node can only *remove* it from the
sorted sequence; the relative order of everyone else is exactly preserved. That
is the headline theorem `delete_order_preserving`, which is the precise property
the old RGA refutes.

## Key encoding and the sort order

`key ts := -(ts : ℤ)`: newer (larger `ts`) ⇒ more negative ⇒ sorts **earlier**,
realising the RGA "siblings newest-first" convention under an ascending sort.

The comparison `nodeLE` is lexicographic on the position path, tie-broken by
`(id, elem)`. The tie-break is invisible on any realistic state (distinct
timestamps give distinct positions, so ties never arise on the concrete
scenarios below) but it makes `nodeLE` **antisymmetric as an equality of node
values**, which is what lets the general theorem hold for an *arbitrary* state
with no well-formedness side condition.

## Modelling choice for `posOf`

A node's position is computed at insert time from its anchor's stored position
(`posOf`). If an anchor has been deleted, `posOf` returns `[]` (root). A fully
faithful implementation would carry an append-only position map so that deleted
anchors still resolve; here the test scenarios always insert *before* any delete
of the relevant anchor, so `posOf` always resolves and this corner never fires.
Positions, once assigned, are immutable — that is the whole point.
-/

namespace RGA_OrderPreserving

/-! ## Data -/

/-- A live node: its identity, its payload element, and its immutable position
(the full path of anchor keys from the root to this node). -/
structure Node where
  id : ℕ
  elem : ℕ
  pos : List ℤ
deriving DecidableEq, Repr

/-- The state is the set of live nodes (kept dedup-by-id in practice). -/
abbrev St := List Node

/-- Newest-first key: larger timestamp ⇒ more negative ⇒ sorts earlier. -/
def key (ts : ℕ) : ℤ := -(ts : ℤ)

/-! ## The comparison

`posLE` is the lexicographic `≤` on `List ℤ`, `nodeLE` lifts it to nodes with a
`(id, elem)` tie-break. Both are computable `Bool` functions (so `native_decide`
reduces them), and we prove they are transitive, total, and antisymmetric — the
hypotheses `mergeSort`'s stability lemmas need. -/

/-- Lexicographic `≤` on `List ℤ`, as a decidable `Bool`. -/
def posLE : List ℤ → List ℤ → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else posLE as bs

theorem posLE_trans :
    ∀ (a b c : List ℤ), posLE a b = true → posLE b c = true → posLE a c = true
  | [], _, _, _, _ => rfl
  | (_ :: _), [], _, h, _ => by simp [posLE] at h
  | (_ :: _), (_ :: _), [], _, h => by simp [posLE] at h
  | (x :: as), (y :: bs), (z :: cs), h1, h2 => by
      by_cases hxy : x < y
      · by_cases hxz : x < z
        · simp only [posLE]; rw [if_pos hxz]
        · exfalso
          have hzy : z < y := by omega
          simp only [posLE] at h2
          rw [if_neg (by omega : ¬ y < z), if_pos hzy] at h2
          simp at h2
      · by_cases hyx : y < x
        · exfalso; simp only [posLE] at h1; rw [if_neg hxy, if_pos hyx] at h1; simp at h1
        · have hxyeq : x = y := by omega
          subst hxyeq
          have e1 : posLE as bs = true := by
            simp only [posLE] at h1; rwa [if_neg hxy, if_neg hxy] at h1
          by_cases hxz : x < z
          · simp only [posLE]; rw [if_pos hxz]
          · by_cases hzx : z < x
            · exfalso; simp only [posLE] at h2; rw [if_neg hxz, if_pos hzx] at h2; simp at h2
            · have hxzeq : x = z := by omega
              subst hxzeq
              have e2 : posLE bs cs = true := by
                simp only [posLE] at h2; rwa [if_neg hxz, if_neg hxz] at h2
              simp only [posLE]; rw [if_neg hxz, if_neg hxz]
              exact posLE_trans as bs cs e1 e2

theorem posLE_total : ∀ (a b : List ℤ), (posLE a b || posLE b a) = true
  | [], _ => by simp [posLE]
  | (_ :: _), [] => by simp [posLE]
  | (x :: as), (y :: bs) => by
      by_cases hxy : x < y
      · simp [posLE, hxy]
      · by_cases hyx : y < x
        · simp [posLE, hxy, hyx]
        · have e1 : posLE (x :: as) (y :: bs) = posLE as bs := by
            simp only [posLE]; rw [if_neg hxy, if_neg hyx]
          have e2 : posLE (y :: bs) (x :: as) = posLE bs as := by
            simp only [posLE]; rw [if_neg hyx, if_neg hxy]
          rw [e1, e2]; exact posLE_total as bs

theorem posLE_antisymm : ∀ {a b : List ℤ}, posLE a b = true → posLE b a = true → a = b
  | [], [], _, _ => rfl
  | [], (_ :: _), _, h => by simp [posLE] at h
  | (_ :: _), [], h, _ => by simp [posLE] at h
  | (x :: as), (y :: bs), h1, h2 => by
      by_cases hxy : x < y
      · exfalso
        simp only [posLE] at h2
        rw [if_neg (by omega : ¬ y < x), if_pos hxy] at h2
        simp at h2
      · by_cases hyx : y < x
        · exfalso; simp only [posLE] at h1; rw [if_neg hxy, if_pos hyx] at h1; simp at h1
        · have hxyeq : x = y := by omega
          subst hxyeq
          have e1 : posLE as bs = true := by
            simp only [posLE] at h1; rwa [if_neg hxy, if_neg hxy] at h1
          have e2 : posLE bs as = true := by
            simp only [posLE] at h2; rwa [if_neg hxy, if_neg hxy] at h2
          rw [posLE_antisymm e1 e2]

/-- `(id, elem)` tie-break, used only when two positions coincide. -/
def idElemLE (m n : Node) : Bool :=
  if m.id = n.id then decide (m.elem ≤ n.elem) else decide (m.id < n.id)

theorem idElemLE_trans (a b c : Node)
    (h1 : idElemLE a b = true) (h2 : idElemLE b c = true) : idElemLE a c = true := by
  simp only [idElemLE] at *
  split_ifs at * <;> simp_all <;> omega

theorem idElemLE_total (a b : Node) : (idElemLE a b || idElemLE b a) = true := by
  simp only [idElemLE]
  split_ifs <;> simp_all <;> omega

theorem idElemLE_antisymm {a b : Node}
    (h1 : idElemLE a b = true) (h2 : idElemLE b a = true) : a.id = b.id ∧ a.elem = b.elem := by
  simp only [idElemLE] at h1 h2
  split_ifs at h1 h2 <;> simp_all <;> omega

/-- Node comparison: lexicographic on position, tie-broken by `(id, elem)`. -/
def nodeLE (m n : Node) : Bool :=
  if m.pos = n.pos then idElemLE m n else posLE m.pos n.pos

theorem nodeLE_trans (a b c : Node)
    (h1 : nodeLE a b = true) (h2 : nodeLE b c = true) : nodeLE a c = true := by
  simp only [nodeLE] at h1 h2 ⊢
  by_cases hab : a.pos = b.pos <;> by_cases hbc : b.pos = c.pos
  · rw [if_pos hab] at h1; rw [if_pos hbc] at h2; rw [if_pos (hab.trans hbc)]
    exact idElemLE_trans a b c h1 h2
  · rw [if_pos hab] at h1; rw [if_neg hbc] at h2
    have hac : a.pos ≠ c.pos := by rw [hab]; exact hbc
    rw [if_neg hac, hab]; exact h2
  · rw [if_neg hab] at h1; rw [if_pos hbc] at h2
    have hac : a.pos ≠ c.pos := by rw [← hbc]; exact hab
    rw [if_neg hac, ← hbc]; exact h1
  · rw [if_neg hab] at h1; rw [if_neg hbc] at h2
    by_cases hac : a.pos = c.pos
    · exfalso; rw [hac] at h1; exact hbc (posLE_antisymm h2 h1)
    · rw [if_neg hac]; exact posLE_trans a.pos b.pos c.pos h1 h2

theorem nodeLE_total (a b : Node) : (nodeLE a b || nodeLE b a) = true := by
  simp only [nodeLE]
  by_cases hp : a.pos = b.pos
  · rw [if_pos hp, if_pos hp.symm]; exact idElemLE_total a b
  · rw [if_neg hp, if_neg (fun h => hp h.symm)]; exact posLE_total a.pos b.pos

theorem nodeLE_antisymm {a b : Node}
    (h1 : nodeLE a b = true) (h2 : nodeLE b a = true) : a = b := by
  simp only [nodeLE] at h1 h2
  by_cases hp : a.pos = b.pos
  · rw [if_pos hp] at h1; rw [if_pos hp.symm] at h2
    obtain ⟨hid, hel⟩ := idElemLE_antisymm h1 h2
    cases a; cases b; simp_all
  · rw [if_neg hp] at h1; rw [if_neg (fun h => hp h.symm)] at h2
    exact absurd (posLE_antisymm h1 h2) hp

/-! ## The datatype -/

/-- Position of the node with id `anchorId`, or `[]` (root sentinel `0`, or an
absent/deleted anchor). See the module docstring on the modelling choice. -/
def posOf (s : St) (anchorId : ℕ) : List ℤ :=
  match s.find? (fun n => n.id == anchorId) with
  | some n => n.pos
  | none => []

/-- Insert `id` (element `elem`, timestamp `ts`) after node `anchorId`: the new
node's position is the anchor's position extended by this node's key. The
position is fixed forever at this moment. -/
def insert (s : St) (id elem ts anchorId : ℕ) : St :=
  ⟨id, elem, posOf s anchorId ++ [key ts]⟩ :: s

/-- Delete: drop the node with id `x` from the live set. No rehoming. -/
def del (s : St) (x : ℕ) : St := s.filter (fun n => n.id != x)

/-- Read: sort the live nodes by position and project their ids (document order). -/
def read (s : St) : List ℕ := (s.mergeSort nodeLE).map (·.id)

/-! ## 1. The headline theorem — DeleteOrderPreserving HOLDS (general)

Deleting a node removes exactly that node from the document and preserves the
relative order of every survivor. This is the *general* theorem over an
arbitrary state, with no well-formedness hypothesis — the precise property the
tombstone-free RGA refutes.

The proof is the standard "stable sort commutes with filter": filtering then
sorting equals sorting then filtering. We derive it from `mergeSort` stability
via `List.Perm.eq_of_pairwise` (two `Pairwise` lists that are permutations of
each other, under an antisymmetric relation, are equal). Antisymmetry is exactly
`nodeLE_antisymm`. -/

/-- Filtering commutes with the position sort: the core stable-sort lemma. -/
theorem filter_mergeSort_comm (q : Node → Bool) (l : St) :
    (l.filter q).mergeSort nodeLE = (l.mergeSort nodeLE).filter q :=
  List.Perm.eq_of_pairwise
    (le := fun a b => nodeLE a b = true)
    (fun _ _ _ _ hab hba => nodeLE_antisymm hab hba)
    (List.pairwise_mergeSort nodeLE_trans nodeLE_total (l.filter q))
    ((List.pairwise_mergeSort nodeLE_trans nodeLE_total l).filter q)
    ((List.mergeSort_perm (l.filter q) nodeLE).trans
      (List.Perm.filter q (List.mergeSort_perm l nodeLE)).symm)

/-- **The prize.** A single delete removes its target from the document and
leaves the relative order of all survivors intact — for *every* state `s`. -/
theorem delete_order_preserving (s : St) (x : ℕ) :
    read (del s x) = (read s).filter (· != x) := by
  simp only [read, del, List.filter_map, filter_mergeSort_comm]
  rfl

/-! ## 2. KC's exact example passes

`ins a(id1,ts1) after 0; ins b(id2,ts2) after 0; ins c(id3,ts3) after a`.
Positions: `a = [-1]`, `b = [-2]`, `c = [-1,-3]`. Newest-first read is `[b,a,c]
= [2,1,3]`; deleting `a` leaves survivors in order `[b,c] = [2,3]` — NOT `[c,b]`,
which is what the tombstone-free RGA produces. -/

def s_bac : St :=
  insert (insert (insert ([] : St) 1 101 1 0) 2 102 2 0) 3 103 3 1

theorem read_s_bac : read s_bac = [2, 1, 3] := by native_decide

theorem del_a_preserves_order : read (del s_bac 1) = [2, 3] := by native_decide

/-- The delete matches "old read with the target filtered out" — here obtained by
instantiating the *general* theorem, so this is a firing of `delete_order_preserving`. -/
theorem del_a_matches_filter :
    read (del s_bac 1) = (read s_bac).filter (· != 1) := delete_order_preserving s_bac 1

/-! ## 3. The concurrent q/r case

`a(id1)` under root; `p(id2)`, `r(id4)` children of `a`; `q(id3)` child of `p`.
Positions: `a=[-1]`, `p=[-1,-2]`, `r=[-1,-4]`, `q=[-1,-2,-3]`. RGA order is
`a, r, p, q = [1,4,2,3]` (`r` newer than `p`). Deleting `p(id2)` keeps `q` and
`r` in their pre-delete relative order (`r` before `q`) — no swap. -/

def s_qr : St :=
  insert (insert (insert (insert ([] : St) 1 201 1 0) 2 202 2 1) 4 204 4 1) 3 203 3 2

theorem read_s_qr : read s_qr = [1, 4, 2, 3] := by native_decide

theorem del_p_preserves_order : read (del s_qr 2) = [1, 4, 3] := by native_decide

theorem del_p_matches_filter :
    read (del s_qr 2) = (read s_qr).filter (· != 2) := delete_order_preserving s_qr 2

/-! ## 4. Non-interleaving of concurrent runs

Two runs after `a`: `x1→x2` (chain) and `y1→y2` (chain). Positions
`x1=[-1,-2]`, `x2=[-1,-2,-3]`, `y1=[-1,-4]`, `y2=[-1,-4,-5]`. The read keeps
each run contiguous: `a, y1, y2, x1, x2 = [1,4,5,2,3]` — the `y`s (4,5) stay
together and the `x`s (2,3) stay together, never interleaved. -/

def s_runs : St :=
  insert (insert (insert (insert (insert ([] : St)
    1 301 1 0)   -- a  (id1) under root
    2 302 2 1)   -- x1 (id2) child of a
    3 303 3 2)   -- x2 (id3) child of x1
    4 304 4 1)   -- y1 (id4) child of a
    5 305 5 4    -- y2 (id5) child of y1

theorem read_s_runs : read s_runs = [1, 4, 5, 2, 3] := by native_decide

/-! ## 5. Convergence of a three-way merge

`merge3 L A B` reconciles by id: the live set is `(A ∪ B)` minus every id that
was in the LCA `L` but is absent from `A` or from `B` (i.e. deleted in a branch).
Positions are immutable, so whichever copy of a shared id we keep agrees on its
position. Convergence (commutativity of the read) therefore relies on the two
branches agreeing on the content of shared ids — which holds because each id is
minted by exactly one `insert`. -/

/-- Is some node with id `i` present in state `s`? -/
def present (s : St) (i : ℕ) : Bool := s.any (fun n => n.id == i)

/-- Three-way merge, reconciled by id. `A`'s copy of a shared id is kept
(positions are immutable so the choice is immaterial). -/
def merge3 (L A B : St) : St :=
  let cand := A ++ B.filter (fun n => ! present A n.id)
  cand.filter (fun n => ! (present L n.id && (! present A n.id || ! present B n.id)))

-- Scenario (a): concurrent inserts under the LCA node `a`.
def m_L : St := insert ([] : St) 1 401 1 0            -- a
def m_A : St := insert m_L 2 402 2 1                   -- + p (child of a)
def m_B : St := insert m_L 3 403 3 1                   -- + r (child of a)

theorem merge_read : read (merge3 m_L m_A m_B) = [1, 3, 2] := by native_decide

theorem merge_comm :
    read (merge3 m_L m_A m_B) = read (merge3 m_L m_B m_A) := by native_decide

-- Scenario (b): branch A deletes an interior node, branch B inserts after it.
-- LCA chain a(1) ← m(2) ← w(3). A deletes m(2). B inserts z(4) after m(2).
def d_L : St := insert (insert (insert ([] : St) 1 501 1 0) 2 502 2 1) 3 503 3 2
def d_A : St := del d_L 2                              -- A deletes interior m(2)
def d_B : St := insert d_L 4 504 4 2                   -- B inserts z(4) after m(2)

/-- `m(2)` (deleted in A) is dropped; survivors `w(3)` and `z(4)` keep the order
`z, w` fixed by their immutable positions — no rehoming. Read `= [1,4,3]`. -/
theorem merge_del_read : read (merge3 d_L d_A d_B) = [1, 4, 3] := by native_decide

theorem merge_del_comm :
    read (merge3 d_L d_A d_B) = read (merge3 d_L d_B d_A) := by native_decide

/-! ## Axiom audit -/

section AxiomAudit
#print axioms delete_order_preserving
#print axioms read_s_bac
#print axioms merge_del_comm
end AxiomAudit

end RGA_OrderPreserving
