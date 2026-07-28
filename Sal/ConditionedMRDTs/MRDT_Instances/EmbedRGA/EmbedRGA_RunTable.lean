import Sal.ConditionedMRDTs.MRDT_Instances.EmbedRGA.EmbedRGA_Recoding
import Sal.MRDTs.RGA_Embed.RunTable

/-!
# The run table at the instance — display identity, T-epoch, SPOTs

The kernel theory (`Sal/MRDTs/RGA_Embed/RunTable.lean`: T-tail, T-repr,
T-cmp, T-walk, T-mut) is state-level and hypothesis-free. This file:

* **display identity** (`runTable_display_identity`): the table walk over a
  version's birth chains reproduces the canonical document's coordinate
  sequence exactly — `whiteboard/run-table-note.md` §8's walk-order gate as
  a theorem;
* **T-epoch** (`runTable_epoch`): composition with the re-coding cluster.
  This is the ONLY theorem in the whole run-table stack that carries a
  settled-cut hypothesis (the `StablePrefixMap` bundle + `Dom` coverage it
  inherits from the epoch map it composes with). Its absence everywhere
  else — T-tail, T-repr, T-cmp, T-walk, T-mut are unconditioned — is the
  formal content of the **no-stability-gate** property: the run table
  exists for every state, unsettled suffixes included;
* **SPOTs** (PASS + FAIL, hand-derived, matching the Python's directed
  cases): the typing table with `(run-id, offset)` addresses, D1's mid-run
  split with the no-split rival pinned to the wrong display
  (`abcdefX`-shaped), D2's liveness split, D4's coalesce necessity (the
  drifted two-entry table re-canonicalizes to ONE entry), D5's
  vanished-anchor materialization, and the comparator against `keyLt`.
-/

namespace Sal.ConditionedMRDTs

open Sal.Emulation
open Sal.EmbedRGA (OrderedPrefixCode keyLt keyLe key unaryCode coordOf
  PosChain keyLt_total keyLt_irrefl keyLt_asymm key_inj)
open Sal.EmbedRGA.RunTable

set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] [Inhabited α]

/-! ## §1  The chain representation of a document -/

/-- The version's records carry exactly the coordinates of a positive,
nonempty birth-chain list (what `EHonestCore.chain_gen` supplies, record for
record, in document order). -/
def ChainRep (Γ : OrderedPrefixCode) (s : EState α)
    (Lc : List (List ℕ)) : Prop :=
  s.map (fun r => r.2.2) = Lc.map (coordOf Γ)
  ∧ (∀ c ∈ Lc, PosChain c) ∧ ([] : List ℕ) ∉ Lc

/-- Strictly `keyLt`-descending coordinate lists with the same members are
equal (the `esorted_ext` argument, at the coordinate level). -/
theorem keyLt_sorted_ext : ∀ {l l' : List (List Bool)},
    l.Pairwise (fun c1 c2 => keyLt (key c2) (key c1) = true) →
    l'.Pairwise (fun c1 c2 => keyLt (key c2) (key c1) = true) →
    (∀ c, c ∈ l ↔ c ∈ l') → l = l'
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, _, hmem =>
      absurd ((hmem y).mpr List.mem_cons_self) (by simp)
  | x :: xs, [], _, _, hmem =>
      absurd ((hmem x).mp List.mem_cons_self) (by simp)
  | x :: xs, y :: ys, hs, hs', hmem => by
      rcases List.pairwise_cons.mp hs with ⟨hx, hxs⟩
      rcases List.pairwise_cons.mp hs' with ⟨hy, hys⟩
      have hxy : x = y := by
        rcases List.mem_cons.mp ((hmem x).mp List.mem_cons_self) with h | h
        · exact h
        · rcases List.mem_cons.mp ((hmem y).mpr List.mem_cons_self)
            with h' | h'
          · exact h'.symm
          · have h1 := hy x h
            have h2 := hx y h'
            rw [keyLt_asymm h1] at h2
            exact Bool.noConfusion h2
      subst hxy
      have htails : ∀ z, z ∈ xs ↔ z ∈ ys := by
        intro z
        constructor
        · intro hz
          rcases List.mem_cons.mp ((hmem z).mp (List.mem_cons_of_mem _ hz))
            with rfl | h
          · exact absurd (hx z hz) (by rw [keyLt_irrefl]; simp)
          · exact h
        · intro hz
          rcases List.mem_cons.mp ((hmem z).mpr (List.mem_cons_of_mem _ hz))
            with rfl | h
          · exact absurd (hy z hz) (by rw [keyLt_irrefl]; simp)
          · exact h
      rw [keyLt_sorted_ext hxs hys htails]

/-! ## §2  Display identity: the walk reproduces the read -/

/-- **T-walk at the instance (walk = query order)**: over any canonical
document with a chain representation, the run-table walk's coordinate
sequence IS the document's coordinate sequence — the display, verbatim, in
order. No honesty, reachability, or stability hypothesis: only sortedness
(the canonical form) and the chain representation itself. -/
theorem runTable_display_identity (Γ : OrderedPrefixCode) (s : EState α)
    (Lc : List (List ℕ)) (hs : ESorted s) (hrep : ChainRep Γ s Lc) :
    (walk Lc).map (coordOf Γ) = s.map (fun r => r.2.2) := by
  obtain ⟨hmap, hpos, hnil⟩ := hrep
  rw [hmap]
  refine keyLt_sorted_ext ?_ ?_ ?_
  · rw [List.pairwise_map]
    exact walk_pairwise_keyLt Γ hpos hnil
  · have h1 : (s.map (fun r => r.2.2)).Pairwise
        (fun c1 c2 => keyLt (key c2) (key c1) = true) := by
      rw [List.pairwise_map]
      exact hs
    rwa [hmap] at h1
  · intro c
    rw [List.mem_map, List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, (mem_walk hnil).mp hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, (mem_walk hnil).mpr hx, rfl⟩

/-! ## §3  T-epoch — composition with the re-coding cluster

The **only** settled-cut hypothesis in the run-table stack lives here: `F`
is a stable-prefix map (H2 = `ord`, H3 = `ext`) and `hdom` says the state at
rest is covered by the cut — exactly the contract `eRecode_*` inherits from
the epoch protocol. Everything else in this development holds at every
state, which is the formal content of the no-stability-gate property (run
table ≈ 21–27 b/ch with NO settled cut, `whiteboard/run-table-note.md` §8). -/

/-- **T-epoch**: after a re-coding epoch, rebuilding the run table over the
re-mapped chains again reproduces the (re-mapped) document verbatim, and the
read is the original read — display identity for the rebuilt table needs no
new order argument beyond H2 (`eRecode_sorted`), and the read identity is
T2 (`eRemapSt_query`). -/
theorem runTable_epoch (Γ : OrderedPrefixCode) (F : StablePrefixMap Γ)
    (s : EState α) (hs : ESorted s) (hdom : ∀ x ∈ s, F.Dom x.2.2)
    (Γ' : OrderedPrefixCode) (Lc' : List (List ℕ))
    (hrep : ChainRep Γ' (eRemapSt F.f s) Lc') :
    (walk Lc').map (coordOf Γ') = (eRemapSt F.f s).map (fun r => r.2.2)
    ∧ (E Γ α).query (eRemapSt F.f s) () = (E Γ α).query s () :=
  ⟨runTable_display_identity Γ' (eRemapSt F.f s) Lc'
      (eRecode_sorted F hs hdom) hrep,
    eRemapSt_query Γ F.f s⟩

/-- T-epoch at a registered version of an honestly reachable configuration:
the version's canonical sortedness is supplied by the recoding cluster
(`eRecode_version_sorted`), so the rebuilt table's walk identity follows for
every version state whose records the cut covers. -/
theorem runTable_epoch_version (Γ : OrderedPrefixCode)
    (F : StablePrefixMap Γ) {C : Configuration (E Γ ℕ)}
    (hReach : EReach Γ C) (hHon : EHonest Γ C)
    {v : Version} {s : EState ℕ}
    {Ev : Set (Op (EOp ℕ))}
    (hv : C.ver v = some (s, Ev))
    (hdom : ∀ x ∈ s, F.Dom x.2.2)
    (Γ' : OrderedPrefixCode) (Lc' : List (List ℕ))
    (hrep : ChainRep Γ' (eRemapSt F.f s) Lc') :
    (walk Lc').map (coordOf Γ') = (eRemapSt F.f s).map (fun r => r.2.2) :=
  runTable_display_identity Γ' (eRemapSt F.f s) Lc'
    (eRecode_version_sorted F hReach hHon hv hdom).2 hrep

/-! ## §4  Axiom audit (theorem layer) -/

#print axioms runTable_display_identity
#print axioms runTable_epoch
#print axioms runTable_epoch_version

/-! ## §5  SPOTs — concrete executions, PASS + FAIL, hand-derived

Chains at the kernel level (one label per keystroke, typing = delta-1
chains); expected tables and walks derived by hand from
`whiteboard/run-table-note.md` §2/§5, never `#eval`'d from the
implementation. The directed shapes match the Python harness's D1–D5. -/

namespace RunTableSPOT

/-- The default entry (out-of-range accessor). -/
def entryAt (T : Table) (j : ℕ) : RTEntry := T.getD j ⟨none, false, 0, 0⟩

/-- Attachments of entry `i`, newest label first — read from the table. -/
def attachedAt (T : Table) (i : ℕ) : List ℕ :=
  ((List.range T.length).filter
    (fun j => (entryAt T j).par.map Prod.fst == some i)).mergeSort
    (fun j k => decide ((entryAt T k).delta ≤ (entryAt T j).delta))

/-- The table-structural walk (Python `table_walk`, one-sided): live
members in offset order, then attachment subtrees newest first — consulting
the TABLE alone. -/
def walkT (T : Table) : ℕ → ℕ → List (List ℕ)
  | 0, _ => []
  | fuel + 1, i =>
      (if (entryAt T i).live
       then (List.range (entryAt T i).len).map
         (fun k => hsAt T i ++ List.replicate k 1)
       else [])
      ++ (attachedAt T i).flatMap (walkT T fuel)

def tableWalk (T : Table) : List (List ℕ) :=
  (((List.range T.length).filter
      (fun j => (entryAt T j).par == none)).mergeSort
    (fun j k => decide ((entryAt T k).delta ≤ (entryAt T j).delta))).flatMap
    (walkT T T.length)

/-- Typing `abcdef`: six keystrokes, each anchored at its predecessor. -/
def L6 : List (List ℕ) :=
  [[1], [1,1], [1,1,1], [1,1,1,1], [1,1,1,1,1], [1,1,1,1,1,1]]

/-- PASS: the typing document compiles to ONE run — six records, one
header, `(run-id, offset)` addresses. -/
theorem spot_typing : tableOf L6 = [⟨none, true, 1, 6⟩] := by native_decide

/-- PASS: the address of the fourth keystroke is `(0, 3)`. -/
theorem spot_typing_address :
    ((headsList L6).idxOf (headOf L6 [1,1,1,1]),
      ([1,1,1,1] : List ℕ).length - (headOf L6 [1,1,1,1]).length)
      = (0, 3) := by native_decide

/-- The same six records as six singleton entries (a member-by-member
delivery without coalesce — the D3 shape). -/
def naive6 : Table :=
  [⟨none, true, 1, 1⟩, ⟨some (0, 0), true, 1, 1⟩, ⟨some (1, 0), true, 1, 1⟩,
   ⟨some (2, 0), true, 1, 1⟩, ⟨some (3, 0), true, 1, 1⟩,
   ⟨some (4, 0), true, 1, 1⟩]

/-- PASS: the naive table denotes exactly the typing state. -/
theorem spot_naive_denotes : stateOf naive6 = L6 := by native_decide

/-- FAIL companion (D3): the naive table is NOT canonical — the rebuild
re-coalesces the six singletons into the single run. -/
theorem spot_naive_drifts :
    tableOf (stateOf naive6) = [⟨none, true, 1, 6⟩]
    ∧ tableOf (stateOf naive6) ≠ naive6 := by native_decide

/-- D1: a concurrent insert `X` (delta 4) after the third keystroke. -/
def L7 : List (List ℕ) := L6 ++ [[1,1,1,4]]

/-- PASS: the run splits into three entries, both children at the tail. -/
theorem spot_d1_split :
    tableOf L7 = [⟨none, true, 1, 3⟩, ⟨some (0, 2), true, 1, 3⟩,
      ⟨some (0, 2), true, 4, 1⟩] := by native_decide

/-- PASS: display = `abcXdef`. -/
theorem spot_d1_walk :
    walk L7 = [[1], [1,1], [1,1,1], [1,1,1,4],
      [1,1,1,1], [1,1,1,1,1], [1,1,1,1,1,1]] := by native_decide

/-- PASS: the table-structural walk agrees with the state walk. -/
theorem spot_d1_tableWalk : tableWalk (tableOf L7) = walk L7 := by
  native_decide

/-- PASS: the GENERIC table-direct walk (`RunTable.tableWalk`, the §7⅞
theorem-bearing definition, proved faithful in `tableWalk_tableOf`) agrees
on the D1 pin too — the SPOT and the generic theorem name the same reading
procedure. -/
theorem spot_d1_tableWalk_generic :
    Sal.EmbedRGA.RunTable.tableWalk (tableOf L7) = walk L7 := by
  native_decide

/-- The no-split rival: `abcdef` kept as ONE run, `X` hung at interior
offset 2 — violating tail attachment. -/
def rival : Table := [⟨none, true, 1, 6⟩, ⟨some (0, 2), true, 4, 1⟩]

/-- PASS: the rival denotes the same seven records ... -/
theorem spot_rival_same_state : (stateOf rival).Perm L7 := by native_decide

/-- FAIL companion (the no-split rival pinned to the wrong display): its
structural walk misplaces `X` to the end — the `abcdefX` shape. -/
theorem spot_rival_wrong_display :
    tableWalk rival = [[1], [1,1], [1,1,1], [1,1,1,1], [1,1,1,1,1],
      [1,1,1,1,1,1], [1,1,1,4]]
    ∧ tableWalk rival ≠ walk L7 := by native_decide

/-- FAIL companion: and it is not canonical — the rebuild is the split
table. -/
theorem spot_rival_not_canonical :
    tableOf (stateOf rival) ≠ rival
    ∧ tableOf (stateOf rival) = tableOf L7 := by native_decide

/-- D2: delete the third keystroke — it has kept children, so it stays as
dead STRUCTURE (the liveness split). -/
def Ldel : List (List ℕ) :=
  [[1], [1,1], [1,1,1,1], [1,1,1,1,1], [1,1,1,1,1,1]]

/-- PASS: three entries — live `[a,b]`, dead `[c]` carved out, live
`[d,e,f]` — liveness uniform per entry. -/
theorem spot_d2_liveness_split :
    tableOf Ldel = [⟨none, true, 1, 2⟩, ⟨some (0, 1), false, 1, 1⟩,
      ⟨some (1, 0), true, 1, 3⟩] := by native_decide

/-- PASS + FAIL: display = `abdef`; the dead chain is structure, not text. -/
theorem spot_d2_walk :
    walk Ldel = [[1], [1,1], [1,1,1,1], [1,1,1,1,1], [1,1,1,1,1,1]]
    ∧ [1,1,1] ∉ walk Ldel := by native_decide

/-- D4 (coalesce is the FORCED delete-inverse): the two halves of the
typing run — what deleting a concurrent interloper leaves if the table does
NOT coalesce — denote exactly the typing document, yet the canonical table
re-fuses them: without the coalesce rule the incremental table has drifted
from canonical. This is also the pin for the `no_fuse` hypothesis of
`tableOf_stateOf`: `Tdrift` satisfies every other canonicity clause and
still fails the round trip. -/
def Tdrift : Table := [⟨none, true, 1, 3⟩, ⟨some (0, 2), true, 1, 3⟩]

theorem spot_d4_coalesce_necessity :
    stateOf Tdrift = L6
    ∧ tableOf (stateOf Tdrift) = [⟨none, true, 1, 6⟩]
    ∧ tableOf (stateOf Tdrift) ≠ Tdrift := by native_decide

/-- D5 (vanished-anchor materialization): after `abc` and a childless
delete of `c`, a delivered insert anchored at `c` carries `c`'s coordinate
level; the kept tree re-materializes `c` as a DEAD entry. -/
def Lmat : List (List ℕ) := [[1], [1,1], [1,1,1,1]]

theorem spot_d5_materialize :
    tableOf Lmat = [⟨none, true, 1, 2⟩, ⟨some (0, 1), false, 1, 1⟩,
      ⟨some (1, 0), true, 1, 1⟩] := by native_decide

/-- PASS + FAIL: display = `abX`; the materialized ancestor is dead
structure, and the table has three entries, not two. -/
theorem spot_d5_walk :
    walk Lmat = [[1], [1,1], [1,1,1,1]] ∧ [1,1,1] ∉ walk Lmat
    ∧ (tableOf Lmat).length = 3 := by native_decide

/-- T-cmp concretely: at the D1 divergence the newer label displays first,
in agreement with the coordinate keys under the unary code — both verdict
directions pinned. -/
theorem spot_cmp :
    cmpTable L7 [1,1,1,4] [1,1,1,1] = true
    ∧ cmpTable L7 [1,1,1,1] [1,1,1,4] = false
    ∧ keyLt (key (coordOf unaryCode [1,1,1,1]))
        (key (coordOf unaryCode [1,1,1,4])) = true := by native_decide

#print axioms spot_typing
#print axioms spot_d1_split
#print axioms spot_rival_wrong_display
#print axioms spot_d4_coalesce_necessity
#print axioms spot_d5_materialize
#print axioms spot_cmp

end RunTableSPOT

end Sal.ConditionedMRDTs
