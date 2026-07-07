import Sal.ConditionedMRDTs.Development.RGA_NoopFeasible_CanonFold
import Sal.ConditionedMRDTs.Development.RGA_RefEdge_FromAccurate

/-!
# `CanonStepOK` from honest facts — the `RefEdge`-free single-op step

*Additive; modifies no existing file; 0 `sorry`.*

The reachability route to unconditional RGA: instead of deriving the canonical fold discipline through
`RefEdge` (which needs `reference⟹vis`), a **reachable** `apply` allocates a *globally fresh* id `t`
(Step3's `h_fresh_t`: `t ∉ events`). The freshness `RefEdge` was buying — that no earlier op references
`t` (`hnoRef`) — then follows from "references are inserted-in-events" (`insertedIn_ev_of_ref`, built)
+ `t ∉ events`. `canonStepOK_ins_of_facts` derives `CanonStepOK` for the `Ins` from `hnoRef` + the
honest facts directly, with no `RefEdge`. Feeding it to `canonInv_doIns` gives single-op `CanonInv`
preservation — the `apply` case of the `CanonMatch` reachability invariant.
-/

set_option maxHeartbeats 1000000

namespace Sal.ConditionedMRDTs.RGACanonStepFromFacts

open Sal.Emulation
open RGACanonConvergence (CanonStepOK ChainOK deletedIn CanonInv delOK_of_accurate
  canonInv_doIns canonInv_doDel)
open RGANoopFeasible (refsOf)
open Sal.ConditionedMRDTs.RGAInvUpdateQ (WfOpGenQ)
open Sal.ConditionedMRDTs.RGARefEdgeFromAccurate (ref_live_of_accurate)

/-- **`CanonStepOK` for an `Ins` from honest facts** (no `RefEdge`).  Given `t` nonzero and fresh in
`s`, `hnoRef` (no op in `F` references `t`), `WfOpGenQ` (chain strictly below `t`), and `ChainOK`
(the anchor chain is a genuine live path — from `accurate`), the canonical step discipline holds. -/
theorem canonStepOK_ins_of_facts (F : List op_t) (s : concrete_st) (t r e a : ℕ) (p : List ℕ)
    (ht0 : t ≠ 0) (htf : contains s t = false)
    (hnoRef : ∀ z ∈ F, t ∉ refsOf z)
    (hgen : WfOpGenQ (t, r, .Ins e p a))
    (hchain : ChainOK s (a :: p)) :
    CanonStepOK F s (t, r, .Ins e p a) := by
  refine ⟨ht0, htf, ?_, ?_, ?_, hchain⟩
  · rintro ⟨t', r', p', hm⟩
    exact hnoRef (t', r', .Del p' t) hm (by simp [refsOf])
  · intro hmem
    exact absurd (hgen.2 t hmem) (lt_irrefl t)
  · intro t' r' e' p' a' hm hmem
    exact hnoRef (t', r', .Ins e' p' a') hm (by simpa [refsOf] using hmem)

#print axioms canonStepOK_ins_of_facts

/-- **Single-op `CanonInv` preservation for an `Ins`, from honest facts** (no `RefEdge`).  Composes
`canonStepOK_ins_of_facts` with `canonInv_doIns`: given the prior canonical invariant, a fresh id,
`hnoRef`, generation discipline, and `ChainOK`, the fold's invariant carries across the `Ins`.  The
`apply`-case for an insert of the `CanonMatch` reachability invariant. -/
theorem canonInv_doIns_of_facts (F : List op_t) (s : concrete_st) (t r e a : ℕ) (p : List ℕ)
    (hinv : CanonInv F s) (htf : contains s t = false)
    (hnoRef : ∀ z ∈ F, t ∉ refsOf z)
    (hgen : WfOpGenQ (t, r, .Ins e p a)) (hchain : ChainOK s (a :: p)) :
    CanonInv (F ++ [(t, r, .Ins e p a)]) (do_ s (t, r, .Ins e p a)) :=
  canonInv_doIns F s t r e a p hinv
    (canonStepOK_ins_of_facts F s t r e a p hgen.1 htf hnoRef hgen hchain)

/-- **Single-op `CanonInv` preservation for a `Del`, from `accurate`** (no `hnoRef` needed).  The `Del`
step discipline (`DelOK`) falls entirely out of `accurate` (`delOK_of_accurate`), so the invariant
carries across an accurately-applied delete given only the prior invariant.  The `apply`-case for a
delete of the `CanonMatch` reachability invariant. -/
theorem canonInv_doDel_of_accurate (F : List op_t) (s : concrete_st) (t r x : ℕ) (p : List ℕ)
    (hinv : CanonInv F s) (hacc : accurate (t, r, .Del p x) s) :
    CanonInv (F ++ [(t, r, .Del p x)]) (do_ s (t, r, .Del p x)) :=
  canonInv_doDel F s t r x p hinv (delOK_of_accurate s t r x p hinv.1 hacc)

#print axioms canonInv_doIns_of_facts
#print axioms canonInv_doDel_of_accurate

/-! ## `hnoRef` from freshness — the last config-level obligation, isolated

`hnoRef` (no op in the applied prefix references the fresh id `t`) is what `RefEdge` used to buy.  On
the reachability route it reduces to two facts about a *reachable* apply: every referenced id in the
prefix is itself the timestamp of an event in the prefix (`RefsInList` — a reachability invariant,
preserved across `apply` by `insertedIn_ev_of_ref` since a fresh op is accurate at its state), and the
new id is globally fresh (`h_fresh_t`: differs from every prior event's timestamp).  `hnoRef` is then a
one-line contradiction. -/

/-- Every id referenced by an op in `F` is the root (`0`) or the timestamp of some op in `F`.  A
reachability invariant of an accurately-executed event prefix. -/
def RefsInList (F : List op_t) : Prop :=
  ∀ z ∈ F, ∀ c ∈ refsOf z, c = 0 ∨ ∃ z' ∈ F, z'.1 = c

/-- **`hnoRef` from freshness.**  If every reference in `F` resolves to an event timestamp in `F`
(`RefsInList`) and the fresh id `t` is nonzero and differs from every timestamp in `F` (`h_fresh_t`),
then no op in `F` references `t`.  This is the exact `hnoRef` hypothesis of `canonInv_doIns_of_facts`,
discharged with no `RefEdge` — only the globally-fresh allocation of a reachable `apply`. -/
theorem hnoRef_of_refsInList (F : List op_t) (t : ℕ) (ht0 : t ≠ 0)
    (hfresh : ∀ z' ∈ F, z'.1 ≠ t) (href : RefsInList F) :
    ∀ z ∈ F, t ∉ refsOf z := by
  intro z hz hmem
  rcases href z hz t hmem with h0 | ⟨z', hz', hz'eq⟩
  · exact ht0 h0
  · exact hfresh z' hz' hz'eq

#print axioms hnoRef_of_refsInList

/-- **`RefsInList` is preserved by an accurate apply.**  Old ops keep their references (monotone under
append); the new op `z`, being `accurate` at the prefix fold `s`, references only ids live in `s`
(`ref_live_of_accurate`), which are therefore inserted in `F` (`hlive_ins` — supplied at the call site
by `insertedIn_of_contains_fold` when `s = applySeqR init_st F`), i.e. timestamps of `Ins` ops in `F`.
This is the `apply` step of the `RefsInList` reachability invariant. -/
theorem refsInList_append_of_accurate (F : List op_t) (z : op_t) (s : concrete_st)
    (href : RefsInList F) (hacc : accurate z s)
    (hlive_ins : ∀ c, c ≠ 0 → contains s c = true → ∃ r e p a, (c, r, .Ins e p a) ∈ F) :
    RefsInList (F ++ [z]) := by
  intro w hw c hc
  rcases List.mem_append.mp hw with hwF | hwz
  · rcases href w hwF c hc with h0 | ⟨z', hz', hz'eq⟩
    · exact Or.inl h0
    · exact Or.inr ⟨z', List.mem_append.mpr (Or.inl hz'), hz'eq⟩
  · simp only [List.mem_singleton] at hwz
    subst hwz
    by_cases hc0 : c = 0
    · exact Or.inl hc0
    · have hlive := ref_live_of_accurate w s c hacc hc hc0
      obtain ⟨r, e, p, a, hin⟩ := hlive_ins c hc0 hlive
      exact Or.inr ⟨(c, r, .Ins e p a), List.mem_append.mpr (Or.inl hin), rfl⟩

#print axioms refsInList_append_of_accurate

/-- **`RefsInList` depends only on membership.**  Transfer across any two lists with the same members
— in particular, `RefsInList` is invariant under permutation.  Needed to move from a structural union
`F ++ G` to the merge's actual `loOnEq`-interleave enumeration (same event set). -/
theorem refsInList_congr_mem (F G : List op_t)
    (hmem : ∀ z, z ∈ F ↔ z ∈ G) (hF : RefsInList F) : RefsInList G := by
  intro z hz c hc
  rcases hF z ((hmem z).mpr hz) c hc with h0 | ⟨z', hz', hz'eq⟩
  · exact Or.inl h0
  · exact Or.inr ⟨z', (hmem z').mp hz', hz'eq⟩

/-- **`RefsInList` is closed under union.**  Both branches' references resolve within their own branch,
hence within the union.  The `merge` step of the `RefsInList` reachability invariant (combine with
`refsInList_congr_mem` for the actual interleaved enumeration). -/
theorem refsInList_of_append (F G : List op_t)
    (hF : RefsInList F) (hG : RefsInList G) : RefsInList (F ++ G) := by
  intro z hz c hc
  rcases List.mem_append.mp hz with hzF | hzG
  · rcases hF z hzF c hc with h0 | ⟨z', hz', hz'eq⟩
    · exact Or.inl h0
    · exact Or.inr ⟨z', List.mem_append.mpr (Or.inl hz'), hz'eq⟩
  · rcases hG z hzG c hc with h0 | ⟨z', hz', hz'eq⟩
    · exact Or.inl h0
    · exact Or.inr ⟨z', List.mem_append.mpr (Or.inr hz'), hz'eq⟩

/-- The empty history vacuously satisfies `RefsInList` — the `init`/`createReplica` base case. -/
theorem refsInList_nil : RefsInList [] := by
  intro z hz; simp at hz

#print axioms refsInList_congr_mem
#print axioms refsInList_of_append
#print axioms refsInList_nil

end Sal.ConditionedMRDTs.RGACanonStepFromFacts
