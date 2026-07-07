import Sal.ConditionedMRDTs.MRDT_Instances.RGA_TombstoneFree.RGA_SubchainResolve
import Sal.ConditionedMRDTs.Development.RGA_EnablementBase

/-!
# From the Key Lemma to per-event faithfulness in a reachable RGA fold

`RecPathFaithful a s` packages the Key Lemma's hypotheses for the event `a` at
the state `s`: there is a capture state `s0` (a's birth) where `a`'s recorded
path `recPath a` was the genuine live ancestor chain of its target
(`IsAncPath`), the target was live, the root sentinel unstored, and `s` is
reachable from `s0` by `okStep`-conditioned `do_` steps (`Reach`).

* Base: an event generated `accurate` (M1's `HistFaithful`) on a root-free
  state with a genuine (nonzero) target is `RecPathFaithful` at its birth.
* Preservation: each `okStep` (fresh `Ins` with no id-reuse in the recorded
  path; `accurate` `Del` sparing the target) extends the `Reach` witness.
* Payoff: `resolve s (recPath a) = anc s (target a)` (directly
  `subchain_resolve`), and hence `Faithful a s` (the GeneralSwap predicate).

HONESTY (what a real fold must supply, discharged by the execution model, not
here): an `Ins`'s freshness/no-reuse comes from monotone allocation
(`mono_alloc`); a concurrent `Del` whose target IS `target a` violates
`okStep` — after it, `a` is *staled* and this file's invariant genuinely does
not apply (that regime is the ChainFaithful-threading story, not this one).
The root-degenerate events excluded by `target a ≠ 0` are covered separately:
a root-anchored `Ins` is `Faithful` on any root-free state
(`faithful_ins_root`); the degenerate `Del [] 0` is *never* `Faithful` (its
`x ≠ 0` conjunct fails by definition), so no bridge exists or is needed.
-/

set_option maxHeartbeats 1000000

open Sal.ConditionedMRDTs.RGAGeneralSwap (Faithful ClimbFaithful DelTargetFaithful)
open Sal.ConditionedMRDTs.RGABubbleWiring (recList)
open RGAEnablementBase (HistFaithful)

namespace RGARecPathFaithful

/-- The node/anchor an event acts on (its recorded leaf). -/
def target (o : op_t) : ℕ := opLeaf o.2.2

/-- The recorded ancestor path of the target (the tail of `recList`). -/
def recPath (o : op_t) : List ℕ := opPath o.2.2

/-- `recList` is the target followed by its recorded path. -/
theorem recList_eq_target_recPath (a : op_t) :
    recList a = target a :: recPath a := by
  obtain ⟨t, r, op⟩ := a
  cases op <;> rfl

/-- **`RecPathFaithful a s`** — the Key Lemma's hypotheses hold for `a` at
`s`: a capture state `s0` (a's birth) with the root unstored, `a`'s target
live, `recPath a` the genuine chain of the target, and `s` reachable from
`s0` by `okStep`-conditioned steps. -/
def RecPathFaithful (a : op_t) (s : concrete_st) : Prop :=
  ∃ s0 : concrete_st,
    contains s0 0 = false ∧
    contains s0 (target a) = true ∧
    IsAncPath s0 (target a) (recPath a) ∧
    Reach (target a) (recPath a) s0 s

/-- **Base.** An event generated `accurate` on a root-free state, with a
genuine (nonzero) target, is `RecPathFaithful` at its birth: `accurate`'s
non-degenerate branch is literally the capture data, and `Reach.refl` starts
the walk. -/
theorem recPathFaithful_of_accurate (a : op_t) (s0 : concrete_st)
    (h0 : contains s0 0 = false) (hacc : accurate a s0)
    (htgt : target a ≠ 0) : RecPathFaithful a s0 := by
  rcases hacc with ⟨hl0, _⟩ | ⟨hlive, hpath⟩
  · exact absurd hl0 htgt
  · exact ⟨s0, h0, hlive, hpath, Reach.refl⟩

/-- The base through M1's `HistFaithful` (definitionally `accurate`). -/
theorem recPathFaithful_of_histFaithful (a : op_t) (s0 : concrete_st)
    (h0 : contains s0 0 = false) (hHist : HistFaithful s0 a)
    (htgt : target a ≠ 0) : RecPathFaithful a s0 :=
  recPathFaithful_of_accurate a s0 h0 hHist htgt

/-- **Preservation.** An `okStep` for `a`'s target/path — a fresh `Ins` whose
id is not reused from `recPath a`, or an `accurate` `Del` sparing `target a`
— extends the `Reach` witness by one step. -/
theorem recPathFaithful_step (a : op_t) (s : concrete_st) (o : op_t)
    (h : RecPathFaithful a s) (hok : okStep (target a) (recPath a) s o) :
    RecPathFaithful a (do_ s o) := by
  obtain ⟨s0, h0, hx, hpath, hreach⟩ := h
  exact ⟨s0, h0, hx, hpath, Reach.step o hreach hok⟩

/-- **Payoff, resolve form (directly the Key Lemma).** At any state where
`RecPathFaithful a` holds, `a`'s recorded path resolves to the target's
current stored anchor. -/
theorem resolve_recPath_of_recPathFaithful (a : op_t) (s : concrete_st)
    (h : RecPathFaithful a s) :
    resolve s (recPath a) = anc s (target a) := by
  obtain ⟨s0, h0, hx, hpath, hreach⟩ := h
  exact subchain_resolve (target a) (recPath a) s0 s h0 hx hpath hreach

/-- The target is still live (companion, from `subchain_live`). -/
theorem target_live_of_recPathFaithful (a : op_t) (s : concrete_st)
    (h : RecPathFaithful a s) : contains s (target a) = true := by
  obtain ⟨s0, h0, hx, hpath, hreach⟩ := h
  exact subchain_live (target a) (recPath a) s0 s h0 hx hpath hreach

/-- On `recList` itself: the recorded list resolves to the (live) target. -/
theorem resolve_recList_of_recPathFaithful (a : op_t) (s : concrete_st)
    (h : RecPathFaithful a s) : resolve s (recList a) = target a := by
  rw [recList_eq_target_recPath]
  exact resolve_live_head s (target a) (recPath a)
    (target_live_of_recPathFaithful a s h)

/-! ## Bridge to the GeneralSwap `Faithful` predicate

`Faithful` consumes `ClimbFaithful` on the recorded list (Ins) or on the path
plus `DelTargetFaithful` and target-genuineness (Del). All of it falls out of
the Key Lemma's inductive invariant `LiveChain`, which we first export. -/

/-- The full invariant at `s`: the live sublist of `recPath a` is the genuine
current chain of `target a` (the same induction as `subchain_resolve`). -/
theorem recPathFaithful_liveChain (a : op_t) (s : concrete_st)
    (h : RecPathFaithful a s) : LiveChain s (target a) (recPath a) := by
  obtain ⟨s0, h0, hx, hpath, hreach⟩ := h
  induction hreach with
  | refl => exact liveChain_capture s0 (target a) (recPath a) h0 hx hpath
  | @step s' o hr hok ih => exact liveChain_step s' (target a) (recPath a) o ih hok

/-- Filtering a fixed id commutes with restricting to the live sublist. -/
theorem liveSub_filter_comm (s : concrete_st) (pre : List ℕ) (y : ℕ) :
    liveSub s (pre.filter (fun c => c != y))
      = (liveSub s pre).filter (fun c => c != y) := by
  unfold liveSub
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro c _
  exact Bool.and_comm _ _

/-- `resolve` of a filtered list may be computed on the live sublist. -/
theorem resolve_filter_liveSub (s : concrete_st) (pre : List ℕ) (y : ℕ) :
    resolve s (pre.filter (fun c => c != y))
      = resolve s ((liveSub s pre).filter (fun c => c != y)) := by
  rw [← resolve_liveSub s (pre.filter (fun c => c != y)), liveSub_filter_comm]

/-- `LiveChain` gives `ClimbFaithful` of the leaf-headed list (the Ins shape):
the climb target is the live leaf `x`, and dropping `x` re-resolves along the
genuine live chain to `anc s x` (`isancpath_resolve_self_filter`). -/
theorem climbFaithful_ins_of_liveChain (s : concrete_st) (x : ℕ) (pre : List ℕ)
    (h : LiveChain s x pre) : ClimbFaithful s (x :: pre) := by
  obtain ⟨h0, hx, hpath⟩ := h
  unfold ClimbFaithful
  rw [resolve_live_head s x pre hx]
  intro _
  have hfc : (x :: pre).filter (fun c => c != x) = pre.filter (fun c => c != x) := by
    rw [List.filter_cons]; simp
  rw [hfc, resolve_filter_liveSub s pre x]
  exact isancpath_resolve_self_filter s x (liveSub s pre) hpath

/-- `LiveChain` gives `ClimbFaithful` of the bare path (the Del shape): the
path's climb target is `anc s x` — the head `c` of the live sublist — and
dropping `c` re-resolves along the live chain to `anc s c`. -/
theorem climbFaithful_path_of_liveChain (s : concrete_st) (x : ℕ) (pre : List ℕ)
    (h : LiveChain s x pre) : ClimbFaithful s pre := by
  have hres : resolve s pre = anc s x := liveChain_resolve s x pre h
  obtain ⟨h0, hx, hpath⟩ := h
  unfold ClimbFaithful
  rw [hres]
  intro hlive
  cases hls : liveSub s pre with
  | nil =>
    rw [hls] at hpath
    simp only [IsAncPath] at hpath
    rw [hpath, h0] at hlive
    exact Bool.noConfusion hlive
  | cons c rest =>
    rw [hls] at hpath
    simp only [IsAncPath] at hpath
    obtain ⟨hancx, _, hrest⟩ := hpath
    rw [hancx, resolve_filter_liveSub s pre c, hls, List.filter_cons]
    simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
    exact isancpath_resolve_self_filter s c rest hrest

/-- **Payoff, `Faithful` form.** A `RecPathFaithful` event is `Faithful` at
`s`. Ins: `ClimbFaithful` of the anchor-headed list. Del: `ClimbFaithful` of
the path, correct rehome target (the Key Lemma), and a genuine target. -/
theorem faithful_of_recPathFaithful (a : op_t) (s : concrete_st)
    (h : RecPathFaithful a s) : Faithful a s := by
  have hlc : LiveChain s (target a) (recPath a) := recPathFaithful_liveChain a s h
  obtain ⟨t, r, op⟩ := a
  cases op with
  | Ins e pre anch =>
    have hlc' : LiveChain s anch pre := hlc
    show ClimbFaithful s (anch :: pre)
    exact climbFaithful_ins_of_liveChain s anch pre hlc'
  | Del pre x =>
    have hlc' : LiveChain s x pre := hlc
    show ClimbFaithful s pre ∧ DelTargetFaithful s pre x ∧ x ≠ 0
    refine ⟨climbFaithful_path_of_liveChain s x pre hlc', ?_, ?_⟩
    · intro _
      exact liveChain_resolve s x pre hlc'
    · exact contains_ne_zero s x hlc'.1 hlc'.2.1

/-- Coverage of the excluded degenerate Ins: a root-anchored `Ins e [] 0` is
`Faithful` on any root-free state outright (its climb premise is vacuous). -/
theorem faithful_ins_root (s : concrete_st) (t r e : ℕ)
    (h0 : contains s 0 = false) : Faithful (t, r, .Ins e [] 0) s := by
  show ClimbFaithful s [0]
  unfold ClimbFaithful
  intro hlive
  have hres : resolve s ([0] : List ℕ) = 0 := by
    simp only [resolve]; split <;> rfl
  rw [hres, h0] at hlive
  exact Bool.noConfusion hlive

/-! ## Axiom audit — kernel-clean, no `sorryAx`, no `native_decide`. -/

#print axioms recPathFaithful_of_accurate
#print axioms recPathFaithful_step
#print axioms resolve_recPath_of_recPathFaithful
#print axioms faithful_of_recPathFaithful

end RGARecPathFaithful
