/-!
# Kill-test: a metadata-free LWW register admits no three-way merge

The boundary behind the `rc`-expressiveness question (Open Question
`oq:rcchain` of the note): whatever a linearization order arbitrates, the
converged outcome must eventually be produced by `mergeL(l, a, b)` — a
function of **three states and nothing else**. For a last-writer-wins
register whose state is the plain value (no stored timestamp), no such
function exists: two executions can present identical state triples while
the timestamp order — hence the correct merge — differs.

Concretely: the LCA holds `w(1, x)`; branch A additionally `w(ta, y)`,
branch B additionally `w(tb, z)`. The states are `(x, y, z)` either way,
but with `ta < tb` the canonical merged value is `z`, and with `tb < ta`
it is `y`.

Consequence: LWW's timestamp is forced into the state by the *merge*, not
by the replay order — so a chain-tolerant `rc` (however the metatheorem's
VC set is generalized) cannot yield a metadata-free LWW. The `rc`
mechanism's honest scope is arbitration whose outcome is recoverable from
the branch states.

Self-contained; no framework imports; kernel-checked by `decide`-free
elementary reasoning.
-/

namespace Sal.ConditionedMRDTs.LWWMergeNeedsTimestamps

/-- Events of a last-writer-wins register: `(timestamp, value)`. -/
abbrev LWWEvent : Type := Nat × Nat

/-- The canonical (converged) value of a finite history: the value of the
timestamp-maximal write, computed as a left fold — replay order is
irrelevant for the *specification*, which is what makes plain-value LWW a
coherent semantics to ask for. -/
def canon (init : Nat) (es : List LWWEvent) : Nat :=
  (es.foldl (fun acc e => if acc.1 ≤ e.1 then e else acc) (0, init)).2

/-- **No plain-value three-way merge realizes LWW.** Any candidate
`m : value → value → value → value` that maps the LCA/branch canonical
*values* to the union's canonical value is refuted by two executions with
identical value triples and opposite timestamp orders. -/
theorem lww_merge_needs_timestamps :
    ¬ ∃ m : Nat → Nat → Nat → Nat,
      ∀ (init : Nat) (L Δa Δb : List LWWEvent),
        m (canon init L) (canon init (L ++ Δa)) (canon init (L ++ Δb))
          = canon init (L ++ Δa ++ Δb) := by
  rintro ⟨m, hm⟩
  -- Execution 1: A's write at time 2, B's at time 3 — B wins.
  have h1 := hm 0 [(1, 10)] [(2, 20)] [(3, 30)]
  -- Execution 2: A's write at time 3, B's at time 2 — A wins.
  have h2 := hm 0 [(1, 10)] [(3, 20)] [(2, 30)]
  -- Identical state triples in both executions: l = 10, a = 20, b = 30.
  have h1' : m 10 20 30 = 30 := h1
  have h2' : m 10 20 30 = 20 := h2
  omega

#print axioms lww_merge_needs_timestamps

end Sal.ConditionedMRDTs.LWWMergeNeedsTimestamps
