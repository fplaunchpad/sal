import Sal.ConditionedMRDTs.Framework.MRDTSig

/-!
# The replicated data store, as operational semantics

The version-DAG store of the Neem paper (arXiv:2502.19967 `lin.tex` §3.1,
Fig. `sem` "Semantics of the replicated datastore"), encoded as an inductive
step relation. This is the setting the paper's Theorem 1 / Theorem 2 quantify
over, and the setting the defeater execution lives in
(`Sal/Operational_Semantics/Defeater_Store_Execution.lean`).

## Why this file exists

`Sal/ConditionedMRDTs/Framework/Base/CRDT_TS.lean` is the *binary* store: per-replica states, no
version graph, no LCA (see its header). The paper's `merge` is **ternary**, and
its third argument is the state of the **LCA of the two versions being merged**
— an object that only exists in a version DAG. So the LCA-legality of an
execution (`L(v_⊤) = L(v₁) ∩ L(v₂)`, the paper's Lemma `LCA`) is not even
expressible in the binary TS. This file supplies the missing layer.

## The configuration

A configuration is the paper's 5-tuple `⟨N, H, L, G, vis⟩` (`lin.tex:57-77`):

| field | paper | here |
|---|---|---|
| `N` | `Version ⇀ Σ` | `Version → Option D.State` |
| `H` | `R ⇀ Version` | `Replica → Option Version` |
| `L` | `Version ⇀ ℙ(E)` | `Version → Option (Set (Op D.AppOp))` |
| `G` | `(dom(N), E)` | `E : Version → Version → Prop` |
| `vis` | `⊆ E × E` | `Op → Op → Prop` |

The version graph's vertex set is *defined* by the paper to be `dom(N)`
(`G = (dom(N), E)`), so it is derived here (`Config.Vertices`) rather than
stored; only the edge relation is a field. Every transition rule of Fig. `sem`
sets `G' = (dom(N'), E ∪ {…})`, so this loses nothing.

## The transition rules

`Step` has exactly one constructor per rule of Fig. `sem`, carrying that rule's
premises as hypotheses and its conclusion as an explicit record. Each is
mirrored by a *smart constructor* (`stepCB`, `stepApply`, `stepMerge`) that
computes the successor configuration, so a concrete execution is a term and its
equational premises hold by `rfl`.

Nothing here is specialized to any MRDT: the file is parametric in
`MRDTSig`, whose `mergeL l a b` is the paper's `merge(σ_⊤, σ₁, σ₂)`.
-/

namespace Sal.ConditionedMRDTs.Store

open Sal.Emulation
open Sal.ConditionedMRDTs

/-- Versions. `Nat` by the repo's convention for identifiers. -/
abbrev Version : Type := Nat

/-- Partial-map update, the paper's `f[a ↦ b]`. -/
def pupd {α β : Type} [DecidableEq α] (f : α → Option β) (a : α) (b : β) :
    α → Option β :=
  fun x => if x = a then some b else f x

@[simp] theorem pupd_self {α β : Type} [DecidableEq α] (f : α → Option β)
    (a : α) (b : β) : pupd f a b a = some b := by
  simp [pupd]

@[simp] theorem pupd_ne {α β : Type} [DecidableEq α] (f : α → Option β)
    {a x : α} (b : β) (h : x ≠ a) : pupd f a b x = f x := by
  simp [pupd, h]

/-! ## §1. Configurations -/

/-- A configuration of the store: the paper's `⟨N, H, L, G, vis⟩`
(`lin.tex:57-77`). The version graph's vertex set is `dom(N)` by the paper's
own definition, hence derived (`Vertices`) rather than stored. -/
structure Config (D : MRDTSig) where
  /-- `N : Version ⇀ Σ`, versions to states. -/
  N : Version → Option D.State
  /-- `H : R ⇀ Version`, replicas to head versions. A replica is *active* iff
  it is in `dom(H)`. -/
  H : Replica → Option Version
  /-- `L : Version ⇀ ℙ(E)`, the events that produced a version. -/
  L : Version → Option (Set (Op D.AppOp))
  /-- The version graph's edge relation; `G = (dom(N), E)`. -/
  E : Version → Version → Prop
  /-- Visibility over events. -/
  vis : Op D.AppOp → Op D.AppOp → Prop

namespace Config

variable {D : MRDTSig}

/-- `dom(N)` — the vertex set of the version graph `G`. -/
def Vertices (C : Config D) (v : Version) : Prop := (C.N v).isSome

/-- `E*`: `v` is a causal ancestor of `w` (`lin.tex:150-152`,
"`v₁` is a causal ancestor of `v₂` iff `(v₁,v₂) ∈ E*`"). -/
def Anc (C : Config D) : Version → Version → Prop :=
  Relation.ReflTransGen C.E

/-- `E_C = ⋃ range(L)` — every event present anywhere in the configuration
(`lin.tex:245-246`). -/
def Events (C : Config D) (e : Op D.AppOp) : Prop :=
  ∃ v s, C.L v = some s ∧ e ∈ s

theorem Anc.refl (C : Config D) (v : Version) : C.Anc v v :=
  Relation.ReflTransGen.refl

theorem Anc.of_edge {C : Config D} {v w : Version} (h : C.E v w) : C.Anc v w :=
  Relation.ReflTransGen.single h

theorem Anc.trans {C : Config D} {u v w : Version}
    (h₁ : C.Anc u v) (h₂ : C.Anc v w) : C.Anc u w :=
  Relation.ReflTransGen.trans h₁ h₂

/-- Ancestry is monotone in the edge relation: a *negative* ancestry fact
proved in a later (bigger) graph transports back to every earlier one. This is
what makes the LCA side conditions of a long execution cheap — see the
defeater file. -/
theorem Anc.mono {C C' : Config D} (h : ∀ x y, C.E x y → C'.E x y)
    {v w : Version} (hvw : C.Anc v w) : C'.Anc v w :=
  Relation.ReflTransGen.mono h hvw

end Config

/-- **LCA** (`lin.tex` Definition, `:161-168`). `v_⊤` is the lowest common
ancestor of `v₁` and `v₂` when (i) it is a common ancestor and (ii) every
common ancestor in the graph reaches it. -/
def IsLCA {D : MRDTSig} (C : Config D) (vt v₁ v₂ : Version) : Prop :=
  C.Anc vt v₁ ∧ C.Anc vt v₂ ∧
    ∀ v, C.Vertices v → C.Anc v v₁ → C.Anc v v₂ → C.Anc v vt

/-- The initial configuration `C₀ = ⟨N₀, H₀, L₀, G₀, ∅⟩` (`lin.tex:127-138`):
one replica `r₀` whose head is `v₀`, at state `σ₀`, having seen nothing. -/
def initConfig (D : MRDTSig) (r₀ : Replica) (v₀ : Version) : Config D where
  N := fun v => if v = v₀ then some D.init else none
  H := fun r => if r = r₀ then some v₀ else none
  L := fun v => if v = v₀ then some (∅ : Set (Op D.AppOp)) else none
  E := fun _ _ => False
  vis := fun _ _ => False

/-! ## §2. Transition labels and the step relation -/

/-- Transition labels, one per rule of Fig. `sem`. The paper notes that "the
label of a transition corresponds to its type", and that `Query`'s return value
is carried on the label. -/
inductive Label (D : MRDTSig) : Type where
  /-- `createBranch(r', r)`: fork `r'` off `r`. -/
  | createBranch (r' r : Replica) : Label D
  /-- `apply(t, r, o)`: apply `o` at `r` with fresh timestamp `t`. -/
  | apply (t : Timestamp) (r : Replica) (o : D.AppOp) : Label D
  /-- `merge(r₁, r₂)`: merge `r₂`'s head into `r₁`. -/
  | merge (r₁ r₂ : Replica) : Label D
  /-- `query(r, q, a)`: observe `r` at `q`, returning `a`. -/
  | query (r : Replica) (q : D.Query) (a : D.Value) : Label D

/-- **The semantics of the replicated datastore** (Fig. `sem`), one constructor
per rule. Each constructor's hypotheses are exactly that rule's premises; its
conclusion names the primed configuration explicitly. -/
inductive Step (D : MRDTSig) : Config D → Label D → Config D → Prop where
  /-- `[CreateBranch]`. Premises: `r ∈ dom(H)`, `r' ∉ dom(H)`, `v ∉ dom(N)`.
  Effects: `N' = N[v ↦ N(H(r))]`, `H' = H[r' ↦ v]`, `L' = L[v ↦ L(H(r))]`,
  `E' = E ∪ {(H(r), v)}`, `vis' = vis`. -/
  | createBranch {C : Config D} {r r' : Replica} {v vr : Version}
      {σ : D.State} {Lr : Set (Op D.AppOp)}
      (hHr : C.H r = some vr) (hHr' : C.H r' = none) (hv : C.N v = none)
      (hN : C.N vr = some σ) (hL : C.L vr = some Lr) :
      Step D C (.createBranch r' r)
        ⟨pupd C.N v σ, pupd C.H r' v, pupd C.L v Lr,
         fun x y => C.E x y ∨ (x = vr ∧ y = v), C.vis⟩
  /-- `[Apply]`. Premises: the event is `e = (t, r, o)`, its timestamp is
  globally fresh (`∀ e' ∈ ⋃ range(L). time(e') ≠ t`), `r ∈ dom(H)`,
  `v ∉ dom(N)`. Effects: `N' = N[v ↦ do(N(H(r)), e)]`, `H' = H[r ↦ v]`,
  `L' = L[v ↦ L(H(r)) ∪ {e}]`, `E' = E ∪ {(H(r), v)}`,
  `vis' = vis ∪ (L(H(r)) × {e})`. -/
  | apply {C : Config D} {t : Timestamp} {r : Replica} {o : D.AppOp}
      {v vr : Version} {σ : D.State} {Lr : Set (Op D.AppOp)}
      (hfresh : ∀ e, C.Events e → Op.time e ≠ t)
      (hHr : C.H r = some vr) (hv : C.N v = none)
      (hN : C.N vr = some σ) (hL : C.L vr = some Lr) :
      Step D C (.apply t r o)
        ⟨pupd C.N v (D.update σ (t, r, o)), pupd C.H r v,
         pupd C.L v (Lr ∪ {(t, r, o)}),
         fun x y => C.E x y ∨ (x = vr ∧ y = v),
         fun x y => C.vis x y ∨ (x ∈ Lr ∧ y = (t, r, o))⟩
  /-- `[Merge]`. Premises: `r₁, r₂ ∈ dom(H)`, `v ∉ dom(N)`, and
  `v_⊤ = LCA(H(r₁), H(r₂))`. Effects:
  `N' = N[v ↦ merge(N(v_⊤), N(H(r₁)), N(H(r₂)))]`, `H' = H[r₁ ↦ v]`,
  `L' = L[v ↦ L(H(r₁)) ∪ L(H(r₂))]`,
  `E' = E ∪ {(H(r₁), v), (H(r₂), v)}`, `vis' = vis`. -/
  | merge {C : Config D} {r₁ r₂ : Replica} {v v₁ v₂ vt : Version}
      {l a b : D.State} {L₁ L₂ : Set (Op D.AppOp)}
      (hH₁ : C.H r₁ = some v₁) (hH₂ : C.H r₂ = some v₂)
      (hv : C.N v = none) (hlca : IsLCA C vt v₁ v₂)
      (hNt : C.N vt = some l) (hN₁ : C.N v₁ = some a) (hN₂ : C.N v₂ = some b)
      (hL₁ : C.L v₁ = some L₁) (hL₂ : C.L v₂ = some L₂) :
      Step D C (.merge r₁ r₂)
        ⟨pupd C.N v (D.mergeL l a b), pupd C.H r₁ v, pupd C.L v (L₁ ∪ L₂),
         fun x y => C.E x y ∨ ((x = v₁ ∨ x = v₂) ∧ y = v), C.vis⟩
  /-- `[Query]`. Premises: `r ∈ dom(H)`, `a = query(N(H(r)), q)`. The
  configuration is unchanged; the answer rides on the label. -/
  | query {C : Config D} {r : Replica} {q : D.Query} {v : Version}
      {σ : D.State}
      (hHr : C.H r = some v) (hN : C.N v = some σ) :
      Step D C (.query r q (D.query σ q)) C

/-! ## §3. Executions

An execution is a finite sequence of transitions `C₀ →t₁ C₁ → … →tₙ Cₙ`
(`lin.tex:139-142`). `Exec` records the label list; `Reachable` forgets it. -/

/-- `Exec D C ℓs C'`: there is an execution from `C` to `C'` with labels `ℓs`. -/
inductive Exec (D : MRDTSig) : Config D → List (Label D) → Config D → Prop where
  | nil (C : Config D) : Exec D C [] C
  | cons {C C' C'' : Config D} {ℓ : Label D} {ℓs : List (Label D)} :
      Step D C ℓ C' → Exec D C' ℓs C'' → Exec D C (ℓ :: ℓs) C''

/-- Reachability, forgetting the labels. -/
def Reachable (D : MRDTSig) (C C' : Config D) : Prop := ∃ ℓs, Exec D C ℓs C'

theorem Exec.trans {D : MRDTSig} {C C' C'' : Config D} {ℓs ℓs' : List (Label D)}
    (h : Exec D C ℓs C') (h' : Exec D C' ℓs' C'') :
    Exec D C (ℓs ++ ℓs') C'' := by
  induction h with
  | nil => simpa using h'
  | cons hstep hrest ih => exact .cons hstep (ih h')

/-- A configuration reachable from `C₀` is a configuration *of the store*: the
object the paper's Def. `lin` and Theorems 1/2 quantify over. -/
def ReachableFromInit (D : MRDTSig) (r₀ : Replica) (v₀ : Version)
    (C : Config D) : Prop := Reachable D (initConfig D r₀ v₀) C

/-! ## §4. Smart constructors

Each returns the successor configuration named by the matching `Step`
constructor, so a concrete execution is a *term* and every equational premise
of Fig. `sem` holds by `rfl`. Only the genuine side conditions (freshness,
activeness, freshness of the version, and the LCA premise) remain to prove. -/

variable {D : MRDTSig}

/-- The `[CreateBranch]` successor. -/
def stepCB (C : Config D) (r' : Replica) (v vr : Version) (σ : D.State)
    (Lr : Set (Op D.AppOp)) : Config D :=
  ⟨pupd C.N v σ, pupd C.H r' v, pupd C.L v Lr,
   fun x y => C.E x y ∨ (x = vr ∧ y = v), C.vis⟩

/-- The `[Apply]` successor. -/
def stepApply (C : Config D) (t : Timestamp) (r : Replica) (o : D.AppOp)
    (v vr : Version) (σ : D.State) (Lr : Set (Op D.AppOp)) : Config D :=
  ⟨pupd C.N v (D.update σ (t, r, o)), pupd C.H r v,
   pupd C.L v (Lr ∪ {(t, r, o)}),
   fun x y => C.E x y ∨ (x = vr ∧ y = v),
   fun x y => C.vis x y ∨ (x ∈ Lr ∧ y = (t, r, o))⟩

/-- The `[Merge]` successor. -/
def stepMerge (C : Config D) (r₁ : Replica) (v v₁ v₂ : Version)
    (l a b : D.State) (L₁ L₂ : Set (Op D.AppOp)) : Config D :=
  ⟨pupd C.N v (D.mergeL l a b), pupd C.H r₁ v, pupd C.L v (L₁ ∪ L₂),
   fun x y => C.E x y ∨ ((x = v₁ ∨ x = v₂) ∧ y = v), C.vis⟩

theorem step_cb {C : Config D} {r r' : Replica} {v vr : Version} {σ : D.State}
    {Lr : Set (Op D.AppOp)}
    (hHr : C.H r = some vr) (hHr' : C.H r' = none) (hv : C.N v = none)
    (hN : C.N vr = some σ) (hL : C.L vr = some Lr) :
    Step D C (.createBranch r' r) (stepCB C r' v vr σ Lr) :=
  Step.createBranch hHr hHr' hv hN hL

theorem step_apply {C : Config D} {t : Timestamp} {r : Replica} {o : D.AppOp}
    {v vr : Version} {σ : D.State} {Lr : Set (Op D.AppOp)}
    (hfresh : ∀ e, C.Events e → Op.time e ≠ t)
    (hHr : C.H r = some vr) (hv : C.N v = none)
    (hN : C.N vr = some σ) (hL : C.L vr = some Lr) :
    Step D C (.apply t r o) (stepApply C t r o v vr σ Lr) :=
  Step.apply hfresh hHr hv hN hL

theorem step_merge {C : Config D} {r₁ r₂ : Replica} {v v₁ v₂ vt : Version}
    {l a b : D.State} {L₁ L₂ : Set (Op D.AppOp)}
    (hH₁ : C.H r₁ = some v₁) (hH₂ : C.H r₂ = some v₂)
    (hv : C.N v = none) (hlca : IsLCA C vt v₁ v₂)
    (hNt : C.N vt = some l) (hN₁ : C.N v₁ = some a) (hN₂ : C.N v₂ = some b)
    (hL₁ : C.L v₁ = some L₁) (hL₂ : C.L v₂ = some L₂) :
    Step D C (.merge r₁ r₂) (stepMerge C r₁ v v₁ v₂ l a b L₁ L₂) :=
  Step.merge hH₁ hH₂ hv hlca hNt hN₁ hN₂ hL₁ hL₂

/-! ### How the event set grows

One lemma per rule: a transition adds only the events it names, so the event
set of a configuration is read off the trace without ever enumerating `dom(L)`.
These are what discharge the `[Apply]` rule's timestamp-freshness premise. -/

theorem events_stepCB {C : Config D} {r' : Replica} {v vr : Version}
    {σ : D.State} {Lr : Set (Op D.AppOp)} {e : Op D.AppOp}
    (h : (stepCB C r' v vr σ Lr).Events e) : e ∈ Lr ∨ C.Events e := by
  obtain ⟨w, s, hs, hes⟩ := h
  by_cases hw : w = v
  · subst hw
    rw [show (stepCB C r' w vr σ Lr).L w = some Lr from pupd_self _ _ _] at hs
    cases hs; exact Or.inl hes
  · refine Or.inr ⟨w, s, ?_, hes⟩
    rwa [show (stepCB C r' v vr σ Lr).L w = C.L w from pupd_ne _ _ hw] at hs

theorem events_stepApply {C : Config D} {t : Timestamp} {r : Replica}
    {o : D.AppOp} {v vr : Version} {σ : D.State} {Lr : Set (Op D.AppOp)}
    {e : Op D.AppOp} (h : (stepApply C t r o v vr σ Lr).Events e) :
    e ∈ Lr ∨ e = (t, r, o) ∨ C.Events e := by
  obtain ⟨w, s, hs, hes⟩ := h
  by_cases hw : w = v
  · subst hw
    rw [show (stepApply C t r o w vr σ Lr).L w = some (Lr ∪ {(t, r, o)}) from
      pupd_self _ _ _] at hs
    cases hs
    rcases hes with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · refine Or.inr (Or.inr ⟨w, s, ?_, hes⟩)
    rwa [show (stepApply C t r o v vr σ Lr).L w = C.L w from
      pupd_ne _ _ hw] at hs

theorem events_stepMerge {C : Config D} {r₁ : Replica} {v v₁ v₂ : Version}
    {l a b : D.State} {L₁ L₂ : Set (Op D.AppOp)} {e : Op D.AppOp}
    (h : (stepMerge C r₁ v v₁ v₂ l a b L₁ L₂).Events e) :
    e ∈ L₁ ∨ e ∈ L₂ ∨ C.Events e := by
  obtain ⟨w, s, hs, hes⟩ := h
  by_cases hw : w = v
  · subst hw
    rw [show (stepMerge C r₁ w v₁ v₂ l a b L₁ L₂).L w = some (L₁ ∪ L₂) from
      pupd_self _ _ _] at hs
    cases hs
    rcases hes with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · refine Or.inr (Or.inr ⟨w, s, ?_, hes⟩)
    rwa [show (stepMerge C r₁ v v₁ v₂ l a b L₁ L₂).L w = C.L w from
      pupd_ne _ _ hw] at hs

/-- The initial configuration has no events. -/
theorem events_initConfig {r₀ v₀ : Version} {e : Op D.AppOp}
    (h : (initConfig D r₀ v₀).Events e) : False := by
  obtain ⟨w, s, hs, hes⟩ := h
  by_cases hw : w = v₀
  · subst hw
    simp only [initConfig] at hs
    cases hs; exact hes
  · simp only [initConfig, if_neg hw] at hs
    cases hs

/-! ## §5. LCA-legality

The paper's Lemma `LCA` (`lin.tex:158-161`) states that in any reachable
configuration, `L(v_⊤) = L(v₁) ∩ L(v₂)`. We do not re-prove it here (its
published proof has a separate gap, mechanized in
`Metatheory/LCA_Lemma.lean`); we *name* the property, so a concrete execution
can be checked against it. -/

/-- `L(v_⊤) = L(v₁) ∩ L(v₂)` at a particular merge: the property the paper's
Lemma `LCA` asserts for every reachable configuration. An execution
satisfying it at a merge is what the defeater file calls *LCA-legal*. -/
def LCALegal (C : Config D) (vt v₁ v₂ : Version) : Prop :=
  ∀ Lt L₁ L₂, C.L vt = some Lt → C.L v₁ = some L₁ → C.L v₂ = some L₂ →
    Lt = L₁ ∩ L₂

end Sal.ConditionedMRDTs.Store
