import Sal.MRDTs.Framework.Signature
import Mathlib.Data.Set.Basic

/-!
# Unconditioned ternary execution

The ranked configuration records only operational coherence.  In particular,
it carries no proof that stored states satisfy a client invariant.
-/

namespace Sal.MRDTs

open Sal.Emulation

abbrev Version : Type := Nat

def Reaches (parents : Version → List Version) : Version → Version → Prop :=
  Relation.ReflTransGen (fun a b => a ∈ parents b)

def IsLCA (parents : Version → List Version) (v₁ v₂ vT : Version) : Prop :=
  Reaches parents vT v₁ ∧ Reaches parents vT v₂ ∧
    ∀ w, Reaches parents w v₁ → Reaches parents w v₂ → Reaches parents w vT

def CommonAnc (parents : Version → List Version) (S : Set Version) (w : Version) :
    Set Version :=
  {x | (∃ u ∈ S, Reaches parents x u) ∧ Reaches parents x w}

def IsMCA (parents : Version → List Version) (S : Set Version) (w m : Version) : Prop :=
  m ∈ CommonAnc parents S w ∧
    ∀ x ∈ CommonAnc parents S w, Reaches parents m x → x = m

theorem parentStep_wf {parents : Version → List Version}
    (h : ∀ v p, p ∈ parents v → p < v) :
    WellFounded (fun a b : Version => a ∈ parents b) := by
  have hsub : Subrelation (fun a b : Version => a ∈ parents b)
      (fun a b : Version => a < b) := by
    intro a b hab
    exact h b a hab
  exact hsub.wf Nat.lt_wfRel.wf

/-- Operational state of the version-DAG semantics.  All fields describe the
shape and coherence of the execution itself; client safety is external. -/
structure Configuration (D : MRDTSig) where
  N : Replica → Option D.State
  L : Replica → Option (Set (Op D.AppOp))
  vis : Op D.AppOp → Op D.AppOp → Prop
  dom_eq : ∀ r, N r = none ↔ L r = none
  vis_src : ∀ {a b}, vis a b → ∃ r s, L r = some s ∧ s a
  vis_tgt : ∀ {a b}, vis a b → ∃ r s, L r = some s ∧ s b
  vis_causal : ∀ {a b r s}, vis a b → L r = some s → s b → s a
  timestamps_distinct :
    ∀ {a b : Op D.AppOp} {r s r' s'},
      L r = some s → s a → L r' = some s' → s' b →
      a ≠ b → a.1 ≠ b.1
  causal_mono : ∀ {a b : Op D.AppOp}, vis a b → a.1 < b.1
  vis_total_same_replica :
    ∀ {a b : Op D.AppOp} {r s r' s'},
      L r = some s → s a → L r' = some s' → s' b →
      a ≠ b → a.2.1 = b.2.1 → vis a b ∨ vis b a
  ver : Version → Option (D.State × Set (Op D.AppOp))
  head : Replica → Option Version
  parents : Version → List Version
  parents_lt : ∀ v p, p ∈ parents v → p < v
  ver_init : ver 0 = some (D.init, ∅)
  head_coherent : ∀ r v, head r = some v →
    (ver v).map Prod.fst = N r ∧ (ver v).map Prod.snd = L r
  lca_events : ∀ {v₁ v₂ vT s₁ e₁ s₂ e₂ sT eT},
    IsLCA parents v₁ v₂ vT →
    ver v₁ = some (s₁, e₁) → ver v₂ = some (s₂, e₂) →
    ver vT = some (sT, eT) → eT = e₁ ∩ e₂

namespace Configuration

variable {D : MRDTSig}

def events (C : Configuration D) : Set (Op D.AppOp) :=
  fun e => ∃ r s, C.L r = some s ∧ s e

def verState (C : Configuration D) (v : Version) : Option D.State :=
  (C.ver v).map Prod.fst

def verEvents (C : Configuration D) (v : Version) : Option (Set (Op D.AppOp)) :=
  (C.ver v).map Prod.snd

/-- Replica-keyed projection consumed by the established binary
linearizability definitions. -/
def core (C : Configuration D) :
    Sal.Emulation.Configuration D.toCRDTSig where
  N := C.N
  L := C.L
  vis := C.vis
  dom_eq := C.dom_eq
  vis_src := C.vis_src
  vis_tgt := C.vis_tgt
  vis_causal := C.vis_causal
  timestamps_distinct := C.timestamps_distinct
  vis_total_same_replica := C.vis_total_same_replica

@[simp] theorem core_events (C : Configuration D) : (core C).events = C.events := rfl

@[simp] theorem core_vis (C : Configuration D) : (core C).vis = C.vis := rfl

theorem parents_wf (C : Configuration D) :
    WellFounded (fun a b : Version => a ∈ C.parents b) :=
  parentStep_wf C.parents_lt

end Configuration

private theorem initVer_decompose {D : MRDTSig}
    {v : Version} {s : D.State} {e : Set (Op D.AppOp)}
    (hv : (if v = 0 then some (D.init, (∅ : Set (Op D.AppOp))) else none) =
      some (s, e)) :
    v = 0 ∧ s = D.init ∧ e = ∅ := by
  by_cases h : v = 0
  · rw [if_pos h, Option.some.injEq, Prod.mk.injEq] at hv
    exact ⟨h, hv.1.symm, hv.2.symm⟩
  · rw [if_neg h] at hv
    simp at hv

/-- Initial configuration.  No invariant witness is required. -/
def initConfig (D : MRDTSig) : Configuration D where
  N := fun r => if r = 0 then some D.init else none
  L := fun r => if r = 0 then some ∅ else none
  vis := fun _ _ => False
  dom_eq := by
    intro r
    by_cases h : r = 0 <;> simp [h]
  vis_src := fun h => absurd h id
  vis_tgt := fun h => absurd h id
  vis_causal := fun h _ _ => absurd h id
  timestamps_distinct := by
    intro a b r s r' s' hLr hsa _ _ _
    by_cases hr : r = 0
    · subst hr
      simp at hLr
      subst hLr
      exact hsa.elim
    · simp [hr] at hLr
  causal_mono := fun h => absurd h id
  vis_total_same_replica := by
    intro a b r s r' s' hLr hsa _ _ _ _
    by_cases hr : r = 0
    · subst hr
      simp at hLr
      subst hLr
      exact hsa.elim
    · simp [hr] at hLr
  ver := fun v => if v = 0 then some (D.init, ∅) else none
  head := fun r => if r = 0 then some 0 else none
  parents := fun _ => []
  parents_lt := by simp
  ver_init := by simp
  head_coherent := by
    intro r v hr
    by_cases hr0 : r = 0
    · subst hr0
      simp at hr
      subst hr
      exact ⟨by simp, by simp⟩
    · simp [hr0] at hr
  lca_events := by
    intro v₁ v₂ vT s₁ e₁ s₂ e₂ sT eT _ hv₁ hv₂ hvT
    have h1 := (initVer_decompose hv₁).2.2
    have h2 := (initVer_decompose hv₂).2.2
    have h3 := (initVer_decompose hvT).2.2
    subst e₁
    subst e₂
    subst eT
    rw [Set.empty_inter]

inductive Label (D : MRDTSig) where
  | createReplica (r : Replica)
  | apply (t : Timestamp) (r : Replica) (o : D.AppOp)
  | merge (r₁ r₂ : Replica)
  | query (r : Replica) (q : D.Query) (v : D.Value)

/-- Raw execution.  Apply deliberately has no client guard. -/
inductive Step (D : MRDTSig) :
    Configuration D → Label D → Configuration D → Prop where
  | createReplica {C : Configuration D} {r : Replica}
      (fresh : C.N r = none) (C' : Configuration D)
      (N : C'.N = updateRep C.N r D.init)
      (L : C'.L = updateRep C.L r ∅)
      (vis : C'.vis = C.vis) (ver : C'.ver = C.ver)
      (head : C'.head = fun r' => if r' = r then some 0 else C.head r')
      (parents : C'.parents = C.parents) :
      Step D C (.createReplica r) C'
  | apply {C : Configuration D} {t : Timestamp} {r : Replica} {o : D.AppOp}
      {v : Version} {s : D.State} {ev : Set (Op D.AppOp)} {vnew : Version}
      (headAt : C.head r = some v) (versionAt : C.ver v = some (s, ev))
      (freshTime : ∀ e', e' ∈ C.events → Op.time e' ≠ t)
      (freshStore : ∀ w sw Ew, C.ver w = some (sw, Ew) →
        ∀ e' ∈ Ew, Op.time e' ≠ t)
      (freshVersion : C.ver vnew = none) (rank : v < vnew)
      (C' : Configuration D)
      (N : C'.N = updateRep C.N r (D.update s (t, r, o)))
      (L : C'.L = updateRep C.L r (ev ∪ {(t, r, o)}))
      (vis : C'.vis = fun a b => C.vis a b ∨ (ev a ∧ b = (t, r, o)))
      (ver : C'.ver = fun w => if w = vnew
        then some (D.update s (t, r, o), ev ∪ {(t, r, o)}) else C.ver w)
      (head : C'.head = fun r' => if r' = r then some vnew else C.head r')
      (parents : C'.parents = fun w => if w = vnew then [v] else C.parents w) :
      Step D C (.apply t r o) C'
  | merge {C : Configuration D} {r₁ r₂ : Replica}
      {v₁ v₂ vT vm : Version} {s₁ s₂ sT : D.State}
      {ev₁ ev₂ evT : Set (Op D.AppOp)}
      (head₁ : C.head r₁ = some v₁) (head₂ : C.head r₂ = some v₂)
      (version₁ : C.ver v₁ = some (s₁, ev₁))
      (version₂ : C.ver v₂ = some (s₂, ev₂))
      (lca : IsLCA C.parents v₁ v₂ vT)
      (versionLCA : C.ver vT = some (sT, evT))
      (freshVersion : C.ver vm = none) (rank₁ : v₁ < vm) (rank₂ : v₂ < vm)
      (C' : Configuration D)
      (N : C'.N = updateRep C.N r₁ (D.mergeL sT s₁ s₂))
      (L : C'.L = updateRep C.L r₁ (ev₁ ∪ ev₂))
      (vis : C'.vis = C.vis)
      (ver : C'.ver = fun w => if w = vm
        then some (D.mergeL sT s₁ s₂, ev₁ ∪ ev₂) else C.ver w)
      (head : C'.head = fun r' => if r' = r₁ then some vm else C.head r')
      (parents : C'.parents = fun w => if w = vm then [v₁, v₂] else C.parents w) :
      Step D C (.merge r₁ r₂) C'
  | query {C : Configuration D} {r : Replica} {q : D.Query}
      {v : D.Value} {s : D.State}
      (stateAt : C.N r = some s) (value : v = D.query s q) :
      Step D C (.query r q v) C

def labeledTS (D : MRDTSig) : LabeledTS where
  State := Configuration D
  Label := Label D
  step := Step D
  silent := fun _ => False

end Sal.MRDTs
