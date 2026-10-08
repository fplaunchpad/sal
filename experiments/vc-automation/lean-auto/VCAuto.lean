import Auto.Tactic
import Duper.Tactic

open Lean Auto in
 def Auto.salDuperRaw (lemmas : Array Lemma) (_inhs : Array Lemma) : MetaM Expr := do
  let lemmas : Array (Expr × Expr × Array Name × Bool) ← lemmas.mapM
    (fun ⟨⟨proof, ty, _⟩, _⟩ => do return (ty, ← Meta.mkAppM ``eq_true #[proof], #[], true))
  Duper.runDuper lemmas.toList [] 0
attribute [rebind Auto.Native.solverFunc] Auto.salDuperRaw
