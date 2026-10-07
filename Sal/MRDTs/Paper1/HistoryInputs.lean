import Sal.MRDTs.Paper1.ProjectedCriterion

/-! History languages may retain complete MRDT event inputs. Relabelling below
changes only the sequential alphabet, not the concrete execution or paper order.
The language and its contextual conflicts remain independently specified. -/
namespace Sal.MRDTs.Paper1
open Foundation

theorem HistorySpec.ext {U Q V : Type} {S T : HistorySpec U Q V}
    (h : S.admits = T.admits) : S = T := by
  cases S
  cases T
  cases h
  rfl

def SeqLabel.mapUpdate {U W Q V : Type} (f : U → W) :
    SeqLabel U Q V → SeqLabel W Q V
  | .update u => .update (f u)
  | .query q v => .query q v

def HistorySpec.withInputs {U W Q V : Type} (S : HistorySpec W Q V)
    (f : U → W) : HistorySpec U Q V where
  admits h := S.admits (h.map (SeqLabel.mapUpdate f))
  empty := S.empty
  prefix_closed pre suf h := S.prefix_closed _ _ (by simpa only [List.map_append] using h)

theorem HistorySpec.withInputs_commutes {U W Q V : Type}
    (S : HistorySpec W Q V) (f : U → W) {a b : U}
    (h : S.Commutes (f a) (f b)) : (S.withInputs f).Commutes a b := by
  intro pre suf
  simpa only [HistorySpec.withInputs, List.map_append, List.map_cons, List.map_nil,
    SeqLabel.mapUpdate] using h (pre.map (SeqLabel.mapUpdate f))
      (suf.map (SeqLabel.mapUpdate f))

private theorem labels_surjective {U W Q V : Type} {f : U → W}
    (hf : Function.Surjective f) :
    Function.Surjective (SeqLabel.mapUpdate (Q := Q) (V := V) f) := by
  intro label
  cases label with
  | update w => obtain ⟨u,rfl⟩ := hf w; exact ⟨.update u,rfl⟩
  | query q v => exact ⟨.query q v,rfl⟩

private theorem histories_surjective {U W Q V : Type} {f : U → W}
    (hf : Function.Surjective f) :
    Function.Surjective (fun h : List (SeqLabel U Q V) => h.map (SeqLabel.mapUpdate f)) := by
  intro h
  induction h with
  | nil => exact ⟨[],rfl⟩
  | cons l ls ih =>
      obtain ⟨u,rfl⟩ := labels_surjective hf l
      obtain ⟨us,rfl⟩ := ih
      exact ⟨u :: us,rfl⟩

/-- Surjective input relabelling preserves contextual conflicts exactly. -/
theorem HistorySpec.withInputs_commutes_iff {U W Q V : Type}
    (S : HistorySpec W Q V) (f : U → W) (hf : Function.Surjective f) (a b : U) :
    (S.withInputs f).Commutes a b ↔ S.Commutes (f a) (f b) := by
  constructor
  · intro h pre suf
    obtain ⟨pre',rfl⟩ := histories_surjective hf pre
    obtain ⟨suf',rfl⟩ := histories_surjective hf suf
    simpa only [HistorySpec.withInputs, List.map_append, List.map_cons, List.map_nil,
      SeqLabel.mapUpdate] using h pre' suf'
  · exact S.withInputs_commutes f

def HistoryMachine.withInputs {U W Q V : Type} (M : HistoryMachine W Q V)
    (f : U → W) : HistoryMachine U Q V where
  State := M.State
  initial := M.initial
  transition s l t := M.transition s (l.mapUpdate f) t

theorem HistoryMachine.runs_withInputs_iff {U W Q V : Type}
    (M : HistoryMachine W Q V) (f : U → W)
    {s t : M.State} {ls : List (SeqLabel U Q V)} :
    Runs (M.withInputs f).transition s ls t ↔
      Runs M.transition s (ls.map (SeqLabel.mapUpdate f)) t := by
  constructor
  · intro h
    induction h with
    | nil => exact .nil _
    | cons h _ ih => exact .cons h ih
  · intro h
    induction ls generalizing s with
    | nil => cases h; exact .nil _
    | cons l ls ih => cases h with
      | cons h rest => exact .cons h (ih rest)

theorem HistoryMachine.toSpec_withInputs {U W Q V : Type}
    (M : HistoryMachine W Q V) (f : U → W) :
    (M.withInputs f).toSpec = M.toSpec.withInputs f := by
  apply HistorySpec.ext
  funext ls
  apply propext
  exact exists_congr (fun _ => M.runs_withInputs_iff f)

theorem projected_withInputs {D : MRDTSig} {U W : Type}
    {P : OperationPolicy D.AppOp} {project : Op D.AppOp → U}
    {f : U → W} {S : HistorySpec W D.Query D.Value} {C : Configuration D}
    (h : ProjectedSpecificationRALinearizable D P (fun e => f (project e)) S C) :
    ProjectedSpecificationRALinearizable D P project (S.withInputs f) C := by
  intro r v s E hh hv q
  obtain ⟨π,hp,ho,hs,ha⟩ := h r v s E hh hv q
  refine ⟨π,hp,ho,?_,?_⟩
  · apply hs.imp
    intro a b hab
    intro hnew
    exact hab ⟨hnew.1, fun hc => hnew.2 (S.withInputs_commutes f hc)⟩
  · simpa only [HistorySpec.withInputs, projectedLabels, List.map_append,
      List.map_cons, List.map_nil, List.map_map, SeqLabel.mapUpdate] using ha

/-- The sequential update alphabet is the exact timestamp/replica/operation
tuple supplied to the concrete MRDT update. -/
abbrev EventSpecificationRALinearizable (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (C : Configuration D) : Prop :=
  ProjectedSpecificationRALinearizable D P id S C

/-- The literal criterion with the same agreed full-input sequential alphabet. -/
def EventRALinearizable (D : MRDTSig) (P : OperationPolicy D.AppOp)
    (S : HistorySpec (Op D.AppOp) D.Query D.Value) (C : Configuration D) : Prop :=
  ∀ r v s E, C.head r = some v → C.ver v = some (s,E) →
    ∀ q, ∃ π : List (Op D.AppOp), listPermOf π E ∧
      respects π (paperOrder P C.replayContext E) ∧
      S.admits (projectedLabels id π ++ [.query q (D.query s q)])

theorem EventSpecificationRALinearizable.active {D : MRDTSig}
    {P : OperationPolicy D.AppOp} {S : HistorySpec (Op D.AppOp) D.Query D.Value}
    {C : Configuration D} (h : EventSpecificationRALinearizable D P S C) :
    EventRALinearizable D P S C := by
  intro r v s E hh hv q
  obtain ⟨π,hp,ho,_,ha⟩ := h r v s E hh hv q
  exact ⟨π,hp,ho,ha⟩

end Sal.MRDTs.Paper1
