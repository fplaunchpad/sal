import LeanProofs.Implementations.MVRegister.LinearExtension

/-!
# The multivalue register: clause 2

The register's sequential specification and the legality of a replay. A read
returns every value whose write has not been overwritten, so the abstraction
is the identity on live tagged writes and `Rel` is `Eq`.

`replay_legal` is where the issuance guard earns its place: a replay is
admitted only because `canIssue` made each write name exactly the writes it
overwrites.
-/

namespace LeanProofs.Implementations.MVRegister
open Artifact.MRDTs
open Artifact.MRDTs.Foundation
open Classical
local instance : EventOrder D.toUpdateSig := replayOrder
set_option maxHeartbeats 1000000

theorem replay_legal {C : Configuration D}
    (mint : MintHonest D issuance.CanIssue C) {E : Set Event}
    (sup : E ⊆ C.events) (closed : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    {ops : List Event} (hp : listPermOf ops E)
    (hr : respects ops (loOn C.replayContext E)) : spec.Legal ops := by
  have hnd : (ops.map Prod.fst).Nodup := by
    apply hp.1.map_on
    intro a ha b hb ht
    exact C.replayContext.ts_unique (sup ((hp.2 a).mp ha)) (sup ((hp.2 b).mp hb)) ht
  refine ⟨hnd,?_⟩
  intro pre e post hsplit n hn
  have he : e ∈ E := (hp.2 e).mp (by rw [hsplit]; simp)
  obtain ⟨a,ha,hv,ht⟩ := issued_overwrite mint (sup he) hn
  have hain : a ∈ ops := (hp.2 a).mpr (closed a e hv he)
  rw [hsplit,List.mem_append,List.mem_cons] at hain
  rcases hain with ha | rfl | ha
  · exact List.mem_map.mpr ⟨a,ha,ht⟩
  · exact ((Nat.lt_irrefl _) (C.causal_mono hv)).elim
  · rw [hsplit] at hr
    have hnlo := (List.pairwise_cons.mp (List.pairwise_append.mp hr).2.1).1 a ha
    apply (hnlo _).elim
    exact Or.inl ⟨hv,Or.inl ((MVR.replayOrder_before_iff a e).mpr
      ⟨C.causal_mono hv,ht ▸ hn⟩)⟩

noncomputable def sequentialCorrectness : SequentialCorrectnessCertificate D issuance replayOrder spec Eq where
  sound C exec replay := by
    obtain ⟨hG,hR⟩ := represented_of_execution exec
    intro v s E hver
    obtain ⟨ops,hp,hr,hfold⟩ := replay v s E hver
    refine ⟨ops,hp,hr,replay_legal exec.mintHonest
      (fun e he => hG.version_events_supported v s E hver e he)
      (hG.version_events_causal v s E hver) hp hr,?_,?_⟩
    · exact hfold.symm
    · intro q
      cases q
      change MVR.queryValues s = MVR.queryValues (spec.run ops)
      rw [← hfold,update_run_eq]

end LeanProofs.Implementations.MVRegister
