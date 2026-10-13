import Sal.MRDTs.Instances.ProductionRGA
import Sal.MRDTs.Paper1.GuardedHistory
import Sal.MRDTs.Paper1.CertifiedRGAScope

/-! Pure history adapters. CanonicalConfig is an explicit input to be supplied by
new VC execution induction. These helpers do not derive it using historical Join.
The insertion-first public witness respects the original semantic policy order;
full specification visibility is a separate obligation. -/
namespace Sal.MRDTs.Paper1.CertifiedRGAHistory
open Foundation
open Instances.ProductionRGA
open Sal.EmbedRGA (OrderedPrefixCode)
variable {α : Type} [DecidableEq α] [Inhabited α]

theorem embedCanonical_seqOK_of {Γ : OrderedPrefixCode}
    {C : Configuration (Sal.MRDTs.Instances.EmbedRGA.E Γ α)}
    (hgood : CanonicalConfig C)
    (hmint : MintHonest (Sal.MRDTs.Instances.EmbedRGA.E Γ α)
      Sal.MRDTs.Instances.EmbedRGA.eApplicable C)
    {v : Version} {s : (Sal.MRDTs.Instances.EmbedRGA.E Γ α).State}
    {E : Set (Op (Sal.MRDTs.Instances.EmbedRGA.EOp α))}
    (hver : C.ver v = some (s, E))
    {ops : List (Op (Sal.MRDTs.Instances.EmbedRGA.EOp α))}
    (hperm : listPermOf ops E) :
    Sal.MRDTs.Instances.EmbedRGA.eSeqOK Γ
      (EmbedWitness.canonical ops) := by
  open Sal.MRDTs.Instances.EmbedRGA in
    have hsub := hgood.version_events_supported v s E hver
    have hclosed := hgood.version_events_causal v s E hver
    have hhon : EHonestCore Γ C.replayContext :=
      eHonest_core (eHonest_of_mint hmint)
    have hcan := EmbedWitness.canonical_listPermOf hperm
    have hord := EmbedWitness.canonical_ordered ops
    intro pre current post split
    have hordSplit :
        (pre ++ current :: post).Pairwise EmbedWitness.LE := by
      simpa [split] using hord
    have hcurrentList : current ∈ EmbedWitness.canonical ops := by
      rw [split]
      simp
    have hcurrentE : current ∈ E := (hcan.2 current).mp hcurrentList
    have hcurrentC : current ∈ C.events := hsub current hcurrentE
    obtain ⟨ts, replica, action⟩ := current
    cases action with
    | ins el pref anchor =>
        have hpreIns : ∀ e ∈ pre, eIsIns e = true :=
          EmbedWitness.prefix_insert_only hord split (by simp [eIsIns])
        have hclock : ∀ x ∈ eInsIds pre, x < ts := by
          intro x hx
          obtain ⟨old, hold, holdIns, holdTime⟩ := mem_eInsIds.mp hx
          have holdList : old ∈ EmbedWitness.canonical ops := by
            rw [split]
            exact List.mem_append_left _ hold
          have holdE : old ∈ E := (hcan.2 old).mp holdList
          have cross := (List.pairwise_append.mp hordSplit).2.2
          have hleRaw := cross old hold (ts, replica, .ins el pref anchor)
            List.mem_cons_self
          have hle : old.1 ≤ ts := by
            obtain ⟨ot, orp, oop⟩ := old
            cases oop <;> simp [eIsIns] at holdIns
            simpa [EmbedWitness.LE, EmbedWitness.leBool] using hleRaw
          have hne : old.1 ≠ ts := by
            intro heq
            have hop : old = (ts, replica, .ins el pref anchor) :=
              C.replayContext.ts_unique (hsub old holdE) hcurrentC heq
            subst old
            have hnd := hcan.1
            rw [split, List.nodup_append] at hnd
            exact hnd.2.2 _ hold _ List.mem_cons_self rfl
          rw [← holdTime]
          exact Nat.lt_of_le_of_ne hle hne
        obtain ⟨origin, horigin, _, hguard⟩ := hmint _ hcurrentC
        change eApplicable (ts, replica, .ins el pref anchor) (eFold Γ origin) at hguard
        simp only [eApplicable] at hguard
        refine ⟨hclock, hguard.1, ?_⟩
        rcases hguard.2 with hroot | ⟨anchorEl, hanchorOrigin⟩
        · exact Or.inl hroot
        · obtain ⟨parent, hparentOrigin, hparentIns, hparentRec⟩ :=
            e_fold_rec_sub Γ origin (anchor, anchorEl, pref) hanchorOrigin
          have hparentPast := (horigin.2 parent).mp hparentOrigin
          have hparentE : parent ∈ E :=
            hclosed parent (ts, replica, .ins el pref anchor)
              hparentPast.2 hcurrentE
          have hparentAll : parent ∈ EmbedWitness.canonical ops :=
            (hcan.2 parent).mpr hparentE
          have hparentTime : parent.1 = anchor := by
            have hfirst := congrArg (fun r : ERec α => r.1) hparentRec
            simpa [eRecOf] using hfirst.symm
          have hparentPre : parent ∈ pre :=
            EmbedWitness.earlier_insert_mem_prefix hord split hparentAll
              (by simp [eIsIns]) hparentIns (by rw [hparentTime]; exact hguard.1)
          have hpreNodup : pre.Nodup := by
            have hnd := hcan.1
            rw [split, List.nodup_append] at hnd
            exact hnd.1
          have hpreSub : ∀ e ∈ pre, e ∈ C.events := by
            intro e he
            apply hsub e
            apply (hcan.2 e).mp
            rw [split]
            exact List.mem_append_left _ he
          have hwf := EmbedWitness.wf_of_insert_only hpreNodup hpreSub hhon hpreIns
          have hnoDels : anchor ∉ eDels pre := by
            rw [EmbedWitness.dels_nil_of_insert_only hpreIns]
            simp
          have hrecPre : (anchor, anchorEl, pref) ∈ eFold Γ pre :=
            (e_fold_mem Γ hwf (anchor, anchorEl, pref)).mpr
              ⟨⟨parent, hparentPre, hparentIns, hparentRec⟩, hnoDels⟩
          exact Or.inr ⟨anchorEl, hrecPre⟩
    | del target =>
        obtain ⟨origin, horigin, _, hguard⟩ := hmint _ hcurrentC
        change eApplicable (ts, replica, .del target) (eFold Γ origin) at hguard
        simp only [eApplicable] at hguard
        obtain ⟨rec, hrecOrigin, htarget⟩ := List.mem_map.mp hguard
        obtain ⟨parent, hparentOrigin, hparentIns, hparentRec⟩ :=
          e_fold_rec_sub Γ origin rec hrecOrigin
        have hparentPast := (horigin.2 parent).mp hparentOrigin
        have hparentE : parent ∈ E :=
          hclosed parent (ts, replica, .del target) hparentPast.2 hcurrentE
        have hparentAll : parent ∈ EmbedWitness.canonical ops :=
          (hcan.2 parent).mpr hparentE
        have hparentPre : parent ∈ pre :=
          EmbedWitness.insert_mem_prefix_of_delete hord split hparentAll
            (by simp [eIsIns]) hparentIns
        refine ⟨parent, hparentPre, hparentIns, ?_⟩
        rw [hparentRec] at htarget
        exact htarget

theorem embedCanonical_respects_of {Γ : OrderedPrefixCode}
    {C : Configuration (Sal.MRDTs.Instances.EmbedRGA.E Γ α)}
    (hgood : CanonicalConfig C)
    (hhon : Sal.MRDTs.Instances.EmbedRGA.EHonestCore Γ C.replayContext)
    {v : Version} {s : (Sal.MRDTs.Instances.EmbedRGA.E Γ α).State}
    {E : Set (Op (Sal.MRDTs.Instances.EmbedRGA.EOp α))}
    (hver : C.ver v = some (s, E))
    {ops : List (Op (Sal.MRDTs.Instances.EmbedRGA.EOp α))}
    (hperm : listPermOf ops E) :
    respects (EmbedWitness.canonical ops)
      (@loOn _ (embedRc Γ) C.replayContext E) := by
  open Sal.MRDTs.Instances.EmbedRGA in
    have hsub := hgood.version_events_supported v s E hver
    have hcan := EmbedWitness.canonical_listPermOf hperm
    have hordered := EmbedWitness.canonical_ordered ops
    have hall : ∀ e ∈ EmbedWitness.canonical ops, e ∈ C.events := by
      intro e he
      exact hsub e ((hcan.2 e).mp he)
    unfold respects
    generalize hwhole : EmbedWitness.canonical ops = whole at hall hordered
    clear hwhole
    induction whole with
    | nil => exact List.Pairwise.nil
    | cons a rest ih =>
        rw [List.pairwise_cons] at hordered ⊢
        refine ⟨?_, ih (fun e he => hall e (List.mem_cons_of_mem _ he))
          hordered.2⟩
        intro b hb hlo
        have hab := hordered.1 b hb
        rcases hlo with hvisConflict | hrc
        · rcases hvisConflict with ⟨hvba, hconflict⟩
          have haC := hall a List.mem_cons_self
          have hbC := hall b (List.mem_cons_of_mem _ hb)
          obtain ⟨ats, ar, aop⟩ := a
          obtain ⟨bt, br, bop⟩ := b
          cases aop with
          | del ax =>
              cases bop with
              | ins bel bpref banchor =>
                  simp [EmbedWitness.LE, EmbedWitness.leBool] at hab
              | del target =>
                  simpa [embedRc, ReplayPolicy.Before,
                    Sal.MRDTs.Instances.EmbedRGA.EReplayPolicy,
                    Sal.MRDTs.Instances.EmbedRGA.eRcOrder,
                    embedSemanticCommutes] using
                    hconflict
          | ins ael apref aanchor =>
              cases bop with
              | ins bel bpref banchor =>
                  simpa [embedRc, ReplayPolicy.Before,
                    Sal.MRDTs.Instances.EmbedRGA.EReplayPolicy,
                    Sal.MRDTs.Instances.EmbedRGA.eRcOrder,
                    embedSemanticCommutes] using
                    hconflict
              | del target =>
                  have hat : ats = target := by
                    have hncBA : ¬ embedSemanticCommutes
                        (bt, br, .del target)
                        (ats, ar, .ins ael apref aanchor) := by
                      exact (embedRc_noncomm Γ _ _).mp hconflict
                    have hnc : ¬ embedSemanticCommutes
                        (ats, ar, .ins ael apref aanchor)
                        (bt, br, .del target) := fun hcomm =>
                      hncBA ((embedSemanticCommutes_symm _ _).mp hcomm)
                    simpa [embedSemanticCommutes] using not_ne_iff.mp hnc
                  obtain ⟨creator, hcreatorC, hcreatorVis, hcreatorTime,
                    _⟩ := hhon.del_has_ins (bt, br, .del target) hbC target rfl
                  have hcreatorEq :
                      creator = (ats, ar, .ins ael apref aanchor) :=
                    C.replayContext.ts_unique hcreatorC haC
                      (hcreatorTime.trans hat.symm)
                  subst creator
                  exact hgood.vis_irrefl _
                    (hgood.vis_trans hcreatorVis hvba)
        · exact (embedRc_not_before Γ _ _ hab) hrc.2.2.1


/-- A supplied stored causal replay yields the unchanged independent public
sequential specification, plus exact replay equality. No merge theorem occurs
in this adapter. Specification-conflict visibility remains separate. -/
theorem embed_history_of_replay {Γ : OrderedPrefixCode}
    {C : Configuration (Sal.MRDTs.Instances.EmbedRGA.E Γ α)}
    (exec : CertifiedExecution (Sal.MRDTs.Instances.EmbedRGA.E Γ α) (Sal.MRDTs.Instances.EmbedRGA.generation Γ) C)
    (hgood : CanonicalConfig C)
    {v : Version} {s : (Sal.MRDTs.Instances.EmbedRGA.E Γ α).State} {E : Set (Op (Sal.MRDTs.Instances.EmbedRGA.EOp α))}
    (hver : C.ver v = some (s,E)) {ops : List (Op (Sal.MRDTs.Instances.EmbedRGA.EOp α))}
    (hperm : listPermOf ops E) (hresp : respects ops C.vis)
    (hfold : Sal.MRDTs.Instances.EmbedRGA.eFold Γ ops = s) :
    ∃ π, listPermOf π E ∧ respects π (@loOn _ (embedRc Γ) C.replayContext E) ∧
      (embedClientSpec Γ).Legal π ∧ Sal.MRDTs.Instances.EmbedRGA.eFold Γ π = s ∧
      embedRel s ((embedClientSpec Γ).run π) ∧
      ∀ q, (Sal.MRDTs.Instances.EmbedRGA.E Γ α).query s q = (embedClientSpec Γ).query ((embedClientSpec Γ).run π) q := by
  open Sal.MRDTs.Instances.EmbedRGA in
    have hseq := embedCanonical_seqOK_of hgood exec.mintHonest hver hperm
    have hlegal := embedLegal_of_seqOK hseq
    have hcan := EmbedWitness.canonical_listPermOf hperm
    have hsub := hgood.version_events_supported v s E hver
    have hclosed := hgood.version_events_causal v s E hver
    have hhon : EHonestCore Γ C.replayContext :=
      eHonest_core (eHonest_of_mint exec.mintHonest)
    have hwfReplay : EWf Γ ops :=
      CertifiedRGAScope.Embedded.wellformed Γ C.replayContext hhon E ops
        hsub hclosed hperm hresp
    have hwfCanonical : EWf Γ (EmbedWitness.canonical ops) :=
      eWf_of_seqOK hseq
    have hcanonFold :
        eFold Γ (EmbedWitness.canonical ops) = eFold Γ ops :=
      e_fold_canon Γ hwfCanonical hwfReplay
        (fun e => (hcan.2 e).trans (hperm.2 e).symm)
    have hstate : eFold Γ (EmbedWitness.canonical ops) = s := by
      rw [hcanonFold]
      exact hfold
    have hsound := embed_seq_sound hseq
    have hrel : embedRel s ((embedClientSpec Γ).run
        (EmbedWitness.canonical ops)) := by
      unfold embedRel
      change s.map eProj = eSpecFold (EmbedWitness.canonical ops)
      rw [← hstate]
      exact hsound
    refine ⟨EmbedWitness.canonical ops, hcan,
      embedCanonical_respects_of hgood hhon hver hperm, hlegal, hstate, hrel, ?_⟩
    intro query
    cases query
    change s.map (fun r => r.2.1) =
      ((embedClientSpec Γ).run (EmbedWitness.canonical ops)).map Prod.snd
    simpa [eProj, List.map_map, Function.comp_def] using
      congrArg (List.map Prod.snd) hrel

/-- A supplied stored causal replay yields the unchanged independent public
sequential specification, plus exact replay equality. No merge theorem occurs
in this adapter. Specification-conflict visibility remains separate. -/
theorem sided_history_of_replay {Γ : OrderedPrefixCode}
    {C : Configuration (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ)}
    (exec : CertifiedExecution (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ) (Sal.MRDTs.Instances.SidedEmbedRGA.generation Γ) C)
    (hgood : CanonicalConfig C)
    {v : Version} {s : (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ).State} {E : Set (Op (Sal.MRDTs.Instances.SidedEmbedRGA.SOp))}
    (hver : C.ver v = some (s,E)) {ops : List (Op (Sal.MRDTs.Instances.SidedEmbedRGA.SOp))}
    (hperm : listPermOf ops E) (hresp : respects ops C.vis)
    (hfold : Sal.MRDTs.Instances.SidedEmbedRGA.sFold Γ ops = s) :
    ∃ π, listPermOf π E ∧ respects π (@loOn _ (sidedRc Γ) C.replayContext E) ∧
      (sidedClientSpec Γ).Legal π ∧ Sal.MRDTs.Instances.SidedEmbedRGA.sFold Γ π = s ∧
      sidedRel s ((sidedClientSpec Γ).run π) ∧
      ∀ q, (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ).query s q = (sidedClientSpec Γ).query ((sidedClientSpec Γ).run π) q := by
  open Sal.MRDTs.Instances.SidedEmbedRGA in
    have hseq := sidedCanonical_seqOK_of hgood exec.mintHonest hver hperm
    have hlegal := sidedLegal_of_seqOK hseq
    have hcan := SidedWitness.canonical_listPermOf hperm
    have hsub := hgood.version_events_supported v s E hver
    have hclosed := hgood.version_events_causal v s E hver
    have hhon : SHonestCore Γ C.replayContext :=
      sHonest_core (sHonest_of_mint exec.mintHonest)
    have hwfReplay : SWf Γ ops :=
      CertifiedRGAScope.Sided.wellformed Γ C.replayContext hhon E ops
        hsub hclosed hperm hresp
    have hwfCanonical : SWf Γ (SidedWitness.canonical ops) :=
      sWf_of_seqOK hseq
    have hcanonFold :
        sFold Γ (SidedWitness.canonical ops) = sFold Γ ops :=
      s_fold_canon Γ hwfCanonical hwfReplay
        (fun e => (hcan.2 e).trans (hperm.2 e).symm)
    have hstate : sFold Γ (SidedWitness.canonical ops) = s := by
      rw [hcanonFold]
      exact hfold
    have hsound := sided_seq_read hseq
    have hrel : sidedRel s ((sidedClientSpec Γ).run
        (SidedWitness.canonical ops)) := by
      unfold sidedRel
      change s.map sProj = (sSpecFold (SidedWitness.canonical ops)).filter
        (fun p => decide (p.1 ≠ 0))
      rw [← hstate]
      exact hsound
    refine ⟨SidedWitness.canonical ops, hcan,
      sidedCanonical_respects_of hgood hhon hver hperm, hlegal, hstate, hrel, ?_⟩
    intro query
    cases query
    change s.map (fun r => r.2.1) =
      (((sidedClientSpec Γ).run (SidedWitness.canonical ops)).filter
        (fun p => decide (p.1 ≠ 0))).map Prod.snd
    simpa [sProj, List.map_map, Function.comp_def] using
      congrArg (List.map Prod.snd) hrel

theorem embed_legal_prefix (Γ : OrderedPrefixCode)
    (pre suf : List (Op (Sal.MRDTs.Instances.EmbedRGA.EOp α)))
    (legal : (embedClientSpec Γ).Legal (pre ++ suf)) :
    (embedClientSpec Γ).Legal pre := by
  intro before e after split
  apply legal before e (after ++ suf)
  simp only [split, List.append_assoc, List.cons_append]

/-- An admitted independent history with the original query. Specification
visibility is not asserted by this adapter; it is a separate obligation. -/
theorem embed_admitted_of_replay {Γ : OrderedPrefixCode}
    {C : Configuration (Sal.MRDTs.Instances.EmbedRGA.E Γ α)}
    (exec : CertifiedExecution (Sal.MRDTs.Instances.EmbedRGA.E Γ α)
      (Sal.MRDTs.Instances.EmbedRGA.generation Γ) C)
    (hgood : CanonicalConfig C)
    {v : Version} {s : (Sal.MRDTs.Instances.EmbedRGA.E Γ α).State} {E : Set (Op (Sal.MRDTs.Instances.EmbedRGA.E Γ α).AppOp)}
    (hver : C.ver v = some (s,E)) {ops : List (Op (Sal.MRDTs.Instances.EmbedRGA.E Γ α).AppOp)}
    (hperm : listPermOf ops E) (hresp : respects ops C.vis)
    (hfold : Sal.MRDTs.Instances.EmbedRGA.eFold Γ ops = s)
    (q : (Sal.MRDTs.Instances.EmbedRGA.E Γ α).Query) :
    ∃ π, listPermOf π E ∧
      (GuardedHistory.language (embedClientSpec Γ)).admits
        (projectedLabels id π ++ [.query q ((Sal.MRDTs.Instances.EmbedRGA.E Γ α).query s q)]) := by
  obtain ⟨π,perm,_,legal,_,_,query⟩ :=
    embed_history_of_replay exec hgood hver hperm hresp hfold
  refine ⟨π,perm,?_⟩
  rw [query q]
  exact GuardedHistory.admits_updates_query (embedClientSpec Γ)
    (embed_legal_prefix Γ) π legal q

theorem sided_legal_prefix (Γ : OrderedPrefixCode)
    (pre suf : List (Op Sal.MRDTs.Instances.SidedEmbedRGA.SOp))
    (legal : (sidedClientSpec Γ).Legal (pre ++ suf)) :
    (sidedClientSpec Γ).Legal pre := by
  intro before e after split
  apply legal before e (after ++ suf)
  simp only [split, List.append_assoc, List.cons_append]

/-- An admitted independent history with the original query. Specification
visibility is not asserted by this adapter; it is a separate obligation. -/
theorem sided_admitted_of_replay {Γ : OrderedPrefixCode}
    {C : Configuration (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ)}
    (exec : CertifiedExecution (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ)
      (Sal.MRDTs.Instances.SidedEmbedRGA.generation Γ) C)
    (hgood : CanonicalConfig C)
    {v : Version} {s : (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ).State} {E : Set (Op (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ).AppOp)}
    (hver : C.ver v = some (s,E)) {ops : List (Op (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ).AppOp)}
    (hperm : listPermOf ops E) (hresp : respects ops C.vis)
    (hfold : Sal.MRDTs.Instances.SidedEmbedRGA.sFold Γ ops = s)
    (q : (Sal.MRDTs.Instances.SidedEmbedRGA.S Γ).Query) :
    ∃ π, listPermOf π E ∧
      (GuardedHistory.language (sidedClientSpec Γ)).admits
        (projectedLabels id π ++ [.query q ((Sal.MRDTs.Instances.SidedEmbedRGA.S Γ).query s q)]) := by
  obtain ⟨π,perm,_,legal,_,_,query⟩ :=
    sided_history_of_replay exec hgood hver hperm hresp hfold
  refine ⟨π,perm,?_⟩
  rw [query q]
  exact GuardedHistory.admits_updates_query (sidedClientSpec Γ)
    (sided_legal_prefix Γ) π legal q

end Sal.MRDTs.Paper1.CertifiedRGAHistory
