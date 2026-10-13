import Sal.MRDTs.Instances.FugueMaxListRefinement

namespace Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax

open Sal.MRDTs.Foundation
open Sal.EmbedRGA (OrderedPrefixCode)

attribute [local instance] rc

/-- Ordinary list legality. An insertion names root or a previously allocated
parent that has not been deleted. A delete names root (the total-index no-op)
or a prior allocation; repeated deletes are idempotent. Metadata does not
participate in legality. -/
def listLegal (ops : KnowM) : Prop :=
  (ops.map MRec.ts).Nodup ∧ (∀ g ∈ ops, 0 < g.ts) ∧
  ∀ pre g post, ops = pre ++ g :: post →
    match g.op with
    | .ins p _ => p = 0 ∨
        (∃ b ∈ pre, mIsIns b = true ∧ b.ts = p) ∧ ∀ d ∈ pre, d.op ≠ .del p
    | .del x => x = 0 ∨ ∃ b ∈ pre, mIsIns b = true ∧ b.ts = x

def listSpec (Γ : OrderedPrefixCode) : SequentialSpec (datatype Γ) where
  State := List (Nat × Nat)
  init := [(0, 0)]
  step := fun s e => listStep s (recordOf e)
  Legal := fun ops => listLegal (ops.map recordOf)
  query := fun s _ => (s.filter (fun p => p.1 != 0)).map Prod.fst

def listRel (s : State) (q : List (Nat × Nat)) : Prop :=
  s.live.map sProj = q.filter (fun p => p.1 != 0)

theorem listSpec_run (Γ : OrderedPrefixCode) (ops : List (Op Payload)) :
    (listSpec Γ).run ops = listRun (ops.map recordOf) := by
  simp only [SequentialSpec.run, SequentialMachine.run, listSpec, listRun, List.foldl_map]
  rfl

private theorem split_staged {L D pre : KnowM} {g : MRec} {post : KnowM}
    (h : L ++ D = pre ++ g :: post) :
    (∃ tail, L = pre ++ g :: tail) ∨
      ∃ head, pre = L ++ head ∧ D = head ++ g :: post := by
  rcases List.append_eq_append_iff.mp h with ⟨head, hp, hd⟩ | ⟨tail, hl, ht⟩
  · exact Or.inr ⟨head, hp, hd⟩
  · cases tail with
    | nil => exact Or.inr ⟨[], by simpa using hl.symm, by simpa using ht.symm⟩
    | cons b tail =>
      simp only [List.cons_append, List.cons.injEq] at ht
      exact Or.inl ⟨tail, by simpa [ht.1] using hl⟩

theorem staged_legal {L D : KnowM}
    (hnd : ((L ++ D).map MRec.ts).Nodup)
    (hpos : ∀ g ∈ L ++ D, 0 < g.ts)
    (hi : ∀ g ∈ L, mIsIns g = true)
    (hd : ∀ g ∈ D, mIsIns g = false)
    (hparents : BirthParents L)
    (htarget : ∀ d ∈ D, ∀ x, d.op = .del x →
      x = 0 ∨ ∃ b ∈ L, mIsIns b = true ∧ b.ts = x) : listLegal (L ++ D) := by
  refine ⟨hnd, hpos, ?_⟩
  intro pre g post heq
  rcases split_staged heq with ⟨tail, hl⟩ | ⟨head, hp, hd'⟩
  · have hg : g ∈ L := by rw [hl]; simp
    have hpre : ∀ b ∈ pre, b ∈ L := by intro b hb; rw [hl]; simp [hb]
    cases hop : g.op with
    | ins p sd =>
      rcases hparents pre g tail hl p sd hop with hz | ⟨b, hb, ht⟩
      · exact Or.inl hz
      · refine Or.inr ⟨⟨b, hb, hi b (hpre b hb), ht⟩, ?_⟩
        intro d hdm hdel
        have h := hi d (hpre d hdm)
        simp [mIsIns, hdel] at h
    | del x => have h := hi g hg; simp [mIsIns, hop] at h
  · have hg : g ∈ D := by rw [hd']; simp
    cases hop : g.op with
    | ins p sd => have h := hd g hg; simp [mIsIns, hop] at h
    | del x =>
      rcases htarget g hg x hop with hz | ⟨b, hb, hi, ht⟩
      · exact Or.inl hz
      · exact Or.inr ⟨b, by rw [hp]; exact List.mem_append_left _ hb, hi, ht⟩

theorem finalNodes_eq_live {Γ : OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (hmint : MintHonest (datatype Γ) (applicable Γ) C) (htrans : Transitive C.vis)
    {ops : List (Op Payload)} {E : Set (Op Payload)}
    (hp : listPermOf ops E) (hsub : ∀ e ∈ E, e ∈ C.events)
    (hr : respects ops (loOn C.replayContext E))
    (inv : KInv Γ (ops.map recordOf)) {L : KnowM}
    (hL : (mMinted (ops.map recordOf)).Perm L)
    (hs : SSorted (buildNodes Γ (ops.map recordOf) L)) :
    finalNodes Γ (ops.map recordOf) L ((ops.map recordOf).filter (fun g => !mIsIns g)) =
      mFold Γ (ops.map recordOf) := by
  apply ssorted_ext ((eraseNodes_sorted hs _).filter _)
    (live_sorted C hmint htrans hp hsub hr)
  intro r
  change r ∈ finalNodes Γ (ops.map recordOf) L
    ((ops.map recordOf).filter (fun g => !mIsIns g)) ↔ r ∈ mFold Γ (ops.map recordOf)
  rw [finalNodes_mem, live_membership C hmint htrans hp hsub hr]
  have hnode : ∀ e ∈ ops, mIsIns (recordOf e) = true →
      node Γ (ops.map recordOf) e.1 = written Γ e := by
    intro e he hi
    have hc := mChainOf_of_mem inv (List.mem_map.mpr ⟨e, he, rfl⟩) hi
    change mChainOf (ops.map recordOf) e.1 = e.2.2.chain at hc
    simp [node, written, hc]
  constructor
  · rintro ⟨⟨g, hg, heq⟩, hn, hd⟩
    obtain ⟨hg, hi⟩ := List.mem_filter.mp (hL.mem_iff.mpr hg)
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hg
    refine ⟨⟨e, (hp.2 e).mp he, hi, heq.trans (hnode e he hi)⟩, ?_⟩
    intro d hdm hdel
    apply hd (recordOf d)
    · exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨d, (hp.2 d).mpr hdm, rfl⟩,
        by simp [mIsIns, recordOf, hdel]⟩
    · exact hdel
  · rintro ⟨⟨e, he, hi, heq⟩, hd⟩
    have heops := (hp.2 e).mpr he
    have hem : recordOf e ∈ ops.map recordOf := List.mem_map.mpr ⟨e, heops, rfl⟩
    refine ⟨⟨recordOf e, hL.mem_iff.mp (List.mem_filter.mpr ⟨hem, hi⟩),
      heq.trans (hnode e heops hi).symm⟩, ?_, ?_⟩
    · rw [heq]
      exact Nat.ne_of_gt (inv.pos (recordOf e) hem)
    · intro d hdm hdel
      obtain ⟨hdm, _⟩ := List.mem_filter.mp hdm
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hdm
      exact hd a ((hp.2 a).mp ha) hdel

theorem staged_respects {Γ : OrderedPrefixCode}
    (C : Configuration (datatype Γ))
    (hmint : MintHonest (datatype Γ) (applicable Γ) C) (htrans : Transitive C.vis)
    (E : Set (Op Payload)) {L D : KnowM}
    (hi : ∀ g ∈ L, mIsIns g = true) (hd : ∀ g ∈ D, mIsIns g = false)
    (hsub : ∀ g ∈ L ++ D, eventOf g ∈ C.events) :
    respects ((L ++ D).map eventOf) (loOn C.replayContext E) := by
  have noBirth : ∀ a ∈ L, ∀ b ∈ L ++ D,
      ¬ loOn C.replayContext E (eventOf b) (eventOf a) := by
    intro a ha b hb hlo
    have hrc := (lo_iff_rc C hmint htrans E (hsub b hb)
      (hsub a (List.mem_append_left _ ha))).mp hlo
    obtain ⟨_, hdel⟩ := (rc_before Γ _ _).mp hrc
    have hop : a.op = .del b.ts := hdel
    have hia := hi a ha
    simp [mIsIns, hop] at hia
  have noDelete : ∀ a ∈ L ++ D, ∀ b ∈ D,
      ¬ loOn C.replayContext E (eventOf b) (eventOf a) := by
    intro a ha b hb hlo
    have hrc := (lo_iff_rc C hmint htrans E
      (hsub b (List.mem_append_right _ hb)) (hsub a ha)).mp hlo
    have hib := (rc_before Γ _ _).mp hrc |>.1
    simp [hd b hb] at hib
  unfold respects
  rw [List.pairwise_map, List.pairwise_append]
  refine ⟨List.pairwise_of_forall_mem_list ?_, List.pairwise_of_forall_mem_list ?_, ?_⟩
  · intro a ha b hb
    exact noBirth a ha b (List.mem_append_left _ hb)
  · intro a ha b hb
    exact noDelete a (List.mem_append_right _ ha) b hb
  · intro a ha b hb
    exact noBirth a ha b (List.mem_append_right _ hb)

theorem records_events (K : KnowM) : (K.map eventOf).map recordOf = K := by
  induction K with
  | nil => rfl
  | cons g K ih => simp only [List.map_cons, recordOf_eventOf, ih]

def listSequentialCorrectness (Γ : OrderedPrefixCode) :
    SequentialCorrectnessCertificate (datatype Γ) (generation Γ) (rc Γ) (listSpec Γ) listRel where
  sound C exec replay := by
    intro v s E hver
    have hc := exec.canonicalConfig (fun C hm => join_of_mint C hm)
    have hsub := hc.version_events_supported v s E hver
    have hclosed := hc.version_events_causal v s E hver
    have htrans : Transitive C.vis := fun _ _ _ => hc.vis_trans
    obtain ⟨ops, hp, hr, hf⟩ := replay v s E hver
    have hevents : ∀ e ∈ ops, e ∈ C.events := fun e he => hsub e ((hp.2 e).mp he)
    obtain ⟨inv, _, _⟩ := invariants_of_mint C exec.mintHonest htrans
      (fun a ha => hc.vis_irrefl a ha) ops hp.1 hevents
      (fun a b hab hb => (hp.2 a).mpr (hclosed a b hab ((hp.2 b).mp hb)))
    let K := ops.map recordOf
    let D := K.filter (fun g => !mIsIns g)
    have hndK : K.Nodup := hp.1.map_on (by
      intro a ha b hb heq
      have h := congrArg eventOf heq
      simpa using h)
    have hndTime : (K.map MRec.ts).Nodup := by
      change ((ops.map recordOf).map MRec.ts).Nodup
      rw [List.map_map]
      apply hp.1.map_on
      intro a ha b hb ht
      exact C.replayContext.ts_unique (hevents a ha) (hevents b hb) ht
    obtain ⟨L, hL, horder⟩ := exists_chain_construction (mMinted K)
    have hLsub : ∀ g ∈ L, g ∈ K ∧ mIsIns g = true :=
      fun g hg => List.mem_filter.mp (hL.mem_iff.mpr hg)
    have hDsub : ∀ g ∈ D, g ∈ K ∧ mIsIns g = false := by
      intro g hg
      obtain ⟨hk, hi⟩ := List.mem_filter.mp hg
      exact ⟨hk, by simpa using hi⟩
    have hperm : (L ++ D).Perm K :=
      (hL.symm.append_right D).trans (List.filter_append_perm mIsIns K)
    have hpermOps : ((L ++ D).map eventOf).Perm ops := by
      have h := hperm.map eventOf
      simpa only [K, events_records] using h
    have hpW : listPermOf ((L ++ D).map eventOf) E :=
      ⟨hpermOps.symm.nodup hp.1, fun e => hpermOps.mem_iff.trans (hp.2 e)⟩
    have hparents := birth_parents_of_construction inv hL horder
    obtain ⟨hbuildSort, hbuild⟩ := births_refine inv hLsub
      (hL.nodup (hndK.filter _)) horder hparents
    have htargets : ∀ d ∈ D, ∀ x, d.op = .del x →
        x = 0 ∨ ∃ b ∈ L, mIsIns b = true ∧ b.ts = x := by
      intro d hd x hop
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp (hDsub d hd).1
      rcases delete_birth_of_mint C exec.mintHonest htrans e (hevents e he) x hop with
        hz | ⟨a, ha, hva, hi, ht⟩
      · exact Or.inl hz
      · have ham : recordOf a ∈ K := List.mem_map.mpr
          ⟨a, (hp.2 a).mpr (hclosed a e hva ((hp.2 e).mp he)), rfl⟩
        exact Or.inr ⟨recordOf a, hL.mem_iff.mp (List.mem_filter.mpr ⟨ham, hi⟩), hi, ht⟩
    have hlegal := staged_legal (hperm.symm.map MRec.ts |>.nodup hndTime)
      (fun g hg => inv.pos g (hperm.mem_iff.mp hg))
      (fun g hg => (hLsub g hg).2) (fun g hg => (hDsub g hg).2) hparents htargets
    have hrel : listRel s ((listSpec Γ).run ((L ++ D).map eventOf)) := by
      rw [listSpec_run, records_events]
      have hfinal := finalNodes_eq_live C exec.mintHonest htrans hp hsub hr inv hL hbuildSort
      have hproject := finalNodes_project hbuild (fun g hg => (hDsub g hg).2)
      rw [rawFold_records] at hf
      have hlive : mFold Γ K = s.live := congrArg State.live hf
      change s.live.map sProj = (listRun (L ++ D)).filter (fun p => p.1 != 0)
      rw [← hlive, ← hfinal]
      exact hproject
    refine ⟨(L ++ D).map eventOf, hpW,
      staged_respects C exec.mintHonest htrans E (fun g hg => (hLsub g hg).2)
        (fun g hg => (hDsub g hg).2) ?_, ?_, hrel, ?_⟩
    · intro g hg
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp (hperm.mem_iff.mp hg)
      simpa using hevents e he
    · change listLegal (((L ++ D).map eventOf).map recordOf)
      rw [records_events]
      exact hlegal
    · intro q
      have h := congrArg (List.map Prod.fst) hrel
      simpa [datatype, listSpec, sIds, sProj, List.map_map] using h

def verified (Γ : OrderedPrefixCode) : VerifiedMRDT (datatype Γ) where
  issuance := generation Γ
  rc := rc Γ
  replayAdequacy := replayAdequacy Γ
  Spec := listSpec Γ
  Rel := listRel
  sequentialCorrectness := listSequentialCorrectness Γ

/-- One public witness establishes ordinary-list correctness and all three
maximal-non-interleaving clauses for the same certified execution. -/
theorem correct {Γ : OrderedPrefixCode} {C : Configuration (datatype Γ)}
    (exec : CertifiedExecution (datatype Γ) (generation Γ) C) :
    ∀ v s E, C.ver v = some (s, E) →
      ∃ ops : List (Op Payload), listPermOf ops E ∧
        respects ops (loOn C.replayContext E) ∧ (listSpec Γ).Legal ops ∧
        listRel s ((listSpec Γ).run ops) ∧
        (∀ q, (datatype Γ).query s q = (listSpec Γ).query ((listSpec Γ).run ops) q) ∧
        MaxNonInterleavingM Γ (ops.map recordOf) := by
  have hspec : IsSpecLinearizable (datatype Γ) (rc Γ) (listSpec Γ) listRel C := by
    cases exec with
    | ordinary h => exact (verified Γ).correct h
    | virtual h => exact (verified Γ).correctV h
  have hc := exec.canonicalConfig (fun C hm => join_of_mint C hm)
  intro v s E hver
  obtain ⟨ops, hp, hr, hl, hrel, hq⟩ := hspec v s E hver
  refine ⟨ops, hp, hr, hl, hrel, hq, noninterleaving_of_mint C exec.mintHonest
    (fun _ _ _ => hc.vis_trans) ops hp.1 ?_ ?_⟩
  · intro e he
    exact hc.version_events_supported v s E hver e ((hp.2 e).mp he)
  · intro a b hab hb
    exact (hp.2 a).mpr (hc.version_events_causal v s E hver a b hab ((hp.2 b).mp hb))

#print axioms staged_legal
#print axioms verified
#print axioms correct

end Sal.MRDTs.Instances.SidedEmbedRGA.FugueMax
