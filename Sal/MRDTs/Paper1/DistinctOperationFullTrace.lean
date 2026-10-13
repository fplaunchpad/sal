import Sal.MRDTs.Paper1.DistinctOperationFullModel

namespace Sal.MRDTs.Paper1.DistinctOperationFullCounterexample
open Foundation ConcreteMRDT
open Classical

private def par (n v : Nat) : List Nat :=
  if v ≤ n then
    if v = 1 then [0] else if v = 2 then [0]
    else if v = 3 then [1] else if v = 4 then [2,3] else []
  else []
private def anc (x y : Nat) : Prop :=
  x = y ∨ x = 0 ∨ (x = 1 ∧ (y = 3 ∨ y = 4)) ∨ ((x = 2 ∨ x = 3) ∧ y = 4)
private theorem par_lt (n v p : Nat) (h : p ∈ par n v) : p < v := by
  by_cases h1 : v = 1 <;> by_cases h2 : v = 2 <;>
    by_cases h3 : v = 3 <;> by_cases h4 : v = 4 <;>
    simp_all [par] <;> omega
private theorem reach_anc {n x y : Nat} (h : Reaches (par n) x y) : anc x y := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail y z h edge ih =>
    by_cases h1 : z = 1 <;> by_cases h2 : z = 2 <;>
      by_cases h3 : z = 3 <;> by_cases h4 : z = 4 <;>
      simp_all [par, anc] <;> grind
private theorem anc_reach {n x y : Nat} (hn : n ≤ 4) (hy : y ≤ n)
    (h : anc x y) : Reaches (par n) x y := by
  have hx : x ≤ y := by unfold anc at h; omega
  have hy4 : y ≤ 4 := hy.trans hn
  have hx4 : x ≤ 4 := hx.trans hy4
  interval_cases y <;> interval_cases x <;> simp_all [anc]
  all_goals first
    | exact .refl
    | exact Relation.ReflTransGen.single (by simp [par]; omega)
    | exact (Relation.ReflTransGen.single (show 0 ∈ par n 1 by simp [par]; omega)).trans
        (Relation.ReflTransGen.single (show 1 ∈ par n 3 by simp [par]; omega))
    | exact (Relation.ReflTransGen.single (show 0 ∈ par n 2 by simp [par]; omega)).trans
        (Relation.ReflTransGen.single (show 2 ∈ par n 4 by simp [par]; omega))
    | exact (Relation.ReflTransGen.single (show 1 ∈ par n 3 by simp [par]; omega)).trans
        (Relation.ReflTransGen.single (show 3 ∈ par n 4 by simp [par]; omega))
private def ev (v : Nat) : Set (Op Unit) :=
  {e | (e = a ∧ anc 2 v) ∨ (e = b ∧ anc 3 v)}
private def st (v : Nat) : Nat := if v = 2 then 1 else if v = 3 ∨ v = 4 then 2 else 0
private def ver (n v : Nat) : Option (D.State × Set (Op Unit)) :=
  if v ≤ n then some (st v, ev v) else none
private def heads (n r : Nat) : Option Nat :=
  if r = 0 then some (if n < 2 then 0 else if n < 4 then 2 else 4)
  else if r = 1 ∧ 1 ≤ n then some (if n < 3 then 1 else 3) else none

private theorem ver_cases {n v s E} (h : ver n v = some (s,E)) :
    v ≤ n ∧ s = st v ∧ E = ev v := by
  simp only [ver] at h
  split at h <;> simp_all

private theorem event_cases {n r E} (h : headEventsFrom (ver n) (heads n) r = some E)
    {e : Op Unit} (he : e ∈ E) : e = a ∨ e = b := by
  change (heads n r).bind (fun v => (ver n v).map Prod.snd) = some E at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨v, hv, heq⟩ := h
  simp only [Option.map_eq_some_iff] at heq
  obtain ⟨⟨s,F⟩, hs, rfl⟩ := heq
  obtain ⟨_,_,rfl⟩ := ver_cases hs
  exact he.imp And.left And.left

private def cfg (n : Nat) (hn : n ≤ 4) : Configuration D where
  vis _ _ := False
  ver := ver n
  head := heads n
  parents := par n
  parents_lt := par_lt n
  ver_init := by simp [ver, st, ev, anc, D]
  head_alloc := by
    intro r v h
    unfold heads at h
    split_ifs at h <;> simp_all [ver] <;> omega
  vis_src := by simp
  vis_tgt := by simp
  vis_causal := by simp
  causal_mono := by simp
  timestamps_distinct := by
    intro e f r E r' E' h he h' hf ne
    rcases event_cases h he with rfl | rfl <;>
      rcases event_cases h' hf with rfl | rfl <;> simp_all [a,b]
  vis_total_same_replica := by
    intro e f r E r' E' h he h' hf ne same
    rcases event_cases h he with rfl | rfl <;>
      rcases event_cases h' hf with rfl | rfl <;> simp_all [a,b]
  gca_events := by
    intro v w t sv Ev sw Ew st Et g hv hw ht
    obtain ⟨hvn,_,rfl⟩ := ver_cases hv
    obtain ⟨hwn,_,rfl⟩ := ver_cases hw
    obtain ⟨htn,_,rfl⟩ := ver_cases ht
    have iffA (x : Nat) : anc x t ↔ anc x v ∧ anc x w := by
      constructor
      · intro h
        have r := anc_reach hn htn h
        exact ⟨reach_anc (r.trans g.1),reach_anc (r.trans g.2.1)⟩
      · rintro ⟨h1,h2⟩
        exact reach_anc (g.2.2 x (anc_reach hn hvn h1) (anc_reach hn hwn h2))
    ext e
    simp only [ev, Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [iffA 2, iffA 3]
    have ne : a ≠ b := by decide
    grind

def afterFork : Configuration D := cfg 1 (by decide)
def afterA : Configuration D := cfg 2 (by decide)
def afterB : Configuration D := cfg 3 (by decide)
def afterMerge : Configuration D := cfg 4 (by decide)

private theorem honest (n : Nat) (hn : n ≤ 4) : MintHonest D issuance.CanIssue (cfg n hn) := by
  intro e he
  obtain ⟨r,E,h,he'⟩ := he
  have cases := event_cases h he'
  refine ⟨[], ?_, by simp [respects], ?_⟩
  · simp [cfg, listPermOf, List.Nodup, List.Perm]
  · exact ⟨cases,rfl⟩

private theorem fork_step : Step D (initConfig D) (.fork 1 0) afterFork := by
  refine .fork (v := 0) (vnew := 1) (s := (0 : Nat)) (ev := ∅)
    (by simp [initConfig]) (by simp [initConfig]) (by simp [initConfig,D])
    (by simp [initConfig]) (by decide) afterFork rfl ?_ ?_ ?_
  · funext w
    by_cases h0 : w = 0 <;> by_cases h1 : w = 1 <;>
      simp_all [afterFork,cfg,ver,st,ev,anc,initConfig,D]
    grind
  · funext r
    simp [afterFork,cfg,heads,initConfig]
    split_ifs <;> simp_all
  · funext w
    simp [afterFork,cfg,par,initConfig]
    split_ifs <;> simp_all <;> omega

private theorem applyA_step : Step D afterFork (.apply 1 0 ()) afterA := by
  refine .apply (v := 0) (vnew := 2) (s := (0 : Nat)) (ev := ∅)
    (by simp [afterFork,cfg,heads]) (by simp [afterFork,cfg,ver,st,ev,anc])
    ?_ ?_ (by simp [afterFork,cfg,ver]) (by decide) afterA ?_ ?_ ?_ ?_
  · intro e he
    obtain ⟨r,E,h,he'⟩ := he
    change e ∈ E at he'
    simp [afterFork,cfg,Configuration.headEvents,heads,headEventsFrom,ver,ev,anc] at h
    split_ifs at h <;> simp_all [ev,anc]
    all_goals subst E; simpa using he'
  · intro w s E h e he
    obtain ⟨hwle,hs,hE⟩ := ver_cases (show ver 1 w = some (s,E) from h)
    interval_cases w <;> simp [ev,anc] at hE <;> subst E <;> simpa using he
  · funext e f; change False = (False ∨ (False ∧ f = (1,0,())))
    simp
  · funext w
    by_cases h0 : w = 0 <;> by_cases h1 : w = 1 <;> by_cases h2 : w = 2 <;>
      simp_all [afterA,afterFork,cfg,ver,st,ev,anc,D,a,Op.time]
    all_goals split_ifs <;> simp_all <;> first | grind | (interval_cases w <;> simp_all)
  · funext r
    simp [afterA,afterFork,cfg,heads]
    split_ifs <;> simp_all <;> omega
  · funext w
    simp [afterA,afterFork,cfg,par]
    split_ifs <;> simp_all <;> omega

private theorem applyB_step : Step D afterA (.apply 2 1 ()) afterB := by
  refine .apply (v := 1) (vnew := 3) (s := (0 : Nat)) (ev := ∅)
    (by simp [afterA,cfg,heads]) (by simp [afterA,cfg,ver,st,ev,anc])
    ?_ ?_ (by simp [afterA,cfg,ver]) (by decide) afterB ?_ ?_ ?_ ?_
  · intro e he
    obtain ⟨r,E,h,he'⟩ := he
    change e ∈ E at he'
    simp [afterA,cfg,Configuration.headEvents,heads,headEventsFrom,ver,ev,anc] at h
    split_ifs at h <;> simp_all
    all_goals subst E; simp_all [a,Op.time]
  · intro w s E h e he
    obtain ⟨hwle,hs,hE⟩ := ver_cases (show ver 2 w = some (s,E) from h)
    interval_cases w <;> simp [ev,anc] at hE <;> subst E <;> simp_all [a,Op.time]
  · funext e f; change False = (False ∨ (False ∧ f = (2,1,())))
    simp
  · funext w
    by_cases h0 : w = 0 <;> by_cases h1 : w = 1 <;>
      by_cases h2 : w = 2 <;> by_cases h3 : w = 3 <;>
      simp_all [afterB,afterA,cfg,ver,st,ev,anc,D,b,Op.time]
    all_goals first | grind | (split_ifs <;> simp_all <;> grind)
  · funext r
    simp [afterB,afterA,cfg,heads]
    split_ifs <;> simp_all <;> omega
  · funext w
    simp [afterB,afterA,cfg,par]
    split_ifs <;> simp_all <;> omega

private theorem merge_step : Step D afterB (.merge 0 1) afterMerge := by
  have gca : IsGCA (par 3) 2 3 0 := by
    refine ⟨anc_reach (by decide) (by decide) (by simp [anc]),
      anc_reach (by decide) (by decide) (by simp [anc]), ?_⟩
    intro w hw2 hw3
    have h2 := reach_anc hw2
    have h3 := reach_anc hw3
    have : w = 0 := by simp [anc] at h2 h3; grind
    subst w
    exact .refl
  refine .merge (v₁ := 2) (v₂ := 3) (vT := 0) (vm := 4)
    (s₁ := (1 : Nat)) (s₂ := (2 : Nat)) (sT := (0 : Nat))
    (ev₁ := ({a} : Set (Op Unit))) (ev₂ := ({b} : Set (Op Unit))) (evT := ∅)
    (by simp [afterB,cfg,heads]) (by simp [afterB,cfg,heads])
    (by simp [afterB,cfg,ver,st,ev,anc]) (by simp [afterB,cfg,ver,st,ev,anc])
    gca (by simp [afterB,cfg,ver,st,ev,anc]) (by simp [afterB,cfg,ver])
    (by decide) (by decide) afterMerge rfl ?_ ?_ ?_
  · funext w
    by_cases h0 : w = 0 <;> by_cases h1 : w = 1 <;>
      by_cases h2 : w = 2 <;> by_cases h3 : w = 3 <;> by_cases h4 : w = 4 <;>
      simp_all [afterMerge,afterB,cfg,ver,st,ev,anc,D]
    all_goals first | grind | (split_ifs <;> simp_all <;> grind)
  · funext r
    simp [afterMerge,afterB,cfg,heads]
    split_ifs <;> simp_all <;> omega
  · funext w
    simp [afterMerge,afterB,cfg,par]
    split_ifs <;> simp_all <;> omega

theorem reached_afterMerge : MintCertifiedReach D issuance afterMerge := by
  have h1 : MintCertifiedReach D issuance afterFork :=
    .step .init (.init : MintCertifiedReach D issuance (initConfig D)).mintHonest
      (.nonApply fork_step (by intros; simp)) (honest 1 (by decide))
  have h2 : MintCertifiedReach D issuance afterA := .step h1 h1.mintHonest
    (.apply (v := 0) (s := (0 : Nat)) (by simp [afterFork,cfg,heads])
      (by simp [afterFork,cfg,ver,st,ev,anc]) (by simp [issuance,a]) applyA_step)
    (honest 2 (by decide))
  have h3 : MintCertifiedReach D issuance afterB := .step h2 h2.mintHonest
    (.apply (v := 1) (s := (0 : Nat)) (by simp [afterA,cfg,heads])
      (by simp [afterA,cfg,ver,st,ev,anc]) (by simp [issuance,b]) applyB_step)
    (honest 3 (by decide))
  exact .step h3 h3.mintHonest (.nonApply merge_step (by intros; simp))
    (honest 4 (by decide))

theorem stored_afterMerge : afterMerge.ver 4 = some (2,{a,b}) := by
  simp [afterMerge,cfg,ver,st,ev,anc]
  ext e
  simp

theorem head_afterMerge : afterMerge.head 0 = some 4 := by
  simp [afterMerge,cfg,heads]

end Sal.MRDTs.Paper1.DistinctOperationFullCounterexample
