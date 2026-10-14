import Sal.MRDTs.Instances.EmbedRGASequential
import Sal.MRDTs.Paper1.CertifiedRGAExecution

namespace Sal.MRDTs.Paper1.EmbedRGAClient
open Foundation Instances.EmbedRGA
open Sal.EmbedRGA (OrderedPrefixCode)
variable {α : Type} [DecidableEq α] [Inhabited α]

inductive Request (α : Type) where
  | insert (index : Nat) (value : α)
  | delete (index : Nat)

def step (view : List (Nat × α)) (stamp : Nat) : Request α → List (Nat × α)
  | .insert index value => view.take index ++ (stamp,value) :: view.drop index
  | .delete index => view.take index ++ view.drop (index+1)

/-- Positions are client requests. Coordinate prefixes come from the source
record and are never supplied by the client. -/
def prepare (s : EState α) (stamp replica : Nat) : Request α → Option (Op (EOp α))
  | .insert index value =>
      if index ≤ s.length then
        if index = 0 then
          if 0 < stamp then some (stamp,replica,.ins value [] 0) else none
        else
          let anchor := s[index-1]!
          if anchor.1 < stamp then some (stamp,replica,.ins value anchor.2.2 anchor.1) else none
      else none
  | .delete index => if index < s.length then some (stamp,replica,.del s[index]!.1) else none

private theorem getElem_mem (s : EState α) (i : Nat) (bound : i < s.length) :
    s[i]! ∈ s := by rw [getElem!_pos s i bound]; exact List.getElem_mem bound

theorem prepared_canIssue {s : EState α} {t r : Nat} {request : Request α}
    {e : Op (EOp α)} (h : prepare s t r request = some e) : eApplicable e s := by
  cases request with
  | insert i value =>
    simp only [prepare] at h
    split at h
    next bound =>
      split at h
      next root =>
        split at h
        next positive => cases h; exact ⟨positive,Or.inl ⟨rfl,rfl⟩⟩
        next => simp at h
      next nonroot =>
        split at h
        next late =>
          cases h
          exact ⟨late,Or.inr ⟨s[i-1]!.2.1,getElem_mem s (i-1) (by omega)⟩⟩
        next => simp at h
    next => simp at h
  | delete i =>
    simp only [prepare] at h
    split at h
    next bound =>
      cases h
      exact List.mem_map.mpr ⟨s[i]!,getElem_mem s i bound,rfl⟩
    next => simp at h

private theorem splice (view : List (Nat × α)) (unique : (view.map Prod.fst).Nodup)
    (noRoot : 0 ∉ view.map Prod.fst) (t i : Nat) (value : α) (bound : i ≤ view.length) :
    (if i = 0 then (t,value)::view else eInsAfter (view[i-1]!).1 (t,value) view) =
      view.take i ++ (t,value)::view.drop i := by
  induction view generalizing i with
  | nil => have hz : i = 0 := by simpa using bound
           subst i; simp
  | cons head tail ih =>
    cases i with
    | zero => simp
    | succ i =>
      cases i with
      | zero => simp [eInsAfter]
      | succ i =>
        have ht : i < tail.length := by simp at bound; omega
        have hn : (tail.map Prod.fst).Nodup := (List.nodup_cons.mp unique).2
        have ne : (tail[i]!).1 ≠ head.1 := by
          intro eq
          exact (List.nodup_cons.mp unique).1 (List.mem_map.mpr
            ⟨tail[i]!,by rw [getElem!_pos tail i ht]; exact List.getElem_mem ht,eq⟩)
        have nr : 0 ∉ tail.map Prod.fst := fun h => noRoot (by simp [h])
        simp only [List.getElem!_eq_getElem?_getD] at ne
        simpa [eInsAfter,ne,Ne.symm ne] using congrArg (List.cons head) (ih hn nr (i+1) (by simp at bound; omega))

/-- Physical source effect, under the source's own honest sequential history
premise. This does not assert concurrent positional-list linearizability. -/
theorem prepared_physical {Γ : OrderedPrefixCode} {history : List (Op (EOp α))}
    {t r : Nat} {request : Request α} {e : Op (EOp α)}
    (prepared : prepare (eFold Γ history) t r request = some e)
    (legal : eSeqOK Γ (history ++ [e]))
    (unique : ((eFold Γ history).map eProj).map Prod.fst |>.Nodup)
    (noRoot : 0 ∉ ((eFold Γ history).map eProj).map Prod.fst) :
    (eUpdate Γ (eFold Γ history) e).map eProj =
      step ((eFold Γ history).map eProj) t request := by
  rw [embed_seq_step legal]
  cases request with
  | insert i value =>
    simp only [prepare] at prepared
    split at prepared
    next bound =>
      split at prepared
      next root =>
        split at prepared
        next => cases prepared; subst i; simp [eSpecStep,step]
        next => simp at prepared
      next nonroot =>
        split at prepared
        next =>
          cases prepared
          have mapped : ((eFold Γ history).map eProj)[i-1]! = eProj ((eFold Γ history)[i-1]!) := by
            rw [getElem!_pos _ _ (by simp; omega),List.getElem_map,getElem!_pos _ _ (by omega)]
          have nonzero : ((eFold Γ history)[i-1]!).1 ≠ 0 := by
            intro eq
            apply noRoot
            exact List.mem_map.mpr ⟨eProj ((eFold Γ history)[i-1]!),List.mem_map.mpr
              ⟨_,getElem_mem _ _ (by omega),rfl⟩,eq⟩
          simp only [List.getElem!_eq_getElem?_getD] at nonzero
          simpa [eSpecStep,step,nonzero,mapped,eProj,nonroot] using
            splice ((eFold Γ history).map eProj) unique noRoot t i value (by simpa using bound)
        next => simp at prepared
    next => simp at prepared
  | delete i =>
    simp only [prepare] at prepared
    split at prepared
    next bound =>
      cases prepared
      have mapped : ((eFold Γ history).map eProj)[i]! = eProj ((eFold Γ history)[i]!) := by
        rw [getElem!_pos _ _ (by simpa using bound),List.getElem_map,getElem!_pos (eFold Γ history) i bound]
      have filtered : ∀ (view : List (Nat × α)) (i : Nat),
          (view.map Prod.fst).Nodup → i < view.length →
          view.filter (fun p => decide (p.1 ≠ view[i]!.1)) =
            view.take i ++ view.drop (i+1) := by
        intro view i uniq hi
        induction view generalizing i with
        | nil => simp at hi
        | cons head tail ih =>
          obtain ⟨fresh,uniq⟩ := List.nodup_cons.mp uniq
          cases i with
          | zero =>
            simp only [List.getElem!_cons_zero,List.filter_cons,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,↓reduceIte,List.take_zero,List.drop_succ_cons,List.drop_zero,List.nil_append]
            apply List.filter_eq_self.mpr
            intro p hp
            have ne : p.1 ≠ head.1 := fun eq => fresh (List.mem_map.mpr ⟨p,hp,eq⟩)
            simpa using ne
          | succ i =>
            have hi' : i < tail.length := by simpa using hi
            have ne : head.1 ≠ tail[i]!.1 := by
              intro eq
              apply fresh
              exact List.mem_map.mpr ⟨tail[i]!,by rw [getElem!_pos tail i hi']; exact List.getElem_mem hi',eq.symm⟩
            simp only [List.getElem!_eq_getElem?_getD] at ne
            simpa [List.filter_cons,ne] using congrArg (List.cons head) (ih i uniq hi')
      have result := filtered ((eFold Γ history).map eProj) i unique (by simpa using bound)
      rw [mapped] at result
      simpa [eSpecStep,step,eProj] using result
    next => simp at prepared

open Sal.EmbedRGA (PosChain coordOf coordOf_append coordOf_inj key keyLt key_inj
  display_iff_chainBefore chainBefore)

/-- The local adjacency facts needed by physical source insertion. -/
theorem geometric_step {Γ : OrderedPrefixCode} {s : EState α} {o : Op (EOp α)}
    (sorted : ESorted s)
    (injective : ∀ a ∈ s, ∀ b ∈ s, a.1 = b.1 → a = b)
    (chains : ∀ {rec}, rec ∈ s → ∃ chain, PosChain chain ∧ chain.sum = rec.1 ∧
      1 ≤ rec.1 ∧ rec.2.2 = coordOf Γ chain)
    (late : ∀ {rec}, rec ∈ s → rec.1 < o.1) (happ : eApplicable o s) :
    (eUpdate Γ s o).map eProj = eSpecStep (s.map eProj) o := by
  obtain ⟨ts, r, op⟩ := o
  cases op with
  | del x =>
      show ((s).filter (fun r => decide (r.1 ≠ x))).map eProj
        = _
      rw [map_eProj_filter]
      rfl
  | ins el π a =>
      simp only [eApplicable] at happ
      obtain ⟨hat, hcase⟩ := happ
      have hat' : a < ts := hat
      have hfresh : (ts, r, EOp.ins el π a).1 ∉ eIds (s) := by
        intro hmem
        obtain ⟨rec, hrec, hr1⟩ := List.mem_map.mp hmem
        have h1 : rec.1 < ts := late hrec
        have h2 : rec.1 = ts := hr1
        omega
      show (eUpdate Γ (s) (ts, r, EOp.ins el π a)).map eProj
        = _
      simp only [eUpdate]
      rw [if_neg hfresh]
      rcases hcase with ⟨rfl, rfl⟩ | ⟨el', hmem⟩
      · -- front insert: the fresh stamp beats every chain
        have hall : ∀ y ∈ s, keyLt (key y.2.2)
            (key (((ts : ℕ), el,
              ([] : List Bool) ++ Γ.enc (ts - 0)) : ERec α).2.2)
            = true := by
          intro y hy
          obtain ⟨chy, hpy, hsy, hy1, hcy⟩ := chains hy
          have hylt : y.1 < ts := late hy
          have hnew : ((((ts : ℕ), el,
              ([] : List Bool) ++ Γ.enc (ts - 0)) : ERec α)).2.2
              = coordOf Γ [ts] := by
            simp [coordOf]
          rw [hnew, hcy]
          cases chy with
          | nil =>
              exfalso
              simp at hsy
              omega
          | cons d rest =>
              have hd : d < ts := by
                have hle : d ≤ (d :: rest).sum := by
                  simp [List.sum_cons]
                omega
              refine (display_iff_chainBefore Γ ?_ hpy ?_).mpr ?_
              · intro z hz
                simp at hz
                omega
              · intro hcontra
                have := congrArg List.sum hcontra
                simp [hsy] at this
                omega
              · exact chainBefore.newer [] ts d [] rest hd
        rw [eInsert_all_lt hall, List.map_cons]
        simp [eProj, eSpecStep]
      · -- anchored insert: the adjacency lemma places it
        have hsort := sorted
        have hinj := injective
        obtain ⟨cha, hpa, hsa, ha1, hca⟩ := chains hmem
        have ha0 : a ≠ 0 := by
          have h1 : (1:ℕ) ≤ a := ha1
          omega
        have hsum_a : cha.sum = a := hsa
        have hcoordnew : π ++ Γ.enc (ts - a)
            = coordOf Γ (cha ++ [ts - a]) := by
          rw [coordOf_append,
            show π = coordOf Γ cha from hca]
          simp [coordOf]
        have hpos_new : PosChain (cha ++ [ts - a]) := by
          intro d hd
          rcases List.mem_append.mp hd with h | h
          · exact hpa d h
          · simp at h
            omega
        have hcane : cha ≠ cha ++ [ts - a] := by
          intro hcontra
          have := congrArg List.length hcontra
          simp at this
        have hkeyne : ∀ rec ∈ s, key rec.2.2 ≠
            key (((ts : ℕ), el, π ++ Γ.enc (ts - a)) : ERec α).2.2 := by
          intro rec hrec hcontra
          obtain ⟨chr, hpr, hsr, -, hcr⟩ := chains hrec
          have hrlt : rec.1 < ts := late hrec
          rw [hcr, show (((ts : ℕ), el, π ++ Γ.enc (ts - a)) :
              ERec α).2.2 = coordOf Γ (cha ++ [ts - a]) from hcoordnew]
            at hcontra
          have h1 := coordOf_inj Γ hpr hpos_new (key_inj hcontra)
          have h2 := congrArg List.sum h1
          rw [hsr, List.sum_append, hsum_a] at h2
          simp at h2
          omega
        have hiff : ∀ rec ∈ s,
            (keyLt (key (((ts : ℕ), el, π ++ Γ.enc (ts - a)) :
                ERec α).2.2) (key rec.2.2) = true ↔
              (rec = ((a : ℕ), el', π) ∨
                keyLt (key (((a : ℕ), el', π) : ERec α).2.2)
                  (key rec.2.2) = true)) := by
          intro rec hrec
          by_cases hreq : rec = ((a : ℕ), el', π)
          · subst hreq
            constructor
            · intro _
              exact Or.inl rfl
            · intro _
              rw [show (((ts : ℕ), el, π ++ Γ.enc (ts - a)) :
                  ERec α).2.2 = coordOf Γ (cha ++ [ts - a])
                  from hcoordnew,
                show (((a : ℕ), el', π) : ERec α).2.2 = coordOf Γ cha
                  from hca]
              exact (display_iff_chainBefore Γ hpa hpos_new
                hcane).mpr
                (chainBefore.ancestor cha [ts - a] (by simp))
          · obtain ⟨chr, hpr, hsr, hr1, hcr⟩ := chains hrec
            have hrlt : rec.1 < ts := late hrec
            have hra : rec.1 ≠ a := fun hcontra =>
              hreq (hinj rec hrec ((a : ℕ), el', π) hmem hcontra)
            have hchne : chr ≠ cha := by
              intro hcontra
              apply hra
              rw [← hsr, ← hsum_a, hcontra]
            have hchne2 : chr ≠ cha ++ [ts - a] := by
              intro hcontra
              have h2 := congrArg List.sum hcontra
              rw [hsr, List.sum_append, hsum_a] at h2
              simp at h2
              omega
            have hmax : ∀ d rest, chr = cha ++ d :: rest →
                d < ts - a := by
              intro d rest hcontra
              have h2 := congrArg List.sum hcontra
              rw [hsr, List.sum_append, hsum_a, List.sum_cons] at h2
              have h4 : a + d ≤ rec.1 := by
                rw [h2]
                omega
              have h3 : a + d < ts := lt_of_le_of_lt h4 hrlt
              exact Nat.lt_sub_of_add_lt
                (by rw [Nat.add_comm]; exact h3)
            rw [show (((ts : ℕ), el, π ++ Γ.enc (ts - a)) :
                ERec α).2.2 = coordOf Γ (cha ++ [ts - a])
                from hcoordnew,
              show (((a : ℕ), el', π) : ERec α).2.2 = coordOf Γ cha
                from hca,
              show rec.2.2 = coordOf Γ chr from hcr,
              display_iff_chainBefore Γ hpr hpos_new hchne2,
              or_iff_right hreq,
              display_iff_chainBefore Γ hpr hpa hchne]
            exact chainBefore_snoc_iff hchne hmax
        rw [eInsert_map_insAfter hsort hmem rfl hinj hkeyne hiff]
        simp [eProj, eSpecStep, ha0]

theorem apply_clock {D : MRDTSig} {C C' : Configuration D} {t r : Nat} {o : D.AppOp}
    (one : Step D C (.apply t r o) C') {v : Version} {s : D.State} {ev : Set (Op D.AppOp)}
    (head : C.head r = some v) (version : C.ver v = some (s,ev)) :
    ∀ e ∈ ev, e.1 < t := by
  cases one with
  | apply hh hv _ _ _ _ C' vis _ _ _ =>
    have same := Option.some.inj (hh.symm.trans head)
    subst v
    have sameState := Option.some.inj (hv.symm.trans version)
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj sameState
    intro e he
    exact C'.causal_mono (by rw [vis]; exact Or.inr ⟨he,rfl⟩)

theorem certified_geometry {Γ : OrderedPrefixCode} {C C' : Configuration (E Γ α)}
    (exec : CertifiedExecution (E Γ α) (generation Γ) C) {t r : Nat} {op : EOp α}
    (one : Step (E Γ α) C (.apply t r op) C')
    {v : Version} {s : EState α} {ev : Set (Op (EOp α))}
    (head : C.head r = some v) (version : C.ver v = some (s,ev)) :
    ESorted s ∧
    (∀ a ∈ s, ∀ b ∈ s, a.1 = b.1 → a = b) ∧
    (∀ rec ∈ s, ∃ chain, PosChain chain ∧ chain.sum = rec.1 ∧
      1 ≤ rec.1 ∧ rec.2.2 = coordOf Γ chain) ∧
    (∀ rec ∈ s, rec.1 < t) := by
  have good := CertifiedRGAExecution.Embedded.canonicalConfig Γ exec
  obtain ⟨ops,perm,order,fold⟩ := good.canonical v s ev version
  change eFold Γ ops = s at fold
  have hon := eHonest_core (eHonest_of_mint exec.mintHonest)
  have supported := good.version_events_supported v s ev version
  have closed := good.version_events_causal v s ev version
  have wf := e_wf_of_enum hon supported (fun a b edge _ hb => closed a b edge hb) perm order
  obtain ⟨chainOf,chainGen⟩ := hon.chain_gen
  have provenance : ∀ rec ∈ s, ∃ o ∈ ops, eIsIns o = true ∧ rec = eRecOf Γ o := by
    rw [← fold]
    exact e_fold_rec_sub Γ ops
  refine ⟨fold ▸ e_fold_sorted Γ wf,fold ▸ e_fold_fst_inj wf,?_,?_⟩
  · intro rec hr
    obtain ⟨o,ho,inserted,hrec⟩ := provenance rec hr
    have member := supported o ((perm.2 o).mp ho)
    obtain ⟨positive,coord,sum⟩ := chainGen o member inserted
    obtain ⟨past,_,_,guard⟩ := exec.mintHonest o member
    have pos : 1 ≤ o.1 := by
      rcases o with ⟨ts,rr,action⟩
      cases action with
      | del x => simp [eIsIns] at inserted
      | ins value coordinateBase anchor => exact Nat.succ_le_of_lt (Nat.zero_lt_of_lt guard.1)
    refine ⟨chainOf o.1,positive,?_,?_,?_⟩
    · simpa [hrec,eRecOf] using sum
    · simpa [hrec,eRecOf] using pos
    · simpa [hrec,eRecOf] using coord
  · intro rec hr
    obtain ⟨o,ho,inserted,hrec⟩ := provenance rec hr
    have clock := apply_clock one head version o ((perm.2 o).mp ho)
    simpa [hrec,eRecOf] using clock

theorem certified_step {Γ : OrderedPrefixCode} {C C' : Configuration (E Γ α)}
    (exec : CertifiedExecution (E Γ α) (generation Γ) C) {t r : Nat} {op : EOp α}
    (one : Step (E Γ α) C (.apply t r op) C')
    {v : Version} {s : EState α} {ev : Set (Op (EOp α))}
    (head : C.head r = some v) (version : C.ver v = some (s,ev))
    (guard : eApplicable (t,r,op) s) :
    (eUpdate Γ s (t,r,op)).map eProj = eSpecStep (s.map eProj) (t,r,op) := by
  obtain ⟨sorted,unique,chains,late⟩ := certified_geometry exec one head version
  exact geometric_step sorted unique (fun h => chains _ h) (fun h => late _ h) guard

theorem certified_prepared_physical {Γ : OrderedPrefixCode}
    {C C' : Configuration (E Γ α)}
    (exec : CertifiedExecution (E Γ α) (generation Γ) C) {t r : Nat} {op : EOp α}
    (one : Step (E Γ α) C (.apply t r op) C')
    {v : Version} {s : EState α} {ev : Set (Op (EOp α))}
    (head : C.head r = some v) (version : C.ver v = some (s,ev))
    {request : Request α}
    (prepared : prepare s t r request = some (t,r,op)) :
    (eUpdate Γ s (t,r,op)).map eProj = step (s.map eProj) t request := by
  obtain ⟨sorted,injective,chains,late⟩ := certified_geometry exec one head version
  have nd : s.Nodup := by
    apply List.Pairwise.imp ?_ sorted
    intro a b relation eq
    subst b
    simpa [Sal.EmbedRGA.keyLt_irrefl] using relation
  have ids : (s.map Prod.fst).Nodup := by
    exact List.Nodup.map_on (fun a ha b hb eq => injective a ha b hb eq) nd
  have unique : ((s.map eProj).map Prod.fst).Nodup := by simpa [List.map_map,eProj,Function.comp_def] using ids
  have noRoot : 0 ∉ (s.map eProj).map Prod.fst := by
    simp only [List.map_map,Function.comp_def,eProj,List.mem_map]
    rintro ⟨rec,hr,eq⟩
    obtain ⟨ch,positive,sum,pos,coord⟩ := chains rec hr
    omega
  rw [certified_step exec one head version (prepared_canIssue prepared)]
  cases request with
  | insert i value =>
    simp only [prepare] at prepared
    split at prepared
    next bound =>
      split at prepared
      next root =>
        split at prepared
        next => cases prepared; subst i; simp [eSpecStep,step]
        next => simp at prepared
      next nonroot =>
        split at prepared
        next =>
          cases prepared
          have mapped : ((s).map eProj)[i-1]! = eProj ((s)[i-1]!) := by
            rw [getElem!_pos _ _ (by simp; omega),List.getElem_map,getElem!_pos _ _ (by omega)]
          have nonzero : ((s)[i-1]!).1 ≠ 0 := by
            intro eq
            apply noRoot
            exact List.mem_map.mpr ⟨eProj ((s)[i-1]!),List.mem_map.mpr
              ⟨_,getElem_mem _ _ (by omega),rfl⟩,eq⟩
          simp only [List.getElem!_eq_getElem?_getD] at nonzero
          simpa [eSpecStep,step,nonzero,mapped,eProj,nonroot] using
            splice ((s).map eProj) unique noRoot t i value (by simpa using bound)
        next => simp at prepared
    next => simp at prepared
  | delete i =>
    simp only [prepare] at prepared
    split at prepared
    next bound =>
      cases prepared
      have mapped : ((s).map eProj)[i]! = eProj ((s)[i]!) := by
        rw [getElem!_pos _ _ (by simpa using bound),List.getElem_map,getElem!_pos (s) i bound]
      have filtered : ∀ (view : List (Nat × α)) (i : Nat),
          (view.map Prod.fst).Nodup → i < view.length →
          view.filter (fun p => decide (p.1 ≠ view[i]!.1)) =
            view.take i ++ view.drop (i+1) := by
        intro view i uniq hi
        induction view generalizing i with
        | nil => simp at hi
        | cons head tail ih =>
          obtain ⟨fresh,uniq⟩ := List.nodup_cons.mp uniq
          cases i with
          | zero =>
            simp only [List.getElem!_cons_zero,List.filter_cons,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,↓reduceIte,List.take_zero,List.drop_succ_cons,List.drop_zero,List.nil_append]
            apply List.filter_eq_self.mpr
            intro p hp
            have ne : p.1 ≠ head.1 := fun eq => fresh (List.mem_map.mpr ⟨p,hp,eq⟩)
            simpa using ne
          | succ i =>
            have hi' : i < tail.length := by simpa using hi
            have ne : head.1 ≠ tail[i]!.1 := by
              intro eq
              apply fresh
              exact List.mem_map.mpr ⟨tail[i]!,by rw [getElem!_pos tail i hi']; exact List.getElem_mem hi',eq.symm⟩
            simp only [List.getElem!_eq_getElem?_getD] at ne
            simpa [List.filter_cons,ne] using congrArg (List.cons head) (ih i uniq hi')
      have result := filtered ((s).map eProj) i unique (by simpa using bound)
      rw [mapped] at result
      simpa [eSpecStep,step,eProj] using result
    next => simp at prepared

#print axioms certified_prepared_physical
#print axioms certified_step
theorem controls :
    prepare (α := Nat) [(4,40,[true]),(6,60,[false])] 9 0 (.insert 1 90) =
      some (9,0,.ins 90 [true] 4) ∧
    prepare (α := Nat) [(4,40,[true]),(6,60,[false])] 9 0 (.insert 1 90) ≠
      some (9,0,.ins 90 [] 0) ∧
    prepare (α := Nat) [(4,40,[true]),(6,60,[false])] 9 0 (.delete 1) =
      some (9,0,.del 6) ∧
    prepare (α := Nat) [] 0 0 (.insert 0 90) = none ∧
    prepare (α := Nat) [] 9 0 (.delete 0) = none := by decide

#print axioms prepared_canIssue
#print axioms prepared_physical
end Sal.MRDTs.Paper1.EmbedRGAClient
