import Sal.MRDTs.Instances.SidedEmbedRGASequential
import Sal.MRDTs.Paper1.EmbedRGAClientLocal

/-! Local positional clients for core sided Embedded RGA. The source payload
is Nat; timestamp, replica, coordinates and sided anchors are replication
metadata generated outside the user request. These theorems preserve the
source issuer and establish local physical effects, not concurrent positional
FIFO/text contracts. Coretext/RichCore formatting extensions are outside this
adapter; no unsupported Coretext deletion operation is introduced. -/
namespace Sal.MRDTs.Paper1.SidedRGAClient
open Foundation Instances.SidedEmbedRGA
open Sal.EmbedRGA (OrderedPrefixCode Side)
inductive Request where
  | insert (index value : Nat)
  | delete (index : Nat)

def step (view : List (Nat × Nat)) (t : Nat) : Request → List (Nat × Nat)
  | .insert i value => view.take i ++ (t,value)::view.drop i
  | .delete i => view.take i ++ view.drop (i+1)

/-- Read positions generate stable anchors and source coordinate priores.
The hidden sentinel is used only when the visible document is empty. -/
def prepare (s : SState) (t r : Nat) : Request → Option (Op SOp)
  | .insert i value =>
    if i ≤ s.length then
      if s = [] then if 0 < t then some (t,r,.ins value [] 0 .R) else none
      else
        let anchor := if i < s.length then s[i]! else s[i-1]!
        let side := if i < s.length then Side.L else Side.R
        if anchor.1 < t then some (t,r,.ins value anchor.2.2 anchor.1 side) else none
    else none
  | .delete i => if i < s.length then some (t,r,.del s[i]!.1) else none

private theorem selected_mem (s : SState) (i : Nat) (bound : i < s.length) : s[i]! ∈ s := by
  rw [getElem!_pos s i bound]; exact List.getElem_mem bound

theorem prepared_canIssue {s : SState} {t r : Nat} {q : Request} {e : Op SOp}
    (h : prepare s t r q = some e) : sApplicable e s := by
  cases q with
  | insert i value =>
    simp only [prepare] at h
    split at h
    next bound =>
      split at h
      next empty =>
        split at h
        next pos => cases h; exact ⟨pos,Or.inl ⟨rfl,rfl⟩⟩
        next => simp at h
      next nonempty =>
        by_cases inside : i < s.length
        · simp only [if_pos inside] at h
          split at h
          next late => cases h; exact ⟨late,Or.inr ⟨_,selected_mem s i inside⟩⟩
          next => simp at h
        · simp only [if_neg inside] at h
          split at h
          next late =>
            cases h
            exact ⟨late,Or.inr ⟨_,selected_mem s (i-1) (by
              have positive : 0 < s.length := by cases s <;> simp_all
              omega)⟩⟩
          next => simp at h
    next => simp at h
  | delete i =>
    simp only [prepare] at h
    split at h
    next bound => cases h; exact List.mem_map.mpr ⟨_,selected_mem s i bound,rfl⟩
    next => simp at h

/-- Exact source physical bridge to the rooted two-sided buffer program.
The sentinel is filtered before observation. Position preparation is checked
against the same concrete source state, rather than against a supplied log. -/
theorem prepared_physical {Γ : OrderedPrefixCode} {history : List (Op SOp)}
    {t r : Nat} {q : Request} {e : Op SOp}
    (prepared : prepare (sFold Γ history) t r q = some e)
    (legal : sSeqOK Γ (history ++ [e])) :
    sApplicable e (sFold Γ history) ∧
    (sUpdate Γ (sFold Γ history) e).map sProj =
      (sSpecStep (sSpecFold history) e).filter (fun p => decide (p.1 ≠ 0)) := by
  refine ⟨prepared_canIssue prepared,?_⟩
  rw [← sFold_snoc, sided_seq_read legal,sSpecFold_snoc]

private theorem hide_before (a : Nat) (p : Nat × Nat) (anchor : a ≠ 0)
    (fresh : p.1 ≠ 0) (view : List (Nat × Nat)) :
    (sInsBefore a p view).filter (fun x => decide (x.1 ≠ 0)) =
      sInsBefore a p (view.filter (fun x => decide (x.1 ≠ 0))) := by
  induction view with
  | nil => rfl
  | cons head tail ih =>
    simp only [ne_eq,decide_not] at ih
    by_cases same : head.1 = a
    · have nonzero : head.1 ≠ 0 := fun h => anchor (same.symm.trans h)
      simp [sInsBefore,List.filter_cons,same,nonzero,fresh,anchor]
    · by_cases root : head.1 = 0
      · simp [sInsBefore,List.filter_cons,same,root,ih,anchor,Ne.symm anchor]
      · simp [sInsBefore,List.filter_cons,same,root,ih,anchor,Ne.symm anchor]

private theorem before_positional (view : List (Nat × Nat)) (i : Nat)
    (p : Nat × Nat) (unique : (view.map Prod.fst).Nodup) (bound : i < view.length) :
    sInsBefore view[i]!.1 p view = view.take i ++ p :: view.drop i := by
  induction view generalizing i with
  | nil => simp at bound
  | cons head tail ih =>
    cases i with
    | zero => simp [sInsBefore]
    | succ i =>
      obtain ⟨fresh,uniq⟩ := List.nodup_cons.mp unique
      have inside : i < tail.length := by simpa using bound
      have ne : head.1 ≠ tail[i]!.1 := by
        intro eq
        exact fresh (List.mem_map.mpr ⟨tail[i]!,by rw [getElem!_pos tail i inside]; exact List.getElem_mem inside,eq.symm⟩)
      simp only [List.getElem!_eq_getElem?_getD] at ne
      simpa [sInsBefore,ne] using congrArg (List.cons head) (ih i uniq inside)

/-- Ordinary visible positional effect for front and interior insertions,
independent of where the hidden sentinel lies in the rooted buffer. -/
theorem prepared_insert_before_physical {Γ : OrderedPrefixCode}
    {history : List (Op SOp)} {t r i value : Nat}
    (inside : i < (sFold Γ history).length)
    (clock : ((sFold Γ history)[i]!).1 < t)
    (legal : sSeqOK Γ (history ++ [(t,r,.ins value ((sFold Γ history)[i]!).2.2
      ((sFold Γ history)[i]!).1 .L)]))
    (unique : ((sFold Γ history).map sProj).map Prod.fst |>.Nodup) :
    (sUpdate Γ (sFold Γ history)
      (t,r,.ins value ((sFold Γ history)[i]!).2.2 ((sFold Γ history)[i]!).1 .L)).map sProj =
      step ((sFold Γ history).map sProj) t (.insert i value) := by
  let e : Op SOp := (t,r,.ins value ((sFold Γ history)[i]!).2.2 ((sFold Γ history)[i]!).1 .L)
  have prep : prepare (sFold Γ history) t r (.insert i value) = some e := by
    have nonempty : sFold Γ history ≠ [] := fun h => by simp [h] at inside
    rw [getElem!_pos (sFold Γ history) i inside] at clock
    simp [prepare,Nat.le_of_lt inside,nonempty,inside,clock,e]
  have physical := (prepared_physical prep legal).2
  have prior := sSeqOK_prefix legal
  have nonzero : ((sFold Γ history)[i]!).1 ≠ 0 := by
    have pos := s_fold_id_pos prior (selected_mem _ _ inside)
    omega
  have positive : t ≠ 0 := by omega
  simp only [e,sSpecStep] at physical
  rw [hide_before _ _ nonzero positive,← sided_seq_read prior] at physical
  have mapped : ((sFold Γ history).map sProj)[i]! = sProj ((sFold Γ history)[i]!) := by
    rw [getElem!_pos _ _ (by simpa using inside),List.getElem_map,getElem!_pos (sFold Γ history) i inside]
  have positional := before_positional ((sFold Γ history).map sProj) i (t,value) unique (by simpa using inside)
  rw [mapped] at positional
  simpa [step,sProj] using physical.trans positional

private theorem hide_after (a : Nat) (p : Nat × Nat) (anchor : a ≠ 0)
    (fresh : p.1 ≠ 0) (view : List (Nat × Nat)) :
    (sInsAfter a p view).filter (fun x => decide (x.1 ≠ 0)) =
      sInsAfter a p (view.filter (fun x => decide (x.1 ≠ 0))) := by
  induction view with
  | nil => rfl
  | cons head tail ih =>
    simp only [ne_eq,decide_not] at ih
    by_cases same : head.1 = a
    · have nonzero : head.1 ≠ 0 := fun h => anchor (same.symm.trans h)
      simp [sInsAfter,List.filter_cons,same,nonzero,fresh,anchor]
    · by_cases root : head.1 = 0
      · simp [sInsAfter,List.filter_cons,same,root,ih,anchor,Ne.symm anchor]
      · simp [sInsAfter,List.filter_cons,same,root,ih,anchor,Ne.symm anchor]

private theorem after_last (view : List (Nat × Nat)) (p : Nat × Nat)
    (unique : (view.map Prod.fst).Nodup) (nonempty : view ≠ []) :
    sInsAfter view[view.length-1]!.1 p view = view ++ [p] := by
  induction view with
  | nil => exact (nonempty rfl).elim
  | cons head tail ih =>
    by_cases empty : tail = []
    · subst tail; simp [sInsAfter]
    · obtain ⟨fresh,uniq⟩ := List.nodup_cons.mp unique
      have positive : 0 < tail.length := by cases tail <;> simp_all
      have bound : tail.length-1 < tail.length := by omega
      have ne : head.1 ≠ tail[tail.length-1]!.1 := by
        intro eq
        exact fresh (List.mem_map.mpr ⟨_,by rw [getElem!_pos tail _ bound]; exact List.getElem_mem bound,eq.symm⟩)
      simp only [List.getElem!_eq_getElem?_getD] at ne
      have length : (head::tail).length-1 = (tail.length-1)+1 := by simp; omega
      rw [length]
      simp only [List.getElem!_cons_succ]
      simpa [sInsAfter,ne] using congrArg (List.cons head) (ih uniq empty)

theorem prepared_append_physical {Γ : OrderedPrefixCode}
    {history : List (Op SOp)} {t r value : Nat}
    (nonempty : sFold Γ history ≠ [])
    (clock : ((sFold Γ history)[(sFold Γ history).length-1]!).1 < t)
    (legal : sSeqOK Γ (history ++ [(t,r,.ins value
      ((sFold Γ history)[(sFold Γ history).length-1]!).2.2
      ((sFold Γ history)[(sFold Γ history).length-1]!).1 .R)]))
    (unique : ((sFold Γ history).map sProj).map Prod.fst |>.Nodup) :
    (sUpdate Γ (sFold Γ history) (t,r,.ins value
      ((sFold Γ history)[(sFold Γ history).length-1]!).2.2
      ((sFold Γ history)[(sFold Γ history).length-1]!).1 .R)).map sProj =
      step ((sFold Γ history).map sProj) t (.insert (sFold Γ history).length value) := by
  have pos : 0 < (sFold Γ history).length := by cases h : sFold Γ history <;> simp_all
  have bound : (sFold Γ history).length-1 < (sFold Γ history).length := by omega
  let e : Op SOp := (t,r,.ins value
      ((sFold Γ history)[(sFold Γ history).length-1]!).2.2
      ((sFold Γ history)[(sFold Γ history).length-1]!).1 .R)
  have prep : prepare (sFold Γ history) t r (.insert (sFold Γ history).length value) = some e := by
    simp only [prepare,if_pos (Nat.le_refl _),if_neg nonempty,lt_self_iff_false,if_false]
    change (if _ then some e else none) = some e
    rw [if_pos clock]
  have physical := (prepared_physical prep legal).2
  have prior := sSeqOK_prefix legal
  have nonzero : ((sFold Γ history)[(sFold Γ history).length-1]!).1 ≠ 0 := by
    have h := s_fold_id_pos prior (selected_mem _ _ bound)
    omega
  have positive : t ≠ 0 := by omega
  simp only [e,sSpecStep] at physical
  rw [hide_after _ _ nonzero positive,← sided_seq_read prior] at physical
  have mapped : ((sFold Γ history).map sProj)[(sFold Γ history).length-1]! =
      sProj ((sFold Γ history)[(sFold Γ history).length-1]!) := by
    rw [getElem!_pos _ _ (by simpa using bound),List.getElem_map,getElem!_pos (sFold Γ history) _ bound]
  have eq := after_last ((sFold Γ history).map sProj) (t,value) unique (by simpa using nonempty)
  simp only [List.length_map] at eq
  rw [mapped] at eq
  have lengths : (sFold Γ history).length = ((sFold Γ history).map sProj).length := (List.length_map sProj).symm
  simpa only [step,lengths,List.take_length,List.drop_length,sProj] using physical.trans eq

theorem prepared_empty_physical {Γ : OrderedPrefixCode}
    {history : List (Op SOp)} {t r value : Nat}
    (empty : sFold Γ history = []) (positive : 0 < t)
    (legal : sSeqOK Γ (history ++ [(t,r,.ins value [] 0 .R)])) :
    prepare (sFold Γ history) t r (.insert 0 value) = some (t,r,.ins value [] 0 .R) ∧
    (sUpdate Γ (sFold Γ history) (t,r,.ins value [] 0 .R)).map sProj = [(t,value)] := by
  refine ⟨by simp [prepare,empty,positive],?_⟩
  have prior := sSeqOK_prefix legal
  have rooted : sRFold Γ history = [rootRec] := by
    apply ssorted_ext (sr_fold_sorted prior) (by simp [SSorted])
    intro rec
    rw [sr_fold_iff prior]
    simp [empty]
  have buffer : sSpecFold history = [(0,0)] := by
    rw [← sided_seq_sound prior,rooted]
    rfl
  rw [← sFold_snoc,sided_seq_read legal,sSpecFold_snoc,buffer]
  simp [sSpecStep,sInsAfter,Nat.ne_of_gt positive]

private theorem delete_positional : ∀ (view : List (Nat × Nat)) (i : Nat),
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

theorem prepared_delete_physical (Γ : OrderedPrefixCode) (s : SState) (t r i : Nat)
    (inside : i < s.length) (unique : (s.map sProj).map Prod.fst |>.Nodup) :
    prepare s t r (.delete i) = some (t,r,.del s[i]!.1) ∧
    (sUpdate Γ s (t,r,.del s[i]!.1)).map sProj = step (s.map sProj) t (.delete i) := by
  refine ⟨by simp [prepare,inside],?_⟩
  have mapped : (s.map sProj)[i]! = sProj s[i]! := by
    rw [getElem!_pos _ _ (by simpa using inside),List.getElem_map,getElem!_pos s i inside]
  have result := delete_positional (s.map sProj) i unique (by simpa using inside)
  rw [mapped] at result
  change (s.filter (fun rec => decide (rec.1 ≠ s[i]!.1))).map sProj = _
  rw [map_sProj_filter]
  simpa [step,sProj] using result


open Sal.EmbedRGA (SChain PosSChain sidedCoordOf sidedCoordOf_append sidedCoordOf_inj
  sKey sBlock keyLt sdisplay_iff_schainBefore schainBefore Side)

theorem geometric_live_step {Γ : OrderedPrefixCode} {s : SState}
    {ts rr el el' a : Nat} {π : List Nat} {sd : Side}
    (sorted : SSorted s)
    (injective : ∀ a ∈ s, ∀ b ∈ s, a.1 = b.1 → a = b)
    (chains : ∀ {rec}, rec ∈ s → ∃ chain, PosSChain chain ∧
      (chain.map Prod.snd).sum = rec.1 ∧ rec.2.2 = sidedCoordOf Γ chain)
    (late : ∀ {rec}, rec ∈ s → rec.1 < ts)
    (hmem : (a,el',π) ∈ s) (hat' : a < ts) :
    (sUpdate Γ s (ts,rr,.ins el π a sd)).map sProj =
      sSpecStep (s.map sProj) (ts,rr,.ins el π a sd) := by
have hts1 : (1:ℕ) ≤ ts :=
  Nat.lt_of_le_of_lt (Nat.zero_le a) hat'
have hsort := sorted
have hinj := injective
have hfresh : (ts, rr, SOp.ins el π a sd).1
    ∉ sIds (s) := by
  intro hmem
  obtain ⟨rec, hrec, hr1⟩ := List.mem_map.mp hmem
  have h1 : rec.1 < ts := late hrec
  rw [hr1] at h1
  exact absurd h1 (Nat.lt_irrefl _)
-- the anchor package: the sentinel serves the root anchor
obtain ⟨ar, cha, harm, hara, har2, hpa, hsa⟩ :
    ∃ (ar : SRec) (cha : SChain), ar ∈ s ∧ ar.1 = a ∧
      ar.2.2 = π ∧ PosSChain cha ∧
      ((cha.map Prod.snd).sum = a ∧
        π = sidedCoordOf Γ cha) := by
  obtain ⟨ch,hp,hs,hc⟩ := chains hmem
  exact ⟨(a,el',π),ch,hmem,rfl,rfl,hp,hs,hc⟩
obtain ⟨hsa, hπeq⟩ := hsa
have harc : ar.2.2 = sidedCoordOf Γ cha := by rw [har2, hπeq]
have hδpos : 1 ≤ ts - a :=
  Nat.le_sub_of_add_le (Nat.add_comm 1 a ▸ hat')
have hcoordnew : π ++ sBlock Γ (sd, ts - a)
    = sidedCoordOf Γ (cha ++ [(sd, ts - a)]) := by
  rw [sidedCoordOf_append, hπeq]
  simp [sidedCoordOf]
have hpos_new : PosSChain (cha ++ [(sd, ts - a)]) := by
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact hpa e h
  · simp at h
    rw [h]
    exact hδpos
have hsum_new : ((cha ++ [(sd, ts - a)]).map Prod.snd).sum
    = ts := by
  rw [List.map_append, List.sum_append, hsa]
  simp
  exact Nat.add_sub_cancel' (Nat.le_of_lt hat')
have hcane : cha ≠ cha ++ [(sd, ts - a)] := by
  intro hcontra
  have := congrArg List.length hcontra
  simp at this
have hkeyne : ∀ rec ∈ s, sKey rec.2.2 ≠
    sKey (((ts : ℕ), el, π ++ sBlock Γ (sd, ts - a))
      : SRec).2.2 := by
  intro rec hrec hcontra
  obtain ⟨chr, hpr, hsr, hcr⟩ := chains hrec
  have hrlt : rec.1 < ts := late hrec
  rw [hcr, show (((ts : ℕ), el, π ++ sBlock Γ (sd, ts - a))
      : SRec).2.2 = sidedCoordOf Γ (cha ++ [(sd, ts - a)])
      from hcoordnew] at hcontra
  have h1 := sidedCoordOf_inj Γ hpr hpos_new
    (sKey_inj hcontra)
  rw [h1, hsum_new] at hsr
  rw [hsr] at hrlt
  exact absurd hrlt (Nat.lt_irrefl _)
show (sUpdate Γ (s) (ts, rr, SOp.ins el π a sd)).map
  sProj = _
simp only [sUpdate]
rw [if_neg hfresh]
-- per-record facts for the divergence analysis
have hrecfacts : ∀ rec ∈ s, rec ≠ ar →
    ∃ chr, PosSChain chr ∧ rec.2.2 = sidedCoordOf Γ chr ∧
      chr ≠ cha ∧ chr ≠ cha ++ [(sd, ts - a)] ∧
      (∀ sd' d rest, chr = cha ++ (sd', d) :: rest →
        d < ts - a) := by
  intro rec hrec hreq
  obtain ⟨chr, hpr, hsr, hcr⟩ := chains hrec
  have hrlt : rec.1 < ts := late hrec
  have hra : rec.1 ≠ a := by
    intro hcontra
    exact hreq (hinj rec hrec ar harm (by rw [hcontra, hara]))
  refine ⟨chr, hpr, hcr, ?_, ?_, ?_⟩
  · intro hcontra
    apply hra
    rw [← hsr, hcontra, hsa]
  · intro hcontra
    rw [hcontra, hsum_new] at hsr
    rw [hsr] at hrlt
    exact absurd hrlt (Nat.lt_irrefl _)
  · intro sd' d rest hcontra
    have h2 := congrArg (fun l => (l.map Prod.snd).sum) hcontra
    simp only [List.map_append, List.sum_append, List.map_cons,
      List.sum_cons] at h2
    rw [hsa, hsr] at h2
    have h3 : a + d ≤ rec.1 := by
      rw [h2]
      omega
    have h4 : a + d < ts := Nat.lt_of_le_of_lt h3 hrlt
    exact Nat.lt_sub_of_add_lt (by rw [Nat.add_comm]; exact h4)
cases sd with
| R =>
    have hiff : ∀ rec ∈ s,
        (keyLt (sKey (((ts : ℕ), el,
            π ++ sBlock Γ (Side.R, ts - a)) : SRec).2.2)
          (sKey rec.2.2) = true ↔
          (rec = ar ∨ keyLt (sKey ar.2.2)
            (sKey rec.2.2) = true)) := by
      intro rec hrec
      by_cases hreq : rec = ar
      · subst hreq
        constructor
        · intro _
          exact Or.inl rfl
        · intro _
          rw [show (((ts : ℕ), el,
              π ++ sBlock Γ (Side.R, ts - a)) : SRec).2.2
              = sidedCoordOf Γ (cha ++ [(Side.R, ts - a)])
              from hcoordnew, harc]
          exact (sdisplay_iff_schainBefore Γ hpa hpos_new
            hcane).mpr (schainBefore.extR cha (ts - a) [])
      · obtain ⟨chr, hpr, hcr, hchne, hchne2, hmax⟩ :=
          hrecfacts rec hrec hreq
        rw [show (((ts : ℕ), el,
            π ++ sBlock Γ (Side.R, ts - a)) : SRec).2.2
            = sidedCoordOf Γ (cha ++ [(Side.R, ts - a)])
            from hcoordnew, harc,
          show rec.2.2 = sidedCoordOf Γ chr from hcr,
          sdisplay_iff_schainBefore Γ hpr hpos_new hchne2,
          or_iff_right hreq,
          sdisplay_iff_schainBefore Γ hpr hpa hchne]
        exact schainBefore_snocR_iff hchne
          (fun d rest h => hmax Side.R d rest h)
    rw [sInsert_map_insAfter hsort harm hara hinj hkeyne hiff ]
    rfl
| L =>
    have hiff : ∀ rec ∈ s,
        (keyLt (sKey rec.2.2)
          (sKey (((ts : ℕ), el,
            π ++ sBlock Γ (Side.L, ts - a)) : SRec).2.2)
            = true ↔
          (rec = ar ∨ keyLt (sKey rec.2.2)
            (sKey ar.2.2) = true)) := by
      intro rec hrec
      by_cases hreq : rec = ar
      · subst hreq
        constructor
        · intro _
          exact Or.inl rfl
        · intro _
          rw [show (((ts : ℕ), el,
              π ++ sBlock Γ (Side.L, ts - a)) : SRec).2.2
              = sidedCoordOf Γ (cha ++ [(Side.L, ts - a)])
              from hcoordnew, harc]
          exact (sdisplay_iff_schainBefore Γ hpos_new hpa
            (Ne.symm hcane)).mpr
            (schainBefore.extL cha (ts - a) [])
      · obtain ⟨chr, hpr, hcr, hchne, hchne2, hmax⟩ :=
          hrecfacts rec hrec hreq
        rw [show (((ts : ℕ), el,
            π ++ sBlock Γ (Side.L, ts - a)) : SRec).2.2
            = sidedCoordOf Γ (cha ++ [(Side.L, ts - a)])
            from hcoordnew, harc,
          show rec.2.2 = sidedCoordOf Γ chr from hcr,
          sdisplay_iff_schainBefore Γ hpos_new hpr
            (Ne.symm hchne2),
          or_iff_right hreq,
          sdisplay_iff_schainBefore Γ hpa hpr (Ne.symm hchne)]
        exact schainBefore_snocL_iff hchne
          (fun d rest h => hmax Side.L d rest h)
    rw [sInsert_map_insBefore hsort harm hara hinj hiff]
    rfl

theorem certified_geometry {Γ : OrderedPrefixCode} {C C' : Configuration (S Γ)}
    (exec : CertifiedExecution (S Γ) (generation Γ) C) {t r : Nat} {op : SOp}
    (one : Step (S Γ) C (.apply t r op) C')
    {v : Version} {s : SState} {ev : Set (Op SOp)}
    (head : C.head r = some v) (version : C.ver v = some (s,ev)) :
    SSorted s ∧
    (∀ a ∈ s, ∀ b ∈ s, a.1 = b.1 → a = b) ∧
    (∀ rec ∈ s, ∃ chain, PosSChain chain ∧ (chain.map Prod.snd).sum = rec.1 ∧
      1 ≤ rec.1 ∧ rec.2.2 = sidedCoordOf Γ chain) ∧
    (∀ rec ∈ s, rec.1 < t) := by
  have good := CertifiedRGAExecution.Sided.canonicalConfig Γ exec
  obtain ⟨ops,perm,order,fold⟩ := good.canonical v s ev version
  change sFold Γ ops = s at fold
  have hon := sHonest_core (sHonest_of_mint exec.mintHonest)
  have supported := good.version_events_supported v s ev version
  have closed := good.version_events_causal v s ev version
  have wf := s_wf_of_enum hon supported (fun a b edge _ hb => closed a b edge hb) perm order
  obtain ⟨chainOf,chainGen⟩ := hon.chain_gen
  have provenance : ∀ rec ∈ s, ∃ o ∈ ops, sIsIns o = true ∧ rec = sRecOf Γ o := by
    rw [← fold]
    exact s_fold_rec_sub Γ ops
  refine ⟨fold ▸ s_fold_sorted Γ wf,?_,?_,?_⟩
  · intro a ha b hb eq
    obtain ⟨oa,hoa,hia,hra⟩ := provenance a ha
    obtain ⟨ob,hob,hib,hrb⟩ := provenance b hb
    have sameTime : oa.1 = ob.1 := by simpa [hra,hrb,sRecOf] using eq
    have same := C.replayContext.ts_unique
      (supported oa ((perm.2 oa).mp hoa)) (supported ob ((perm.2 ob).mp hob)) sameTime
    simp [hra,hrb,same]
  · intro rec hr
    obtain ⟨o,ho,inserted,hrec⟩ := provenance rec hr
    have member := supported o ((perm.2 o).mp ho)
    obtain ⟨positive,coord,sum⟩ := chainGen o member inserted
    obtain ⟨past,_,_,guard⟩ := exec.mintHonest o member
    have pos : 1 ≤ o.1 := by
      rcases o with ⟨ts,rr,action⟩
      cases action with
      | del x => simp [sIsIns] at inserted
      | ins value coordinateBase anchor side => exact Nat.succ_le_of_lt (Nat.zero_lt_of_lt guard.1)
    refine ⟨chainOf o.1,positive,?_,?_,?_⟩
    · simpa [hrec,sRecOf] using sum
    · simpa [hrec,sRecOf] using pos
    · simpa [hrec,sRecOf] using coord
  · intro rec hr
    obtain ⟨o,ho,inserted,hrec⟩ := provenance rec hr
    have clock := EmbedRGAClient.apply_clock one head version o ((perm.2 o).mp ho)
    simpa [hrec,sRecOf] using clock

theorem certified_prepared_physical {Γ : OrderedPrefixCode}
    {C C' : Configuration (S Γ)}
    (exec : CertifiedExecution (S Γ) (generation Γ) C) {t r : Nat} {op : SOp}
    (one : Step (S Γ) C (.apply t r op) C')
    {v : Version} {s : SState} {ev : Set (Op SOp)}
    (head : C.head r = some v) (version : C.ver v = some (s,ev))
    {request : Request} (prepared : prepare s t r request = some (t,r,op)) :
    (sUpdate Γ s (t,r,op)).map sProj = step (s.map sProj) t request := by
  obtain ⟨sorted,injective,chains,late⟩ := certified_geometry exec one head version
  have nd : s.Nodup := by
    apply List.Pairwise.imp ?_ sorted
    intro a b relation eq
    subst b
    simpa [Sal.EmbedRGA.keyLt_irrefl] using relation
  have ids : (s.map Prod.fst).Nodup :=
    List.Nodup.map_on (fun a ha b hb eq => injective a ha b hb eq) nd
  have unique : ((s.map sProj).map Prod.fst).Nodup := by
    simpa [List.map_map,sProj,Function.comp_def] using ids
  have sourceChains : ∀ {rec}, rec ∈ s → ∃ chain, PosSChain chain ∧
      (chain.map Prod.snd).sum = rec.1 ∧ rec.2.2 = sidedCoordOf Γ chain := by
    intro rec hr
    obtain ⟨ch,hp,hs,_,hc⟩ := chains rec hr
    exact ⟨ch,hp,hs,hc⟩
  cases request with
  | delete i =>
    simp only [prepare] at prepared
    split at prepared
    next inside => cases prepared; exact (prepared_delete_physical Γ s t r i inside unique).2
    next => simp at prepared
  | insert i value =>
    simp only [prepare] at prepared
    split at prepared
    next bound =>
      split at prepared
      next empty =>
        subst s
        have zero : i = 0 := by simpa using bound
        subst i
        split at prepared
        next positive => cases prepared; simp [sUpdate,sInsert,sProj,step,sIds]
        next => simp at prepared
      next nonempty =>
        by_cases inside : i < s.length
        · simp only [if_pos inside] at prepared
          split at prepared
          next clock =>
            cases prepared
            have actual := geometric_live_step (rr := r) (el := value) (sd := .L) sorted injective sourceChains
              (fun hr => late _ hr) (selected_mem s i inside) clock
            have mapped : (s.map sProj)[i]! = sProj s[i]! := by
              rw [getElem!_pos _ _ (by simpa using inside),List.getElem_map,getElem!_pos s i inside]
            have positional := before_positional (s.map sProj) i (t,value) unique (by simpa using inside)
            rw [mapped] at positional
            simpa [sSpecStep,step,sProj] using actual.trans positional
          next => simp at prepared
        · simp only [if_neg inside] at prepared
          split at prepared
          next clock =>
            cases prepared
            have index : i = s.length := by omega
            subst i
            have positive : 0 < s.length := by cases s <;> simp_all
            have last : s.length-1 < s.length := by omega
            have actual := geometric_live_step (rr := r) (el := value) (sd := .R) sorted injective sourceChains
              (fun hr => late _ hr) (selected_mem s (s.length-1) last) clock
            have mapped : (s.map sProj)[s.length-1]! = sProj s[s.length-1]! := by
              rw [getElem!_pos _ _ (by simpa using last),List.getElem_map,getElem!_pos s _ last]
            have positional := after_last (s.map sProj) (t,value) unique (by simpa using nonempty)
            simp only [List.length_map] at positional
            rw [mapped] at positional
            have lengths : s.length = (s.map sProj).length := (List.length_map sProj).symm
            simpa only [sSpecStep,step,sProj,lengths,List.take_length,List.drop_length] using actual.trans positional
          next => simp at prepared
    next => simp at prepared

#print axioms certified_prepared_physical
theorem controls :
    prepare [(4,40,[1]),(6,60,[2])] 9 0 (.insert 1 90) =
      some (9,0,.ins 90 [2] 6 .L) ∧
    prepare [(4,40,[1]),(6,60,[2])] 9 0 (.insert 1 90) ≠
      some (9,0,.ins 90 [1] 4 .L) ∧
    prepare [(4,40,[1]),(6,60,[2])] 9 0 (.insert 2 90) =
      some (9,0,.ins 90 [2] 6 .R) ∧
    prepare [(4,40,[1]),(6,60,[2])] 9 0 (.delete 1) = some (9,0,.del 6) ∧
    prepare [] 9 0 (.insert 0 90) = some (9,0,.ins 90 [] 0 .R) ∧
    prepare [] 0 0 (.insert 0 90) = none ∧
    prepare [] 9 0 (.delete 0) = none := by decide

/-- Hand-derived physical controls: a left insertion precedes its live
anchor; deleting the anchor leaves its inserted neighbour. -/
theorem physical_controls :
    let Γ := Sal.EmbedRGA.unaryCode
    let s := sUpdate Γ [] (1,0,.ins 10 [] 0 .R)
    let e := (2,0,SOp.ins 20 (Sal.EmbedRGA.sBlock Γ (.R,1)) 1 .L)
    (sUpdate Γ s e).map sProj = [(2,20),(1,10)] ∧
    (sUpdate Γ s e).map sProj ≠ [(1,10),(2,20)] ∧
    (sUpdate Γ (sUpdate Γ s e) (3,0,.del 1)).map sProj = [(2,20)] ∧
    (sUpdate Γ (sUpdate Γ s e) (3,0,.del 1)).map sProj ≠ [(2,20),(1,10)] := by decide

#print axioms prepared_empty_physical
#print axioms prepared_append_physical
#print axioms prepared_delete_physical
#print axioms prepared_insert_before_physical
#print axioms prepared_canIssue
#print axioms prepared_physical
end Sal.MRDTs.Paper1.SidedRGAClient
