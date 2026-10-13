import Sal.MRDTs.Paper1.Automation.GenericGuardedFold
import Sal.MRDTs.Instances.EmbedRGASequential

/-! A checked boundary experiment on the production embedded RGA. The generic
engine owns history induction. The local obligation below exposes the finite
insert/delete cases and the ordered-chain adjacency argument; it does not call
`embed_seq_sound` or any completed history bridge. The existing prefix invariant
helpers (chain provenance, sortedness, record identity) remain explicit inputs
to that local argument. The implementation, spec, and sequential discipline
are unchanged. -/
namespace Sal.MRDTs.Paper1.Automation.EmbeddedSequentialBridge
open Sal.MRDTs.Foundation Sal.MRDTs.Instances.EmbedRGA
open Sal.EmbedRGA (OrderedPrefixCode PosChain coordOf coordOf_inj
  coordOf_append key_inj keyLt keyLe key keyLt_total keyLt_irrefl
  keyLt_asymm chainBefore chainBefore_total display_iff_chainBefore)
variable {α : Type} [DecidableEq α] [Inhabited α]

theorem projection_step {Γ : OrderedPrefixCode}
    (ρ : List (Op (EOp α))) (o : Op (EOp α))
    (hOK : eSeqOK Γ (ρ ++ [o])) :
    (eFold Γ (ρ ++ [o])).map eProj =
      eSpecStep ((eFold Γ ρ).map eProj) o := by
  have hOK' := eSeqOK_prefix hOK
  have hwf' := eWf_of_seqOK hOK'
  rw [eFold_snoc]
  obtain ⟨ts, r, op⟩ := o
  cases op with
  | del x =>
      show ((eFold Γ ρ).filter (fun r => decide (r.1 ≠ x))).map eProj
        = _
      exact map_filter_project eProj (fun p => decide (p.1 ≠ x)) (eFold Γ ρ)
  | ins el π a =>
      have happ := (hOK ρ (ts, r, .ins el π a) [] (by simp)).2
      simp only [eApplicable] at happ
      obtain ⟨hat, hcase⟩ := happ
      have hat' : a < ts := hat
      have hfresh : (ts, r, EOp.ins el π a).1 ∉ eIds (eFold Γ ρ) := by
        intro hmem
        obtain ⟨rec, hrec, hr1⟩ := List.mem_map.mp hmem
        have h1 : rec.1 < ts := e_fold_id_lt hOK (by simp [eIsIns]) hrec
        have h2 : rec.1 = ts := hr1
        omega
      show (eUpdate Γ (eFold Γ ρ) (ts, r, EOp.ins el π a)).map eProj
        = _
      simp only [eUpdate]
      rw [if_neg hfresh]
      rcases hcase with ⟨rfl, rfl⟩ | ⟨el', hmem⟩
      · -- front insert: the fresh stamp beats every chain
        have hall : ∀ y ∈ eFold Γ ρ, keyLt (key y.2.2)
            (key (((ts : ℕ), el,
              ([] : List Bool) ++ Γ.enc (ts - 0)) : ERec α).2.2)
            = true := by
          intro y hy
          obtain ⟨chy, hpy, hsy, hy1, hcy⟩ := e_fold_chain hOK' hy
          have hylt : y.1 < ts := e_fold_id_lt hOK (by simp [eIsIns]) hy
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
        have hsort := e_fold_sorted Γ hwf'
        have hinj := e_fold_fst_inj hwf'
        obtain ⟨cha, hpa, hsa, ha1, hca⟩ := e_fold_chain hOK' hmem
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
        have hkeyne : ∀ rec ∈ eFold Γ ρ, key rec.2.2 ≠
            key (((ts : ℕ), el, π ++ Γ.enc (ts - a)) : ERec α).2.2 := by
          intro rec hrec hcontra
          obtain ⟨chr, hpr, hsr, -, hcr⟩ := e_fold_chain hOK' hrec
          have hrlt : rec.1 < ts := e_fold_id_lt hOK (by simp [eIsIns]) hrec
          rw [hcr, show (((ts : ℕ), el, π ++ Γ.enc (ts - a)) :
              ERec α).2.2 = coordOf Γ (cha ++ [ts - a]) from hcoordnew]
            at hcontra
          have h1 := coordOf_inj Γ hpr hpos_new (key_inj hcontra)
          have h2 := congrArg List.sum h1
          rw [hsr, List.sum_append, hsum_a] at h2
          simp at h2
          omega
        have hiff : ∀ rec ∈ eFold Γ ρ,
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
          · obtain ⟨chr, hpr, hsr, hr1, hcr⟩ := e_fold_chain hOK' hrec
            have hrlt : rec.1 < ts := e_fold_id_lt hOK (by simp [eIsIns]) hrec
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

/-- The original production sequential statement, derived by generic induction
from the datatype's local projection obligation. -/
theorem sound {Γ : OrderedPrefixCode} {ρ : List (Op (EOp α))}
    (hOK : eSeqOK Γ ρ) : (eFold Γ ρ).map eProj = eSpecFold ρ := by
  exact guarded_fold_projection (eFold Γ) eSpecFold (List.map eProj) eSpecStep
    (eSeqOK Γ) rfl eSpecFold_snoc
    (fun _ _ h => eSeqOK_prefix h) projection_step hOK

#print axioms sound
end Sal.MRDTs.Paper1.Automation.EmbeddedSequentialBridge
