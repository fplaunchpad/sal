import Sal.MRDTs.Instances.FugueMax
import Sal.MRDTs.Paper1.Automation.GenericCodeCombinators
import Sal.MRDTs.Paper1.Automation.GenericTerminatedTags

namespace Sal.MRDTs.Paper1.Automation.FugueCodes
open Sal.EmbedRGA PrefixCodes

private def deltaCode (Γ : OrderedPrefixCode) : Code (fun d : Nat => 1 ≤ d) Γ.enc where
  nonempty := nonempty_of_prefixFree _ _
    (fun _ _ hd he ne => Γ.prefixFree hd he ne)
    (by intro d hd; exact ⟨d + 1, by omega, by omega⟩)
  prefixFree := fun _ _ hd he ne => Γ.prefixFree hd he ne

private def symbolCode : Code (fun k : Nat => k ≤ 5) fw :=
  Code.fixedWidth _ _ 2 (by omega) (by intros; rfl) (by
    intro a b ha hb eq
    simp only [fw, List.cons.injEq] at eq
    omega)

private theorem tagSymbols {t : List Nat} (ht : TagOK t) : ∀ k ∈ t, k ≤ 5 :=
  TerminatedTag.allSymbols (by omega) (by omega) ht

private def tagCode : Code TagOK fwTag := by
  have C := symbolCode.words TagOK (fun _ ht => tagSymbols ht)
    (fun _ ht => TerminatedTag.nonempty ht)
    (fun _ _ ha hb ne => TerminatedTag.prefixFree ha hb ne)
  convert C using 1
  funext t
  exact encode_eq fw fwTag rfl (by intros; rfl) t

private theorem fwSymbols {t : List Nat} (ht : TagOK t) : ∀ k ∈ fwTag t, k ≤ 2 := by
  rw [encode_eq fw fwTag rfl (by intros; rfl)]
  apply encode_all
  intro x hx k hk
  have bound := tagSymbols ht x hx
  simp only [fw, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl <;> omega

/-- Prefix-code composition for unchanged tagged R and mirrored L blocks. -/
def blockCode (Γ : OrderedPrefixCode) :
    Code (fun e => 1 ≤ fmδ e ∧ fmTagOK e) (fmBlock Γ) := by
  let rSymbol := fun bit : Bool => symR (!bit)
  let lSymbol := fun bit : Bool => symL (!bit)
  have R := (deltaCode Γ).map rSymbol
    (by intro a b; cases a <;> cases b <;> simp [rSymbol,symR])
  have L := (deltaCode Γ).map lSymbol
    (by intro a b; cases a <;> cases b <;> simp [lSymbol,symL])
  have sum := (tagCode.product R).sum L (by
    intro a b ha hb x hx y hy
    obtain ⟨bit,hbit,rfl⟩ := List.mem_map.mp hy
    have high : 4 ≤ lSymbol bit := by cases bit <;> simp [lSymbol,symL]
    have low : x ≤ 2 := by
      rcases List.mem_append.mp hx with hx | hx
      · exact fwSymbols ha.1 x hx
      · obtain ⟨bit,hbit,rfl⟩ := List.mem_map.mp hx
        cases bit <;> simp [rSymbol,symR]
    omega)
  let label : FMEntry → (List Nat × Nat) ⊕ Nat := fun e =>
    match e with | .R t d => .inl (t,d) | .L d => .inr d
  have C := sum.relabel label (fun e => 1 ≤ fmδ e ∧ fmTagOK e)
    (by
      intro e he
      cases e with
      | R t d => exact ⟨he.2,he.1⟩
      | L d => exact he.1)
    (by intro a b ha hb eq; cases a <;> cases b <;> simp_all [label])
  convert C using 1
  funext e
  cases e <;> simp [label,fmBlock,Sal.EmbedRGA.compl,List.map_map,rSymbol,lSymbol]

private theorem blockSymbols (Γ : OrderedPrefixCode) {e : FMEntry} (valid : fmTagOK e) :
    ∀ k ∈ fmBlock Γ e, k ≠ 3 ∧ k ≤ 5 := by
  cases e with
  | R t d =>
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · have := fwSymbols valid k hk; omega
    · obtain ⟨bit,hbit,rfl⟩ := List.mem_map.mp hk
      cases bit <;> simp [symR]
  | L d =>
    intro k hk
    obtain ⟨bit,hbit,rfl⟩ := List.mem_map.mp hk
    cases bit <;> simp [symL]

/-- The reserved-marker format is closed under minting a native coordinate key. -/
theorem key_tag (Γ : OrderedPrefixCode) {ch : FMChain}
    (positive : PosFMChain ch) (tags : TagsOK ch) (nonempty : ch ≠ []) :
    TagOK (sKey (fmCoordOf Γ ch)) := by
  have symbols : ∀ k ∈ fmCoordOf Γ ch, k ≠ 3 ∧ k ≤ 5 := by
    rw [encode_eq (fmBlock Γ) (fmCoordOf Γ) rfl (by intros; rfl)]
    exact encode_all _ _ ch (fun e he => blockSymbols Γ (tags e he))
  obtain ⟨e,es,rfl⟩ : ∃ e es, ch = e :: es := by
    cases ch with
    | nil => exact (nonempty rfl).elim
    | cons e es => exact ⟨e,es,rfl⟩
  have head : ∃ h rest, fmCoordOf Γ (e :: es) = h :: rest ∧ h ≠ 0 := by
    cases e with
    | R t d =>
      have ht := tags (.R t d) List.mem_cons_self
      obtain ⟨a,body,shape,bound⟩ : ∃ a body, t = a :: body ∧ a ≤ 5 := by
        rcases ht with rfl | ⟨a,body,rfl,_,_,bound,_⟩
        · exact ⟨0,[],rfl,by omega⟩
        · exact ⟨a,body ++ [3],rfl,bound⟩
      refine ⟨(8-a)/3, (8-a)%3 :: (fwTag body ++
        (Sal.EmbedRGA.compl (Γ.enc d)).map symR ++ fmCoordOf Γ es), ?_, by omega⟩
      simp [fmCoordOf,fmBlock,shape,fwTag,fw]
    | L d =>
      obtain ⟨bit,body,shape⟩ : ∃ bit body, Γ.enc d = bit :: body := by
        cases h : Γ.enc d with
        | nil => exact ((deltaCode Γ).nonempty d
            (positive (.L d) List.mem_cons_self) h).elim
        | cons bit body => exact ⟨bit,body,rfl⟩
      refine ⟨symL (!bit), (Sal.EmbedRGA.compl body).map symL ++ fmCoordOf Γ es, ?_, ?_⟩
      · simp [fmCoordOf,fmBlock,shape,Sal.EmbedRGA.compl]
      · cases bit <;> simp [symL]
  obtain ⟨h,rest,shape,nonzero⟩ := head
  refine Or.inr ⟨h,rest,congrArg (fun c => c ++ [3]) shape,nonzero,?_,?_,?_⟩
  · exact (symbols h (by rw [shape]; exact List.mem_cons_self)).1
  · exact (symbols h (by rw [shape]; exact List.mem_cons_self)).2
  · intro k hk
    exact symbols k (by rw [shape]; exact List.mem_cons_of_mem _ hk)

/-- Generic concatenated-code decoding supplies native coordinate injection. -/
theorem coordinate_injective (Γ : OrderedPrefixCode) {a b : FMChain}
    (pa : PosFMChain a) (pb : PosFMChain b) (ta : TagsOK a) (tb : TagsOK b)
    (eq : fmCoordOf Γ a = fmCoordOf Γ b) : a = b := by
  have equations := encode_eq (fmBlock Γ) (fmCoordOf Γ) rfl (by intros; rfl)
  exact encode_injective (blockCode Γ) a b
    (fun e he => ⟨pa e he,ta e he⟩) (fun e he => ⟨pb e he,tb e he⟩)
    (by simpa only [equations] using eq)
end Sal.MRDTs.Paper1.Automation.FugueCodes
