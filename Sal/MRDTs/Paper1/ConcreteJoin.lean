import Sal.MRDTs.Paper1.ConcreteMetadata
import Sal.MRDTs.Paper1.GuardedReplay

namespace Sal.MRDTs.Paper1.ConcreteMRDT.Raw
open Foundation Classical
variable {D : MRDTSig}

structure Context (P : OperationPolicy D.AppOp)
    (scheme : ∀ C, MetadataDependencies C) (C : ReplayContext D.toUpdateSig)
    (E₁ E₂ : Set (Op D.AppOp)) (e : Op D.AppOp) : Prop where
  trans : Transitive C.vis
  irrefl : ∀ x, ¬ C.vis x x
  supported₁ : Supported C E₁
  supported₂ : Supported C E₂
  closed₁ : (scheme C).Closed E₁
  closed₂ : (scheme C).Closed E₂
  semantic : ∀ x ∈ E₁ ∪ E₂, x ≠ e → ¬ paperOrder P C (E₁ ∪ E₂) e x
  metadata : ∀ x ∈ E₁ ∪ E₂, x ≠ e → ¬ (scheme C).before e x

structure PeelChoice (P : OperationPolicy D.AppOp)
    (R : Representation D) (C : ReplayContext D.toUpdateSig)
    (M : MetadataDependencies C) (U : Set (Op D.AppOp)) where
  event : Op D.AppOp
  member : event ∈ U
  semantic_maximal : ∀ x ∈ U, x ≠ event → ¬ paperOrder P C U event x
  metadata_maximal : ∀ x ∈ U, x ≠ event → ¬ M.before event x
  remainder : D.State
  past : D.State
  remainder_rep : R C (U \ {event}) remainder
  past_rep : R C (M.Past event \ {event}) past
  reconstructed_past : R C (M.Past event) (D.update past event)
  reconstructed_union : R C U (D.update remainder event)

/-- The five usual algebraic equations, guarded by indexed representations.
The local/shared smaller-union representation is evidence produced by the
strictly smaller induction call, never a global Join hypothesis. Their side
reconstruction evidence is likewise derived on proper subsets, or by the
causal equation for the whole union. -/
structure MergeVCs (P : OperationPolicy D.AppOp)
    (R : Representation D) (scheme : ∀ C, MetadataDependencies C) : Prop where
  merge_comm : ∀ C E₁ E₂ l a b,
    Supported C E₁ → Supported C E₂ → (scheme C).Closed E₁ → (scheme C).Closed E₂ →
    R C (E₁ ∩ E₂) l → R C E₁ a → R C E₂ b → D.merge l a b = D.merge l b a
  init : ∀ C E s, Supported C E → (scheme C).Closed E → R C E s →
    D.merge D.init D.init s = s
  causal_delta : ∀ C U s B e,
    Transitive C.vis → (∀ x, ¬ C.vis x x) → Supported C U → (scheme C).Closed U → e ∈ U →
    (∀ x ∈ U, x ≠ e → ¬ paperOrder P C U e x) →
    (∀ x ∈ U, x ≠ e → ¬ (scheme C).before e x) →
    R C (U \ {e}) s → R C ((scheme C).Past e \ {e}) B →
    R C ((scheme C).Past e) (D.update B e) → R C U (D.update s e) →
    D.merge B s (D.update B e) = D.update s e
  local_redistribute : ∀ C E₁ E₂ l B t b e, Context P scheme C E₁ E₂ e → e ∈ E₁ → e ∉ E₂ →
    R C (E₁ ∩ E₂) l → R C ((scheme C).Past e \ {e}) B →
    R C (E₁ \ {e}) t → R C E₂ b → R C ((scheme C).Past e) (D.update B e) →
    R C E₁ (D.merge B t (D.update B e)) →
    R C ((E₁ ∪ E₂) \ {e}) (D.merge l t b) →
    D.merge l (D.merge B t (D.update B e)) b =
      D.merge B (D.merge l t b) (D.update B e)
  shared : ∀ C E₁ E₂ t₀ t₁ t₂ B e, Context P scheme C E₁ E₂ e → e ∈ E₁ → e ∈ E₂ →
    R C ((E₁ ∩ E₂) \ {e}) t₀ → R C ((scheme C).Past e \ {e}) B →
    R C (E₁ \ {e}) t₁ → R C (E₂ \ {e}) t₂ → R C ((scheme C).Past e) (D.update B e) →
    R C (E₁ ∩ E₂) (D.merge B t₀ (D.update B e)) →
    R C E₁ (D.merge B t₁ (D.update B e)) → R C E₂ (D.merge B t₂ (D.update B e)) →
    R C ((E₁ ∪ E₂) \ {e}) (D.merge t₀ t₁ t₂) →
    D.merge (D.merge B t₀ (D.update B e)) (D.merge B t₁ (D.update B e))
      (D.merge B t₂ (D.update B e)) = D.merge B (D.merge t₀ t₁ t₂) (D.update B e)

def Unique (R : Representation D) : Prop := ∀ C E a b, R C E a → R C E b → a = b

structure ReplaySupply (P : OperationPolicy D.AppOp)
    (R : Representation D) (scheme : ∀ C, MetadataDependencies C)
    (C : ReplayContext D.toUpdateSig) where
  represented : ∀ E π, listPermOf π E → Supported C E → ∃ s, R C E s
  peel : ∀ E s, R C E s → Supported C E → E.Nonempty → (scheme C).Closed E →
    Nonempty (PeelChoice P R C (scheme C) E)

private theorem causal_frame {P : OperationPolicy D.AppOp}
    {R : Representation D} {scheme : ∀ C, MetadataDependencies C}
    (vcs : MergeVCs P R scheme) (unique : Unique R)
    (C : ReplayContext D.toUpdateSig) (U : Set (Op D.AppOp))
    (choice : PeelChoice P R C (scheme C) U)
    (trans : Transitive C.vis) (irrefl : ∀ x, ¬ C.vis x x)
    (supported : Supported C U) (closed : (scheme C).Closed U)
    (mid : D.State) (represented : R C (U \ {choice.event}) mid) :
    R C U (D.merge choice.past mid (D.update choice.past choice.event)) := by
  have eq := unique C _ mid choice.remainder represented choice.remainder_rep
  rw [eq, vcs.causal_delta C U choice.remainder choice.past choice.event trans irrefl
    supported closed choice.member choice.semantic_maximal choice.metadata_maximal
    choice.remainder_rep choice.past_rep choice.reconstructed_past choice.reconstructed_union]
  exact choice.reconstructed_union

def JoinAtSize (P : OperationPolicy D.AppOp)
    (R : Representation D) (C : ReplayContext D.toUpdateSig)
    (M : MetadataDependencies C) (n : Nat) : Prop :=
  ∀ E₁ E₂ l a b π, listPermOf π (E₁ ∪ E₂) → π.length = n →
    Supported C E₁ → Supported C E₂ → M.Closed E₁ → M.Closed E₂ →
    R C (E₁ ∩ E₂) l → R C E₁ a → R C E₂ b → R C (E₁ ∪ E₂) (D.merge l a b)

private theorem enumeration_length_lt {β : Type} {xs ys : List β}
    {E U : Set β} {x : β} (h : listPermOf xs E) (k : listPermOf ys U)
    (subset : E ⊆ U) (member : x ∈ U) (absent : x ∉ E) : xs.length < ys.length := by
  have nd : (x :: xs).Nodup := by
    rw [List.nodup_cons]
    exact ⟨fun mem => absent ((h.2 x).mp mem),h.1⟩
  have subperm : List.Subperm (x :: xs) ys := by
    refine List.subperm_of_subset nd ?_
    intro a mem
    rcases List.mem_cons.mp mem with rfl | mem
    · exact (k.2 a).mpr member
    · exact (k.2 a).mpr (subset ((h.2 a).mp mem))
  have bound := subperm.length_le
  simp only [List.length_cons] at bound
  omega

theorem side_decomposition {P : OperationPolicy D.AppOp}
    {R : Representation D} {scheme : ∀ C, MetadataDependencies C}
    (vcs : MergeVCs P R scheme) (unique : Unique R)
    (finite : ∀ C E s, R C E s → ∃ π, listPermOf π E)
    (C : ReplayContext D.toUpdateSig) (U : Set (Op D.AppOp))
    (choice : PeelChoice P R C (scheme C) U)
    (trans : Transitive C.vis) (irrefl : ∀ x, ¬ C.vis x x)
    (supported : Supported C U) (closed : (scheme C).Closed U)
    (π : List (Op D.AppOp)) (perm : listPermOf π U)
    (IH : ∀ m, m < π.length → JoinAtSize P R C (scheme C) m)
    (E : Set (Op D.AppOp)) (s t : D.State) (subset : E ⊆ U)
    (closedSide : (scheme C).Closed E) (member : choice.event ∈ E)
    (represented : R C E s) (pre : R C (E \ {choice.event}) t) :
    R C E
      (D.merge choice.past t (D.update choice.past choice.event)) := by
  classical
  by_cases equal : E = U
  · subst E
    exact causal_frame vcs unique C U choice trans irrefl supported closed t pre
  · obtain ⟨xs,hp⟩ := finite C E s represented
    obtain ⟨x,hx,absent⟩ : ∃ x ∈ U, x ∉ E := by
      by_contra h
      push_neg at h
      exact equal (Set.Subset.antisymm subset h)
    have smaller := enumeration_length_lt hp perm subset hx absent
    have pastSub := (scheme C).past_subset E choice.event closedSide member
    have intersection : (E \ {choice.event}) ∩ (scheme C).Past choice.event =
        (scheme C).Past choice.event \ {choice.event} := by
      ext x
      constructor
      · exact fun h => ⟨h.2,h.1.2⟩
      · exact fun h => ⟨⟨pastSub h.1,h.2⟩,h.1⟩
    have union : (E \ {choice.event}) ∪ (scheme C).Past choice.event = E := by
      ext x
      constructor
      · exact fun h => h.elim (fun h => h.1) (fun h => pastSub h)
      · intro hx
        by_cases equal : x = choice.event
        · exact Or.inr (Or.inl equal)
        · exact Or.inl ⟨hx,equal⟩
    have base : R C ((E \ {choice.event}) ∩ (scheme C).Past choice.event) choice.past := by
      rw [intersection]
      exact choice.past_rep
    have result := IH xs.length smaller (E \ {choice.event}) ((scheme C).Past choice.event)
      choice.past t (D.update choice.past choice.event) xs (by simpa [union] using hp) rfl
      (fun x h => supported x (subset h.1)) (fun x h => supported x (subset (pastSub h)))
      ((scheme C).closed_diff_of_max U E choice.event subset closedSide choice.metadata_maximal)
      ((scheme C).past_closed choice.event) base pre choice.reconstructed_past
    simpa only [union] using result


private theorem local_step {P : OperationPolicy D.AppOp}
    {R : Representation D} {scheme : ∀ C, MetadataDependencies C}
    (vcs : MergeVCs P R scheme) (unique : Unique R)
    (C : ReplayContext D.toUpdateSig) (E₁ E₂ : Set (Op D.AppOp))
    (choice : PeelChoice P R C (scheme C) (E₁ ∪ E₂))
    (ctx : Context P scheme C E₁ E₂ choice.event)
    (l a b t : D.State) (member : choice.event ∈ E₁) (absent : choice.event ∉ E₂)
    (base : R C (E₁ ∩ E₂) l) (side : R C E₁ a)
    (other : R C E₂ b) (pre : R C (E₁ \ {choice.event}) t)
    (dec : R C E₁ (D.merge choice.past t (D.update choice.past choice.event)))
    (smaller : R C ((E₁ ∪ E₂) \ {choice.event}) (D.merge l t b)) :
    R C (E₁ ∪ E₂) (D.merge l a b) := by
  have target := causal_frame vcs unique C (E₁ ∪ E₂) choice ctx.trans ctx.irrefl
    (fun x h => h.elim (ctx.supported₁ x) (ctx.supported₂ x))
    (fun x y edge h => h.elim (fun h => Or.inl (ctx.closed₁ x y edge h))
      (fun h => Or.inr (ctx.closed₂ x y edge h))) (D.merge l t b) smaller
  rw [unique C E₁ a _ side dec,
    vcs.local_redistribute C E₁ E₂ l choice.past t b choice.event ctx member absent
      base choice.past_rep pre other choice.reconstructed_past dec smaller]
  exact target

private theorem shared_step {P : OperationPolicy D.AppOp}
    {R : Representation D} {scheme : ∀ C, MetadataDependencies C}
    (vcs : MergeVCs P R scheme) (unique : Unique R)
    (C : ReplayContext D.toUpdateSig) (E₁ E₂ : Set (Op D.AppOp))
    (choice : PeelChoice P R C (scheme C) (E₁ ∪ E₂))
    (ctx : Context P scheme C E₁ E₂ choice.event)
    (l a b t₀ t₁ t₂ : D.State) (mem₁ : choice.event ∈ E₁) (mem₂ : choice.event ∈ E₂)
    (base : R C (E₁ ∩ E₂) l) (side₁ : R C E₁ a) (side₂ : R C E₂ b)
    (pre₀ : R C ((E₁ ∩ E₂) \ {choice.event}) t₀)
    (pre₁ : R C (E₁ \ {choice.event}) t₁) (pre₂ : R C (E₂ \ {choice.event}) t₂)
    (dec₀ : R C (E₁ ∩ E₂) (D.merge choice.past t₀ (D.update choice.past choice.event)))
    (dec₁ : R C E₁ (D.merge choice.past t₁ (D.update choice.past choice.event)))
    (dec₂ : R C E₂ (D.merge choice.past t₂ (D.update choice.past choice.event)))
    (smaller : R C ((E₁ ∪ E₂) \ {choice.event}) (D.merge t₀ t₁ t₂)) :
    R C (E₁ ∪ E₂) (D.merge l a b) := by
  have target := causal_frame vcs unique C (E₁ ∪ E₂) choice ctx.trans ctx.irrefl
    (fun x h => h.elim (ctx.supported₁ x) (ctx.supported₂ x))
    (fun x y edge h => h.elim (fun h => Or.inl (ctx.closed₁ x y edge h))
      (fun h => Or.inr (ctx.closed₂ x y edge h))) (D.merge t₀ t₁ t₂) smaller
  rw [unique C _ l _ base dec₀, unique C _ a _ side₁ dec₁, unique C _ b _ side₂ dec₂,
    vcs.shared C E₁ E₂ t₀ t₁ t₂ choice.past choice.event ctx mem₁ mem₂
      pre₀ choice.past_rep pre₁ pre₂ choice.reconstructed_past dec₀ dec₁ dec₂ smaller]
  exact target

theorem join_at_sizes {P : OperationPolicy D.AppOp}
    {R : Representation D} {scheme : ∀ C, MetadataDependencies C}
    (vcs : MergeVCs P R scheme) (unique : Unique R)
    (initial : ∀ C E s, R C E s → R C ∅ D.init)
    (finite : ∀ C E s, R C E s → ∃ π, listPermOf π E)
    (C : ReplayContext D.toUpdateSig) (trans : Transitive C.vis)
    (irrefl : ∀ x, ¬ C.vis x x)
    (supply : ∀ E π, listPermOf π E → Supported C E → ∃ s, R C E s)
    (peel : ∀ E s, R C E s → Supported C E → E.Nonempty → (scheme C).Closed E →
      Nonempty (PeelChoice P R C (scheme C) E)) :
    ∀ n, JoinAtSize P R C (scheme C) n := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro E₁ E₂ l a b π perm length sup₁ sup₂ closed₁ closed₂ hl ha hb
    rcases Set.eq_empty_or_nonempty E₁ with empty | nonempty₁
    · subst E₁
      have el : l = D.init := unique C ∅ l D.init (by simpa using hl) (initial C E₂ b hb)
      have ea : a = D.init := unique C ∅ a D.init ha (initial C E₂ b hb)
      rw [el, ea, vcs.init C E₂ b sup₂ closed₂ hb]
      simpa using hb
    rcases Set.eq_empty_or_nonempty E₂ with empty | nonempty₂
    · subst E₂
      rw [vcs.merge_comm C E₁ ∅ l a b sup₁ sup₂ closed₁ closed₂ hl ha hb]
      have el : l = D.init := unique C ∅ l D.init (by simpa using hl) (initial C E₁ a ha)
      have eb : b = D.init := unique C ∅ b D.init hb (initial C E₁ a ha)
      rw [el, eb, vcs.init C E₁ a sup₁ closed₁ ha]
      simpa using ha
    have supU : Supported C (E₁ ∪ E₂) := fun x h => h.elim (sup₁ x) (sup₂ x)
    have closedU : (scheme C).Closed (E₁ ∪ E₂) := fun x y edge h =>
      h.elim (fun h => Or.inl (closed₁ x y edge h)) (fun h => Or.inr (closed₂ x y edge h))
    obtain ⟨s,hs⟩ := supply (E₁ ∪ E₂) π perm supU
    obtain ⟨choice⟩ := peel (E₁ ∪ E₂) s hs supU
      (nonempty₁.mono Set.subset_union_left) closedU
    have recurs : ∀ m, m < π.length → JoinAtSize P R C (scheme C) m := by
      simpa only [length] using IH
    have eventMem := (perm.2 choice.event).mpr choice.member
    have permDiff : listPermOf (π.filter (· ≠ choice.event)) ((E₁ ∪ E₂) \ {choice.event}) :=
      filter_ne_listPermOf_basic (D := D.toUpdateSig) perm eventMem
    have smaller : (π.filter (· ≠ choice.event)).length < n := by
      have size := listPermOf_diff_length perm eventMem permDiff
      have positive := List.length_pos_of_mem eventMem
      omega
    have closedPre₁ := (scheme C).closed_diff_of_max (E₁ ∪ E₂) E₁ choice.event
      Set.subset_union_left closed₁ choice.metadata_maximal
    have closedPre₂ := (scheme C).closed_diff_of_max (E₁ ∪ E₂) E₂ choice.event
      Set.subset_union_right closed₂ choice.metadata_maximal
    have ctx : Context P scheme C E₁ E₂ choice.event :=
      ⟨trans,irrefl,sup₁,sup₂,closed₁,closed₂,choice.semantic_maximal,choice.metadata_maximal⟩
    have sideSupply : ∀ E, E ⊆ E₁ ∪ E₂ → ∃ t, R C (E \ {choice.event}) t := by
      intro E subset
      obtain ⟨xs,hp⟩ := enumeration_subset perm
        (show E \ {choice.event} ⊆ E₁ ∪ E₂ from fun _ h => subset h.1)
      obtain ⟨t,ht⟩ := supply _ xs hp (fun x h => supU x (subset h.1))
      exact ⟨t,ht⟩
    by_cases member₁ : choice.event ∈ E₁
    · obtain ⟨t₁,ht₁⟩ := sideSupply E₁ Set.subset_union_left
      have dec₁ := side_decomposition vcs unique finite C (E₁ ∪ E₂)
        choice trans irrefl supU closedU π perm recurs E₁ a t₁
        Set.subset_union_left closed₁ member₁ ha ht₁
      by_cases member₂ : choice.event ∈ E₂
      · obtain ⟨t₂,ht₂⟩ := sideSupply E₂ Set.subset_union_right
        obtain ⟨t₀,ht₀⟩ := sideSupply (E₁ ∩ E₂) (fun _ h => Or.inl h.1)
        have closedBase : (scheme C).Closed (E₁ ∩ E₂) :=
          fun x y edge h => ⟨closed₁ x y edge h.1,closed₂ x y edge h.2⟩
        have dec₂ := side_decomposition vcs unique finite C (E₁ ∪ E₂)
          choice trans irrefl supU closedU π perm recurs E₂ b t₂
          Set.subset_union_right closed₂ member₂ hb ht₂
        have dec₀ := side_decomposition vcs unique finite C (E₁ ∪ E₂)
          choice trans irrefl supU closedU π perm recurs (E₁ ∩ E₂) l t₀
          (fun _ h => Or.inl h.1) closedBase ⟨member₁,member₂⟩ hl ht₀
        have union : (E₁ \ {choice.event}) ∪ (E₂ \ {choice.event}) =
            (E₁ ∪ E₂) \ {choice.event} := by ext x; simp only [Set.mem_union,Set.mem_diff]; tauto
        have intersection : (E₁ \ {choice.event}) ∩ (E₂ \ {choice.event}) =
            (E₁ ∩ E₂) \ {choice.event} := by ext x; simp only [Set.mem_inter_iff,Set.mem_diff]; tauto
        have mid := IH _ smaller (E₁ \ {choice.event}) (E₂ \ {choice.event}) t₀ t₁ t₂
          (π.filter (· ≠ choice.event)) (by simpa only [union] using permDiff) rfl
          (fun x h => sup₁ x h.1) (fun x h => sup₂ x h.1) closedPre₁ closedPre₂
          (by simpa only [intersection] using ht₀) ht₁ ht₂
        exact shared_step vcs unique C E₁ E₂ choice ctx
          l a b t₀ t₁ t₂ member₁ member₂ hl ha hb ht₀ ht₁ ht₂ dec₀ dec₁ dec₂
          (by simpa only [union] using mid)
      · have union : (E₁ \ {choice.event}) ∪ E₂ = (E₁ ∪ E₂) \ {choice.event} := by
          ext x
          simp only [Set.mem_union,Set.mem_diff,Set.mem_singleton_iff]
          constructor
          · rintro (h | h)
            · exact ⟨Or.inl h.1,h.2⟩
            · exact ⟨Or.inr h,fun equal => member₂ (equal ▸ h)⟩
          · rintro ⟨h | h,ne⟩
            · exact Or.inl ⟨h,ne⟩
            · exact Or.inr h
        have intersection : (E₁ \ {choice.event}) ∩ E₂ = E₁ ∩ E₂ := by
          ext x
          simp only [Set.mem_inter_iff,Set.mem_diff,Set.mem_singleton_iff]
          constructor
          · exact fun h => ⟨h.1.1,h.2⟩
          · exact fun h => ⟨⟨h.1,fun equal => member₂ (equal ▸ h.2)⟩,h.2⟩
        have mid := IH _ smaller (E₁ \ {choice.event}) E₂ l t₁ b
          (π.filter (· ≠ choice.event)) (by simpa only [union] using permDiff) rfl
          (fun x h => sup₁ x h.1) sup₂ closedPre₁ closed₂
          (by simpa only [intersection] using hl) ht₁ hb
        exact local_step vcs unique C E₁ E₂ choice ctx
          l a b t₁ member₁ member₂ hl ha hb ht₁
          dec₁ (by simpa only [union] using mid)
    · have member₂ : choice.event ∈ E₂ := choice.member.resolve_left member₁
      obtain ⟨t₂,ht₂⟩ := sideSupply E₂ Set.subset_union_right
      have dec₂ := side_decomposition vcs unique finite C (E₁ ∪ E₂)
        choice trans irrefl supU closedU π perm recurs E₂ b t₂
        Set.subset_union_right closed₂ member₂ hb ht₂
      have union : (E₂ \ {choice.event}) ∪ E₁ = (E₁ ∪ E₂) \ {choice.event} := by
        ext x
        simp only [Set.mem_union,Set.mem_diff,Set.mem_singleton_iff]
        constructor
        · rintro (h | h)
          · exact ⟨Or.inr h.1,h.2⟩
          · exact ⟨Or.inl h,fun equal => member₁ (equal ▸ h)⟩
        · rintro ⟨h | h,ne⟩
          · exact Or.inr h
          · exact Or.inl ⟨h,ne⟩
      have intersection : (E₂ \ {choice.event}) ∩ E₁ = E₁ ∩ E₂ := by
        ext x
        simp only [Set.mem_inter_iff,Set.mem_diff,Set.mem_singleton_iff]
        constructor
        · exact fun h => ⟨h.2,h.1.1⟩
        · exact fun h => ⟨⟨h.2,fun equal => member₁ (equal ▸ h.1)⟩,h.1⟩
      have mid := IH _ smaller (E₂ \ {choice.event}) E₁ l t₂ a
        (π.filter (· ≠ choice.event)) (by simpa only [union] using permDiff) rfl
        (fun x h => sup₂ x h.1) sup₁ closedPre₂ closed₁
        (by simpa only [intersection] using hl) ht₂ ha
      have midU : R C ((E₁ ∪ E₂) \ {choice.event}) (D.merge l t₂ a) := by
        simpa only [union] using mid
      let swappedChoice : PeelChoice P R C (scheme C) (E₂ ∪ E₁) := {
        event := choice.event
        member := by simpa only [Set.union_comm] using choice.member
        semantic_maximal := by simpa only [Set.union_comm] using choice.semantic_maximal
        metadata_maximal := by simpa only [Set.union_comm] using choice.metadata_maximal
        remainder := choice.remainder
        past := choice.past
        remainder_rep := by simpa only [Set.union_comm] using choice.remainder_rep
        past_rep := choice.past_rep
        reconstructed_past := choice.reconstructed_past
        reconstructed_union := by simpa only [Set.union_comm] using choice.reconstructed_union }
      have swappedCtx : Context P scheme C E₂ E₁ swappedChoice.event := by
        simpa only [swappedChoice,Set.union_comm] using
          (show Context P scheme C E₂ E₁ choice.event from
            ⟨trans,irrefl,sup₂,sup₁,closed₂,closed₁,
              by simpa only [Set.union_comm] using choice.semantic_maximal,
              by simpa only [Set.union_comm] using choice.metadata_maximal⟩)
      have result := local_step vcs unique C E₂ E₁ swappedChoice swappedCtx
        l b a t₂ (by simpa only [swappedChoice] using member₂)
        (by simpa only [swappedChoice] using member₁)
        (by simpa only [Set.inter_comm] using (show R C (E₁ ∩ E₂) l from
          hl)) hb ha
        (by simpa only [swappedChoice] using ht₂)
        (by simpa only [swappedChoice] using dec₂)
        (by simpa only [swappedChoice,Set.union_comm] using midU)
      rw [vcs.merge_comm C E₁ E₂ l a b sup₁ sup₂ closed₁ closed₂ hl ha hb]
      simpa only [Set.union_comm] using result


/-- The five raw equality VCs derive Join by strict finite-history induction.
No merge-preservation or canonical-merge premise is supplied. -/
theorem representationJoin_of_vcs {P : OperationPolicy D.AppOp}
    {R : Representation D} {scheme : ∀ C, MetadataDependencies C}
    (vcs : MergeVCs P R scheme) (unique : Unique R)
    (initial : ∀ C E s, R C E s → R C ∅ D.init)
    (finite : ∀ C E s, R C E s → ∃ π, listPermOf π E)
    (supply : ∀ C E₁ E₂ a b, Transitive C.vis → (∀ x, ¬ C.vis x x) →
      Supported C E₁ → Supported C E₂ → R C E₁ a → R C E₂ b →
      ReplaySupply P R scheme C) : RepresentationJoin R := by
  intro C E₁ E₂ l a b trans irrefl sup₁ sup₂ closed₁ closed₂ hl ha hb
  obtain ⟨π₁,hp₁⟩ := finite C E₁ a ha
  obtain ⟨π₂,hp₂⟩ := finite C E₂ b hb
  have perm := listPermOf_union (D := D.toUpdateSig) hp₁ hp₂
  have kit := supply C E₁ E₂ a b trans irrefl sup₁ sup₂ ha hb
  have sizes := join_at_sizes vcs unique initial finite C trans irrefl
    kit.represented kit.peel
  exact sizes _ E₁ E₂ l a b _ perm rfl sup₁ sup₂
    (fun x y edge h => closed₁ x y ((scheme C).causal x y edge) h)
    (fun x y edge h => closed₂ x y ((scheme C).causal x y edge) h) hl ha hb

end Sal.MRDTs.Paper1.ConcreteMRDT.Raw
