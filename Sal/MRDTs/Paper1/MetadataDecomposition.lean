import Sal.MRDTs.Paper1.MetadataRedistribution

namespace Sal.MRDTs.Paper1.AbstractMRDT
open Foundation
variable {D : MRDTSig}

def RepresentedJoinAtSize (A : Model D) (P : OperationPolicy D.AppOp)
    (R : Representation D) (C : ReplayContext D.toUpdateSig)
    (M : MetadataDependencies A C) (n : Nat) : Prop :=
  ∀ E₁ E₂ l a b π, listPermOf π (E₁ ∪ E₂) → π.length = n →
    Supported C E₁ → Supported C E₂ → M.Closed E₁ → M.Closed E₂ →
    R C (E₁ ∩ E₂) l → R C E₁ a → R C E₂ b →
    Admissible A P R C (E₁ ∪ E₂) (D.merge l a b)

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

/-- A side reconstruction uses smaller Join only for a proper subset of the
current union. If the side is the whole union, guarded causal framing closes
it directly. Hence the premise does not assume the Join being proved. -/
theorem side_decomposition {A : Model D} {P : OperationPolicy D.AppOp}
    {R : Representation D} {scheme : ∀ C, MetadataDependencies A C}
    (laws : Laws A P) (vcs : DependencyMergeVCs A P R scheme)
    (canonical : RepresentsCanonical A P R) (causal : CausalMetadata A P R scheme)
    (substitute : MetadataSubstitution A R)
    (C : ReplayContext D.toUpdateSig) (U : Set (Op D.AppOp))
    (choice : DependencyPeelChoice A P R C (scheme C) U)
    (trans : Transitive C.vis) (irrefl : ∀ x, ¬ C.vis x x)
    (supported : Supported C U) (closed : (scheme C).Closed U)
    (π : List (Op D.AppOp)) (perm : listPermOf π U)
    (IH : ∀ m, m < π.length → RepresentedJoinAtSize A P R C (scheme C) m)
    (E : Set (Op D.AppOp)) (s t : D.State) (subset : E ⊆ U)
    (closedSide : (scheme C).Closed E) (member : choice.event ∈ E)
    (represented : R C E s) (pre : R C (E \ {choice.event}) t) :
    Admissible A P R C E
      (D.merge choice.past t (D.update choice.past choice.event)) := by
  classical
  by_cases equal : E = U
  · subst E
    exact causal_frame laws vcs causal substitute C U choice trans irrefl supported closed t pre
  · obtain ⟨xs,hp,_,_⟩ := canonical C E s represented
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
      exact choice.past_admissible.2
    have result := IH xs.length smaller (E \ {choice.event}) ((scheme C).Past choice.event)
      choice.past t (D.update choice.past choice.event) xs (by simpa [union] using hp) rfl
      (fun x h => supported x (subset h.1)) (fun x h => supported x (subset (pastSub h)))
      ((scheme C).closed_diff_of_max U E choice.event subset closedSide choice.metadata_maximal)
      ((scheme C).past_closed choice.event) base pre choice.reconstructed_past
    simpa only [union] using result

end Sal.MRDTs.Paper1.AbstractMRDT
