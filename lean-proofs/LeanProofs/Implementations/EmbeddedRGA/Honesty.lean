import LeanProofs_no_spec_non_comm.Implementations.EmbeddedRGA.Join

/-!
# Embedded RGA: the two context obligations, from issuance

`CoordHonest` and `DelBorn` are the only hypotheses the development carries
about the context. Both come from the issuance guard.

`DelBorn` would be circular if it went through `fold_live`, which assumes
`BirthFirst`, which is what `DelBorn` is for. `mem_fold_writer` breaks the
circle: every record of a replay is written by an insertion of the list,
and that half needs no ordering at all. A deletion's guard asks for its
target to be live in the causal-past replay, so the writer of that record
is an insertion of the causal past.

`CoordHonest` is the unique-decodability argument. An insertion carries its
anchor's coordinate, so `enc_append_cancel` splits a shared coordinate into
a shared prefix and a shared codeword. The prefix is either empty, forcing
both anchors to the root, or it is itself a written coordinate, and then
the two anchor records are compared by induction on coordinate length,
which the anchor's strictly shortens. Issuance supplies both halves: that
the carried prefix is genuine, and that the clock exceeds the anchor, which
is what turns equal codewords into equal timestamps.
-/

namespace LeanProofs.NoSpecNonComm.Implementations.EmbeddedRGA

open Artifact.MRDTs Artifact.MRDTs.Foundation Artifact.MRDTs.Paper1
open LeanProofs.NoSpecNonComm.Interface

variable {Γ : Scheme} {α : Type} [DecidableEq α] {Q : QueryOf Γ α}

/-- Every record of a replay is written by an insertion of the list. No
ordering is needed, which is what breaks the circularity: this is the half
of `fold_live` that `DelBorn` itself is proved from. -/
theorem mem_fold_writer : ∀ {xs : List (Op (AppOp Γ α))} {z : Record Γ α},
    z ∈ xs.foldl step [] → ∃ e ∈ xs, Writes e z := by
  intro xs
  induction xs using List.reverseRecOn with
  | nil => intro z hz; simp at hz
  | append_singleton xs e ih =>
    intro z hz
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at hz
    cases hop : e.op with
    | ins v p an g =>
      simp only [step, hop] at hz
      split_ifs at hz with hmem
      · obtain ⟨u, hu, hwu⟩ := ih hz
        exact ⟨u, List.mem_append_left _ hu, hwu⟩
      · rcases mem_insertDown.mp hz with rfl | hz'
        · exact ⟨e, List.mem_append_right _ List.mem_cons_self, ⟨v, p, an, g, hop, rfl⟩⟩
        · obtain ⟨u, hu, hwu⟩ := ih hz'
          exact ⟨u, List.mem_append_left _ hu, hwu⟩
    | del x =>
      simp only [step, hop, List.mem_filter] at hz
      obtain ⟨u, hu, hwu⟩ := ih hz.1
      exact ⟨u, List.mem_append_left _ hu, hwu⟩

/-- A written coordinate is never empty. -/
theorem writes_coord_ne_nil {e : Op (AppOp Γ α)} {z : Record Γ α} (h : Writes e z) :
    z.2.2 ≠ [] := by
  obtain ⟨v, p, a, g, -, rfl⟩ := h
  simp [Γ.code_ne_nil]

/-- A written coordinate ends in the delimiter. -/
theorem writes_coordWf {e : Op (AppOp Γ α)} {z : Record Γ α} (h : Writes e z) :
    Γ.Wf z.2.2 := by
  obtain ⟨v, p, a, g, -, rfl⟩ := h
  exact Γ.wf_append p _ _

/-- **What `MintHonest` gives this row.** Every observed event was issued
from a replay of events that `C` observes and that are `vis`-before it, and
that replay satisfies the issuance guard. -/
def Issued (C : Ctx (Dα Γ α Q)) : Prop :=
  ∀ f ∈ C.events, ∃ π : List (Op (AppOp Γ α)), (∀ u ∈ π, u ∈ C.events) ∧
    (∀ u ∈ π, C.vis u f) ∧ CoreGuard f (π.foldl step [])

/-- **`DelBorn` from issuance.** A deletion names a live identity, and a
live identity is one some insertion of the causal past wrote. -/
theorem delBorn_of_issued {C : Ctx (Dα Γ α Q)} (hi : Issued C) : DelBorn C := by
  intro f hf x hfop
  obtain ⟨π, hsup, hvis, hguard⟩ := hi f hf
  simp only [CoreGuard, hfop] at hguard
  simp only [ids, List.mem_map] at hguard
  obtain ⟨w, hw, hwx⟩ := hguard
  obtain ⟨e, he, hwe⟩ := mem_fold_writer hw
  obtain ⟨v, p, an, g, hope, -⟩ := id hwe
  exact ⟨e, hsup e he, (writes_fst hwe).symm.trans hwx, ⟨v, p, an, g, hope⟩, hvis e he⟩

/-- **`CoordHonest` from issuance.** An insertion carries its anchor's
coordinate, so a coordinate decomposes uniquely into the anchor's
coordinate and the codeword of the clock gap. Induction is on the length of
the coordinate, which the anchor's strictly shortens. -/
theorem coordHonest_of_issued {C : Ctx (Dα Γ α Q)} (hi : Issued C) : CoordHonest C := by
  have main : ∀ n : Nat, ∀ e₁ ∈ C.events, ∀ e₂ ∈ C.events, ∀ z₁ z₂ : Record Γ α,
      Writes e₁ z₁ → Writes e₂ z₂ → z₁.2.2.length ≤ n → z₁.2.2 = z₂.2.2 → z₁ = z₂ := by
    intro n
    induction n with
    | zero =>
      intro e₁ he₁ e₂ he₂ z₁ z₂ hw₁ hw₂ hlen _
      exact absurd (List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen))
        (writes_coord_ne_nil hw₁)
    | succ n ih =>
      intro e₁ he₁ e₂ he₂ z₁ z₂ hw₁ hw₂ hlen hco
      obtain ⟨v₁, p₁, a₁, k₁, hop₁, rfl⟩ := hw₁
      obtain ⟨v₂, p₂, a₂, k₂, hop₂, rfl⟩ := hw₂
      -- the carried prefixes are genuine coordinates
      obtain ⟨π₁, hsup₁, -, hg₁⟩ := hi e₁ he₁
      obtain ⟨π₂, hsup₂, -, hg₂⟩ := hi e₂ he₂
      simp only [CoreGuard, hop₁] at hg₁
      simp only [CoreGuard, hop₂] at hg₂
      obtain ⟨hlt₁, hanch₁⟩ := hg₁
      obtain ⟨hlt₂, hanch₂⟩ := hg₂
      have hwf₁ : Γ.Wf p₁ := by
        rcases hanch₁ with ⟨-, rfl⟩ | ⟨v, hmem⟩
        · exact Γ.wf_nil
        · obtain ⟨g, -, hwg⟩ := mem_fold_writer hmem
          exact writes_coordWf hwg
      have hwf₂ : Γ.Wf p₂ := by
        rcases hanch₂ with ⟨-, rfl⟩ | ⟨v, hmem⟩
        · exact Γ.wf_nil
        · obtain ⟨g, -, hwg⟩ := mem_fold_writer hmem
          exact writes_coordWf hwg
      obtain ⟨hpp, hgg, hdd⟩ := Γ.cancel hwf₁ hwf₂ hco
      -- the anchors agree
      have hanchors : a₁ = a₂ := by
        rcases hanch₁ with ⟨ha₁, hp₁nil⟩ | ⟨w₁, hmem₁⟩
        · rcases hanch₂ with ⟨ha₂, -⟩ | ⟨w₂, hmem₂⟩
          · rw [ha₁, ha₂]
          · obtain ⟨g, hg, hwg⟩ := mem_fold_writer hmem₂
            exact absurd (hpp ▸ hp₁nil : p₂ = []) (writes_coord_ne_nil hwg)
        · obtain ⟨g₁, hg₁, hwg₁⟩ := mem_fold_writer hmem₁
          rcases hanch₂ with ⟨-, hp₂nil⟩ | ⟨w₂, hmem₂⟩
          · exact absurd (hpp.trans hp₂nil) (writes_coord_ne_nil hwg₁)
          · obtain ⟨g₂, hg₂, hwg₂⟩ := mem_fold_writer hmem₂
            have hlen' : ((a₁, w₁, p₁) : Record Γ α).2.2.length ≤ n := by
              have hl1 := Γ.length_lt p₁ k₁ (e₁.time - a₁)
              have hl2 : (p₁ ++ Γ.code k₁ (e₁.time - a₁)).length ≤ n + 1 := hlen
              show p₁.length ≤ n
              omega
            have := ih g₁ (hsup₁ g₁ hg₁) g₂ (hsup₂ g₂ hg₂) _ _ hwg₁ hwg₂ hlen' hpp
            exact congrArg Prod.fst this
      have hte : e₁.time = e₂.time := by
        have h1 : a₁ ≤ e₁.time := Nat.le_of_lt hlt₁
        have h2 : a₂ ≤ e₂.time := Nat.le_of_lt hlt₂
        calc e₁.time = (e₁.time - a₁) + a₁ := (Nat.sub_add_cancel h1).symm
          _ = (e₂.time - a₂) + a₁ := by rw [hdd]
          _ = (e₂.time - a₂) + a₂ := by rw [hanchors]
          _ = e₂.time := Nat.sub_add_cancel h2
      have hsame : e₂ = e₁ := by
        by_contra hne
        exact time_ne he₂ he₁ hne hte.symm
      subst hsame
      rw [hop₁] at hop₂
      cases hop₂
      rfl
  intro e₁ he₁ e₂ he₂ z₁ z₂ hw₁ hw₂ hco
  exact main z₁.2.2.length e₁ he₁ e₂ he₂ z₁ z₂ hw₁ hw₂ (Nat.le_refl _) hco

end LeanProofs.NoSpecNonComm.Implementations.EmbeddedRGA
