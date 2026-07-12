import Sal.ConditionedMRDTs.MRDT_Instances.Shesha.Shesha_Evolution

/-! # Shesha — the replay layer (phase 2d)

Machinery for the effective-witness join hook `shesha_join_at_eff`
(`Shesha_Cond.lean`): the merge output is the fold of an explicitly
constructed enumeration — **all inserts** (in reverse-output order: anchors
before children, same-anchor runs right-to-left so that heads land last),
then **all deletes**. This file provides the layers that construction rests
on:

* §1 **Commutation** — the positive commutation lemmas the `respects`
  analysis needs: inserts at unrelated anchors commute
  (`insert_insert_comm`), and a delete commutes with an insert it does not
  touch (`delete_insert_comm`). Together with honesty (which excludes
  `vis`-edges from a delete into an insert of its own target or anchor)
  these make the inserts-then-deletes shape `loOn`-respecting.

* §2 **Graft algebra** — `graft s p G` prepends a forest `G` at the head of
  `p`'s row; `insert` is the singleton graft, and grafts at fresh keys
  commute past each other.

* §3 **The insert-phase realization** — `plan` linearizes a target forest
  into insert ops (rightmost sibling first, parent before children), and
  `steps_planF`: folding the plan grafts the forest — from the empty
  document, the plan *builds the forest exactly*. This realizes the
  pre-splice tree of the replay witness; the delete phase then splices it
  down to the merge output. -/

namespace Shesha

/-! ## §1 Commutation -/

section Comm

variable {x a y b : Nat}

theorem insF_nil : insF x a [] = [] := rfl

mutual
  theorem insT_insT_comm (hab : a ≠ b) (hay : a ≠ y) (hbx : b ≠ x) :
      ∀ t : Tree, insT y b (insT x a t) = insT x a (insT y b t)
    | .node i cs => by
        rw [insT, insT]
        by_cases hia : i = a
        · have hib : ¬ i = b := fun h => hab ((hia ▸ h : a = b))
          rw [if_pos hia, if_neg hib, insT, insT, if_neg hib, if_pos hia,
            insF, insT, if_neg (fun h : x = b => hbx h.symm), insF_nil,
            insF_insF_comm hab hay hbx cs]
        · rw [if_neg hia]
          by_cases hib : i = b
          · rw [if_pos hib, insT, insT, if_pos hib, if_neg hia, insF, insT,
              if_neg (fun h : y = a => hay h.symm), insF_nil,
              insF_insF_comm hab hay hbx cs]
          · rw [if_neg hib, insT, insT, if_neg hia, if_neg hib,
              insF_insF_comm hab hay hbx cs]
  theorem insF_insF_comm (hab : a ≠ b) (hay : a ≠ y) (hbx : b ≠ x) :
      ∀ F : List Tree, insF y b (insF x a F) = insF x a (insF y b F)
    | [] => rfl
    | t :: ts => by
        rw [insF, insF, insF, insF, insT_insT_comm hab hay hbx t,
          insF_insF_comm hab hay hbx ts]
end

/-- **Inserts at unrelated anchors commute** (semantically, at every state):
distinct anchors, neither anchored at the other's new node. -/
theorem insert_insert_comm (hab : a ≠ b) (hay : a ≠ y) (hbx : b ≠ x)
    (s : St) :
    Shesha.insert (Shesha.insert s x a) y b
      = Shesha.insert (Shesha.insert s y b) x a := by
  rw [Shesha.insert, Shesha.insert]
  by_cases ha : a = 0
  · have hb : ¬ b = 0 := fun h => hab (ha.trans h.symm)
    rw [if_pos ha, if_neg hb, Shesha.insert, Shesha.insert, if_neg hb,
      if_pos ha, insF, insT, if_neg (fun h : x = b => hbx h.symm), insF]
  · rw [if_neg ha]
    by_cases hb : b = 0
    · rw [if_pos hb, Shesha.insert, Shesha.insert, if_pos hb, if_neg ha,
        insF, insT, if_neg (fun h : y = a => hay h.symm), insF]
    · rw [if_neg hb, Shesha.insert, Shesha.insert, if_neg hb, if_neg ha,
        insF_insF_comm hab hay hbx s]

end Comm

section DelComm

variable {x a d : Nat}

theorem delF_nil : delF d [] = [] := rfl

theorem insF_cons {x a : Nat} {t : Tree} {ts : List Tree} :
    insF x a (t :: ts) = insT x a t :: insF x a ts := rfl

theorem insF_append {x a : Nat} :
    ∀ F G : List Tree, insF x a (F ++ G) = insF x a F ++ insF x a G
  | [], _ => rfl
  | t :: ts, G => by
      rw [List.cons_append, insF_cons, insF_cons, insF_append ts G,
        List.cons_append]

theorem delF_cons {d : Nat} {t : Tree} {ts : List Tree} :
    delF d (t :: ts) = delT d t ++ delF d ts := rfl

mutual
  theorem delT_insT_comm (hdx : d ≠ x) (hda : d ≠ a) :
      ∀ t : Tree, delT d (insT x a t) = insF x a (delT d t)
    | .node i cs => by
        have hxd : ¬ x = d := fun h => hdx h.symm
        by_cases hia : i = a
        · have hid : ¬ a = d := fun h => hda h.symm
          simp [insT, delT, delF, insF, hia, hid, hxd,
            delF_insF_comm hdx hda cs]
        · by_cases hid : i = d
          · simp [insT, delT, hid, hda, delF_insF_comm hdx hda cs]
          · simp [insT, delT, insF, hia, hid,
              delF_insF_comm hdx hda cs]
  theorem delF_insF_comm (hdx : d ≠ x) (hda : d ≠ a) :
      ∀ F : List Tree, delF d (insF x a F) = insF x a (delF d F)
    | [] => rfl
    | t :: ts => by
        rw [insF_cons, delF_cons, delF_cons, delT_insT_comm hdx hda t,
          delF_insF_comm hdx hda ts, insF_append]
end

/-- **A delete commutes with an insert it does not touch** (semantically, at
every state): the deleted id is neither the new node nor its anchor. -/
theorem delete_insert_comm (hdx : d ≠ x) (hda : d ≠ a) (s : St) :
    Shesha.delete (Shesha.insert s x a) d
      = Shesha.insert (Shesha.delete s d) x a := by
  rw [Shesha.insert, Shesha.delete, Shesha.insert]
  by_cases ha : a = 0
  · rw [if_pos ha, if_pos ha, delF, delT,
      if_neg (fun h : x = d => hdx h.symm), delF_nil, Shesha.delete]
    rfl
  · rw [if_neg ha, if_neg ha, Shesha.delete, delF_insF_comm hdx hda s]

end DelComm

/-! ## §2 Graft algebra -/

mutual
  /-- Prepend the forest `G` at the head of `p`'s row, everywhere `p`
  occurs (mirroring `insert`'s totality; on WF states `p` occurs once). -/
  def graftT (p : Nat) (G : List Tree) : Tree → Tree
    | .node i cs =>
        if i = p then .node i (G ++ graftF p G cs)
        else .node i (graftF p G cs)
  def graftF (p : Nat) (G : List Tree) : List Tree → List Tree
    | [] => []
    | t :: ts => graftT p G t :: graftF p G ts
end

/-- Prepend `G` at the head of `p`'s row (`p = 0`: the root row). -/
def graft (s : St) (p : Nat) (G : List Tree) : St :=
  if p = 0 then G ++ s else graftF p G s

theorem graftF_nil {p : Nat} {G : List Tree} : graftF p G [] = [] := rfl

theorem graftF_cons {p : Nat} {G : List Tree} {t : Tree} {ts : List Tree} :
    graftF p G (t :: ts) = graftT p G t :: graftF p G ts := rfl

theorem graftF_append {p : Nat} {G : List Tree} :
    ∀ F₁ F₂ : List Tree,
      graftF p G (F₁ ++ F₂) = graftF p G F₁ ++ graftF p G F₂
  | [], _ => rfl
  | t :: ts, F₂ => by
      rw [List.cons_append, graftF_cons, graftF_cons,
        graftF_append ts F₂, List.cons_append]

mutual
  /-- Grafting at an absent key is a no-op. -/
  theorem graftT_no_op {p : Nat} {G : List Tree} :
      ∀ t : Tree, containsT p t = false → graftT p G t = t
    | .node i cs, h => by
        rw [containsT] at h
        rcases Bool.or_eq_false_iff.mp h with ⟨h1, h2⟩
        rw [graftT, if_neg (fun he : i = p => by
            rw [he] at h1
            simp at h1),
          graftF_no_op cs h2]
  theorem graftF_no_op {p : Nat} {G : List Tree} :
      ∀ F : List Tree, containsF p F = false → graftF p G F = F
    | [], _ => rfl
    | t :: ts, h => by
        rw [containsF] at h
        rcases Bool.or_eq_false_iff.mp h with ⟨h1, h2⟩
        rw [graftF_cons, graftT_no_op t h1, graftF_no_op ts h2]
end

mutual
  /-- `insert` is the singleton graft. -/
  theorem insT_eq_graftT {x p : Nat} :
      ∀ t : Tree, insT x p t = graftT p [Tree.node x []] t
    | .node i cs => by
        rw [insT, graftT]
        by_cases h : i = p
        · rw [if_pos h, if_pos h, insF_eq_graftF cs]
          rfl
        · rw [if_neg h, if_neg h, insF_eq_graftF cs]
  theorem insF_eq_graftF {x p : Nat} :
      ∀ F : List Tree, insF x p F = graftF p [Tree.node x []] F
    | [] => rfl
    | t :: ts => by
        rw [insF_cons, graftF_cons, insT_eq_graftT t, insF_eq_graftF ts]
end

theorem insert_eq_graft {x p : Nat} (s : St) :
    Shesha.insert s x p = graft s p [Tree.node x []] := by
  rw [Shesha.insert, graft]
  by_cases h : p = 0
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h, insF_eq_graftF s]

theorem containsF_append {u : Nat} :
    ∀ F₁ F₂ : List Tree,
      containsF u (F₁ ++ F₂) = (containsF u F₁ || containsF u F₂)
  | [], F₂ => by simp [containsF]
  | t :: ts, F₂ => by
      simp [containsF, containsF_append ts F₂, Bool.or_assoc]

mutual
  /-- Grafting the empty forest is the identity. -/
  theorem graftT_nil {p : Nat} :
      ∀ t : Tree, graftT p [] t = t
    | .node i cs => by
        rw [graftT]
        by_cases h : i = p
        · rw [if_pos h, List.nil_append, graftF_nil' cs]
        · rw [if_neg h, graftF_nil' cs]
  theorem graftF_nil' {p : Nat} :
      ∀ F : List Tree, graftF p [] F = F
    | [] => rfl
    | t :: ts => by rw [graftF_cons, graftT_nil t, graftF_nil' ts]
end

theorem graft_nil {p : Nat} (s : St) : graft s p [] = s := by
  rw [graft]
  by_cases h : p = 0
  · rw [if_pos h, List.nil_append]
  · rw [if_neg h, graftF_nil' s]

mutual
  /-- Grafts don't create occurrences of an absent id. -/
  theorem containsT_graftT_false {u p : Nat} {G : List Tree} :
      ∀ t : Tree, containsT u t = false → containsF u G = false →
        containsT u (graftT p G t) = false
    | .node i cs, ht, hG => by
        rw [containsT] at ht
        rcases Bool.or_eq_false_iff.mp ht with ⟨h1, h2⟩
        rw [graftT]
        by_cases h : i = p
        · rw [if_pos h, containsT, containsF_append, hG,
            containsF_graftF_false cs h2 hG, h1]
          rfl
        · rw [if_neg h, containsT, containsF_graftF_false cs h2 hG, h1]
          rfl
  theorem containsF_graftF_false {u p : Nat} {G : List Tree} :
      ∀ F : List Tree, containsF u F = false → containsF u G = false →
        containsF u (graftF p G F) = false
    | [], _, _ => rfl
    | t :: ts, hF, hG => by
        rw [containsF] at hF
        rcases Bool.or_eq_false_iff.mp hF with ⟨h1, h2⟩
        rw [graftF_cons, containsF, containsT_graftT_false t h1 hG,
          containsF_graftF_false ts h2 hG]
        rfl
end

/-- Membership in a graft is inherited from the state or the graft. -/
theorem contains_graft_false {u p : Nat} {G : List Tree} (s : St)
    (hs : containsF u s = false) (hG : containsF u G = false) :
    containsF u (graft s p G) = false := by
  rw [graft]
  by_cases h : p = 0
  · rw [if_pos h, containsF_append, hs, hG]
    rfl
  · rw [if_neg h]
    exact containsF_graftF_false s hs hG

mutual
  /-- Composition of grafts at the same key: the later graft prepends. -/
  theorem graftT_graftT {p : Nat} {G' G : List Tree}
      (hG : containsF p G = false) :
      ∀ t : Tree, graftT p G' (graftT p G t) = graftT p (G' ++ G) t
    | .node i cs => by
        by_cases h : i = p
        · simp [graftT, h, graftF_append, graftF_no_op G hG,
            graftF_graftF hG cs, List.append_assoc]
        · simp [graftT, h, graftF_graftF hG cs]
  theorem graftF_graftF {p : Nat} {G' G : List Tree}
      (hG : containsF p G = false) :
      ∀ F : List Tree, graftF p G' (graftF p G F) = graftF p (G' ++ G) F
    | [] => rfl
    | t :: ts => by
        rw [graftF_cons, graftF_cons, graftF_cons, graftT_graftT hG t,
          graftF_graftF hG ts]
end

mutual
  /-- A graft at a key occurring only inside the grafted forest `G`
  commutes inward. -/
  theorem graftT_swap {q p : Nat} {H G : List Tree} :
      ∀ t : Tree, containsT q t = false →
        graftT q H (graftT p G t) = graftT p (graftF q H G) t
    | .node i cs, ht => by
        rw [containsT] at ht
        rcases Bool.or_eq_false_iff.mp ht with ⟨h1, h2⟩
        have hiq : ¬ i = q := fun he => by
          rw [he] at h1
          simp at h1
        rw [graftT, graftT]
        by_cases h : i = p
        · rw [if_pos h, graftT, if_neg hiq, if_pos h, graftF_append,
            graftF_swap cs h2]
        · rw [if_neg h, graftT, if_neg hiq, if_neg h, graftF_swap cs h2]
  theorem graftF_swap {q p : Nat} {H G : List Tree} :
      ∀ F : List Tree, containsF q F = false →
        graftF q H (graftF p G F) = graftF p (graftF q H G) F
    | [], _ => rfl
    | t :: ts, hF => by
        rw [containsF] at hF
        rcases Bool.or_eq_false_iff.mp hF with ⟨h1, h2⟩
        rw [graftF_cons, graftF_cons, graftF_cons, graftT_swap t h1,
          graftF_swap ts h2]
end

/-- Sibling composition: grafting a fresh leaf onto an existing graft. -/
theorem graft_graft {p : Nat} {G' G : List Tree} (s : St)
    (hG : containsF p G = false) :
    graft (graft s p G) p G' = graft s p (G' ++ G) := by
  rw [graft, graft, graft]
  by_cases h : p = 0
  · rw [if_pos h, if_pos h, if_pos h, List.append_assoc]
  · rw [if_neg h, if_neg h, if_neg h, graftF_graftF hG s]

/-- Child composition: filling in a freshly grafted node's row. -/
theorem graft_child {p i : Nat} (s : St) (cs ts : List Tree)
    (hi0 : i ≠ 0)
    (his : containsF i s = false)
    (hits : containsF i ts = false) :
    graft (graft s p (Tree.node i [] :: ts)) i cs
      = graft s p (Tree.node i cs :: ts) := by
  have hkey : graftF i cs (Tree.node i [] :: ts) = Tree.node i cs :: ts := by
    rw [graftF_cons, graftT, if_pos rfl, graftF_nil, List.append_nil,
      graftF_no_op ts hits]
  by_cases h : p = 0
  · rw [graft, if_neg hi0, graft, if_pos h, graft, if_pos h,
      List.cons_append, graftF_cons, graftF_append, graftT, if_pos rfl,
      graftF_nil, List.append_nil, graftF_no_op ts hits,
      graftF_no_op s his, List.cons_append]
  · rw [graft, if_neg hi0, graft, if_neg h, graft, if_neg h,
      graftF_swap s (H := cs) (G := Tree.node i [] :: ts) his, hkey]

end Shesha
