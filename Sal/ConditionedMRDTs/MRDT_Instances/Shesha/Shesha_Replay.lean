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

end Shesha
