import Sal.MRDTs.Paper1.PriorityQueueSameRecordVC
import Sal.MRDTs.Paper1.PriorityQueueSameRecordSpec

/-! Birth provenance for the same-record repair. `BirthComplete` rules out the
source's transient early-delivery placeholders. It is an invariant of honest
preparation from birth-complete states, preserved by union merge. It is not an
additional client guard, and these local lemmas alone are not a history cert. -/
namespace Sal.MRDTs.Paper1.PriorityQueueSameRecord
open Foundation Instances.PriorityQueueSameRecord

/-- Every increment attachment names a known birth, including dead records. -/
def BirthComplete (s : State) : Prop :=
  ∀ a ∈ s.increments, ∃ v, (a.1,v) ∈ s.births

theorem birthComplete_init : BirthComplete {} := by
  intro a ha
  exact False.elim (Finset.notMem_empty _ ha)

theorem observed_has_birth (s : State) (complete : BirthComplete s) (x t : Nat)
    (seen : t ∈ Instances.PublishedAddWinsPriorityQueue.observed s x) :
    ∃ v, ((x,t),v) ∈ s.births := by
  obtain ⟨tag,htag,ht⟩ := Finset.mem_image.mp seen
  obtain ⟨alive,key⟩ := Finset.mem_filter.mp htag
  obtain ⟨record,_⟩ := Finset.mem_sdiff.mp alive
  have equal : tag = (x,t) := Prod.ext key ht
  rcases Finset.mem_union.mp record with birth | increment
  · obtain ⟨b,hb,hbtag⟩ := Finset.mem_image.mp birth
    exact ⟨b.2,by simpa only [← equal,← hbtag] using hb⟩
  · obtain ⟨a,ha,hatag⟩ := Finset.mem_image.mp increment
    obtain ⟨v,hv⟩ := complete a ha
    exact ⟨v,by simpa only [hatag,equal] using hv⟩

theorem birthComplete_merge (l a b : State) (ha : BirthComplete a) (hb : BirthComplete b) :
    BirthComplete (merge l a b) := by
  intro inc member
  rcases Finset.mem_union.mp member with left | right
  · obtain ⟨v,hv⟩ := ha inc left
    exact ⟨v,Finset.mem_union_left _ hv⟩
  · obtain ⟨v,hv⟩ := hb inc right
    exact ⟨v,Finset.mem_union_right _ hv⟩

private theorem birthComplete_inc (s : State) (complete : BirthComplete s)
    (t r x : Nat) (n : Int) :
    BirthComplete (step s (t,r,.inc x n (Instances.PublishedAddWinsPriorityQueue.observed s x))) := by
  intro inc member
  rcases Finset.mem_union.mp member with old | newborn
  · exact complete inc old
  · obtain ⟨tag,seen,equal⟩ := Finset.mem_image.mp newborn
    subst inc
    exact observed_has_birth s complete x tag seen

/-- The exact executable source preparation guard preserves birth completeness;
there is no stronger hidden operation-generation predicate. -/
theorem birthComplete_prepared (s : State) (complete : BirthComplete s) (e : Event)
    (issued : generation.CanIssue e s) : BirthComplete (step s e) := by
  rcases e with ⟨t,r,op⟩
  cases op with
  | add x v =>
    intro inc member
    obtain ⟨w,hw⟩ := complete inc member
    exact ⟨w,Finset.mem_insert_of_mem hw⟩
  | remove x observed => exact complete
  | inc x n observed =>
    change prepare s t r (.inc x n) = some (t,r,.inc x n observed) at issued
    unfold prepare Instances.PublishedAddWinsPriorityQueue.prepare at issued
    cases h : Instances.PublishedAddWinsPriorityQueue.lookup s x <;> simp [h] at issued
    cases issued
    exact birthComplete_inc s complete t r x n

/-- On birth-complete states lookup from the published live-record projection
and lookup from the repaired finite priority map coincide. -/
theorem elements_eq_source (s : State) (complete : BirthComplete s) :
    elements s = Instances.PublishedAddWinsPriorityQueue.liveElements s := by
  ext x
  simp only [elements,Instances.PublishedAddWinsPriorityQueue.liveElements,
    Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨b,⟨birth,live⟩,key⟩
    refine ⟨b.1,Finset.mem_sdiff.mpr ⟨?_,live⟩,key⟩
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b,birth,rfl⟩)
  · rintro ⟨tag,alive,key⟩
    have obs : tag.2 ∈ Instances.PublishedAddWinsPriorityQueue.observed s x :=
      Finset.mem_image.mpr ⟨tag,Finset.mem_filter.mpr ⟨alive,key⟩,rfl⟩
    obtain ⟨v,birth⟩ := observed_has_birth s complete x tag.2 obs
    refine ⟨((x,tag.2),v),⟨birth,?_⟩,rfl⟩
    have equal : tag = (x,tag.2) := Prod.ext key rfl
    rw [← equal]
    exact (Finset.mem_sdiff.mp alive).2

private theorem step_births (s : State) (e : Event) (b : Instances.PublishedAddWinsPriorityQueue.Birth) :
    b ∈ (step s e).births ↔ b ∈ s.births ∨ b ∈ (step {} e).births := by
  rcases e with ⟨t,r,op⟩
  cases op <;> simp [step,Instances.PublishedAddWinsPriorityQueue.step,or_comm]

private theorem step_increments (s : State) (e : Event)
    (a : Instances.PublishedAddWinsPriorityQueue.Attachment) :
    a ∈ (step s e).increments ↔ a ∈ s.increments ∨ a ∈ (step {} e).increments := by
  rcases e with ⟨t,r,op⟩
  cases op <;> simp [step,Instances.PublishedAddWinsPriorityQueue.step]

private theorem step_removed (s : State) (e : Event) (tag : Instances.PublishedAddWinsPriorityQueue.Tag) :
    tag ∈ (step s e).removed ↔ tag ∈ s.removed ∨ tag ∈ (step {} e).removed := by
  rcases e with ⟨t,r,op⟩
  cases op <;> simp [step,Instances.PublishedAddWinsPriorityQueue.step]

theorem fold_births (s : State) (events : List Event) (b : Instances.PublishedAddWinsPriorityQueue.Birth) :
    b ∈ (applySeq D.toUpdateSig s events).births ↔
      b ∈ s.births ∨ ∃ e ∈ events, b ∈ (step {} e).births := by
  induction events generalizing s with
  | nil => simp [applySeq]
  | cons e events ih =>
    change b ∈ (applySeq D.toUpdateSig (step s e) events).births ↔ _
    rw [ih,step_births]
    simp only [List.mem_cons,exists_eq_or_imp]
    tauto

theorem fold_increments (s : State) (events : List Event)
    (a : Instances.PublishedAddWinsPriorityQueue.Attachment) :
    a ∈ (applySeq D.toUpdateSig s events).increments ↔
      a ∈ s.increments ∨ ∃ e ∈ events, a ∈ (step {} e).increments := by
  induction events generalizing s with
  | nil => simp [applySeq]
  | cons e events ih =>
    change a ∈ (applySeq D.toUpdateSig (step s e) events).increments ↔ _
    rw [ih,step_increments]
    simp only [List.mem_cons,exists_eq_or_imp]
    tauto

theorem fold_removed (s : State) (events : List Event) (tag : Instances.PublishedAddWinsPriorityQueue.Tag) :
    tag ∈ (applySeq D.toUpdateSig s events).removed ↔
      tag ∈ s.removed ∨ ∃ e ∈ events, tag ∈ (step {} e).removed := by
  induction events generalizing s with
  | nil => simp [applySeq]
  | cons e events ih =>
    change tag ∈ (applySeq D.toUpdateSig (step s e) events).removed ↔ _
    rw [ih,step_removed]
    simp only [List.mem_cons,exists_eq_or_imp]
    tauto

private theorem prepared_increment_has_birth (s : State) (complete : BirthComplete s)
    (e : Event) (issued : generation.CanIssue e s)
    (a : Instances.PublishedAddWinsPriorityQueue.Attachment)
    (attachment : a ∈ (step {} e).increments) : ∃ v, (a.1,v) ∈ s.births := by
  rcases e with ⟨t,r,op⟩
  cases op with
  | add x v => exact False.elim (Finset.notMem_empty _ attachment)
  | remove x observed => exact False.elim (Finset.notMem_empty _ attachment)
  | inc x n observed =>
    change prepare s t r (.inc x n) = some (t,r,.inc x n observed) at issued
    unfold prepare Instances.PublishedAddWinsPriorityQueue.prepare at issued
    cases h : Instances.PublishedAddWinsPriorityQueue.lookup s x <;> simp [h] at issued
    cases issued
    have member : a ∈ (Instances.PublishedAddWinsPriorityQueue.observed s x).image
        (fun tag => ((x,tag),t,n)) := by simpa [step,Instances.PublishedAddWinsPriorityQueue.step] using attachment
    obtain ⟨tag,seen,equal⟩ := Finset.mem_image.mp member
    subst a
    exact observed_has_birth s complete x tag seen

/-- Honest mint snapshots guarantee that every increment target has a visible
birth. The proof uses well-founded causal timestamps to rule out a chain of
unborn placeholders; no extra source preparation guard is introduced. -/
theorem honest_increment_birth (C : Configuration D)
    (honest : MintHonest D generation.CanIssue C)
    (trans : ∀ {a b c : Event}, C.vis a b → C.vis b c → C.vis a c)
    (e : Event) (member : e ∈ C.events)
    (a : Instances.PublishedAddWinsPriorityQueue.Attachment)
    (attachment : a ∈ (step {} e).increments) :
    ∃ b ∈ C.events, C.vis b e ∧ ∃ v, (a.1,v) ∈ (step {} b).births := by
  have claim : ∀ n : Nat, ∀ e : Event, e.time = n → e ∈ C.events →
      ∀ a, a ∈ (step {} e).increments →
        ∃ b ∈ C.events, C.vis b e ∧ ∃ v, (a.1,v) ∈ (step {} b).births := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro e time member a attachment
      obtain ⟨past,enumerated,ordered,guard⟩ := honest e member
      have complete : BirthComplete (applySeq D.toUpdateSig D.init past) := by
        intro inc incMember
        have delta := (fold_increments D.init past inc).mp incMember
        rcases delta with empty | ⟨previous,inPast,generated⟩
        · exact False.elim (Finset.notMem_empty _ empty)
        · have old := (enumerated.2 previous).mp inPast
          have earlier : previous.time < n := by
            have causal : previous.time < e.time := C.causal_mono old.2
            simpa only [time] using causal
          obtain ⟨birth,birthSupported,beforePrevious,v,born⟩ :=
            ih previous.time earlier previous rfl old.1 inc generated
          have before := trans beforePrevious old.2
          have included : birth ∈ past := (enumerated.2 birth).mpr ⟨birthSupported,before⟩
          exact ⟨v,(fold_births D.init past (inc.1,v)).mpr (Or.inr ⟨birth,included,born⟩)⟩
      obtain ⟨v,birth⟩ := prepared_increment_has_birth _ complete e guard a attachment
      rcases (fold_births D.init past (a.1,v)).mp birth with empty | ⟨b,hb,born⟩
      · exact False.elim (Finset.notMem_empty _ empty)
      · have supported := (enumerated.2 b).mp hb
        exact ⟨b,supported.1,supported.2,v,born⟩
  exact claim e.time e rfl member a attachment

/-- Every finite, supported causal cut also has complete birth provenance,
using mint honesty rather than assuming an issuer version for the cut. -/
theorem birthComplete_closed_fold (C : Configuration D)
    (honest : MintHonest D generation.CanIssue C)
    (trans : ∀ {a b c : Event}, C.vis a b → C.vis b c → C.vis a c)
    (events : List Event) (E : Set Event) (enumerated : listPermOf events E)
    (supported : ∀ e ∈ E, e ∈ C.events)
    (closed : ∀ a b, C.vis a b → b ∈ E → a ∈ E) :
    BirthComplete (applySeq D.toUpdateSig D.init events) := by
  intro inc member
  rcases (fold_increments D.init events inc).mp member with empty | ⟨e,he,generated⟩
  · exact False.elim (Finset.notMem_empty _ empty)
  · have inE := (enumerated.2 e).mp he
    obtain ⟨birth,_,before,v,born⟩ := honest_increment_birth C honest trans e
      (supported e inE) inc generated
    have included := (enumerated.2 birth).mpr (closed birth e before inE)
    exact ⟨v,(fold_births D.init events (inc.1,v)).mpr (Or.inr ⟨birth,included,born⟩)⟩

private theorem prepared_remove_has_birth (s : State) (complete : BirthComplete s)
    (e : Event) (issued : generation.CanIssue e s) (tag : Instances.PublishedAddWinsPriorityQueue.Tag)
    (removed : tag ∈ (step {} e).removed) : ∃ v, (tag,v) ∈ s.births := by
  rcases e with ⟨t,r,op⟩
  cases op with
  | add x v => exact False.elim (Finset.notMem_empty _ removed)
  | inc x n observed => exact False.elim (Finset.notMem_empty _ removed)
  | remove x observed =>
    change prepare s t r (.remove x) = some (t,r,.remove x observed) at issued
    unfold prepare Instances.PublishedAddWinsPriorityQueue.prepare at issued
    cases h : Instances.PublishedAddWinsPriorityQueue.lookup s x <;> simp [h] at issued
    cases issued
    have member : tag ∈ (Instances.PublishedAddWinsPriorityQueue.observed s x).image
        (fun tag => (x,tag)) := by simpa [step,Instances.PublishedAddWinsPriorityQueue.step] using removed
    obtain ⟨timestamp,seen,equal⟩ := Finset.mem_image.mp member
    subst tag
    exact observed_has_birth s complete x timestamp seen

theorem honest_remove_birth (C : Configuration D)
    (honest : MintHonest D generation.CanIssue C)
    (trans : ∀ {a b c : Event}, C.vis a b → C.vis b c → C.vis a c)
    (e : Event) (member : e ∈ C.events) (tag : Instances.PublishedAddWinsPriorityQueue.Tag)
    (removed : tag ∈ (step {} e).removed) :
    ∃ b ∈ C.events, C.vis b e ∧ ∃ v, (tag,v) ∈ (step {} b).births := by
  obtain ⟨past,enumerated,ordered,guard⟩ := honest e member
  have complete := birthComplete_closed_fold C honest trans past _ enumerated
    (fun e he => he.1) (fun a b ab hb => ⟨C.vis_src ab,trans ab hb.2⟩)
  obtain ⟨v,birth⟩ := prepared_remove_has_birth _ complete e guard tag removed
  rcases (fold_births D.init past (tag,v)).mp birth with empty | ⟨b,hb,born⟩
  · exact False.elim (Finset.notMem_empty _ empty)
  · have supported := (enumerated.2 b).mp hb
    exact ⟨b,supported.1,supported.2,v,born⟩

theorem birth_effect_iff (e : Event) (x t : Nat) (v : Int) :
    ((x,t),v) ∈ (step {} e).births ↔ e.op = .add x v ∧ e.time = t := by
  rcases e with ⟨et,er,op⟩
  cases op <;> simp [step,Instances.PublishedAddWinsPriorityQueue.step,Op.op,Op.time,
    Prod.mk.injEq] <;> tauto

/-- An attachment to a particular honest birth preserves its Add-to-Inc
visibility edge; metadata commutation does not erase this specification edge. -/
theorem attached_increment_visible (C : Configuration D)
    (honest : MintHonest D generation.CanIssue C)
    (trans : ∀ {a b c : Event}, C.vis a b → C.vis b c → C.vis a c)
    (birth inc : Event) (birthSupported : birth ∈ C.events) (incSupported : inc ∈ C.events)
    (x t : Nat) (v : Int) (born : ((x,t),v) ∈ (step {} birth).births)
    (attachment : ∃ n, ((x,t),inc.time,n) ∈ (step {} inc).increments) : C.vis birth inc := by
  obtain ⟨n,attached⟩ := attachment
  obtain ⟨b,supported,before,w,born'⟩ := honest_increment_birth C honest trans inc incSupported _ attached
  have time := (birth_effect_iff birth x t v).mp born
  have time' := (birth_effect_iff b x t w).mp born'
  have equal : b = birth := C.replayContext.ts_unique supported birthSupported (time'.2.trans time.2.symm)
  exact equal ▸ before

private theorem fold_removed_subset (pre post : List Event)
    (sub : ∀ e ∈ pre, e ∈ post) :
    (applySeq D.toUpdateSig D.init pre).removed ⊆ (applySeq D.toUpdateSig D.init post).removed := by
  intro tag member
  rcases (fold_removed D.init pre tag).mp member with empty | ⟨e,he,removed⟩
  · exact False.elim (Finset.notMem_empty _ empty)
  · exact (fold_removed D.init post tag).mpr (Or.inr ⟨e,sub e he,removed⟩)

private theorem live_birth_observed (s : State) (x t : Nat) (v : Int)
    (born : ((x,t),v) ∈ s.births) (alive : (x,t) ∉ s.removed) :
    t ∈ Instances.PublishedAddWinsPriorityQueue.observed s x ∧
      Instances.PublishedAddWinsPriorityQueue.lookup s x = true := by
  have live : (x,t) ∈ Instances.PublishedAddWinsPriorityQueue.liveTags s :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨((x,t),v),born,rfl⟩),alive⟩
  constructor
  · exact Finset.mem_image.mpr ⟨(x,t),Finset.mem_filter.mpr ⟨live,rfl⟩,rfl⟩
  · change decide (x ∈ Instances.PublishedAddWinsPriorityQueue.liveElements s) = true
    exact decide_eq_true (Finset.mem_image.mpr ⟨(x,t),live,rfl⟩)

/-- The key present-case ordering fact: every same-element visible successor of
ANY surviving birth is an increment targeting that birth. Add is forbidden by
its actual absence guard, and Remove would contradict final survival. -/
theorem surviving_birth_successor (C : Configuration D)
    (honest : MintHonest D generation.CanIssue C)
    (trans : ∀ {a b c : Event}, C.vis a b → C.vis b c → C.vis a c)
    (events : List Event) (E : Set Event) (enumerated : listPermOf events E)
    (supported : ∀ e ∈ E, e ∈ C.events)
    (closed : ∀ a b, C.vis a b → b ∈ E → a ∈ E)
    (birth e : Event) (member : e ∈ E) (before : C.vis birth e)
    (x t : Nat) (v : Int) (born : ((x,t),v) ∈ (step {} birth).births)
    (alive : (x,t) ∉ (applySeq D.toUpdateSig D.init events).removed)
    (sameKey : elementOf e.op = x) :
    ∃ n observed, e.op = .inc x n observed ∧ t ∈ observed := by
  obtain ⟨past,pastEnum,_,guard⟩ := honest e (supported e member)
  have inPast : birth ∈ past := (pastEnum.2 birth).mpr ⟨supported birth (closed birth e before member),before⟩
  have presentBirth : ((x,t),v) ∈ (applySeq D.toUpdateSig D.init past).births :=
    (fold_births D.init past _).mpr (Or.inr ⟨birth,inPast,born⟩)
  have sub : ∀ a ∈ past, a ∈ events := by
    intro a ha
    have earlier := (pastEnum.2 a).mp ha
    exact (enumerated.2 a).mpr (closed a e earlier.2 member)
  have priorAlive : (x,t) ∉ (applySeq D.toUpdateSig D.init past).removed :=
    fun removed => alive (fold_removed_subset past events sub removed)
  have live := live_birth_observed _ x t v presentBirth priorAlive
  rcases e with ⟨et,er,op⟩
  cases op with
  | add y innate =>
    change y = x at sameKey
    subst y
    change prepare _ et er (.add x innate) = some (et,er,.add x innate) at guard
    simp [prepare,Instances.PublishedAddWinsPriorityQueue.prepare,live.2] at guard
  | inc y n observed =>
    change y = x at sameKey
    subst y
    change prepare _ et er (.inc x n) = some (et,er,.inc x n observed) at guard
    simp [prepare,Instances.PublishedAddWinsPriorityQueue.prepare,live.2] at guard
    cases guard
    exact ⟨n,_,rfl,live.1⟩
  | remove y observed =>
    change y = x at sameKey
    subst y
    change prepare _ et er (.remove x) = some (et,er,.remove x observed) at guard
    simp [prepare,Instances.PublishedAddWinsPriorityQueue.prepare,live.2] at guard
    cases guard
    have removed : (x,t) ∈ (step {} (et,er,.remove x
        (Instances.PublishedAddWinsPriorityQueue.observed (applySeq D.toUpdateSig D.init past) x))).removed := by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨t,live.1,rfl⟩
    exact False.elim (alive ((fold_removed D.init events (x,t)).mpr
      (Or.inr ⟨_,(enumerated.2 _).mpr member,removed⟩)))

theorem remove_effect_iff (e : Event) (x t : Nat) :
    (x,t) ∈ (step {} e).removed ↔ ∃ observed, e.op = .remove x observed ∧ t ∈ observed := by
  rcases e with ⟨et,er,op⟩
  cases op <;> simp [step,Instances.PublishedAddWinsPriorityQueue.step,Op.op,
    Prod.mk.injEq] <;> grind

theorem removed_birth_visible (C : Configuration D)
    (honest : MintHonest D generation.CanIssue C)
    (trans : ∀ {a b c : Event}, C.vis a b → C.vis b c → C.vis a c)
    (birth removal : Event) (birthSupported : birth ∈ C.events) (removeSupported : removal ∈ C.events)
    (x t : Nat) (v : Int) (born : ((x,t),v) ∈ (step {} birth).births)
    (removed : (x,t) ∈ (step {} removal).removed) : C.vis birth removal := by
  obtain ⟨b,supported,before,w,born'⟩ := honest_remove_birth C honest trans removal removeSupported _ removed
  have time := (birth_effect_iff birth x t v).mp born
  have time' := (birth_effect_iff b x t w).mp born'
  have equal : b = birth := C.replayContext.ts_unique supported birthSupported (time'.2.trans time.2.symm)
  exact equal ▸ before

/-- Any birth of an absent element is disabled by a visible removal in the
same finite cut. This supplies the empty-case reset witness. -/
theorem absent_birth_has_remover (C : Configuration D)
    (honest : MintHonest D generation.CanIssue C)
    (trans : ∀ {a b c : Event}, C.vis a b → C.vis b c → C.vis a c)
    (events : List Event) (E : Set Event) (enumerated : listPermOf events E)
    (supported : ∀ e ∈ E, e ∈ C.events)
    (x : Nat) (absent : priority (applySeq D.toUpdateSig D.init events) x = none)
    (birth : Event) (member : birth ∈ E) (v : Int) (add : birth.op = .add x v) :
    ∃ removal ∈ E, C.vis birth removal ∧ ∃ observed, removal.op = .remove x observed := by
  have born : ((x,birth.time),v) ∈ (step {} birth).births := (birth_effect_iff birth _ _ _).mpr ⟨add,rfl⟩
  have known : ((x,birth.time),v) ∈ (applySeq D.toUpdateSig D.init events).births :=
    (fold_births D.init events _).mpr (Or.inr ⟨birth,(enumerated.2 _).mpr member,born⟩)
  have removed : (x,birth.time) ∈ (applySeq D.toUpdateSig D.init events).removed := by
    by_contra alive
    have live : x ∈ elements (applySeq D.toUpdateSig D.init events) :=
      Finset.mem_image.mpr ⟨((x,birth.time),v),Finset.mem_filter.mpr ⟨known,alive⟩,rfl⟩
    exact (priority_none_iff _ _).mp absent live
  rcases (fold_removed D.init events _).mp removed with empty | ⟨r,hr,killed⟩
  · exact False.elim (Finset.notMem_empty _ empty)
  · have inE := (enumerated.2 r).mp hr
    have before := removed_birth_visible C honest trans birth r (supported birth member)
      (supported r inE) x birth.time v born killed
    obtain ⟨observed,op,_⟩ := (remove_effect_iff r _ _).mp killed
    exact ⟨r,inE,before,observed,op⟩

/-- Once a maximal same-element removal is chosen for an absent element, no
Add of that element can follow it in visibility. All remaining successors are
increments and are ordinary absent-element no-ops. -/
theorem absent_no_add_after_maximal_remove (C : Configuration D)
    (honest : MintHonest D generation.CanIssue C)
    (trans : ∀ {a b c : Event}, C.vis a b → C.vis b c → C.vis a c)
    (events : List Event) (E : Set Event) (enumerated : listPermOf events E)
    (supported : ∀ e ∈ E, e ∈ C.events)
    (x : Nat) (absent : priority (applySeq D.toUpdateSig D.init events) x = none)
    (r : Event)
    (maximal : ∀ q ∈ E, (∃ observed, q.op = .remove x observed) → ¬ C.vis r q)
    (a : Event) (member : a ∈ E) (v : Int) (add : a.op = .add x v) : ¬ C.vis r a := by
  intro before
  obtain ⟨q,inE,after,isRemove⟩ := absent_birth_has_remover C honest trans events E enumerated
    supported x absent a member v add
  exact maximal q inE isRemove (trans before after)

/-- A source-valid Inc requires a known, visible prior Add; presence is not
inferred merely from the request label or from an arbitrary replay prefix. -/
theorem honest_inc_prior_birth (C : Configuration D)
    (honest : MintHonest D generation.CanIssue C)
    (trans : ∀ {a b c : Event}, C.vis a b → C.vis b c → C.vis a c)
    (e : Event) (member : e ∈ C.events) (x : Nat) (n : Int) (observed : Finset Nat)
    (inc : e.op = .inc x n observed) :
    ∃ birth ∈ C.events, C.vis birth e ∧ ∃ v, birth.op = .add x v := by
  obtain ⟨past,pastEnum,_,guard⟩ := honest e member
  have complete := birthComplete_closed_fold C honest trans past _ pastEnum
    (fun e he => he.1) (fun a b ab hb => ⟨C.vis_src ab,trans ab hb.2⟩)
  have present : Instances.PublishedAddWinsPriorityQueue.lookup (applySeq D.toUpdateSig D.init past) x = true := by
    rcases e with ⟨t,r,op⟩
    change op = .inc x n observed at inc
    subst op
    change prepare _ t r (.inc x n) = some (t,r,.inc x n observed) at guard
    cases h : Instances.PublishedAddWinsPriorityQueue.lookup (applySeq D.toUpdateSig D.init past) x <;>
      simp [prepare,Instances.PublishedAddWinsPriorityQueue.prepare,h] at guard ⊢
  have memberKey : x ∈ elements (applySeq D.toUpdateSig D.init past) := by
    rw [elements_eq_source _ complete]
    exact of_decide_eq_true present
  obtain ⟨⟨⟨key,t⟩,v⟩,hb,keyEq⟩ := Finset.mem_image.mp memberKey
  obtain ⟨born,_⟩ := Finset.mem_filter.mp hb
  change key = x at keyEq
  subst key
  rcases (fold_births D.init past ((x,t),v)).mp born with empty | ⟨birth,hbirth,born⟩
  · exact False.elim (Finset.notMem_empty _ empty)
  · have evidence := (pastEnum.2 birth).mp hbirth
    exact ⟨birth,evidence.1,evidence.2,v,((birth_effect_iff birth x t v).mp born).1⟩

private def VersionsBirthComplete (C : Configuration D) : Prop :=
  ∀ v s E, C.ver v = some (s,E) → BirthComplete s

private theorem birthComplete_raw_step {C C' : Configuration D} {label : Label D}
    (invariant : VersionsBirthComplete C) (raw : Step D C label C')
    (guard : ∀ t r o, label = .apply t r o → ∀ v s E,
      C.head r = some v → C.ver v = some (s,E) → generation.CanIssue (t,r,o) s) :
    VersionsBirthComplete C' := by
  cases raw with
  | fork freshReplica sourceHead sourceVersion freshVersion rank C' vis ver head parents =>
    intro w state E stored
    rw [ver] at stored
    dsimp only at stored
    split at stored
    · cases stored
      exact invariant _ _ _ sourceVersion
    · exact invariant _ _ _ stored
  | apply headAt versionAt freshTime freshStore freshVersion rank C' vis ver head parents =>
    intro w state E stored
    rw [ver] at stored
    dsimp only at stored
    split at stored
    · cases stored
      exact birthComplete_prepared _ (invariant _ _ _ versionAt) _
        (guard _ _ _ rfl _ _ _ headAt versionAt)
    · exact invariant _ _ _ stored
  | merge head₁ head₂ version₁ version₂ gca versionGCA freshVersion rank₁ rank₂ C' vis ver head parents =>
    intro w state E stored
    rw [ver] at stored
    dsimp only at stored
    split at stored
    · cases stored
      exact birthComplete_merge {} _ _ (invariant _ _ _ version₁) (invariant _ _ _ version₂)
    · exact invariant _ _ _ stored
  | query stateAt value => exact invariant

private theorem birthComplete_issued_step {C C' : Configuration D} {label : Label D}
    (invariant : VersionsBirthComplete C) (issued : IssuedStep D generation C label C') :
    VersionsBirthComplete C' := by
  apply birthComplete_raw_step invariant issued.toRaw
  cases issued with
  | nonApply raw nonApply =>
    intro t r o equal
    exact False.elim (nonApply t r o equal)
  | apply headAt versionAt guard raw =>
    intro t' r' o' equal w state E head stored
    cases equal
    have sameVersion := Option.some.inj (headAt.symm.trans head)
    rw [← sameVersion] at stored
    rw [stored] at versionAt
    simp only [Option.map_some,Option.some.injEq] at versionAt
    simpa only [← versionAt] using guard

private theorem birthComplete_issued_stepV {C C' : Configuration D} {label : Label D}
    (invariant : VersionsBirthComplete C)
    (issued : IssuedStepV D (canonicalVirtualMergeBase D) generation C label C') :
    VersionsBirthComplete C' := by
  cases issued with
  | base one => exact birthComplete_issued_step invariant one
  | virtual raw notBase =>
    cases raw with
    | base one => exact False.elim (notBase one)
    | mergeVirtual head₁ head₂ version₁ version₂ freshVersion rank₁ rank₂ C' vis ver head parents =>
      intro w state E stored
      rw [ver] at stored
      dsimp only at stored
      split at stored
      · cases stored
        exact birthComplete_merge {} _ _ (invariant _ _ _ version₁) (invariant _ _ _ version₂)
      · exact invariant _ _ _ stored

/-- Every allocated stored version is birth-complete, for ordinary and recursive
virtual-base executions. No causal delivery assumption on a separate op-based
network is asserted: Sal transfers whole stored versions. -/
theorem birthComplete_versions {C : Configuration D}
    (reach : MintCertifiedReachV D (canonicalVirtualMergeBase D) generation C) :
    ∀ v s E, C.ver v = some (s,E) → BirthComplete s := by
  induction reach with
  | init =>
    intro v s E stored
    change (if v = 0 then some (D.init,∅) else none) = some (s,E) at stored
    split at stored
    · cases stored; exact birthComplete_init
    · cases stored
  | step previous before one after ih => exact birthComplete_issued_stepV ih one

#print axioms birthComplete_prepared
#print axioms elements_eq_source
#print axioms birthComplete_versions
#print axioms honest_increment_birth
#print axioms birthComplete_closed_fold
#print axioms honest_remove_birth
#print axioms attached_increment_visible
#print axioms surviving_birth_successor
#print axioms absent_birth_has_remover
#print axioms absent_no_add_after_maximal_remove
#print axioms honest_inc_prior_birth
end Sal.MRDTs.Paper1.PriorityQueueSameRecord
