import Sal.MRDTs.Instances.NotionCoreMachinePrefix
import Sal.MRDTs.Instances.NotionCoreMachineBirths
import Sal.MRDTs.Instances.NotionCoreTableView

/-! Exact table and pending-delete representation through actual accepted
machine execution. This retrospective layer does not establish replay progress. -/
namespace Sal.MRDTs.Instances.NotionCoreMachineTables
open NotionRunAllocation (Id)
open NotionCorePayload (BlockKey Transaction Operation)
open NotionCoreParentMap (Row Table)
open NotionCoreMachine

private def fetch (entries : List (Nat × Instance)) (key : Nat) : Instance :=
  ((entries.find? (fun pair => pair.1 == key)).map Prod.snd).getD {}

private theorem fetch_cons (pair : Nat × Instance) (rest : List (Nat × Instance)) (key : Nat) :
    fetch (pair :: rest) key = if pair.1 = key then pair.2 else fetch rest key := by
  by_cases same : pair.1 = key
  · simp [fetch, List.find?, same]
  · have no : (pair.1 == key) = false := Bool.eq_false_iff.mpr (by simpa using same)
    simp [fetch, List.find?, same, no]

private theorem fetch_updated (entries : List (Nat × Instance)) (inst key : Nat) (value : Instance) :
    fetch (entries.map (fun pair => if pair.1 = inst then (inst,value) else pair)) key =
      if key = inst ∧ entries.any (fun pair => pair.1 == inst) then value else fetch entries key := by
  induction entries with
  | nil => simp [fetch]
  | cons pair rest ih =>
    simp only [List.map_cons, fetch_cons, List.any_cons]
    by_cases changed : pair.1 = inst
    · by_cases selected : key = inst
      · simp [changed, selected]
      · have different : inst ≠ key := Ne.symm selected
        simp [changed, selected, different, ih]
    · have no : (pair.1 == inst) = false := Bool.eq_false_iff.mpr (by simpa using changed)
      by_cases selected : pair.1 = key
      · have different : key ≠ inst := by intro same; exact changed (selected.trans same)
        simp [selected, different]
      · simp only [if_neg changed, if_neg selected]
        rw [ih, no]
        rfl

/-- Actual get/put storage equations do not require a unique instance map. -/
theorem getInstance_put (state : State) (inst key : Nat) (value : Instance) :
    getInstance (putInstance state inst value) key = if key = inst then value else getInstance state key := by
  unfold putInstance
  split
  · simp only [beq_iff_eq]
    change fetch (state.instances.map (fun pair => if pair.1 = inst then (inst,value) else pair)) key = _
    rw [fetch_updated]
    simp_all [fetch, getInstance]
  · rename_i absent
    have no : state.instances.find? (fun pair => pair.1 == inst) = none :=
      List.find?_eq_none.mpr (by
        intro pair member selected
        exact absent (List.any_eq_true.mpr ⟨pair, member, selected⟩))
    by_cases same : key = inst
    · subst key
      simp [getInstance, List.find?_append, no]
    · simp [getInstance, List.find?_append, same, Ne.symm same]

private theorem integrate_fresh_result (old result : Table) (row : Row)
    (fresh : row.item.id ∉ old.map (fun row => row.item.id))
    (accepted : integrate old row = some result) : result = old ++ [row] := by
  simp only [integrate, NotionCoreMachineRows.lookup_absent old row.item.id fresh] at accepted
  split at accepted
  · contradiction
  · exact (Option.some.inj accepted).symm

/-- Accepted integration of a fresh decoded run is exactly append. No rank
hypothesis is needed: a rejected self-origin cannot satisfy acceptance. -/
theorem integrateRows_fresh_result (old fresh result : Table)
    (unique : NotionCoreParentMap.Unique fresh)
    (apart : List.Disjoint (old.map (fun row => row.item.id)) (fresh.map (fun row => row.item.id)))
    (accepted : integrateRows old fresh = some result) : result = old ++ fresh := by
  induction fresh generalizing old with
  | nil => simpa [integrateRows] using accepted.symm
  | cons row rest ih =>
    cases first : integrate old row with
    | none => simp [integrateRows, first] at accepted
    | some middle =>
      simp [integrateRows, first] at accepted
      have absent : row.item.id ∉ old.map (fun row => row.item.id) := by
        intro present
        exact List.disjoint_left.mp apart present (by simp)
      have same := integrate_fresh_result old middle row absent first
      subst middle
      have restUnique := (List.nodup_cons.mp unique).2
      have restApart : List.Disjoint ((old ++ [row]).map (fun row => row.item.id))
          (rest.map (fun row => row.item.id)) := by
        apply List.disjoint_left.mpr
        intro id present newest
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at present
        rcases present with oldMember | rfl
        · exact List.disjoint_left.mp apart oldMember (List.mem_cons_of_mem _ newest)
        · exact (List.nodup_cons.mp unique).1 newest
      simpa only [List.append_assoc] using ih (old ++ [row]) restUnique restApart accepted


private theorem create_storage (state result : State) (block : BlockKey) (after : Option BlockKey)
    (accepted : applyOperation state (.create block after) = some result) :
    ∀ key, getInstance result key = getInstance state key := by
  simp only [applyOperation] at accepted
  split at accepted
  · simp only [Option.some.injEq] at accepted; subst result; simp
  · simp only [Option.some.injEq] at accepted; subst result
    intro key
    change getInstance (if state.instances.any (fun pair => pair.1 == blockName block)
      then state else putInstance state (blockName block) {}) key = _
    split
    · rfl
    · rename_i absent
      rw [getInstance_put]
      split
      · rename_i same
        subst key
        have missing : state.instances.find? (fun pair => pair.1 == blockName block) = none :=
          List.find?_eq_none.mpr (by intro pair member selected; exact absent (List.any_eq_true.mpr ⟨pair,member,selected⟩))
        simp [getInstance, missing]
      · rfl

private theorem move_storage (state result : State) (block inst : BlockKey)
    (marker : Id) (target : BlockKey)
    (accepted : applyOperation state (.moveInto block inst marker target) = some result) :
    ∀ key, getInstance result key = getInstance state key := by
  simp only [applyOperation] at accepted
  split at accepted
  · contradiction
  · cases selected : NotionCoreSliceForest.detachForest
      (NotionCorePhysicalReplay.address (blockName inst) marker) state.forest with
    | none => simp [selected] at accepted
    | some pair => simp [selected] at accepted; subst result; exact fun _ => rfl

private theorem insert_storage (state result : State) (block inst : BlockKey)
    (first : Id) (origin : NotionCoreOriginTree.Origin) (atoms : List Nat)
    (unique : NotionCoreParentMap.Unique (NotionCoreParentMap.runRows origin
      (NotionCorePayload.textItems first atoms (fun id => decide (id ∈ (getInstance state (blockName inst)).pending)))))
    (apart : List.Disjoint ((getInstance state (blockName inst)).rows.map (fun row => row.item.id))
      ((NotionCoreParentMap.runRows origin (NotionCorePayload.textItems first atoms
        (fun id => decide (id ∈ (getInstance state (blockName inst)).pending)))).map (fun row => row.item.id)))
    (accepted : applyOperation state (.insert block inst first origin atoms) = some result) :
    ∀ key, getInstance result key = if key = blockName inst then
      {getInstance state (blockName inst) with rows := (getInstance state (blockName inst)).rows ++
        (NotionCoreParentMap.runRows origin (NotionCorePayload.textItems first atoms
          (fun id => decide (id ∈ (getInstance state (blockName inst)).pending))))}
      else getInstance state key := by
  simp only [applyOperation] at accepted
  cases selected : integrateRows (getInstance state (blockName inst)).rows
    (NotionCoreParentMap.runRows origin (NotionCorePayload.textItems first atoms
      (fun id => decide (id ∈ (getInstance state (blockName inst)).pending)))) with
  | none => simp [selected] at accepted
  | some rows =>
      have equal := integrateRows_fresh_result _ _ rows unique apart selected
      simp [selected] at accepted; subst result
      simp [getInstance_put, equal]

private theorem erase_storage (state result : State) (block inst : BlockKey) (targets : List Id)
    (accepted : applyOperation state (.erase block inst targets) = some result) :
    ∀ key, getInstance result key = if key = blockName inst then
      ⟨NotionCoreParentErase.erase targets (getInstance state (blockName inst)).rows,
       (getInstance state (blockName inst)).pending ++ targets⟩ else getInstance state key := by
  simp only [applyOperation, Option.some.injEq] at accepted; subst result
  exact fun key => getInstance_put state (blockName inst) key _

private theorem marker_storage (state result : State) (block inst : BlockKey)
    (id : Id) (origin : NotionCoreOriginTree.Origin)
    (fresh : id ∉ (getInstance state (blockName inst)).rows.map (fun row => row.item.id))
    (accepted : applyOperation state (.marker block inst id origin) = some result) :
    ∀ key, getInstance result key = if key = blockName inst then
      {getInstance state (blockName inst) with rows := (getInstance state (blockName inst)).rows ++
        [⟨⟨id,.split⟩,origin⟩]} else getInstance state key := by
  simp only [applyOperation] at accepted
  cases selected : integrate (getInstance state (blockName inst)).rows ⟨⟨id,.split⟩,origin⟩ with
  | none => simp [selected] at accepted
  | some rows =>
      have equal := integrate_fresh_result _ rows _ fresh selected
      simp only [selected] at accepted
      dsimp only [Bind.bind, Option.bind] at accepted
      split at accepted
      · contradiction
      · dsimp only at accepted
        split at accepted
        · simp at accepted; subst result
          intro key
          change getInstance (putInstance state (blockName inst) _) key = _
          rw [getInstance_put, equal]
        · contradiction


def birthIds (txs : List Transaction) : List Id :=
  txs.flatMap fun tx => (NotionCorePayload.births tx (fun _ _ => false)).map NotionCorePayload.birthId

def View (state : State) (txs : List Transaction) : Prop :=
  ∀ inst, getInstance state (blockName inst) =
    ⟨NotionCoreTableView.rows txs inst, NotionCoreTableView.targets txs inst⟩

private theorem transaction_id_member (tx : Transaction) (inst : BlockKey)
    (deleted : BlockKey → Id → Bool) (id : Id)
    (member : id ∈ (NotionCoreMachinePrefix.transactionRows tx inst deleted).map (fun row => row.item.id)) :
    id ∈ (NotionCorePayload.births tx (fun _ _ => false)).map NotionCorePayload.birthId := by
  obtain ⟨row, present, same⟩ := List.mem_map.mp member
  have birth := (NotionCoreMachinePrefix.transaction_row_member tx inst deleted row).mp present
  have belongs : id ∈ (NotionCorePayload.births tx deleted).map NotionCorePayload.birthId :=
    List.mem_map.mpr ⟨(inst,row),birth,same⟩
  rw [NotionCorePayload.birth_ids] at belongs ⊢
  exact belongs

private theorem view_id_member (state : State) (pre : List Transaction) (view : View state pre)
    (inst : BlockKey) (id : Id)
    (member : id ∈ (getInstance state (blockName inst)).rows.map (fun row => row.item.id)) :
    id ∈ birthIds pre := by
  rw [view inst] at member
  simp only [NotionCoreTableView.rows, NotionCoreParentErase.erase,
    List.map_map] at member
  change id ∈ (NotionCoreTableView.birthsRows pre inst).map (fun row => row.item.id) at member
  obtain ⟨row, present, same⟩ := List.mem_map.mp member
  obtain ⟨tx, earlier, born⟩ := List.mem_flatMap.mp present
  exact List.mem_flatMap.mpr ⟨tx,earlier,transaction_id_member tx inst (fun _ _ => false) id
    (List.mem_map.mpr ⟨row,born,same⟩)⟩

private theorem fresh_transaction_rows (state : State) (pre : List Transaction) (tx : Transaction)
    (view : View state pre) (unique : (birthIds (pre ++ [tx])).Nodup)
    (inst : BlockKey) (deleted : BlockKey → Id → Bool) :
    List.Disjoint ((getInstance state (blockName inst)).rows.map (fun row => row.item.id))
      ((NotionCoreMachinePrefix.transactionRows tx inst deleted).map (fun row => row.item.id)) := by
  have separate : List.Disjoint (birthIds pre)
      ((NotionCorePayload.births tx (fun _ _ => false)).map NotionCorePayload.birthId) := by
    simpa [birthIds] using (List.nodup_append'.mp (by simpa [birthIds] using unique)).2.2
  apply List.disjoint_left.mpr
  intro id old new
  exact List.disjoint_left.mp separate (view_id_member state pre view inst id old)
    (transaction_id_member tx inst deleted id new)

private theorem accept_cons (state result : State) (op : Operation) (rest : List Operation)
    (accepted : applyOperations state (op :: rest) = some result) :
    ∃ middle, applyOperation state op = some middle ∧ applyOperations middle rest = some result := by
  cases first : applyOperation state op with
  | none => simp [applyOperations, first] at accepted
  | some middle => exact ⟨middle,rfl,by simpa [applyOperations,first] using accepted⟩

private theorem insert_rows (id : Id) (block key inst : BlockKey)
    (origin : NotionCoreOriginTree.Origin) (atoms : List Nat) (deleted : BlockKey → Id → Bool) :
    NotionCoreMachinePrefix.transactionRows ⟨id,.insert block key origin atoms⟩ inst deleted =
      if key = inst then NotionCoreParentMap.runRows origin (NotionCorePayload.textItems id atoms (deleted key)) else [] := by
  by_cases same : key = inst
  · subst key
    simp [NotionCoreMachinePrefix.transactionRows, NotionCorePayload.births, NotionCorePayload.operations,
      NotionCorePayload.Operation.births, List.filterMap_map, Function.comp_def]
  · simp [NotionCoreMachinePrefix.transactionRows, NotionCorePayload.births, NotionCorePayload.operations,
      NotionCorePayload.Operation.births, List.filterMap_map, Function.comp_def, same]


private theorem bootstrap_rows (id : Id) (inst : BlockKey) (atoms : List Nat)
    (deleted : BlockKey → Id → Bool) :
    NotionCoreMachinePrefix.transactionRows ⟨id,.bootstrap atoms⟩ inst deleted =
      if .initial = inst then NotionCoreParentMap.runRows .start
        (NotionCorePayload.textItems id atoms (deleted .initial)) else [] := by
  have same : NotionCoreMachinePrefix.transactionRows ⟨id,.bootstrap atoms⟩ inst deleted =
      NotionCoreMachinePrefix.transactionRows ⟨id,.insert .initial .initial .start atoms⟩ inst deleted := by
    simp [NotionCoreMachinePrefix.transactionRows, NotionCorePayload.births, NotionCorePayload.operations,
      NotionCorePayload.Operation.births]
  rw [same, insert_rows]

private theorem split_rows (id : Id) (block key inst : BlockKey)
    (origin : NotionCoreOriginTree.Origin) (deleted : BlockKey → Id → Bool) :
    NotionCoreMachinePrefix.transactionRows ⟨id,.split block key origin⟩ inst deleted =
      if key = inst then [⟨⟨id,.split⟩,origin⟩] else [] := by
  by_cases same : key = inst <;>
    simp [NotionCoreMachinePrefix.transactionRows, NotionCorePayload.births, NotionCorePayload.operations,
      NotionCorePayload.Operation.births, same]

/-- Exact transaction storage change, independently of its slice routing.
Freshness is derived from the existing replay view and whole-list birth ND. -/
private theorem transaction_storage (state result : State) (pre : List Transaction) (tx : Transaction)
    (view : View state pre) (unique : (birthIds (pre ++ [tx])).Nodup)
    (accepted : applyTransaction state tx = some result) :
    ∀ query, getInstance result (blockName query) =
      ⟨NotionCoreParentErase.erase (NotionCoreTableView.transactionTargets tx query)
          (getInstance state (blockName query)).rows ++
        NotionCoreMachinePrefix.transactionRows tx query
          (fun _ id => decide (id ∈ (getInstance state (blockName query)).pending)),
       (getInstance state (blockName query)).pending ++ NotionCoreTableView.transactionTargets tx query⟩ := by
  cases tx with
  | mk id payload =>
    cases payload with
    | create afterBlock =>
      have step : applyOperation state (.create (.issued id) afterBlock) = some result := by
        simpa [applyTransaction, NotionCorePayload.operations, applyOperations] using accepted
      intro query
      rw [create_storage state result (.issued id) afterBlock step]
      simp [NotionCoreTableView.transactionTargets, NotionCoreMachinePrefix.transactionRows,
        NotionCorePayload.births, NotionCorePayload.operations, NotionCorePayload.Operation.births]
    | erase block key ids =>
      have step : applyOperation state (.erase block key ids) = some result := by
        simpa [applyTransaction, NotionCorePayload.operations, applyOperations] using accepted
      intro query
      rw [erase_storage state result block key ids step]
      by_cases same : key = query
      · subst query
        simp [NotionCoreTableView.transactionTargets, NotionCoreMachinePrefix.transactionRows,
          NotionCorePayload.births, NotionCorePayload.operations, NotionCorePayload.Operation.births]
      · have different : blockName query ≠ blockName key := by
          intro equal; exact same (blockName_injective equal).symm
        simp [different, same, NotionCoreTableView.transactionTargets, NotionCoreMachinePrefix.transactionRows,
          NotionCorePayload.births, NotionCorePayload.operations, NotionCorePayload.Operation.births]
    | insert block key origin atoms =>
      have step : applyOperation state (.insert block key id origin atoms) = some result := by
        simpa [applyTransaction, NotionCorePayload.operations, applyOperations] using accepted
      let deleted : BlockKey → Id → Bool := fun _ id => decide (id ∈ (getInstance state (blockName key)).pending)
      have freshUnique := NotionCoreMachinePrefix.transaction_rows_unique ⟨id,.insert block key origin atoms⟩ key deleted
      have apart := fresh_transaction_rows state pre ⟨id,.insert block key origin atoms⟩ view unique key deleted
      rw [insert_rows, if_pos rfl] at freshUnique apart
      have storage := insert_storage state result block key id origin atoms freshUnique apart step
      intro query
      rw [storage (blockName query), insert_rows]
      by_cases same : key = query
      · subst query
        simp [NotionCoreTableView.transactionTargets]
      · have different : blockName query ≠ blockName key := by
          intro equal; exact same (blockName_injective equal).symm
        simp [different, same, NotionCoreTableView.transactionTargets]
    | bootstrap atoms =>
      change applyOperations state [.create .initial none,.insert .initial .initial id .start atoms] = some result at accepted
      obtain ⟨middle, created, later⟩ := accept_cons state result _ _ accepted
      have inserted : applyOperation middle (.insert .initial .initial id .start atoms) = some result := by
        simpa [applyOperations] using later
      have frame := create_storage state middle .initial none created
      let deleted : BlockKey → Id → Bool := fun _ id => decide (id ∈ (getInstance state (blockName .initial)).pending)
      have freshUnique := NotionCoreMachinePrefix.transaction_rows_unique ⟨id,.bootstrap atoms⟩ .initial deleted
      have apart := fresh_transaction_rows state pre ⟨id,.bootstrap atoms⟩ view unique .initial deleted
      rw [bootstrap_rows, if_pos rfl] at freshUnique apart
      have freshUnique' : NotionCoreParentMap.Unique (NotionCoreParentMap.runRows .start
          (NotionCorePayload.textItems id atoms (fun id => decide (id ∈ (getInstance middle (blockName .initial)).pending)))) := by
        simpa only [frame] using freshUnique
      have apart' : List.Disjoint ((getInstance middle (blockName .initial)).rows.map (fun row => row.item.id))
          ((NotionCoreParentMap.runRows .start (NotionCorePayload.textItems id atoms
            (fun id => decide (id ∈ (getInstance middle (blockName .initial)).pending)))).map (fun row => row.item.id)) := by
        simpa only [frame] using apart
      have storage := insert_storage middle result .initial .initial id .start atoms freshUnique' apart' inserted
      intro query
      rw [storage (blockName query), bootstrap_rows]
      simp only [frame]
      by_cases same : .initial = query
      · subst query; simp [NotionCoreTableView.transactionTargets]
      · have different : blockName query ≠ blockName .initial := by
          intro equal; exact same (blockName_injective equal).symm
        simp [different, same, NotionCoreTableView.transactionTargets]
    | split block key origin =>
      change applyOperations state [.create (.issued id) (some block),.marker block key id origin,
        .moveInto block key id (.issued id)] = some result at accepted
      obtain ⟨middle, created, later⟩ := accept_cons state result _ _ accepted
      obtain ⟨marked, markerAccepted, later⟩ := accept_cons middle result _ _ later
      have moved : applyOperation marked (.moveInto block key id (.issued id)) = some result := by
        simpa [applyOperations] using later
      have frame := create_storage state middle (.issued id) (some block) created
      have apart := fresh_transaction_rows state pre ⟨id,.split block key origin⟩ view unique key (fun _ _ => false)
      rw [split_rows, if_pos rfl] at apart
      have fresh : id ∉ (getInstance middle (blockName key)).rows.map (fun row => row.item.id) := by
        rw [frame]
        intro member
        exact List.disjoint_left.mp apart member (by simp)
      have storage := marker_storage middle marked block key id origin fresh markerAccepted
      intro query
      rw [move_storage marked result block key id (.issued id) moved, storage (blockName query), split_rows]
      simp only [frame]
      by_cases same : key = query
      · subst query; simp [NotionCoreTableView.transactionTargets]
      · have different : blockName query ≠ blockName key := by
          intro equal; exact same (blockName_injective equal).symm
        simp [different, same, NotionCoreTableView.transactionTargets]


private theorem singleton_rows (tx : Transaction) (inst : BlockKey) :
    NotionCoreTableView.rows [tx] inst = NotionCoreMachinePrefix.transactionRows tx inst (fun _ _ => false) := by
  simp only [NotionCoreTableView.rows, NotionCoreTableView.targets, NotionCoreTableView.birthsRows,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  cases tx with
  | mk id payload =>
    cases payload <;> simp [NotionCoreTableView.transactionTargets]
    simp [NotionCoreMachinePrefix.transactionRows, NotionCorePayload.births,
      NotionCorePayload.operations, NotionCorePayload.Operation.births, NotionCoreParentErase.erase]

private theorem transaction_view (state result : State) (pre : List Transaction) (tx : Transaction)
    (view : View state pre) (unique : (birthIds (pre ++ [tx])).Nodup)
    (accepted : applyTransaction state tx = some result) : View result (pre ++ [tx]) := by
  intro inst
  rw [transaction_storage state result pre tx view unique accepted inst, view inst]
  congr 1
  · rw [NotionCoreTableView.transactionRows_pending, NotionCoreTableView.rows_append,
      singleton_rows]
    simp [NotionCoreTableView.targets]
  · simp [NotionCoreTableView.targets]

private theorem replay_append (state : State) (a b : List Transaction) :
    replay state (a ++ b) = (replay state a).bind (fun middle => replay middle b) := by
  induction a generalizing state with
  | nil => simp [replay]
  | cons tx rest ih =>
      cases first : applyTransaction state tx <;> simp [replay, first, ih]

/-- Exact complete table and pending-list representation for actual accepted
replay. Global decoded birth uniqueness is the only additional graph guard;
no per-step output representation or traversal equation is assumed. -/
theorem replay_view (txs : List Transaction) (state : State)
    (accepted : replay {} txs = some state) (unique : (birthIds txs).Nodup) : View state txs := by
  induction txs using List.reverseRecOn generalizing state with
  | nil =>
      simp [replay] at accepted
      subst state
      simp [View, getInstance, NotionCoreTableView.rows, NotionCoreTableView.targets, NotionCoreTableView.birthsRows]
  | append_singleton pre tx ih =>
      rw [replay_append] at accepted
      cases replayPrefix : replay {} pre with
      | none => simp [replayPrefix] at accepted
      | some before =>
          simp [replayPrefix, replay] at accepted
          have prior : (birthIds pre).Nodup := by
            have divided : (birthIds pre ++ (NotionCorePayload.births tx (fun _ _ => false)).map NotionCorePayload.birthId).Nodup := by
              simpa [birthIds] using unique
            exact (List.nodup_append'.mp divided).1
          exact transaction_view before state pre tx (ih before replayPrefix prior) unique accepted

theorem replay_tables (txs : List Transaction) (state : State)
    (accepted : replay {} txs = some state) (unique : (birthIds txs).Nodup) :
    ∀ inst, (getInstance state (blockName inst)).rows = NotionCoreTableView.rows txs inst ∧
      (getInstance state (blockName inst)).pending = NotionCoreTableView.targets txs inst := by
  intro inst
  have exactView := replay_view txs state accepted unique inst
  exact ⟨congrArg Instance.rows exactView, congrArg Instance.pending exactView⟩


private def a : Id := ⟨1,[65]⟩
private def b : Id := ⟨2,[65]⟩
private def x : Id := ⟨4,[66]⟩
private def marker : Id := ⟨3,[66]⟩
private def seed : Transaction := NotionCorePayload.bootstrap [97,98]
private def earlyDelete : Transaction := ⟨⟨3,[67]⟩,.erase .initial .initial [x]⟩
private def insertion : Transaction := ⟨x,.insert .initial .initial (.item a) [88]⟩
private def cut : Transaction := ⟨marker,.split .initial .initial (.item a)⟩
private def markerDelete : Transaction := ⟨⟨4,[67]⟩,.erase .initial .initial [marker]⟩
private def repeatedDelete : Transaction := ⟨⟨5,[67]⟩,.erase .initial .initial [b,b]⟩

/-- PASS+FAIL: raw accepted replay preserves an early deletion at a later
birth. This tests pending-delete semantics; it is not an honest-client
issuance witness for selecting an item that has not yet been born. -/
theorem pending_birth_control :
    (replay {} [seed,earlyDelete,insertion]).map (fun state => getInstance state (blockName .initial)) =
      some ⟨[⟨⟨a,.text 97 false⟩,.start⟩,⟨⟨b,.text 98 false⟩,.item a⟩,
        ⟨⟨x,.text 88 true⟩,.item a⟩],[x]⟩ ∧
    (replay {} [seed,earlyDelete,insertion]).map (fun state => getInstance state (blockName .initial)) ≠
      some ⟨[⟨⟨a,.text 97 false⟩,.start⟩,⟨⟨b,.text 98 false⟩,.item a⟩,
        ⟨⟨x,.text 88 false⟩,.item a⟩],[]⟩ := by decide

/-- PASS+FAIL: decoded target chronology and duplicates remain in the Lean
pending list; marker kind and parent links remain physical. JS's pending set
has the same membership, not this list's sequence or duplicate multiplicity. -/
theorem marker_pending_control :
    (replay {} [seed,cut,markerDelete,repeatedDelete]).map
      (fun state => getInstance state (blockName .initial)) =
      some ⟨[⟨⟨a,.text 97 false⟩,.start⟩,⟨⟨b,.text 98 true⟩,.item a⟩,
        ⟨⟨marker,.split⟩,.item a⟩],[marker,b,b]⟩ ∧
    (replay {} [seed,cut,markerDelete,repeatedDelete]).map
      (fun state => getInstance state (blockName (.issued marker))) ≠
      some ⟨[⟨⟨marker,.split⟩,.item a⟩],[marker,b,b]⟩ := by decide

/-- The same hand-derived state is also the deletion-aware algebraic table;
this links the concrete operational control to the representation's meaning. -/
theorem table_view_control :
    NotionCoreTableView.rows [seed,earlyDelete,insertion] .initial =
      [⟨⟨a,.text 97 false⟩,.start⟩,⟨⟨b,.text 98 false⟩,.item a⟩,⟨⟨x,.text 88 true⟩,.item a⟩] ∧
    NotionCoreTableView.targets [seed,earlyDelete,insertion] .initial ≠ [] := by decide

#print axioms replay_tables
end Sal.MRDTs.Instances.NotionCoreMachineTables
