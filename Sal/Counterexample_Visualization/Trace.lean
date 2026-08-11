import ProofWidgets

/-!
# Execution traces and their diagrams

The state-agnostic half of the counterexample visualizer: an execution as a tree
of `do` edges and three-way merges, and a ProofWidgets renderer for it.

Nothing here knows what a state *is* — everything is parametric in `σ` and asks
only for `[ToString σ]`. That is what lets one renderer serve representations
that have nothing in common: a Boolean-predicate set with a display universe
(`Sal/Counterexample_Visualization/WriterMonad_Set.lean`), a pair of such sets
(the add-wins set), and a bare `Int × Bool` (the enable-wins flag). A client
supplies its own state type, a `ToString` for it, and its pure `do_`/`merge`;
`stepWith` and `mergeWith` do the rest.

## Why a tree and not a log

The writer-monad layer in `WriterMonad_Set.lean` records an execution as a flat
list of `(pre, label, post)` transitions. That is enough to print, but not to
draw: recovering the branching structure from a flat log means scanning for the
reserved `"LMerge"`/`"AMerge"`/`"BMerge"` labels, and once an execution contains
more than one merge those scans cannot tell an inner merge's labels from the
outer one's. `Trace` carries the structure instead of recovering it, so
`renderTrace` recurses and the number of merges in a diagram is unbounded — the
add-wins-set defeater of
`Sal/ConditionedMRDTs/Refutations/InterLca2op_Defeater_Arbiter.lean` has four.
-/


/-! ## The trace -/

/-- An execution as a tree: `do_` edges along a replica, `mrg` where two versions
are reconciled against an LCA. -/
inductive Trace (σ : Type) where
  /-- A starting version, typically `init_st`. -/
  | leaf : σ → Trace σ
  /-- One `do_` edge: a labelled transition to a new version. -/
  | step : Trace σ → String → σ → Trace σ
  /-- A three-way merge: the LCA's trace, the two branch traces, the merged version. -/
  | mrg : Trace σ → Trace σ → Trace σ → σ → Trace σ
  /-- A version drawn elsewhere in the diagram, shown here as a single named node.
  A `Trace` is a tree but an execution is a DAG: when one version feeds several
  merges, draw it once and `ref` it thereafter. -/
  | ref : String → σ → Trace σ

/-- The version a trace ends at. -/
def Trace.result {σ : Type} : Trace σ → σ
  | .leaf s => s
  | .step _ _ s => s
  | .mrg _ _ _ s => s
  | .ref _ s => s

/-- Restart a trace as a bare node at the version it ended on. Open a branch with
this: the opening `leaf` is suppressed when the branch is drawn, so the version it
descends from appears once, at the merge's apex, instead of once per branch. -/
def Trace.reroot {σ : Type} (t : Trace σ) : Trace σ := .leaf t.result


/-! ## Building traces

Both combinators take the client's *pure* state functions — no logging, no
display bookkeeping — so a client whose state needs extra bookkeeping (a display
universe, say) wraps these rather than reimplementing them. -/

/-- Extend a trace by one operation, given a pure state transition and a way to
label it. `ω` is the client's operation type; nothing here constrains its shape. -/
def stepWith {σ ω : Type} (step : σ → ω → σ) (op_string : ω → String)
(t : Trace σ) (o : ω) : Trace σ :=
  .step t (op_string o) (step t.result o)

/-- A three-way merge node over three sub-traces, given a pure merge. Unlike the
flat-log form this nests: the branches may themselves be merges. -/
def mergeWith {σ : Type} (merge : σ → σ → σ → σ) (l a b : Trace σ) : Trace σ :=
  .mrg l a b (merge l.result a.result b.result)


/-! ## Drawing -/

open ProofWidgets Jsx in
/-- A state box. Generic over the state type: any `[ToString σ]` will do. -/
def renderNode  {σ : Type} [ToString σ]  (state : σ) : Html :=
  <div style={json% {
    border: "2px solid #3b82f6",
    borderRadius: "8px",
    padding: "12px 16px",
    backgroundColor: "#eff6ff",
    fontWeight: "bold",
    fontFamily: "arial",
    textAlign: "center",
    minWidth: "100px",
    margin: "0 auto",
    color: "#000000",
    fontSize: "20px"
  }}>
    {Html.text (toString state)}
  </div>

open ProofWidgets Jsx in
/-- A labelled connector between two state boxes. -/
def renderEdge (label : String) : Html :=
  <div style={json% {
    display: "flex",
    flexDirection: "column",
    alignItems: "center",
    margin: "5px 0"
  }}>
    <div style={json% {
      width: "2px",
      height: "20px",
      backgroundColor: "#6b7280"
    }}/>
    <div style={json% {
      padding: "4px 12px",
      backgroundColor: "#fef3c7",
      border: "1px solid #f59e0b",
      borderRadius: "4px",
      fontSize: "20px",
      fontWeight: "1000",
      margin: "5px 0",
      color: "#000000"
    }}>
      {Html.text label}
    </div>
    <div style={json% {
      width: "2px",
      height: "20px",
      backgroundColor: "#6b7280"
    }}/>
  </div>

open ProofWidgets Jsx in
/-- A grey caption above a node or a branch column. -/
def renderLabel (label : String) : Html :=
  <div style={json% {
    fontSize: "20px",
    fontWeight: "bold",
    color: "#6b7280",
    fontFamily: "arial",
    marginBottom: "10px"
  }}>
    {Html.text label}
  </div>

open ProofWidgets Jsx in
/-- Recursive trace renderer: a nested merge is drawn exactly like a top-level one.

`drawRoot := false` suppresses the trace's opening `leaf`, so a branch descending
from its merge's own LCA does not redraw the node sitting directly above it — the
shared version appears once, at the apex. Use `ref` instead of `leaf` for a branch
that starts at some *other* version: a `ref` is always drawn, with its name as a
caption. `Trace.reroot` builds the suppressed-`leaf` form. -/
def renderTraceInner {σ : Type} [ToString σ] (drawRoot : Bool) : Trace σ → Html
  | .leaf s => if drawRoot then renderNode s else Html.element "div" #[] #[]
  | .ref name s =>
    <div style={json% {
      display: "flex",
      flexDirection: "column",
      alignItems: "center"
    }}>
      {renderLabel name}
      {renderNode s}
    </div>
  | .step t label s =>
    <div style={json% {
      display: "flex",
      flexDirection: "column",
      alignItems: "center"
    }}>
      {renderTraceInner drawRoot t}
      {renderEdge label}
      {renderNode s}
    </div>
  | .mrg l a b r =>
    <div style={json% {
      display: "flex",
      flexDirection: "column",
      alignItems: "center"
    }}>
      {renderTraceInner drawRoot l}
      <div style={json% {
        display: "flex",
        justifyContent: "center",
        gap: "100px",
        width: "100%",
        marginTop: "20px",
        marginBottom: "20px"
      }}>
        <div style={json% {
          display: "flex",
          flexDirection: "column",
          alignItems: "center"
        }}>
          {renderLabel "Left Branch"}
          {renderTraceInner false a}
        </div>
        <div style={json% {
          display: "flex",
          flexDirection: "column",
          alignItems: "center"
        }}>
          {renderLabel "Right Branch"}
          {renderTraceInner false b}
        </div>
      </div>
      <div style={json% {
        fontSize: "20px",
        color: "#6b7280",
        fontFamily: "arial",
        marginBottom: "10px"
      }}>
        {Html.text "↓ All paths converge ↓"}
      </div>
      {renderNode r}
    </div>

open ProofWidgets Jsx in
/-- The entry point: `renderTraceInner` inside a framed panel. -/
def renderTrace {σ : Type} [ToString σ] (t : Trace σ) : Html :=
  <div style={json% {
    padding: "20px",
    backgroundColor: "#f9fafb",
    borderRadius: "8px",
    border: "2px solid #e5e7eb",
    display: "flex",
    flexDirection: "column",
    alignItems: "center"
  }}>
    {renderTraceInner true t}
  </div>
