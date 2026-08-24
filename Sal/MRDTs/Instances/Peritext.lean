import Sal.MRDTs.Instances.ProductionRGA

/-! # Native Peritext certificate

Peritext is an embedded RGA whose payload contains characters and invisible
format boundaries.  Its replicated ordering proof is therefore the generic
payload-parametric EmbedRGA proof; this module supplies the rich-text payload
and the independent sequential renderer exposed to clients.
-/

namespace Sal.MRDTs.Instances.Peritext

open Sal.MRDTs.Foundation
open Sal.EmbedRGA (OrderedPrefixCode)
open Sal.MRDTs.Instances.EmbedRGA

inductive Mark where
  | bold | italic | underline | strike
  | link (url : String)
  | comment (author : Nat) (text : String)
  | color (rgb : Nat)
  | heading (level : Nat)
  deriving DecidableEq

inductive Element where
  | char (codepoint : Nat)
  | bound (markId : Nat) (mark : Mark) (isStart : Bool)
  deriving DecidableEq, Inhabited

abbrev D (Γ : OrderedPrefixCode) := E Γ Element

/-- The complete algebraic, generation, virtual-LCA, and sequential package
for the embedded Peritext representation. -/
noncomputable def replayVerified (Γ : OrderedPrefixCode) : ReplayVerifiedMRDT (D Γ) :=
  ProductionRGA.replayEmbed Γ

/-- Public merged-history certificate inherited from the payload-parametric
EmbedRGA legalization theorem. -/
noncomputable def verified (Γ : OrderedPrefixCode) : VerifiedMRDT (D Γ) :=
  ProductionRGA.embed Γ

abbrev OpenMarks := List (Nat × Mark)
abbrev Rendered := Nat × OpenMarks

def renderAux : List Element → OpenMarks → List Rendered
  | [], _ => []
  | Element.char c :: rest, acc => (c, acc) :: renderAux rest acc
  | Element.bound id mark side :: rest, acc =>
      if side then renderAux rest ((id, mark) :: acc)
      else renderAux rest (acc.filter fun p => p.1 != id)

def render (elements : List Element) : List Rendered := renderAux elements []

def document (state : EState Element) : List Element :=
  state.map fun record => record.2.1

def editorDocument (state : List (Nat × Element)) : List Element :=
  state.map Prod.snd

/-- Sequentially certified histories render exactly like the ordinary editor
buffer obtained by splicing after anchors and deleting by identifier. -/
theorem render_sequentially_correct (Γ : OrderedPrefixCode)
    (ops : List (Op (EOp Element)))
    (h : LinearMintHistory (D Γ) eApplicable ops) :
    render (document (applySeq (D Γ).toCRDTSig (D Γ).init ops)) =
      render (editorDocument ((replayVerified Γ).Machine.run ops)) := by
  have hs := (replayVerified Γ).sequentially_correct ops h
  simpa [document, editorDocument, eProj, List.map_map] using
    congrArg (fun state => render (state.map Prod.snd)) hs

#print axioms replayVerified
#print axioms verified
#print axioms render_sequentially_correct

end Sal.MRDTs.Instances.Peritext
