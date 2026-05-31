import GaugeGeometry.QFT.Combinatorial.FeynmanGraphs
import GaugeGeometry.QFT.Combinatorial.OneLoopGraphs
import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic

namespace GaugeGeometry.QFT.Combinatorial

/--
A Wick pair contracts two external legs.
Version 1 is purely combinatorial and does not yet impose symmetry
or ordering conventions.
-/
structure WickPair where
  left : ExternalLeg
  right : ExternalLeg
  deriving DecidableEq

namespace WickPair

/--
A Wick pair is supported on a multiset of external legs if both legs
occur in that multiset.
-/
def SupportedOn (p : WickPair) (legs : Multiset ExternalLeg) : Prop :=
  p.left ∈ legs ∧ p.right ∈ legs

@[simp] theorem supportedOn_def (p : WickPair) (legs : Multiset ExternalLeg) :
    p.SupportedOn legs = (p.left ∈ legs ∧ p.right ∈ legs) := by
  rfl

end WickPair

/--
A Wick contraction is a multiset of Wick pairs.
-/
structure WickContraction where
  pairs : Multiset WickPair

namespace WickContraction

/--
Number of Wick pairs.
-/
def pairCount (C : WickContraction) : Nat :=
  C.pairs.card

/--
Number of contracted external-leg slots.
Each Wick pair consumes two legs.
-/
def contractedLegCount (C : WickContraction) : Nat :=
  2 * C.pairCount

/--
A contraction is complete on a multiset of external legs if it contracts
exactly all of them, counted with multiplicity.
-/
def IsCompleteOn (C : WickContraction) (legs : Multiset ExternalLeg) : Prop :=
  C.contractedLegCount = legs.card

/--
A contraction is complete for a Feynman graph if it is complete on the
graph's external legs.
-/
def IsCompleteFor (C : WickContraction) (G : FeynmanGraph) : Prop :=
  C.IsCompleteOn G.externalLegs

@[simp] theorem pairCount_def (C : WickContraction) :
    C.pairCount = C.pairs.card := by
  rfl

@[simp] theorem contractedLegCount_def (C : WickContraction) :
    C.contractedLegCount = 2 * C.pairCount := by
  rfl

@[simp] theorem isCompleteOn_def (C : WickContraction) (legs : Multiset ExternalLeg) :
    C.IsCompleteOn legs = (C.contractedLegCount = legs.card) := by
  rfl

@[simp] theorem isCompleteFor_def (C : WickContraction) (G : FeynmanGraph) :
    C.IsCompleteFor G = C.IsCompleteOn G.externalLegs := by
  rfl

/--
The empty Wick contraction.
-/
def emptyContraction : WickContraction where
  pairs := 0

@[simp] theorem emptyContraction_pairs :
    emptyContraction.pairs = 0 := by
  rfl

@[simp] theorem emptyContraction_pairCount :
    emptyContraction.pairCount = 0 := by
  rfl

@[simp] theorem emptyContraction_contractedLegCount :
    emptyContraction.contractedLegCount = 0 := by
  rfl

theorem emptyContraction_complete_on_empty :
    emptyContraction.IsCompleteOn 0 := by
  simp [WickContraction.IsCompleteOn]

theorem emptyContraction_complete_for_emptyGraph :
    emptyContraction.IsCompleteFor FeynmanGraph.emptyGraph := by
  simp [WickContraction.IsCompleteFor, FeynmanGraph.emptyGraph_externalLegs]

theorem emptyContraction_complete_for_oneLoopTadpole :
    emptyContraction.IsCompleteFor oneLoopTadpole := by
  simp [WickContraction.IsCompleteFor, oneLoopTadpole_externalLegs]

/--
If a contraction is complete on a leg multiset, then that multiset has even size.
-/
theorem completeOn_has_even_legCount
    (C : WickContraction) (legs : Multiset ExternalLeg)
    (h : C.IsCompleteOn legs) :
    ∃ k : Nat, legs.card = 2 * k := by
  refine ⟨C.pairCount, ?_⟩
  exact h.symm

end WickContraction

/--
A Wick expansion term is a Feynman graph equipped with a contraction
of its external legs.
-/
structure WickExpansionTerm where
  graph : FeynmanGraph
  contraction : WickContraction

namespace WickExpansionTerm

/--
Basic well-formedness for a Wick expansion term:
the graph is well formed and the contraction is complete for that graph.
-/
def WellFormed (T : WickExpansionTerm) : Prop :=
  T.graph.WellFormed ∧ T.contraction.IsCompleteFor T.graph

@[simp] theorem wellFormed_def (T : WickExpansionTerm) :
    T.WellFormed = (T.graph.WellFormed ∧ T.contraction.IsCompleteFor T.graph) := by
  rfl

@[simp] theorem WickExpansionTerm_eta (T : WickExpansionTerm) :
    WickExpansionTerm.mk T.graph T.contraction = T := by
  cases T
  rfl

end WickExpansionTerm

/--
The empty vacuum Wick-expansion term.
-/
def emptyVacuumTerm : WickExpansionTerm where
  graph := FeynmanGraph.emptyGraph
  contraction := WickContraction.emptyContraction

theorem emptyVacuumTerm_wellFormed :
    emptyVacuumTerm.WellFormed := by
  constructor
  · exact FeynmanGraph.emptyGraph_wellFormed
  · exact WickContraction.emptyContraction_complete_for_emptyGraph

/--
The canonical one-loop tadpole viewed as a Wick-expansion term.
Since it has no external legs, the empty contraction is complete for it.
-/
def oneLoopTadpoleVacuumTerm : WickExpansionTerm where
  graph := oneLoopTadpole
  contraction := WickContraction.emptyContraction

@[simp] theorem oneLoopTadpoleVacuumTerm_graph :
    oneLoopTadpoleVacuumTerm.graph = oneLoopTadpole := by
  rfl

theorem oneLoopTadpoleVacuumTerm_wellFormed :
    oneLoopTadpoleVacuumTerm.WellFormed := by
  constructor
  · exact oneLoopTadpole_wellFormed
  · exact WickContraction.emptyContraction_complete_for_oneLoopTadpole

end GaugeGeometry.QFT.Combinatorial
