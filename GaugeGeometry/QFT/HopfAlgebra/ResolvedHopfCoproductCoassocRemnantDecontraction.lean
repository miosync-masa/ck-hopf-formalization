import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantScout
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromoteGen

/-!
# R-6c-heart-6a-4b — remnant de-contraction geometry supply (`remnantGen` ← `remnantClass_eq`)

The remnant of a forest choice is a genuine de-contraction (6a-4 scout).  Rather than duplicate the
hard contract-twice geometry, this file **normalizes** it into one supply
`ResolvedRemnantDecontractionSupply` whose only graph obligation is the **class equality**

  `(remnantComponent o).toResolvedFeynmanGraph.toResolvedClass = (contractedSourceGraph o).toResolvedClass`

— exactly the same shape as `right_eq`'s contract-twice = contract-once class equality (5c-2).  From it
the remnant generator equality `remnantGen` follows by `congrArg X ∘ Subtype.ext` (the same term-mode
reduction as `right_eq_of_contract_class_eq`), since both `resolvedComponentGenTerm (remnantComponent o)`
(via CD) and `rightTermOf o` are `X (graph.toResolvedHopfGen _)`.

Landed:

* `ResolvedRemnantDecontractionSupply` — `remnantComponent` + `remnantCD` + the class equality
  `remnantClass_eq` (the single heavy de-contraction datum);
* `ResolvedRemnantDecontractionSupply.remnantGen` — `resolvedComponentGenTerm (remnantComponent o) =
  rightTermOf o`, derived from `remnantClass_eq`.

So the remnant embedding is reduced to `remnantComponent` + `remnantClass_eq` (shared geometry with
`right_eq`).  No facade, no flat term, no `forgetHopf`, no rep/perm.  Constructing `remnantComponent` and
proving `remnantClass_eq` (the de-contraction) is the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-4b — the remnant de-contraction geometry supply.**  For a fixed split choice: the
remnant embedding of each forest-choice occurrence into the selected-outer quotient graph, its
connected-divergence, and the single graph obligation `remnantClass_eq` (the de-contraction class
equality — the same contract-twice = contract-once shape as `right_eq`). -/
structure ResolvedRemnantDecontractionSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) (s : ResolvedCoassocSplitChoice D G) where
  /-- The remnant of a forest choice, embedded into the quotient graph. -/
  remnantComponent : s.ForestChoiceOccurrence → ResolvedFeynmanSubgraph s.selectedOuterContractGraph
  /-- Each remnant component is connected-divergent. -/
  remnantCD : ∀ o, (remnantComponent o).forget.IsConnectedDivergent
  /-- **The de-contraction class equality** — the remnant component is the contracted source forest, as
  resolved classes (contract `B` inside `γ` = the remnant in `selectedOuter.contractWithStars`). -/
  remnantClass_eq : ∀ o, (remnantComponent o).toResolvedFeynmanGraph.toResolvedClass
    = o.contractedSourceGraph.toResolvedClass

/-- **R-6c-heart-6a-4b — the remnant generator equality from the class equality.**  `resolvedComponentGen
Term (remnantComponent o) = rightTermOf o` — both are `X (graph.toResolvedHopfGen _)`, so the class
equality (CD proof irrelevant) gives it by `congrArg X ∘ Subtype.ext`. -/
theorem ResolvedRemnantDecontractionSupply.remnantGen
    {s : ResolvedCoassocSplitChoice D G} (Geo : ResolvedRemnantDecontractionSupply D G s)
    (o : s.ForestChoiceOccurrence) :
    resolvedComponentGenTerm (Geo.remnantComponent o) = o.rightTermOf := by
  rw [resolvedComponentGenTerm_of_cd (Geo.remnantCD o)]
  exact congrArg MvPolynomial.X (Subtype.ext (Geo.remnantClass_eq o))

end GaugeGeometry.QFT.Combinatorial
