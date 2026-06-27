import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocContractTwice
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantDecontraction

/-!
# R-6c-heart-6a-4c — sharing the contract-twice class-equality engine

`right_eq` (5c-2) and `remnantClass_eq` (6a-4b) are the **same** geometry — a contract-twice =
contract-once equality of resolved classes — at two granularities (the whole input outer forest `A`
vs a per-occurrence forest choice `B`).  This file extracts the shared **engine** and wires the remnant
side onto it, so both flow from one primitive.

The engine: a resolved class equality from a **star permutation + three graph-field equalities** (a graph
is its relabeled twin), `toResolvedClass_eq_of_mapPerm_fields`.  It already underlies `right_eq`'s
`ResolvedContractTwiceOnceGeometrySupply.contract_class_eq`; here it equally produces the remnant class
equality from a per-occurrence `ResolvedRemnantContractGeometrySupply`.

Landed:

* `ResolvedFeynmanGraph.toResolvedClass_eq_of_mapPerm_fields` — the shared engine (class equality from
  `σ` + the three field equalities);
* `ResolvedRemnantContractGeometrySupply` — the remnant-side geometry (per occurrence: `remnantComponent`
  + `remnantCD` + `starPerm` + the three field equalities `remnantComponent = contractedSourceGraph.map
  Perm σ`);
* `.remnantClass_eq` / `.toDecontractionSupply` — derive the remnant class equality (hence `remnantGen`)
  from the field equalities, via the shared engine.

So `right_eq` and `remnantGen` now both reduce to **the same shape** of obligation — a star permutation +
`vertices/internalEdges/externalLegs` field equalities.  No facade, no flat term, no `forgetHopf`.  The
field equalities themselves (the genuine de-contraction star geometry) are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-4c — the shared contract-twice class engine.**  Two resolved graphs have the same
resolved class once one is the other relabeled by a vertex permutation (given as the three graph-field
equalities) — `toResolvedClass` is `mapPerm`-invariant.  This is the single primitive behind both
`right_eq`'s `contract_class_eq` and the remnant `remnantClass_eq`. -/
theorem ResolvedFeynmanGraph.toResolvedClass_eq_of_mapPerm_fields {G₁ G₂ : ResolvedFeynmanGraph}
    (σ : Equiv.Perm VertexId) (hv : G₁.vertices = (G₂.mapPerm σ).vertices)
    (hi : G₁.internalEdges = (G₂.mapPerm σ).internalEdges)
    (he : G₁.externalLegs = (G₂.mapPerm σ).externalLegs) :
    G₁.toResolvedClass = G₂.toResolvedClass := by
  rw [ResolvedFeynmanGraph.ext' hv hi he, ResolvedFeynmanGraph.toResolvedClass_mapPerm]

/-- **R-6c-heart-6a-4c — `right_eq`'s class equality via the shared engine.**  Re-presents the
contract-twice = contract-once class equality (the whole-`A` granularity) as the shared engine applied to
`branchRightGraph` / `imageInnerRightGraph`. -/
theorem contract_class_eq_of_mapPerm_fields
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (s : ResolvedCoassocSplitChoice D G) (σ : Equiv.Perm VertexId)
    (hv : (branchRightGraph s).vertices = ((imageInnerRightGraph imageOf s).mapPerm σ).vertices)
    (hi : (branchRightGraph s).internalEdges = ((imageInnerRightGraph imageOf s).mapPerm σ).internalEdges)
    (he : (branchRightGraph s).externalLegs = ((imageInnerRightGraph imageOf s).mapPerm σ).externalLegs) :
    (branchRightGraph s).toResolvedClass = (imageInnerRightGraph imageOf s).toResolvedClass :=
  ResolvedFeynmanGraph.toResolvedClass_eq_of_mapPerm_fields σ hv hi he

/-- **R-6c-heart-6a-4c — the remnant-side contract-twice geometry.**  Per forest-choice occurrence: the
remnant embedding, its connected-divergence, and the star permutation + three field equalities saying the
remnant component is the contracted source forest relabeled by `σ`. -/
structure ResolvedRemnantContractGeometrySupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) (s : ResolvedCoassocSplitChoice D G) where
  /-- The remnant of a forest choice, embedded into the quotient graph. -/
  remnantComponent : s.ForestChoiceOccurrence → ResolvedFeynmanSubgraph s.selectedOuterContractGraph
  /-- Each remnant component is connected-divergent. -/
  remnantCD : ∀ o, (remnantComponent o).forget.IsConnectedDivergent
  /-- The star permutation matching the remnant component to the contracted source forest. -/
  starPerm : s.ForestChoiceOccurrence → Equiv.Perm VertexId
  /-- Remnant component vertices = relabeled contracted-source vertices. -/
  vertices_eq : ∀ o, (remnantComponent o).toResolvedFeynmanGraph.vertices
    = (o.contractedSourceGraph.mapPerm (starPerm o)).vertices
  /-- Remnant component internal edges = relabeled contracted-source internal edges. -/
  internalEdges_eq : ∀ o, (remnantComponent o).toResolvedFeynmanGraph.internalEdges
    = (o.contractedSourceGraph.mapPerm (starPerm o)).internalEdges
  /-- Remnant component external legs = relabeled contracted-source external legs. -/
  externalLegs_eq : ∀ o, (remnantComponent o).toResolvedFeynmanGraph.externalLegs
    = (o.contractedSourceGraph.mapPerm (starPerm o)).externalLegs

/-- **R-6c-heart-6a-4c — the remnant class equality from the shared engine.** -/
theorem ResolvedRemnantContractGeometrySupply.remnantClass_eq
    {s : ResolvedCoassocSplitChoice D G} (Geo : ResolvedRemnantContractGeometrySupply D G s)
    (o : s.ForestChoiceOccurrence) :
    (Geo.remnantComponent o).toResolvedFeynmanGraph.toResolvedClass
      = o.contractedSourceGraph.toResolvedClass :=
  ResolvedFeynmanGraph.toResolvedClass_eq_of_mapPerm_fields (Geo.starPerm o)
    (Geo.vertices_eq o) (Geo.internalEdges_eq o) (Geo.externalLegs_eq o)

/-- **R-6c-heart-6a-4c — the de-contraction supply from the remnant geometry.**  Packages the remnant
embedding + CD + the derived class equality, ready to feed `remnantGen` (6a-4b). -/
def ResolvedRemnantContractGeometrySupply.toDecontractionSupply
    {s : ResolvedCoassocSplitChoice D G} (Geo : ResolvedRemnantContractGeometrySupply D G s) :
    ResolvedRemnantDecontractionSupply D G s where
  remnantComponent := Geo.remnantComponent
  remnantCD := Geo.remnantCD
  remnantClass_eq := Geo.remnantClass_eq

end GaugeGeometry.QFT.Combinatorial
