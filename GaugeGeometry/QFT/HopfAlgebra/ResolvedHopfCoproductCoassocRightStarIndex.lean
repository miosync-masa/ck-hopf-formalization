import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightCheapGeometry

/-!
# R-6c-heart-6a-8a — RIGHT star index types (the entrance to the BIGGEST)

Before constructing the star bijection `starToStar`, this gives its domain and codomain **meaningful
indices** instead of bare star-vertex subtypes: a one-stage star is the star of a component of the input
outer forest `s.1.1`; a two-stage star is the star of a component of the quotient forest.  Each carries the
component witness, maps to its star `VertexId`, and bridges to the `{v // isContractStarVertex …}` subtype
`starToStar` actually operates on.

This makes the BIGGEST (`OneStageStarIndex ≃ TwoStageStarIndex`, the genuine `componentPartition` /
`Right ⊔ Remnant` correspondence) tractable: the equivalence will be between these indices, then transported
to the subtypes through the bridges below.

Per the HALT, NO bijection between indices, NO `starToStar`, NO `componentPartition` / `Right ⊔ Remnant`
correspondence.

Landed:

* `OneStageStarIndex D G s` / `TwoStageStarIndex D G imageOf s` — the meaningful star indices;
* `.vertex` — the star `VertexId`;
* `.toStarVertex` — the bridge into the star-vertex subtype.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-8a — a one-stage star index.**  A component of the input outer forest `s.1.1`; its
star vertex is `D.starOf G s.1.1 η`. -/
structure OneStageStarIndex (D : ResolvedCoproductProperForestData) (G : ResolvedFeynmanGraph)
    (s : ResolvedCoassocSplitChoice D G) where
  /-- The input-outer component. -/
  η : ResolvedFeynmanSubgraph G
  /-- It is a component of `s.1.1`. -/
  hη : η ∈ s.1.1.elements

/-- **R-6c-heart-6a-8a — a two-stage star index.**  A component of the quotient forest; its star vertex is
`D.starOf (quotient graph) quotientForest δ`. -/
structure TwoStageStarIndex (D : ResolvedCoproductProperForestData) (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (s : ResolvedCoassocSplitChoice D G) where
  /-- The quotient-forest component. -/
  δ : ResolvedFeynmanSubgraph (resolvedCoassocQuotientGraph (imageOf s))
  /-- It is a component of the quotient forest. -/
  hδ : δ ∈ (imageOf s).quotientForest.elements

/-- **R-6c-heart-6a-8a — the one-stage star vertex. -/
noncomputable def OneStageStarIndex.vertex {s : ResolvedCoassocSplitChoice D G} (i : OneStageStarIndex D G s) :
    VertexId := D.starOf G s.1.1 i.η

/-- **R-6c-heart-6a-8a — the two-stage star vertex. -/
noncomputable def TwoStageStarIndex.vertex
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    {s : ResolvedCoassocSplitChoice D G} (i : TwoStageStarIndex D G imageOf s) : VertexId :=
  D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest i.δ

/-- **R-6c-heart-6a-8a — bridge: a one-stage star index is a one-stage star vertex. -/
noncomputable def OneStageStarIndex.toStarVertex {s : ResolvedCoassocSplitChoice D G} (i : OneStageStarIndex D G s) :
    {v : VertexId // isContractStarVertex s.1.1 (D.starOf G s.1.1) v} :=
  ⟨i.vertex, ResolvedAdmissibleSubgraph.mem_starVertices.mpr ⟨i.η, i.hη, rfl⟩⟩

/-- **R-6c-heart-6a-8a — bridge: a two-stage star index is a two-stage star vertex. -/
noncomputable def TwoStageStarIndex.toStarVertex
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    {s : ResolvedCoassocSplitChoice D G} (i : TwoStageStarIndex D G imageOf s) :
    {v : VertexId // isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) v} :=
  ⟨i.vertex, ResolvedAdmissibleSubgraph.mem_starVertices.mpr ⟨i.δ, i.hδ, rfl⟩⟩

end GaugeGeometry.QFT.Combinatorial
