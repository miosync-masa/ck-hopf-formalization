import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientGraphAlign

/-!
# R-6c-body-9 — quotient forest avoids outer survivors (from the G-vertices subset)

Ninth genuine-body step, the second Transport surviving containment (pairing with body-8's
`selectedOuter_vertices_subset`).  `quotientForest_avoids_outer_survivors` (an ambient vertex outside the input
outer is not in the quotient forest) is the contrapositive of the fact that the quotient forest's *`G`-vertices*
lie in the input outer.

The quotient forest is `Right ⊔ Remnant` over the quotient (contract) graph, whose vertices are `(G.vertices \
selectedOuter) ∪ fresh stars`.  A right-survivor keeps its right-primitive component's vertices (⊆ input outer);
a remnant's `G`-vertices are the surviving-within-parent vertices (⊆ the parent ⊆ input outer) — its only
non-input vertices are the FRESH stars (∉ `G.vertices`).  So every `G`-vertex of the quotient forest is an
input-outer vertex: `quotientForest_gvertices_subset` (the genuine region geometry, fielded), from which
`quotientForest_avoids_outer_survivors` is immediate.

Per the HALT, the region subset is a supply field; `leftStar_toSurvivor` / `twoStageSurvivor_cases` untouched.

Landed:

* `ResolvedQuotientForestVerticesSubsetSupply D G imageOf` — `quotientForest_gvertices_subset`;
* `.quotientForest_avoids_outer_survivors` — the Transport containment (contrapositive).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}

/-- **R-6c-body-9 — the quotient-forest G-vertices region supply.**  Every ambient (`G`) vertex of the
quotient forest is an input-outer vertex (its non-input vertices are the fresh stars). -/
structure ResolvedQuotientForestVerticesSubsetSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- A `G`-vertex of the quotient forest lies in the input outer forest. -/
  quotientForest_gvertices_subset : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    v ∈ (imageOf s).quotientForest.vertices → v ∈ G.vertices → v ∈ s.1.1.vertices

/-- **R-6c-body-9 — the Transport `quotientForest_avoids_outer_survivors` containment.**  Contrapositive of the
`G`-vertices subset. -/
theorem ResolvedQuotientForestVerticesSubsetSupply.quotientForest_avoids_outer_survivors
    (S : ResolvedQuotientForestVerticesSubsetSupply D G imageOf) :
    ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
      v ∈ G.vertices → v ∉ s.1.1.vertices → v ∉ (imageOf s).quotientForest.vertices :=
  fun s _ hvG hvA hvQ => hvA (S.quotientForest_gvertices_subset s hvQ hvG)

end GaugeGeometry.QFT.Combinatorial
