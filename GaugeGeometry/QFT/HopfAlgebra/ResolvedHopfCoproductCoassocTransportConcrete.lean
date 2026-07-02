import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTransportLeaves

/-!
# R-6c-leaf-34 — the three-route transport facts (mismatch-corrected vertex partition), isolated

Twenty-ninth leaf-body discharge — factoring leaf-17's transport connector into its two halves and naming the
genuine mismatch-corrected vertex-partition facts on their own.  After the 6a-8c-0 star↔star fix, the two
facts are:

* `left_star_survives` — a left-primitive one-stage `δ`-star is a two-stage SURVIVOR (not a quotient star);
* `two_stage_survivor_split` — every two-stage surviving vertex is either an original outer survivor or a
  left-primitive one-stage star.

These are the genuine selected-outer / quotient-forest vertex-partition content (the correct frame after the
mismatch fix), kept as supply fields.  Combined with the two correct surviving containments (leaf-17), they
give the full `ResolvedThreeRouteTransportConnector` (and hence, via leaf-17, the vertex transport supply with
`survivingOriginal_to` derived).

Per the HALT, the two facts are supply fields (the vertex-partition geometry); Retarget / Sector untouched.

Landed:

* `ResolvedThreeRouteTransportFactSupply D G imageOf` — `left_star_survives` + `two_stage_survivor_split`;
* `.toTransportConnector` — combine with the two containments into leaf-17's connector.

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

/-- **R-6c-leaf-34 — the mismatch-corrected three-route vertex-partition facts.**  A left-primitive one-stage
star survives the two-stage contraction; and the two-stage survivors are exactly the original survivors plus
the left-primitive stars. -/
structure ResolvedThreeRouteTransportFactSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- A left-primitive one-stage `δ`-star is a two-stage survivor (NOT a quotient star — the 6a-8c-0 fix). -/
  left_star_survives : ∀ (s : ResolvedCoassocSplitChoice D G) (i : OneStageStarIndex D G s),
    i.isLeft → isContractSurvivingVertex (imageOf s).quotientForest i.vertex
  /-- A two-stage surviving vertex is an original survivor or a left-primitive `δ`-star. -/
  two_stage_survivor_split : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    isContractSurvivingVertex (imageOf s).quotientForest v →
      isContractSurvivingVertex s.1.1 v ∨
        ∃ i : OneStageStarIndex D G s, i.isLeft ∧ i.vertex = v

/-- **R-6c-leaf-34 — the leaf-17 transport connector from the facts + the two correct surviving containments. -/
def ResolvedThreeRouteTransportFactSupply.toTransportConnector
    (Facts : ResolvedThreeRouteTransportFactSupply D G imageOf)
    (selectedOuter_vertices_subset : ∀ s : ResolvedCoassocSplitChoice D G,
      (imageOf s).selectedOuter.1.vertices ⊆ s.1.1.vertices)
    (quotientForest_avoids_outer_survivors : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
      v ∈ G.vertices → v ∉ s.1.1.vertices → v ∉ (imageOf s).quotientForest.vertices) :
    ResolvedThreeRouteTransportConnector D G imageOf where
  selectedOuter_vertices_subset := selectedOuter_vertices_subset
  quotientForest_avoids_outer_survivors := quotientForest_avoids_outer_survivors
  leftStar_toSurvivor := Facts.left_star_survives
  twoStageSurvivor_cases := Facts.two_stage_survivor_split

end GaugeGeometry.QFT.Combinatorial
