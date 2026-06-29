import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteVertexMap

/-!
# R-6c-heart-6a-9d — three-route vertex transport + quotient-star supplies

The genuine route geometry of the three-route correspondence splits cleanly into two supplies:

* **`ResolvedThreeRouteVertexTransportSupply`** — the `selectedOuter` / `quotientForest` *vertex* facts:
  `survivingOriginal_to` (an outer survivor survives the two-stage), `leftStar_toSurvivor` (a left `δ`-star
  is a two-stage survivor), `twoStageSurvivor_cases` (a two-stage survivor is original or a left `δ`-star);
* **`ResolvedThreeRouteQuotientStarSupply`** — the BIGGEST genuine index correspondence
  `quotientStarEquiv : {hasQuotientStar} ≃ TwoStageStarIndex` (right/forest one-stage stars ↔ quotient
  forest stars).

`toVertexMapSupply` assembles the three-route map supply (fix-1) from them.  So the proved correspondence's
route side is now `Transport + QuotientStar` (this file) + `Recover + Fresh` (6a-9b mechanical) +
`leftStar_unique` / `originalSurvivor_not_leftStar` (6a-9c).

Per the HALT, none of the transport facts are proved, `quotientStarEquiv` is NOT constructed, `Edge` /
`retargetVertex_eq` are NOT touched.

Landed:

* `ResolvedThreeRouteVertexTransportSupply D G imageOf` — the three vertex transport facts;
* `ResolvedThreeRouteQuotientStarSupply D G imageOf` — the `quotientStarEquiv` field;
* `.toVertexMapSupply` — the assembled `ResolvedThreeRouteVertexMapSupply`.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-9d — the vertex transport supply.**  The `selectedOuter` / `quotientForest` vertex
facts behind the surviving / left routes. -/
structure ResolvedThreeRouteVertexTransportSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- An outer survivor survives the two-stage contraction. -/
  survivingOriginal_to : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    isContractSurvivingVertex s.1.1 v → isContractSurvivingVertex (imageOf s).quotientForest v
  /-- A left-primitive one-stage star is a two-stage survivor. -/
  leftStar_toSurvivor : ∀ (s : ResolvedCoassocSplitChoice D G) (i : OneStageStarIndex D G s),
    i.isLeft → isContractSurvivingVertex (imageOf s).quotientForest i.vertex
  /-- A two-stage surviving vertex is an original survivor or a left-primitive `δ`-star. -/
  twoStageSurvivor_cases : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    isContractSurvivingVertex (imageOf s).quotientForest v →
      isContractSurvivingVertex s.1.1 v ∨
        ∃ i : OneStageStarIndex D G s, i.isLeft ∧ i.vertex = v

/-- **R-6c-heart-6a-9d — the quotient-star equivalence supply (the BIGGEST genuine correspondence).** -/
structure ResolvedThreeRouteQuotientStarSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- The right/forest one-stage stars ≃ the quotient-forest stars. -/
  quotientStarEquiv : ∀ s : ResolvedCoassocSplitChoice D G,
    {i : OneStageStarIndex D G s // i.hasQuotientStar} ≃ TwoStageStarIndex D G imageOf s

variable {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}

/-- **R-6c-heart-6a-9d — the three-route map supply from transport + quotient-star. -/
def ResolvedThreeRouteVertexTransportSupply.toVertexMapSupply
    (T : ResolvedThreeRouteVertexTransportSupply D G imageOf)
    (Q : ResolvedThreeRouteQuotientStarSupply D G imageOf) :
    ResolvedThreeRouteVertexMapSupply D G imageOf where
  survivingOriginal_to := T.survivingOriginal_to
  leftStar_toSurvivor := T.leftStar_toSurvivor
  quotientStarEquiv := Q.quotientStarEquiv

end GaugeGeometry.QFT.Combinatorial
