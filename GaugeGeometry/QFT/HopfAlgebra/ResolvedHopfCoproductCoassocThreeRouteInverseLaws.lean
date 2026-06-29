import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteToFun
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteInvFun

/-!
# R-6c-heart-6a-8c-fix-3c-0 — three-route inverse-law hypotheses + the assembled correspondence

The forward (`threeRouteCorrToFun`, fix-3b-1) and inverse (`threeRouteCorrInvFun`, fix-3b-2) maps are
constructed; this file bundles them and the (not-yet-proved) inverse laws into the full
`ResolvedContractTwiceVertexCorrespondence`, replacing fix-2's raw `corrToFun` / `corrInvFun` fields with
the real constructions.

To keep the maps consistent (both must use the *same* route data) and to name the inverse-law field types,
the route data is merged into one `ResolvedThreeRouteFullSupply` (diamond `extends` over the shared map
supply), and the inverse laws are stated against the constructed maps applied to `route`'s projections —
`route` being a plain field, its `to…` projections are nameable.

Per the HALT, the inverse laws are FIELDS here (their case-by-case proofs — `Classical.choose` stability,
`leftStar_unique`, `originalSurvivor_not_leftStar` — come next); no concrete `quotientStarEquiv` /
recoveries, no old-chain edits.

Landed:

* `ResolvedThreeRouteFullSupply D G imageOf` — all route data (toFun + invFun) merged, plus
  `leftStar_unique` / `originalSurvivor_not_leftStar`;
* `ResolvedThreeRouteInverseLawSupply D G imageOf` — `route` + `corrLeftInv` / `corrRightInv` (against the
  constructed maps);
* `.toVertexCorrespondence s` — the full `ResolvedContractTwiceVertexCorrespondence` from the real maps.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-8c-fix-3c-0 — the merged route supply.**  Forward + inverse route data over one shared
map base (diamond `extends`), plus the left-star partition facts. -/
structure ResolvedThreeRouteFullSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    extends ResolvedThreeRouteToFunSupply D G imageOf,
      ResolvedThreeRouteInvFunSupply D G imageOf where
  /-- Distinct left-primitive stars are distinct vertices. -/
  leftStar_unique : ∀ (s : ResolvedCoassocSplitChoice D G) (i j : OneStageStarIndex D G s),
    i.isLeft → j.isLeft → i.vertex = j.vertex → i = j
  /-- Original survivors and left-primitive `δ`-stars are disjoint. -/
  originalSurvivor_not_leftStar : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    isContractSurvivingVertex s.1.1 v → ∀ (i : OneStageStarIndex D G s), i.isLeft → v ≠ i.vertex

/-- **R-6c-heart-6a-8c-fix-3c-0 — the inverse-law supply.**  The merged route data plus the two inverse
laws against the constructed maps. -/
structure ResolvedThreeRouteInverseLawSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- The merged route data. -/
  route : ResolvedThreeRouteFullSupply D G imageOf
  /-- The constructed inverse map is a left inverse of the constructed forward map. -/
  corrLeftInv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.LeftInverse (threeRouteCorrInvFun route.toResolvedThreeRouteInvFunSupply s)
      (threeRouteCorrToFun route.toResolvedThreeRouteToFunSupply s)
  /-- ... and a right inverse. -/
  corrRightInv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.RightInverse (threeRouteCorrInvFun route.toResolvedThreeRouteInvFunSupply s)
      (threeRouteCorrToFun route.toResolvedThreeRouteToFunSupply s)

/-- **R-6c-heart-6a-8c-fix-3c-0 — the full vertex correspondence from the constructed maps. -/
noncomputable def ResolvedThreeRouteInverseLawSupply.toVertexCorrespondence
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (S : ResolvedThreeRouteInverseLawSupply D G imageOf) (s : ResolvedCoassocSplitChoice D G) :
    ResolvedContractTwiceVertexCorrespondence (oneStageContractGraph s)
      (twoStageContractGraph imageOf s) where
  toFun := threeRouteCorrToFun S.route.toResolvedThreeRouteToFunSupply s
  invFun := threeRouteCorrInvFun S.route.toResolvedThreeRouteInvFunSupply s
  left_inv := S.corrLeftInv s
  right_inv := S.corrRightInv s

end GaugeGeometry.QFT.Combinatorial
