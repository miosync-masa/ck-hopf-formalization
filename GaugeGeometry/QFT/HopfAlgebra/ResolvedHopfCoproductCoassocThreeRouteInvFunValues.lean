import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteProvedCorrespondence
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteRightInvOriginal
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteRoundTripLeft
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteRoundTripQuotient

/-!
# R-6c-body-29 — three-route `invFun` value lemmas at the correspondence level

Twenty-ninth genuine-body step, lifting the three constructed `invFun` value lemmas
(`threeRouteCorrInvFun_survivorOriginal_val` / `_survivorLeft_val` / `_star_val`) from the raw
`ResolvedThreeRouteInvFunSupply` to the packaged `Three.toVertexCorrespondence s` used by the retarget cases
(body-27/28).  This removes the accessor-path plumbing and the `invFun = threeRouteCorrInvFun` defeq from every
downstream retarget-route proof.

The bridge is `threeRoute_invFun_eq` (`rfl`): `Three.toVertexCorrespondence s .invFun` unfolds — through
`ResolvedThreeRouteProvedSupply.toVertexCorrespondence` → `ResolvedThreeRouteInverseLawSupply.toVertexCorrespondence`
→ the `invFun := threeRouteCorrInvFun route.toResolvedThreeRouteInvFunSupply s` field — to the raw
`threeRouteCorrInvFun` of the supply.  The three value lemmas then re-export directly.

* `threeRoute_invFun_original_val` — a survivingOriginal two-stage vertex maps to itself (`.1 = w.1`).  This is
  exactly body-28's `corr_invFun_survivor` shape (given the survivor / not-star hypotheses).
* `threeRoute_invFun_leftStar_val` — a two-stage LEFT survivor maps to the chosen left star.
* `threeRoute_invFun_star_val` — a two-stage quotient star maps to the recovered one-stage star.

Per the HALT, the inner-left / inner-right retarget routes are NOT proved here; this only packages the value
lemmas.

Landed:

* `threeRoute_invFun_eq` — the `rfl` bridge to `threeRouteCorrInvFun`;
* `threeRoute_invFun_original_val` / `_leftStar_val` / `_star_val` — the three re-exported values.

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

/-- **R-6c-body-29 — the correspondence `invFun` is the raw `threeRouteCorrInvFun`** (`rfl` bridge). -/
theorem threeRoute_invFun_eq (Three : ResolvedThreeRouteProvedSupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G)
    (w : {v : VertexId // v ∈ (twoStageContractGraph imageOf s).vertices}) :
    (Three.toVertexCorrespondence s).invFun w =
      threeRouteCorrInvFun Three.toInverseLawSupply.route.toResolvedThreeRouteInvFunSupply s w :=
  rfl

/-- **R-6c-body-29 — survivingOriginal `invFun` value** (`.1 = w.1`).  Body-28's `corr_invFun_survivor` shape. -/
theorem threeRoute_invFun_original_val (Three : ResolvedThreeRouteProvedSupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G)
    (w : {v : VertexId // v ∈ (twoStageContractGraph imageOf s).vertices})
    (hnotstarB : ¬ isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) w.1)
    (hOrig : isContractSurvivingVertex s.1.1 w.1) :
    ((Three.toVertexCorrespondence s).invFun w).1 = w.1 :=
  threeRouteCorrInvFun_survivorOriginal_val
    Three.toInverseLawSupply.route.toResolvedThreeRouteInvFunSupply s w hnotstarB hOrig

/-- **R-6c-body-29 — left-star (two-stage LEFT survivor) `invFun` value.** -/
theorem threeRoute_invFun_leftStar_val (Three : ResolvedThreeRouteProvedSupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G)
    (w : {v : VertexId // v ∈ (twoStageContractGraph imageOf s).vertices})
    (hstar : ¬ isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) w.1)
    (hO : ¬ isContractSurvivingVertex s.1.1 w.1) :
    ((Three.toVertexCorrespondence s).invFun w).1
      = (Classical.choose
          ((Three.toInverseLawSupply.route.toResolvedThreeRouteInvFunSupply.twoStageSurvivor_cases s
            ((contractWithStars_vertex_cases (imageOf s).quotientForest
              (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
              w.2).resolve_right hstar)).resolve_left hO)).toStarVertex.1 :=
  threeRouteCorrInvFun_survivorLeft_val
    Three.toInverseLawSupply.route.toResolvedThreeRouteInvFunSupply s w hstar hO

/-- **R-6c-body-29 — quotient-star (two-stage star) `invFun` value.** -/
theorem threeRoute_invFun_star_val (Three : ResolvedThreeRouteProvedSupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G)
    (w : {v : VertexId // v ∈ (twoStageContractGraph imageOf s).vertices})
    (hstar : isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) w.1) :
    ((Three.toVertexCorrespondence s).invFun w).1
      = ((Three.toInverseLawSupply.route.toResolvedThreeRouteInvFunSupply.quotientStarEquiv s).symm
          (Three.toInverseLawSupply.route.toResolvedThreeRouteInvFunSupply.twoStarRecover s
            ⟨w.1, hstar⟩)).1.toStarVertex.1 :=
  threeRouteCorrInvFun_star_val
    Three.toInverseLawSupply.route.toResolvedThreeRouteInvFunSupply s w hstar

end GaugeGeometry.QFT.Combinatorial
