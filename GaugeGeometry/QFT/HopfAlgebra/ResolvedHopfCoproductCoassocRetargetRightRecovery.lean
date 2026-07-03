import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRetargetCoordinateWitnesses

/-!
# R-6c-body-48 — the right recovery reduced to the quotient-sector inverse leaf

Forty-eighth genuine-body step, reducing body-42/45's `rightStar_recovery` (the right-route index-inverse) to
the pure quotient-sector inverse, discharging the `twoStarRecover` step.

`rightStar_recovery`'s RHS is `((quotientStarEquiv s).symm (twoStarRecover s ⟨TSV, ·⟩)).1.toStarVertex.1`.  By
body-43's `right_index_of_quotientStar`, the quotient star `⟨TSV, ·⟩` IS a `TwoStageStarIndex` `j`'s star
vertex (`j.toStarVertex.1 = TSV`), so `⟨TSV, ·⟩ = j.toStarVertex` (`Subtype.ext`) and the mechanical two-star
recovery `htwoInv` collapses `twoStarRecover s j.toStarVertex = j`.  What remains is

```text
s.1.1.retargetVertex (D.starOf G s.1.1) v = ((quotientStarEquiv s).symm j).1.toStarVertex.1
```

— the source one-stage star recovered by the `quotientStarEquiv` inverse.  This is the pure quotient-sector
inverse leaf (`quotientStar_symm_recovers`): the `{hasQuotientStar}` ≃ `TwoStageStarIndex` equivalence's inverse
sends the two-stage star `j` back to the source index whose star vertex is the one-stage star.

Per the HALT, the `twoStarRecover` step is discharged and the `quotientStarEquiv` `sumCongr` internals are NOT
expanded; `quotientStar_symm_recovers` is the fielded sector-inverse leaf and `htwoInv` the mechanical recovery.

Landed:

* `ResolvedRightStarRecoveryIndexSupply D G imageOf Three App` — `htwoInv` (mechanical two-star recovery) +
  `quotientStar_symm_recovers` (the sector inverse);
* `.rightStar_recovery` — body-45's right recovery, PROVED.

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

/-- **R-6c-body-48 — the right-recovery index supply.**  The mechanical two-star recovery and the pure
quotient-sector inverse (the `quotientStarEquiv` inverse returning the source one-stage star). -/
structure ResolvedRightStarRecoveryIndexSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (Three : ResolvedThreeRouteProvedSupply D G imageOf)
    (App : ResolvedRetargetInnerApplicabilitySupply D G imageOf) where
  /-- Mechanical: `twoStarRecover` recovers the two-stage star index. -/
  htwoInv : ∀ (s : ResolvedCoassocSplitChoice D G) (j : TwoStageStarIndex D G imageOf s),
    Three.toInverseLawSupply.route.toResolvedThreeRouteInvFunSupply.twoStarRecover s j.toStarVertex = j
  /-- Sector inverse: `quotientStarEquiv.symm` of the two-stage star `j` gives the one-stage star `v` maps to. -/
  quotientStar_symm_recovers : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    v ∈ s.1.1.vertices → ¬ App.innerLeft s v →
    ∀ (j : TwoStageStarIndex D G imageOf s),
      j.toStarVertex.1 = (imageOf s).quotientForest.retargetVertex
        (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
        (rightVertexDomain (imageOf s) v) →
      s.1.1.retargetVertex (D.starOf G s.1.1) v
        = ((Three.toInverseLawSupply.route.toResolvedThreeRouteInvFunSupply.quotientStarEquiv s).symm j).1.toStarVertex.1

/-- **R-6c-body-48 — body-45's right recovery, PROVED from the two-star recovery + the sector inverse. -/
theorem ResolvedRightStarRecoveryIndexSupply.rightStar_recovery
    {Three : ResolvedThreeRouteProvedSupply D G imageOf}
    {App : ResolvedRetargetInnerApplicabilitySupply D G imageOf}
    (R : ResolvedRightStarRecoveryIndexSupply D G imageOf Three App)
    (s : ResolvedCoassocSplitChoice D G) {v : VertexId}
    (hin : v ∈ s.1.1.vertices) (hnleft : ¬ App.innerLeft s v) :
    s.1.1.retargetVertex (D.starOf G s.1.1) v
      = ((Three.toInverseLawSupply.route.toResolvedThreeRouteInvFunSupply.quotientStarEquiv s).symm
          (Three.toInverseLawSupply.route.toResolvedThreeRouteInvFunSupply.twoStarRecover s
            ⟨(imageOf s).quotientForest.retargetVertex
                (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
                (rightVertexDomain (imageOf s) v),
              App.inner_right_is_quotientStar s hin hnleft⟩)).1.toStarVertex.1 := by
  obtain ⟨j, hjeq⟩ := right_index_of_quotientStar s (App.inner_right_is_quotientStar s hin hnleft)
  have hpair : (⟨(imageOf s).quotientForest.retargetVertex
        (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
        (rightVertexDomain (imageOf s) v), App.inner_right_is_quotientStar s hin hnleft⟩ :
        {w : VertexId // isContractStarVertex (imageOf s).quotientForest
          (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) w})
      = j.toStarVertex := Subtype.ext hjeq.symm
  rw [hpair, R.htwoInv s j]
  exact R.quotientStar_symm_recovers s hin hnleft j hjeq

end GaugeGeometry.QFT.Combinatorial
