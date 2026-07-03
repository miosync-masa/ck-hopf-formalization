import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRetargetRightRecovery

/-!
# R-6c-body-49 — the right sector inverse leaf: `quotientStarEquiv.symm` returns the source index

Forty-ninth genuine-body step, naming body-48's residual `quotientStar_symm_recovers` as the RIGHT
sector-equivalence inverse leaf and expressing it through the recovered source index's vertex.

`((quotientStarEquiv s).symm j).1` is a one-stage star index (a `{i // i.hasQuotientStar}`), whose
`toStarVertex.1` is its `vertex = D.starOf G s.1.1 (·.η)`.  So `quotientStar_symm_recovers` says the
`quotientStarEquiv` inverse of the two-stage star `j` returns the source one-stage index whose star vertex is
the one-stage star `s.1.1.retargetVertex (D.starOf G s.1.1) v`:

```text
((quotientStarEquiv s).symm j).1.vertex = s.1.1.retargetVertex (D.starOf G s.1.1) v
```

`quotientStarEquiv : {i // i.hasQuotientStar} ≃ TwoStageStarIndex` is built (VertexMap 10a–10c) from the
`SectorLeafBundle` (leaf-24) — the right/forest sector equivalences and their four inverse laws.  Per the HALT,
those `sumCongr` internals are NOT expanded; `symm_recovers` is the irreducible RIGHT sector-inverse leaf,
mirroring LEFT's `star_coherence` (body-47).  This is the QUOTIENT-SECTOR-EQUIVALENCE counterpart of the LEFT
COHERENCE — the two halves of the retarget star geometry.

Landed:

* `ResolvedQuotientStarSymmRecoverySupply D G imageOf Three App` — `symm_recovers` (the source-index vertex
  equality);
* `.toRightStarRecoveryIndexSupply` — body-48's `quotientStar_symm_recovers`, from `symm_recovers` (`.symm`,
  `toStarVertex.1 = vertex`).  (`htwoInv` is passed through as the mechanical recovery.)

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

/-- **R-6c-body-49 — the right sector-inverse supply.**  The mechanical two-star recovery, and the source
one-stage index vertex the `quotientStarEquiv` inverse returns. -/
structure ResolvedQuotientStarSymmRecoverySupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (Three : ResolvedThreeRouteProvedSupply D G imageOf)
    (App : ResolvedRetargetInnerApplicabilitySupply D G imageOf) where
  /-- Mechanical: `twoStarRecover` recovers the two-stage star index. -/
  htwoInv : ∀ (s : ResolvedCoassocSplitChoice D G) (j : TwoStageStarIndex D G imageOf s),
    Three.toInverseLawSupply.route.toResolvedThreeRouteInvFunSupply.twoStarRecover s j.toStarVertex = j
  /-- Sector inverse: the source one-stage index returned by `quotientStarEquiv.symm j` has the one-stage
  star as its vertex. -/
  symm_recovers : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    v ∈ s.1.1.vertices → ¬ App.innerLeft s v →
    ∀ (j : TwoStageStarIndex D G imageOf s),
      j.toStarVertex.1 = (imageOf s).quotientForest.retargetVertex
        (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
        (rightVertexDomain (imageOf s) v) →
      ((Three.toInverseLawSupply.route.toResolvedThreeRouteInvFunSupply.quotientStarEquiv s).symm j).1.vertex
        = s.1.1.retargetVertex (D.starOf G s.1.1) v

/-- **R-6c-body-49 — body-48's right-recovery index supply from the sector inverse. -/
def ResolvedQuotientStarSymmRecoverySupply.toRightStarRecoveryIndexSupply
    {Three : ResolvedThreeRouteProvedSupply D G imageOf}
    {App : ResolvedRetargetInnerApplicabilitySupply D G imageOf}
    (R : ResolvedQuotientStarSymmRecoverySupply D G imageOf Three App) :
    ResolvedRightStarRecoveryIndexSupply D G imageOf Three App where
  htwoInv := R.htwoInv
  quotientStar_symm_recovers := by
    intro s v hin hnleft j hjeq
    exact (R.symm_recovers s hin hnleft j hjeq).symm

end GaugeGeometry.QFT.Combinatorial
