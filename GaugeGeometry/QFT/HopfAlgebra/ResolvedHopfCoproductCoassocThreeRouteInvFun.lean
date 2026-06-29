import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteVertexMap

/-!
# R-6c-heart-6a-8c-fix-3b-2 — `corrInvFun` from the three routes (inverse map)

The inverse half of the three-route vertex correspondence.  Symmetric to `corrToFun` (fix-3b-1), but a
two-stage **surviving** vertex must be split into an *original* survivor or a *left*-`δ`-star (the route-2
image), via the partition field `twoStageSurvivor_cases`:

```
two-stage surviving vertex
  ├ original survivor       → one-stage surviving original   (same VertexId)
  └ left δ-star (∃ i)        → one-stage left star            (i.toStarVertex)
two-stage star vertex       → one-stage right/forest star     (quotientStarEquiv.symm)
```

The two-stage star is decoded by a recovery equivalence `twoStarRecover` (the two-stage analogue of
`oneStarRecover`).  `Or` cannot be eliminated into a `Type`, so the survivor sub-split uses a `Classical`
`dite` on `isContractSurvivingVertex s.1.1 w` plus `Classical.choose` on the left-star existential.

Per the HALT, only `corrInvFun` is built: no inverse laws, no concrete `quotientStarEquiv` /
`twoStarRecover`.

Landed:

* `ResolvedThreeRouteInvFunSupply D G imageOf` — the routes + `twoStageSurvivor_cases` + `twoStarRecover`;
* `threeRouteCorrInvFun` — the assembled inverse map.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-8c-fix-3b-2 — the inverse-map supply.**  The routes, the two-stage survivor split, and
the two-stage star recovery. -/
structure ResolvedThreeRouteInvFunSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    extends ResolvedThreeRouteVertexMapSupply D G imageOf where
  /-- A two-stage surviving vertex is an original survivor or a left-primitive `δ`-star. -/
  twoStageSurvivor_cases : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    isContractSurvivingVertex (imageOf s).quotientForest v →
      isContractSurvivingVertex s.1.1 v ∨
        ∃ i : OneStageStarIndex D G s, i.isLeft ∧ i.vertex = v
  /-- Recover the two-stage star index from a star vertex. -/
  twoStarRecover : ∀ s : ResolvedCoassocSplitChoice D G,
    {w : VertexId // isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) w}
      ≃ TwoStageStarIndex D G imageOf s

open Classical in
/-- **R-6c-heart-6a-8c-fix-3b-2 — the three-route inverse map.** -/
noncomputable def threeRouteCorrInvFun
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (S : ResolvedThreeRouteInvFunSupply D G imageOf) (s : ResolvedCoassocSplitChoice D G) :
    {w : VertexId // w ∈ (twoStageContractGraph imageOf s).vertices} →
      {v : VertexId // v ∈ (oneStageContractGraph s).vertices} :=
  fun w =>
    if hstar : isContractStarVertex (imageOf s).quotientForest
        (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) w.1 then
      let k := (S.quotientStarEquiv s).symm (S.twoStarRecover s ⟨w.1, hstar⟩)
      ⟨k.1.toStarVertex.1, star_mem_contractWithStars s.1.1 (D.starOf G s.1.1) k.1.toStarVertex.2⟩
    else
      have hsurv := (contractWithStars_vertex_cases (imageOf s).quotientForest
        (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) w.2).resolve_right hstar
      if hO : isContractSurvivingVertex s.1.1 w.1 then
        ⟨w.1, surviving_mem_contractWithStars s.1.1 (D.starOf G s.1.1) hO⟩
      else
        let i := Classical.choose ((S.twoStageSurvivor_cases s hsurv).resolve_left hO)
        ⟨i.toStarVertex.1, star_mem_contractWithStars s.1.1 (D.starOf G s.1.1) i.toStarVertex.2⟩

end GaugeGeometry.QFT.Combinatorial
