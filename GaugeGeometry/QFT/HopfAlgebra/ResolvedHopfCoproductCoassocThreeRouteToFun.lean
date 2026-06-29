import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteVertexMap

/-!
# R-6c-heart-6a-8c-fix-3b-1 — `corrToFun` from the three routes (forward map)

The forward half of the three-route vertex correspondence, constructed from the route data: a one-stage
vertex is sent by `contractWithStars_vertex_cases`:

```
surviving original vertex → two-stage surviving original   (survivingOriginal_to)
star vertex
  ├ left primitive        → two-stage surviving vertex      (leftStar_toSurvivor, same VertexId)
  └ right / forest         → two-stage star                 (quotientStarEquiv)
```

The star vertex is decoded into its `OneStageStarIndex` via a recovery equivalence `oneStarRecover` (its
inverse of `toStarVertex`, with the `.vertex` agreement so the left route can keep the same `VertexId`).
`oneStarRecover` is a supply field here — it is later produced by `starVertexEquivIndex` (6a-8b-2) from
`starOf` injectivity, independent of the old star-map chain.

Per the HALT, only `corrToFun` is built: no `corrInvFun`, no inverse laws, no concrete `quotientStarEquiv`.

Landed:

* `ResolvedThreeRouteToFunSupply D G imageOf` — the three routes + `oneStarRecover` (+ its `.vertex`
  agreement);
* `threeRouteCorrToFun` — the assembled forward map.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-8c-fix-3b-1 — the forward-map supply.**  The three routes plus the star-vertex recovery
(with its `.vertex` agreement, so the left route preserves the `VertexId`). -/
structure ResolvedThreeRouteToFunSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    extends ResolvedThreeRouteVertexMapSupply D G imageOf where
  /-- Recover the one-stage star index from a star vertex. -/
  oneStarRecover : ∀ s : ResolvedCoassocSplitChoice D G,
    {v : VertexId // isContractStarVertex s.1.1 (D.starOf G s.1.1) v} ≃ OneStageStarIndex D G s
  /-- The recovered index's star vertex is the original. -/
  oneStarRecover_vertex : ∀ (s : ResolvedCoassocSplitChoice D G)
    (w : {v : VertexId // isContractStarVertex s.1.1 (D.starOf G s.1.1) v}),
    (oneStarRecover s w).vertex = w.1

open Classical in
/-- **R-6c-heart-6a-8c-fix-3b-1 — the three-route forward map.** -/
noncomputable def threeRouteCorrToFun
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (S : ResolvedThreeRouteToFunSupply D G imageOf) (s : ResolvedCoassocSplitChoice D G) :
    {v : VertexId // v ∈ (oneStageContractGraph s).vertices} →
      {w : VertexId // w ∈ (twoStageContractGraph imageOf s).vertices} :=
  fun v =>
    if hstar : isContractStarVertex s.1.1 (D.starOf G s.1.1) v.1 then
      let i := S.oneStarRecover s ⟨v.1, hstar⟩
      if hL : i.isLeft then
        ⟨v.1, surviving_mem_contractWithStars (imageOf s).quotientForest
          (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
          (S.oneStarRecover_vertex s ⟨v.1, hstar⟩ ▸ S.leftStar_toSurvivor s i hL)⟩
      else
        let j := S.quotientStarEquiv s ⟨i, i.isLeft_or_hasQuotientStar.resolve_left hL⟩
        ⟨j.toStarVertex.1, star_mem_contractWithStars (imageOf s).quotientForest
          (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
          j.toStarVertex.2⟩
    else
      ⟨v.1, surviving_mem_contractWithStars (imageOf s).quotientForest
        (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
        (S.survivingOriginal_to s
          ((contractWithStars_vertex_cases s.1.1 (D.starOf G s.1.1) v.2).resolve_right hstar))⟩

end GaugeGeometry.QFT.Combinatorial
