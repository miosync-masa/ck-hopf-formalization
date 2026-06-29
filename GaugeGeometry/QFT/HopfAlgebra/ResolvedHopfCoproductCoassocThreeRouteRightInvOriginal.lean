import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteRoundTripOriginal

/-!
# R-6c-heart-6a-8c-fix-3c-3c — right-inverse original-survivor case (route 1)

The third (and simplest) `corrRightInv` case: a two-stage original survivor round-trips to itself.  Both
maps stay on the surviving routes (same `VertexId`).  Mirror of the left-inverse original case (fix-3c-1c):

```
two-stage original survivor → corrInvFun survivor + original branch → one-stage survivor (same vertex)
  → corrToFun survivor branch → same vertex
```

The inverse takes the survivor branch (`¬star` via `hfreshB`) and the *original* sub-branch (its `hO`
holds — `hOrig`); the forward takes the survivor branch (`¬star` via `hfreshA` + the `s.1.1`-survivor fact).
No `twoStageSurvivor_cases` / `originalSurvivor_not_leftStar` needed.

Per the HALT, only the original-survivor right-inverse case; with fix-3c-3a / 3b this completes all three
right-inverse cases.

Landed:

* `threeRoute_rightInv_originalSurvivor` — the route-1 right-inverse round trip.

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

/-- **fix-3c-3c — the route-1 right-inverse round trip.**  A two-stage original survivor round-trips to
itself. -/
theorem threeRoute_rightInv_originalSurvivor (S : ResolvedThreeRouteFullSupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) (w : {v : VertexId // v ∈ (twoStageContractGraph imageOf s).vertices})
    (hSurv : isContractSurvivingVertex (imageOf s).quotientForest w.1)
    (hOrig : isContractSurvivingVertex s.1.1 w.1)
    (hfreshA : ∀ η ∈ s.1.1.elements, D.starOf G s.1.1 η ∉ G.vertices)
    (hfreshB : ∀ η ∈ (imageOf s).quotientForest.elements,
      D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest η
        ∉ (resolvedCoassocQuotientGraph (imageOf s)).vertices) :
    threeRouteCorrToFun S.toResolvedThreeRouteToFunSupply s
        (threeRouteCorrInvFun S.toResolvedThreeRouteInvFunSupply s w) = w := by
  -- inverse stays surviving + original
  have hnotstarB : ¬ isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) w.1 :=
    fun hst => contract_surviving_not_star (imageOf s).quotientForest _ hfreshB hSurv hst
  have hinv : (threeRouteCorrInvFun S.toResolvedThreeRouteInvFunSupply s w).1 = w.1 :=
    threeRouteCorrInvFun_survivorOriginal_val S.toResolvedThreeRouteInvFunSupply s w hnotstarB hOrig
  -- inverse output is an s.1.1 survivor, hence not an s.1.1 star
  have hOrig' : isContractSurvivingVertex s.1.1
      (threeRouteCorrInvFun S.toResolvedThreeRouteInvFunSupply s w).1 := by rw [hinv]; exact hOrig
  have hnotstarA : ¬ isContractStarVertex s.1.1 (D.starOf G s.1.1)
      (threeRouteCorrInvFun S.toResolvedThreeRouteInvFunSupply s w).1 :=
    fun hst => contract_surviving_not_star s.1.1 _ hfreshA hOrig' hst
  -- forward keeps the vertex
  apply Subtype.ext
  rw [threeRouteCorrToFun_survivor_val S.toResolvedThreeRouteToFunSupply s _ hnotstarA, hinv]

end GaugeGeometry.QFT.Combinatorial
