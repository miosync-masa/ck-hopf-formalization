import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteInverseLaws

/-!
# R-6c-heart-6a-8c-fix-3c-1c — original-survivor round trip (route 1)

The third and simplest inverse-law case: a one-stage original survivor (`G \ A`) round-trips to itself.
Both maps stay on the surviving routes (same `VertexId` throughout):

```
one-stage original survivor → (survivingOriginal_to) two-stage survivor (same vertex)
  → corrInvFun survivor + original branch → same one-stage survivor
```

The forward map takes the surviving branch (the vertex is *not* a star, by `contract_surviving_not_star` +
the input-outer star freshness `hfreshA`); the inverse map takes the surviving branch (output not a
two-stage star, by `contract_surviving_not_star` + `hfreshB`) and then the *original* sub-branch (its `hO`
holds — the vertex IS an `s.1.1` survivor), returning the same vertex.  No `twoStageSurvivor_cases` and no
`originalSurvivor_not_leftStar` are needed (the `dif_pos hO` original branch fires directly).

Per the HALT, only the original-survivor case; no `corrLeftInv` assembly, no right-inverse cases.

Landed:

* `threeRouteCorrToFun_survivor_val` / `threeRouteCorrInvFun_survivorOriginal_val` — the two dite
  evaluations;
* `threeRoute_leftInv_originalSurvivor` — the route-1 left-inverse round trip.

With fix-3c-1a / 1b this completes all three left-inverse cases.

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

/-- **fix-3c-1c — `corrToFun` value on a survivor.**  In the `¬star` branch, the forward map keeps the
`VertexId`. -/
theorem threeRouteCorrToFun_survivor_val (S : ResolvedThreeRouteToFunSupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) (w : {v : VertexId // v ∈ (oneStageContractGraph s).vertices})
    (hnotstar : ¬ isContractStarVertex s.1.1 (D.starOf G s.1.1) w.1) :
    (threeRouteCorrToFun S s w).1 = w.1 := by
  simp only [threeRouteCorrToFun, dif_neg hnotstar]

/-- **fix-3c-1c — `corrInvFun` value on an original two-stage survivor.**  In the `¬star` + original branch,
the inverse map keeps the `VertexId`. -/
theorem threeRouteCorrInvFun_survivorOriginal_val (S : ResolvedThreeRouteInvFunSupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) (w : {v : VertexId // v ∈ (twoStageContractGraph imageOf s).vertices})
    (hstar : ¬ isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) w.1)
    (hO : isContractSurvivingVertex s.1.1 w.1) :
    (threeRouteCorrInvFun S s w).1 = w.1 := by
  simp only [threeRouteCorrInvFun, dif_neg hstar, dif_pos hO]

/-- **fix-3c-1c — the route-1 left-inverse round trip.**  A one-stage original survivor round-trips to
itself. -/
theorem threeRoute_leftInv_originalSurvivor (S : ResolvedThreeRouteFullSupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) (w : {v : VertexId // v ∈ (oneStageContractGraph s).vertices})
    (hSurv : isContractSurvivingVertex s.1.1 w.1)
    (hfreshA : ∀ η ∈ s.1.1.elements, D.starOf G s.1.1 η ∉ G.vertices)
    (hfreshB : ∀ η ∈ (imageOf s).quotientForest.elements,
      D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest η
        ∉ (resolvedCoassocQuotientGraph (imageOf s)).vertices) :
    threeRouteCorrInvFun S.toResolvedThreeRouteInvFunSupply s
        (threeRouteCorrToFun S.toResolvedThreeRouteToFunSupply s w) = w := by
  -- forward stays surviving
  have hnotstarA : ¬ isContractStarVertex s.1.1 (D.starOf G s.1.1) w.1 :=
    fun hst => contract_surviving_not_star s.1.1 (D.starOf G s.1.1) hfreshA hSurv hst
  have hfwd : (threeRouteCorrToFun S.toResolvedThreeRouteToFunSupply s w).1 = w.1 :=
    threeRouteCorrToFun_survivor_val S.toResolvedThreeRouteToFunSupply s w hnotstarA
  -- forward output is a two-stage survivor, hence not a two-stage star
  have hsurvfwd : isContractSurvivingVertex (imageOf s).quotientForest w.1 :=
    S.survivingOriginal_to s hSurv
  have hnotstarB : ¬ isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) w.1 :=
    fun hst => contract_surviving_not_star (imageOf s).quotientForest _ hfreshB hsurvfwd hst
  -- inverse takes the surviving + original branch, returning the same vertex
  apply Subtype.ext
  rw [threeRouteCorrInvFun_survivorOriginal_val S.toResolvedThreeRouteInvFunSupply s _
    (hfwd.symm ▸ hnotstarB) (hfwd.symm ▸ hSurv), hfwd]

end GaugeGeometry.QFT.Combinatorial
