import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteInverseLaws

/-!
# R-6c-heart-6a-8c-fix-3c-1b — left-star round trip (route 2)

The second inverse-law case: a one-stage **left** primitive star round-trips to itself.  Unlike the
quotient star, it routes through a two-stage *survivor*:

```
one-stage left star → (leftStar_toSurvivor) two-stage survivor (same VertexId)
  → corrInvFun survivor branch → (twoStageSurvivor_cases) the left-star sub-branch → one-stage star
```

The forward map sees `isLeft` (so the left branch fires); the inverse map sees the output is a *survivor*
(via `contract_surviving_not_star` + the quotient-forest star freshness `hfreshB`), is *not* an original
survivor (via `originalSurvivor_not_leftStar`), and so takes the left-star sub-branch, whose chosen index has
`.vertex = w.1` by `twoStageSurvivor_cases`'s existential — closing the round trip (no `leftStar_unique`
needed: the vertex equality is read straight off `Classical.choose_spec`).

Hypotheses beyond the supply: `honeInv` (`oneStarRecover` inverts `toStarVertex`, so the forward sees
`isLeft`) and `hfreshB` (quotient-forest star freshness) — both free from the concrete recoveries / the
canonical fresh-star property (6a-7a / 6a-8b-2).

Per the HALT, only the left-star case; no original-survivor round trip, no full `corrLeftInv`.

Landed:

* `threeRouteCorrToFun_leftStar_val` / `threeRouteCorrInvFun_survivorLeft_val` — the two dite evaluations;
* `threeRoute_leftInv_leftStar` — the route-2 left-inverse round trip.

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

/-- **fix-3c-1b — `corrToFun` value on a left star.**  In the star + `isLeft` branch, the forward map keeps
the same `VertexId`. -/
theorem threeRouteCorrToFun_leftStar_val (S : ResolvedThreeRouteToFunSupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) (w : {v : VertexId // v ∈ (oneStageContractGraph s).vertices})
    (hstar : isContractStarVertex s.1.1 (D.starOf G s.1.1) w.1)
    (hL : (S.oneStarRecover s ⟨w.1, hstar⟩).isLeft) :
    (threeRouteCorrToFun S s w).1 = w.1 := by
  simp only [threeRouteCorrToFun, dif_pos hstar, dif_pos hL]

/-- **fix-3c-1b — `corrInvFun` value on a non-original two-stage survivor.**  In the surviving + `¬original`
branch, the inverse map emits the chosen left index's star vertex. -/
theorem threeRouteCorrInvFun_survivorLeft_val (S : ResolvedThreeRouteInvFunSupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) (w : {v : VertexId // v ∈ (twoStageContractGraph imageOf s).vertices})
    (hstar : ¬ isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) w.1)
    (hO : ¬ isContractSurvivingVertex s.1.1 w.1) :
    (threeRouteCorrInvFun S s w).1
      = (Classical.choose ((S.twoStageSurvivor_cases s
          ((contractWithStars_vertex_cases (imageOf s).quotientForest
            (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
            w.2).resolve_right hstar)).resolve_left hO)).toStarVertex.1 := by
  simp only [threeRouteCorrInvFun, dif_neg hstar, dif_neg hO]

/-- **fix-3c-1b — the route-2 left-inverse round trip.**  A one-stage left star round-trips to itself. -/
theorem threeRoute_leftInv_leftStar (S : ResolvedThreeRouteFullSupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) (w : {v : VertexId // v ∈ (oneStageContractGraph s).vertices})
    (hstar : isContractStarVertex s.1.1 (D.starOf G s.1.1) w.1)
    (hL : (S.oneStarRecover s ⟨w.1, hstar⟩).isLeft)
    (hfreshB : ∀ η ∈ (imageOf s).quotientForest.elements,
      D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest η
        ∉ (resolvedCoassocQuotientGraph (imageOf s)).vertices) :
    threeRouteCorrInvFun S.toResolvedThreeRouteInvFunSupply s
        (threeRouteCorrToFun S.toResolvedThreeRouteToFunSupply s w) = w := by
  set i := S.oneStarRecover s ⟨w.1, hstar⟩ with hi
  -- the recovered index's vertex is w.1
  have hiv : i.vertex = w.1 := S.oneStarRecover_vertex s ⟨w.1, hstar⟩
  -- forward keeps the vertex
  have hfwd : (threeRouteCorrToFun S.toResolvedThreeRouteToFunSupply s w).1 = w.1 :=
    threeRouteCorrToFun_leftStar_val S.toResolvedThreeRouteToFunSupply s w hstar hL
  -- the forward output is a two-stage survivor
  have hsurv : isContractSurvivingVertex (imageOf s).quotientForest w.1 := by
    have h := S.leftStar_toSurvivor s i hL
    rwa [hiv] at h
  -- ... hence not a two-stage star
  have hnotstar : ¬ isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) w.1 :=
    fun hst => contract_surviving_not_star (imageOf s).quotientForest _ hfreshB hsurv hst
  -- ... and not an original survivor
  have hO : ¬ isContractSurvivingVertex s.1.1 w.1 :=
    fun hOs => S.originalSurvivor_not_leftStar s hOs i hL (hiv.symm)
  -- transport the two facts to the forward output's vertex
  have hnotstar' : ¬ isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
      (threeRouteCorrToFun S.toResolvedThreeRouteToFunSupply s w).1 := by rw [hfwd]; exact hnotstar
  have hO' : ¬ isContractSurvivingVertex s.1.1
      (threeRouteCorrToFun S.toResolvedThreeRouteToFunSupply s w).1 := by rw [hfwd]; exact hO
  -- evaluate the inverse
  apply Subtype.ext
  rw [threeRouteCorrInvFun_survivorLeft_val S.toResolvedThreeRouteInvFunSupply s _ hnotstar' hO']
  -- the chosen index's vertex is the forward output's vertex = w.1
  have hspec := (S.twoStageSurvivor_cases s
    ((contractWithStars_vertex_cases (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
      (threeRouteCorrToFun S.toResolvedThreeRouteToFunSupply s w).2).resolve_right hnotstar')).resolve_left hO'
  exact (Classical.choose_spec hspec).2.trans hfwd

end GaugeGeometry.QFT.Combinatorial
