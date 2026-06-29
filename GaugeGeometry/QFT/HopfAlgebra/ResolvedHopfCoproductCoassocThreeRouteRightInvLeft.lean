import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteRoundTripLeft

/-!
# R-6c-heart-6a-8c-fix-3c-3b — right-inverse left-star survivor case (route 2)

The second `corrRightInv` case: a two-stage **survivor** that is a left-primitive `δ`-star round-trips to
itself.  Mirror of the left-inverse left-star case (fix-3c-1b):

```
two-stage survivor (a left δ-star) → corrInvFun survivor + ¬original branch → chosen left index → one-stage star
  → corrToFun left branch → same vertex
```

The inverse takes the survivor branch (`¬star` via `contract_surviving_not_star` + `hfreshB`) and the
`¬original` sub-branch (`originalSurvivor_not_leftStar` against the given left witness); `twoStageSurvivor_cases`'
chosen index has `.vertex = w.1` (`Classical.choose_spec`).  The forward recovers that index
(`honeRecover`), sees `isLeft`, and keeps the vertex.  No `leftStar_unique` needed.

Per the HALT, only the left-star survivor right-inverse case; no original-survivor case, no full
`corrRightInv`.

Landed:

* `threeRoute_rightInv_leftStarSurvivor` — the route-2 right-inverse round trip.

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

/-- **fix-3c-3b — the route-2 right-inverse round trip.**  A two-stage left-`δ`-star survivor round-trips to
itself. -/
theorem threeRoute_rightInv_leftStarSurvivor (S : ResolvedThreeRouteInverseLawSupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) (w : {v : VertexId // v ∈ (twoStageContractGraph imageOf s).vertices})
    (i : OneStageStarIndex D G s) (hL : i.isLeft) (hvw : i.vertex = w.1)
    (honeRecover : ∀ k : OneStageStarIndex D G s, S.route.oneStarRecover s k.toStarVertex = k)
    (hfreshB : ∀ η ∈ (imageOf s).quotientForest.elements,
      D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest η
        ∉ (resolvedCoassocQuotientGraph (imageOf s)).vertices)
    (hSurv : isContractSurvivingVertex (imageOf s).quotientForest w.1) :
    threeRouteCorrToFun S.route.toResolvedThreeRouteToFunSupply s
        (threeRouteCorrInvFun S.route.toResolvedThreeRouteInvFunSupply s w) = w := by
  -- inverse takes the survivor + ¬original branch
  have hnotstar : ¬ isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) w.1 :=
    fun hst => contract_surviving_not_star (imageOf s).quotientForest _ hfreshB hSurv hst
  have hO : ¬ isContractSurvivingVertex s.1.1 w.1 :=
    fun hOs => S.route.originalSurvivor_not_leftStar s hOs i hL hvw.symm
  have hEx := (S.route.twoStageSurvivor_cases s
    ((contractWithStars_vertex_cases (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
      w.2).resolve_right hnotstar)).resolve_left hO
  have hspec := Classical.choose_spec hEx
  -- inverse output value
  have hinv : (threeRouteCorrInvFun S.route.toResolvedThreeRouteInvFunSupply s w).1
      = (Classical.choose hEx).toStarVertex.1 :=
    threeRouteCorrInvFun_survivorLeft_val S.route.toResolvedThreeRouteInvFunSupply s w hnotstar hO
  -- the inverse output is a one-stage star
  have hfwdstar : isContractStarVertex s.1.1 (D.starOf G s.1.1)
      (threeRouteCorrInvFun S.route.toResolvedThreeRouteInvFunSupply s w).1 := by
    rw [hinv]; exact (Classical.choose hEx).toStarVertex.2
  -- the forward recovers the chosen index
  have hrec : S.route.oneStarRecover s
      ⟨(threeRouteCorrInvFun S.route.toResolvedThreeRouteInvFunSupply s w).1, hfwdstar⟩
      = Classical.choose hEx := by
    have he : (⟨(threeRouteCorrInvFun S.route.toResolvedThreeRouteInvFunSupply s w).1, hfwdstar⟩ :
        {v : VertexId // isContractStarVertex s.1.1 (D.starOf G s.1.1) v})
        = (Classical.choose hEx).toStarVertex := Subtype.ext hinv
    rw [he, honeRecover]
  have hfwdleft : (S.route.oneStarRecover s
      ⟨(threeRouteCorrInvFun S.route.toResolvedThreeRouteInvFunSupply s w).1, hfwdstar⟩).isLeft := by
    rw [hrec]; exact hspec.1
  -- forward keeps the vertex; chosen index's vertex is w.1
  apply Subtype.ext
  rw [threeRouteCorrToFun_leftStar_val S.route.toResolvedThreeRouteToFunSupply s _ hfwdstar hfwdleft, hinv]
  exact hspec.2

end GaugeGeometry.QFT.Combinatorial
