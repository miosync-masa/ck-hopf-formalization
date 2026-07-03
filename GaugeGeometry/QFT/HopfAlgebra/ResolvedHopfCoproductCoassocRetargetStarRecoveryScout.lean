import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRetargetStarRecoveries

/-!
# R-6c-body-45 — retarget star-recovery scout: the LEFT recovery is `one-stage star = TSV`

Forty-fifth genuine-body step, a SCOUT of body-42's two star recoveries against the existing three-route
right-inverse machinery — with a partial discharge on the left.

## Finding (left): the `Classical.choose` is eliminable

`twoStageSurvivor_cases s (h) : isContractSurvivingVertex s.1.1 v ∨ ∃ i : OneStageStarIndex, i.isLeft ∧
i.vertex = v` (TransportLeaves).  So the `Classical.choose` in `leftStar_recovery` picks an `i` with
`i.vertex = TSV`, and `Classical.choose_spec … |>.2` gives `(choose).vertex = TSV`, hence `(choose).toStarVertex.1
= TSV` (`toStarVertex.1 = vertex`).  This is exactly the intermediate `hspec` used in
`threeRoute_rightInv_leftStarSurvivor` (fix-3c-3b).  Therefore `leftStar_recovery` collapses to the clean vertex
equality `s.1.1.retargetVertex (D.starOf G s.1.1) v = TSV` — the one-stage star equals the two-stage vertex (a
LEFT star survives the quotient unchanged) — with NO `Classical.choose` remaining.

## Finding (right): keeps the `quotientStarEquiv` navigation

`rightStar_recovery`'s RHS is `((quotientStarEquiv s).symm (twoStarRecover s ⟨TSV, ·⟩)).1.toStarVertex.1` — no
`Classical.choose`, but the recovered one-stage index runs through the `quotientStarEquiv` / `twoStarRecover`
inverse maps (as in `threeRoute_rightInv_quotientStar`).  Reducing it to a raw vertex equality needs the
`quotientStarEquiv` sector inverse; per the HALT that is left as the fielded right recovery.

So the two recoveries split: LEFT is a clean `one-stage star = TSV` fact; RIGHT stays the index-inverse leaf.

Per the HALT, only `Classical.choose_spec .2` (a vertex equality) is used — no proof-term / index-equality
comparison; the `quotientStarEquiv` internals are untouched.

Landed:

* `ResolvedRetargetStarRecoveryFactsSupply D G imageOf Three App` — `left_oneStageStar_eq_TSV` (the clean left
  fact) + `rightStar_recovery` (the fielded right leaf);
* `.toStarRecoverySupply` — body-42's supply (left recovery derived by eliminating `Classical.choose`).

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

/-- **R-6c-body-45 — the star-recovery facts supply.**  The LEFT recovery as the clean `one-stage star = TSV`
vertex equality, plus the RIGHT recovery (still the `quotientStarEquiv` index-inverse leaf). -/
structure ResolvedRetargetStarRecoveryFactsSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (Three : ResolvedThreeRouteProvedSupply D G imageOf)
    (App : ResolvedRetargetInnerApplicabilitySupply D G imageOf) where
  /-- LEFT: the one-stage star equals the two-stage vertex (a left star survives unchanged). -/
  left_oneStageStar_eq_TSV : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId}
    (_hv : v ∈ G.vertices) (_hin : v ∈ s.1.1.vertices) (_hleft : App.innerLeft s v),
    s.1.1.retargetVertex (D.starOf G s.1.1) v
      = (imageOf s).quotientForest.retargetVertex
          (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
          (rightVertexDomain (imageOf s) v)
  /-- RIGHT: the one-stage star is the recovered index's vertex (the `quotientStarEquiv` inverse leaf). -/
  rightStar_recovery : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId}
    (hin : v ∈ s.1.1.vertices) (hnleft : ¬ App.innerLeft s v),
    s.1.1.retargetVertex (D.starOf G s.1.1) v
      = ((Three.toInverseLawSupply.route.toResolvedThreeRouteInvFunSupply.quotientStarEquiv s).symm
          (Three.toInverseLawSupply.route.toResolvedThreeRouteInvFunSupply.twoStarRecover s
            ⟨(imageOf s).quotientForest.retargetVertex
                (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
                (rightVertexDomain (imageOf s) v),
              App.inner_right_is_quotientStar s hin hnleft⟩)).1.toStarVertex.1

variable {Three : ResolvedThreeRouteProvedSupply D G imageOf}
  {App : ResolvedRetargetInnerApplicabilitySupply D G imageOf}

/-- **R-6c-body-45 — body-42's recovery supply from the facts.**  The LEFT recovery follows by eliminating the
`Classical.choose` with `choose_spec .2` (`(choose).vertex = TSV`). -/
def ResolvedRetargetStarRecoveryFactsSupply.toStarRecoverySupply
    (F : ResolvedRetargetStarRecoveryFactsSupply D G imageOf Three App) :
    ResolvedRetargetStarRecoverySupply D G imageOf Three App where
  leftStar_recovery := by
    intro s v hv hin hleft
    rw [F.left_oneStageStar_eq_TSV s hv hin hleft]
    exact (Classical.choose_spec
      ((Three.toInverseLawSupply.route.toResolvedThreeRouteInvFunSupply.twoStageSurvivor_cases s
        ((contractWithStars_vertex_cases (imageOf s).quotientForest
          (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
          (resolved_retarget_rhs_mem s hv)).resolve_right
            (App.inner_left_not_quotientStar s hin hleft))).resolve_left
            (App.inner_left_not_survivor s hin hleft))).2.symm
  rightStar_recovery := F.rightStar_recovery

end GaugeGeometry.QFT.Combinatorial
