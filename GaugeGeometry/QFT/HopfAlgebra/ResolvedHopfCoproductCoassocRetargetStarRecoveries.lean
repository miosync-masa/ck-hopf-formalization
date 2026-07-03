import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRetargetCoordinateBridge

/-!
# R-6c-body-42 — retarget star recoveries as the two index-inverse leaves

Forty-second genuine-body step, isolating the two remaining star RECOVERIES (`leftStar_recovery` /
`rightStar_recovery`) of body-30/31 into a dedicated supply, so — with the applicability now fully derived
(body-40/41) — the entire retarget three-route reduces to `{coordinate bridge + applicability}` plus exactly
these two index-inverse leaves.

Both recoveries state that the one-stage star `s.1.1.retargetVertex (D.starOf G s.1.1) v` equals the value the
correspondence's inverse returns:

* `leftStar_recovery` — `= (Classical.choose (twoStageSurvivor_cases … left branch)).toStarVertex.1` (the
  chosen left one-stage star);
* `rightStar_recovery` — `= ((quotientStarEquiv s).symm (twoStarRecover s ⟨TSV, ·⟩)).1.toStarVertex.1` (the
  recovered one-stage star from the two-stage quotient star).

These are the genuine "the inverse returns the right index" facts — the deepest retarget geometry.  Per the
HALT they are NOT proved (no `Classical.choose` witness proof-term comparison, no descent into the
`quotientStarEquiv` sector inverse); they are packaged as the two named recovery leaves, parameterized by the
applicability supply `App` (body-40) so their `Classical.choose` / `twoStarRecover` witnesses reference `App`'s
derived applicability facts.

Landed:

* `ResolvedRetargetStarRecoverySupply D G imageOf Three App` — the two recovery leaves over an applicability
  supply;
* `.toInnerLeftSupply` / `.toInnerRightSupply` — body-30 / body-31 supplies, completed from `App` + the
  recoveries.

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

/-- **R-6c-body-42 — the star-recovery supply.**  The two index-inverse recovery leaves, over an applicability
supply `App` (so the `Classical.choose` / `twoStarRecover` witnesses use `App`'s derived applicability). -/
structure ResolvedRetargetStarRecoverySupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (Three : ResolvedThreeRouteProvedSupply D G imageOf)
    (App : ResolvedRetargetInnerApplicabilitySupply D G imageOf) where
  /-- LEFT recovery: the one-stage star is the chosen left one-stage star (`twoStageSurvivor_cases`). -/
  leftStar_recovery : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId}
    (hv : v ∈ G.vertices) (hin : v ∈ s.1.1.vertices) (hleft : App.innerLeft s v),
    s.1.1.retargetVertex (D.starOf G s.1.1) v
      = (Classical.choose
          ((Three.toInverseLawSupply.route.toResolvedThreeRouteInvFunSupply.twoStageSurvivor_cases s
            ((contractWithStars_vertex_cases (imageOf s).quotientForest
              (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
              (resolved_retarget_rhs_mem s hv)).resolve_right
                (App.inner_left_not_quotientStar s hin hleft))).resolve_left
                (App.inner_left_not_survivor s hin hleft))).toStarVertex.1
  /-- RIGHT recovery: the one-stage star is the recovered one-stage star (`quotientStarEquiv.symm ∘
  twoStarRecover`). -/
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

/-- **R-6c-body-42 — body-30's inner-left supply from applicability + the left recovery. -/
def ResolvedRetargetStarRecoverySupply.toInnerLeftSupply
    (R : ResolvedRetargetStarRecoverySupply D G imageOf Three App) :
    ResolvedRetargetInnerLeftSupply D G imageOf Three where
  innerLeft := App.innerLeft
  two_stage_not_quotientStar := App.inner_left_not_quotientStar
  two_stage_not_survivor := App.inner_left_not_survivor
  leftStar_recovery := R.leftStar_recovery

/-- **R-6c-body-42 — body-31's inner-right supply from applicability + the right recovery. -/
def ResolvedRetargetStarRecoverySupply.toInnerRightSupply
    (R : ResolvedRetargetStarRecoverySupply D G imageOf Three App) :
    ResolvedRetargetInnerRightSupply D G imageOf Three where
  innerLeft := App.innerLeft
  two_stage_is_quotientStar := App.inner_right_is_quotientStar
  rightStar_recovery := R.rightStar_recovery

end GaugeGeometry.QFT.Combinatorial
