import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRetargetInnerLeft

/-!
# R-6c-body-31 — the inner-right (quotient-star) retarget route

Thirty-first genuine-body step, isolating body-27's `inner_right_case` — the inner-RIGHT route of
`retarget_corr_on_vertices` — through body-29's packaged `threeRoute_invFun_star_val`.  Completes the three
routes (outer body-29b + inner-left body-30 + inner-right here).

For `v ∈ G.vertices`, `v ∈ s.1.1.vertices` in a forest/right component (`¬ innerLeft`), the LHS is the one-stage
star `s.1.1.retargetVertex (D.starOf G s.1.1) v`.  On the RHS the two-stage vertex `TSV =
quotientForest.retarget … (rightVertexDomain … v)` IS a quotient star (`two_stage_is_quotientStar`), so
`threeRoute_invFun_star_val` evaluates the correspondence's `invFun` to the recovered one-stage star
`((quotientStarEquiv s).symm (twoStarRecover s ⟨TSV,·⟩)).1.toStarVertex.1`, which the construction sends back
to the one-stage star (`rightStar_recovery`).

The quotient-star applicability and the recovery are the fielded right/forest geometry; the assembly
(`inner_right_case`) is proved by rewriting through `threeRoute_invFun_star_val`.

Per the HALT, parent/quotient recovery is fielded (not proved); `innerLeft` is carried as the partition
predicate; no off-vertex bridge.

Landed:

* `ResolvedRetargetInnerRightSupply D G imageOf Three` — `innerLeft` + the quotient-star applicability + the
  one-stage-star recovery;
* `.inner_right_case` — body-27's inner-right route, PROVED via `threeRoute_invFun_star_val`.

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

/-- **R-6c-body-31 — the inner-right route supply.**  The partition predicate, the two-stage vertex being a
quotient star, and the one-stage-star recovery value. -/
structure ResolvedRetargetInnerRightSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (Three : ResolvedThreeRouteProvedSupply D G imageOf) where
  /-- The inner left/right partition (left-selection classification). -/
  innerLeft : ResolvedCoassocSplitChoice D G → VertexId → Prop
  /-- The two-stage vertex IS a quotient star (right/forest route). -/
  two_stage_is_quotientStar : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    v ∈ s.1.1.vertices → ¬ innerLeft s v →
    isContractStarVertex (imageOf s).quotientForest
        (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
        ((imageOf s).quotientForest.retargetVertex
          (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
          (rightVertexDomain (imageOf s) v))
  /-- The recovered one-stage star (from the two-stage quotient star) is the one-stage star. -/
  rightStar_recovery : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId}
    (hin : v ∈ s.1.1.vertices) (hnleft : ¬ innerLeft s v),
    s.1.1.retargetVertex (D.starOf G s.1.1) v
      = ((Three.toInverseLawSupply.route.toResolvedThreeRouteInvFunSupply.quotientStarEquiv s).symm
          (Three.toInverseLawSupply.route.toResolvedThreeRouteInvFunSupply.twoStarRecover s
            ⟨(imageOf s).quotientForest.retargetVertex
                (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
                (rightVertexDomain (imageOf s) v),
              two_stage_is_quotientStar s hin hnleft⟩)).1.toStarVertex.1

/-- **R-6c-body-31 — body-27's `inner_right_case`, PROVED via `threeRoute_invFun_star_val`. -/
theorem ResolvedRetargetInnerRightSupply.inner_right_case
    {Three : ResolvedThreeRouteProvedSupply D G imageOf}
    (F : ResolvedRetargetInnerRightSupply D G imageOf Three)
    (s : ResolvedCoassocSplitChoice D G) {v : VertexId} (hv : v ∈ G.vertices)
    (hin : v ∈ s.1.1.vertices) (hnleft : ¬ F.innerLeft s v) :
    RetargetCorrOnVerticesTarget Three s hv := by
  show s.1.1.retargetVertex (D.starOf G s.1.1) v = _
  rw [threeRoute_invFun_star_val Three s
    ⟨(imageOf s).quotientForest.retargetVertex
        (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
        (rightVertexDomain (imageOf s) v), resolved_retarget_rhs_mem s hv⟩
    (F.two_stage_is_quotientStar s hin hnleft)]
  exact F.rightStar_recovery s hin hnleft

end GaugeGeometry.QFT.Combinatorial
