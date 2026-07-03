import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRetargetOuterConcrete

/-!
# R-6c-body-30 — the inner-left (left-star survivor) retarget route

Thirtieth genuine-body step, isolating body-27's `inner_left_case` — the inner-LEFT route of
`retarget_corr_on_vertices` — through body-29's packaged `threeRoute_invFun_leftStar_val`.

For `v ∈ G.vertices`, `v ∈ s.1.1.vertices` in a left/selected component, the LHS is the one-stage LEFT star
`s.1.1.retargetVertex (D.starOf G s.1.1) v`.  On the RHS the two-stage vertex `TSV = quotientForest.retarget …
(rightVertexDomain … v)` is a two-stage SURVIVOR (a LEFT star survives the quotient — body-10), so it is
neither a quotient star (`two_stage_not_quotientStar`) nor an `s.1.1` survivor (`two_stage_not_survivor`);
`threeRoute_invFun_leftStar_val` then evaluates the correspondence's `invFun` to the recovered left star
`Classical.choose (…twoStageSurvivor_cases…)`, which the construction sends back to the one-stage star
(`leftStar_recovery`).

The two applicability facts and the recovery are the fielded left-star geometry; the assembly
(`inner_left_case`) is proved by rewriting through `threeRoute_invFun_leftStar_val`.

Per the HALT, `inner_right` is untouched; `innerLeft` is carried as the partition predicate; parent recovery is
fielded, not proved.

Landed:

* `ResolvedRetargetInnerLeftSupply D G imageOf Three` — `innerLeft` + the two applicability facts + the
  left-star recovery;
* `.inner_left_case` — body-27's inner-left route, PROVED via `threeRoute_invFun_leftStar_val`.

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

/-- **R-6c-body-30 — the inner-left route supply.**  The partition predicate, the two-stage vertex being a
left survivor (not a quotient star / not an `s.1.1` survivor), and the left-star recovery value. -/
structure ResolvedRetargetInnerLeftSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (Three : ResolvedThreeRouteProvedSupply D G imageOf) where
  /-- The inner left/right partition (left-selection classification). -/
  innerLeft : ResolvedCoassocSplitChoice D G → VertexId → Prop
  /-- The two-stage vertex is NOT a quotient star (the left star survives — body-10). -/
  two_stage_not_quotientStar : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    v ∈ s.1.1.vertices → innerLeft s v →
    ¬ isContractStarVertex (imageOf s).quotientForest
        (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
        ((imageOf s).quotientForest.retargetVertex
          (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
          (rightVertexDomain (imageOf s) v))
  /-- The two-stage vertex is NOT an `s.1.1` survivor (it is a star, hence fresh / not in `G`). -/
  two_stage_not_survivor : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    v ∈ s.1.1.vertices → innerLeft s v →
    ¬ isContractSurvivingVertex s.1.1
        ((imageOf s).quotientForest.retargetVertex
          (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
          (rightVertexDomain (imageOf s) v))
  /-- The recovered left star (from the two-stage survivor case) is the one-stage left star. -/
  leftStar_recovery : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId}
    (hv : v ∈ G.vertices) (hin : v ∈ s.1.1.vertices) (hleft : innerLeft s v),
    s.1.1.retargetVertex (D.starOf G s.1.1) v
      = (Classical.choose
          ((Three.toInverseLawSupply.route.toResolvedThreeRouteInvFunSupply.twoStageSurvivor_cases s
            ((contractWithStars_vertex_cases (imageOf s).quotientForest
              (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
              (resolved_retarget_rhs_mem s hv)).resolve_right
                (two_stage_not_quotientStar s hin hleft))).resolve_left
                (two_stage_not_survivor s hin hleft))).toStarVertex.1

/-- **R-6c-body-30 — body-27's `inner_left_case`, PROVED via `threeRoute_invFun_leftStar_val`. -/
theorem ResolvedRetargetInnerLeftSupply.inner_left_case
    {Three : ResolvedThreeRouteProvedSupply D G imageOf}
    (F : ResolvedRetargetInnerLeftSupply D G imageOf Three)
    (s : ResolvedCoassocSplitChoice D G) {v : VertexId} (hv : v ∈ G.vertices)
    (hin : v ∈ s.1.1.vertices) (hleft : F.innerLeft s v) :
    RetargetCorrOnVerticesTarget Three s hv := by
  show s.1.1.retargetVertex (D.starOf G s.1.1) v = _
  rw [threeRoute_invFun_leftStar_val Three s
    ⟨(imageOf s).quotientForest.retargetVertex
        (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
        (rightVertexDomain (imageOf s) v), resolved_retarget_rhs_mem s hv⟩
    (F.two_stage_not_quotientStar s hin hleft) (F.two_stage_not_survivor s hin hleft)]
  exact F.leftStar_recovery s hv hin hleft

end GaugeGeometry.QFT.Combinatorial
