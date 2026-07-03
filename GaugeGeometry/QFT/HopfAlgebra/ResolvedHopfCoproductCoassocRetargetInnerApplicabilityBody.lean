import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRetargetInnerRight

/-!
# R-6c-body-40 — retarget inner applicability from the Transport survivor/star facts

Fortieth genuine-body step, discharging the *applicability* halves of body-30 (`two_stage_not_quotientStar`,
`two_stage_not_survivor`) and body-31 (`two_stage_is_quotientStar`) from more atomic Transport-level facts,
leaving only the star RECOVERIES on the inner routes.

The two-stage vertex on the inner routes is `TSV = (imageOf s).quotientForest.retargetVertex (starB)
(rightVertexDomain (imageOf s) v)`.  Body-10 (left star survives) and body-11 (two-stage survivor split) say,
in these retarget coordinates:

* on a left/selected `v`, `TSV` is a quotient-forest SURVIVOR (`isContractSurvivingVertex quotientForest`) and
  is a fresh star (`∉ G.vertices`);
* on a right/forest `v`, `TSV` IS a quotient star.

Given those, the body-30/31 applicability facts are DERIVED:

* `two_stage_not_quotientStar` — a survivor is not a star (`contract_surviving_not_star` + `freshB`);
* `two_stage_not_survivor` — a fresh star (`∉ G.vertices`) is not an `s.1.1` survivor (which needs
  `∈ G.vertices`);
* `two_stage_is_quotientStar` — directly the right-route fact.

So the three fielded applicability facts collapse to the survivor/fresh/quotient-star Transport facts (body-10/11
in TSV coordinates) + `freshB`.  Per the HALT, the coordinate bridge to body-10's `OneStageStarIndex`/`i.vertex`
form and the star recoveries are NOT entered here — only the applicability, and only via
`contract_surviving_not_star`.

Landed:

* `ResolvedRetargetInnerApplicabilitySupply D G imageOf` — `innerLeft` + `freshB` + the three Transport facts;
* `.inner_left_not_quotientStar` / `.inner_left_not_survivor` / `.inner_right_is_quotientStar` — the body-30/31
  applicability fields, PROVED.

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

/-- **R-6c-body-40 — the inner-route applicability supply.**  The partition predicate, the quotient-star
freshness, and the three Transport-level facts about the two-stage vertex `TSV` (a left survivor + fresh, a
right quotient star) — body-10/11 content in retarget coordinates. -/
structure ResolvedRetargetInnerApplicabilitySupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- The inner left/right partition. -/
  innerLeft : ResolvedCoassocSplitChoice D G → VertexId → Prop
  /-- The quotient forest's stars are fresh (outside the quotient graph). -/
  freshB : ∀ (s : ResolvedCoassocSplitChoice D G),
    ∀ η ∈ (imageOf s).quotientForest.elements,
      D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest η
        ∉ (resolvedCoassocQuotientGraph (imageOf s)).vertices
  /-- LEFT: the two-stage vertex is a quotient-forest survivor (body-10, the left star survives). -/
  left_TSV_survivor : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    v ∈ s.1.1.vertices → innerLeft s v →
    isContractSurvivingVertex (imageOf s).quotientForest
      ((imageOf s).quotientForest.retargetVertex
        (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
        (rightVertexDomain (imageOf s) v))
  /-- LEFT: the two-stage vertex is a fresh star (outside `G`). -/
  left_TSV_fresh : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    v ∈ s.1.1.vertices → innerLeft s v →
    (imageOf s).quotientForest.retargetVertex
        (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
        (rightVertexDomain (imageOf s) v) ∉ G.vertices
  /-- RIGHT: the two-stage vertex is a quotient star (body-11 right route). -/
  right_TSV_quotientStar : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    v ∈ s.1.1.vertices → ¬ innerLeft s v →
    isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
      ((imageOf s).quotientForest.retargetVertex
        (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
        (rightVertexDomain (imageOf s) v))

/-- **R-6c-body-40 — body-30's `two_stage_not_quotientStar`, PROVED** (a survivor is not a star). -/
theorem ResolvedRetargetInnerApplicabilitySupply.inner_left_not_quotientStar
    (App : ResolvedRetargetInnerApplicabilitySupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) {v : VertexId}
    (hin : v ∈ s.1.1.vertices) (hleft : App.innerLeft s v) :
    ¬ isContractStarVertex (imageOf s).quotientForest
        (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
        ((imageOf s).quotientForest.retargetVertex
          (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
          (rightVertexDomain (imageOf s) v)) :=
  fun hst => contract_surviving_not_star (imageOf s).quotientForest _ (App.freshB s)
    (App.left_TSV_survivor s hin hleft) hst

/-- **R-6c-body-40 — body-30's `two_stage_not_survivor`, PROVED** (a fresh star is not an `s.1.1` survivor). -/
theorem ResolvedRetargetInnerApplicabilitySupply.inner_left_not_survivor
    (App : ResolvedRetargetInnerApplicabilitySupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) {v : VertexId}
    (hin : v ∈ s.1.1.vertices) (hleft : App.innerLeft s v) :
    ¬ isContractSurvivingVertex s.1.1
        ((imageOf s).quotientForest.retargetVertex
          (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
          (rightVertexDomain (imageOf s) v)) :=
  fun hsurv => App.left_TSV_fresh s hin hleft hsurv.1

/-- **R-6c-body-40 — body-31's `two_stage_is_quotientStar`, PROVED** (directly the right-route fact). -/
theorem ResolvedRetargetInnerApplicabilitySupply.inner_right_is_quotientStar
    (App : ResolvedRetargetInnerApplicabilitySupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) {v : VertexId}
    (hin : v ∈ s.1.1.vertices) (hnleft : ¬ App.innerLeft s v) :
    isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
      ((imageOf s).quotientForest.retargetVertex
        (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
        (rightVertexDomain (imageOf s) v)) :=
  App.right_TSV_quotientStar s hin hnleft

end GaugeGeometry.QFT.Combinatorial
