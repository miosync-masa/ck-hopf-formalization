import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRetargetInnerApplicabilityBody
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftStarSurvives
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightStarIndexScout

/-!
# R-6c-body-41 — retarget coordinate bridge: TSV facts from the star-index facts

Forty-first genuine-body step, connecting body-40's two-stage-vertex (`TSV`) applicability facts to the
`OneStageStarIndex` / `TwoStageStarIndex` facts of body-10/11, so the applicability flows from the existing
Transport machinery rather than from raw `TSV` fields.

`innerLeft` is FIXED as the concrete predicate "the two-stage vertex is a LEFT one-stage star":
`innerLeft s v := ∃ i : OneStageStarIndex D G s, i.isLeft ∧ i.vertex = TSV`.  Then:

* **left survivor** — from `ResolvedLeftStarSurvivalSupply` (body-10): a left index's vertex is in the quotient
  graph (`left_star_mem_quotientGraph`) and not in the quotient forest (`left_star_not_mem_quotientForest`), so
  it is a quotient-forest survivor; rewriting `i.vertex = TSV` gives `left_TSV_survivor`;
* **left fresh** — `i.vertex = D.starOf G s.1.1 i.η` is fresh (`freshA`), so `left_TSV_fresh`;
* **right quotient star** — from a `TwoStageStarIndex j` with `j.toStarVertex.1 = TSV`, `j.toStarVertex.2` IS the
  `isContractStarVertex` proof, giving `right_TSV_quotientStar`.

So body-40's three raw `TSV` facts are DERIVED from `{survival, freshA, freshB, right_index}` — the body-10/11
star-index facts.  Per the HALT, `innerLeft` is now fixed, `quotientStarEquiv.symm` values are untouched, and
the star recoveries are deferred (body-42+).

Landed:

* `retargetInnerLeft` — the fixed `innerLeft` predicate (`∃ left index with vertex = TSV`);
* `ResolvedRetargetCoordinateBridgeSupply D G imageOf` — `survival` + `freshA` + `freshB` + `right_index`;
* `.toInnerApplicabilitySupply` — body-40's supply, with the three TSV facts derived from the index facts.

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

/-- **R-6c-body-41 — the fixed `innerLeft` predicate.**  The two-stage vertex is a LEFT one-stage star. -/
def retargetInnerLeft (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (s : ResolvedCoassocSplitChoice D G) (v : VertexId) : Prop :=
  ∃ i : OneStageStarIndex D G s, i.isLeft ∧
    i.vertex = (imageOf s).quotientForest.retargetVertex
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
      (rightVertexDomain (imageOf s) v)

/-- **R-6c-body-41 — the coordinate bridge supply.**  The body-10 left-star survival, the one-stage / quotient
star freshnesses, and a right-route two-stage star index witness. -/
structure ResolvedRetargetCoordinateBridgeSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- Body-10: left one-stage stars survive stage 2. -/
  survival : ResolvedLeftStarSurvivalSupply D G imageOf
  /-- The input outer forest's stars are fresh (one-stage freshness). -/
  freshA : ∀ (s : ResolvedCoassocSplitChoice D G), ∀ η ∈ s.1.1.elements,
    D.starOf G s.1.1 η ∉ G.vertices
  /-- The quotient forest's stars are fresh (two-stage freshness). -/
  freshB : ∀ (s : ResolvedCoassocSplitChoice D G),
    ∀ η ∈ (imageOf s).quotientForest.elements,
      D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest η
        ∉ (resolvedCoassocQuotientGraph (imageOf s)).vertices
  /-- RIGHT: a non-left inner vertex's two-stage vertex is a `TwoStageStarIndex`'s star vertex. -/
  right_index : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    v ∈ s.1.1.vertices → ¬ retargetInnerLeft imageOf s v →
    ∃ j : TwoStageStarIndex D G imageOf s,
      j.toStarVertex.1 = (imageOf s).quotientForest.retargetVertex
        (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
        (rightVertexDomain (imageOf s) v)

/-- **R-6c-body-41 — body-40's applicability supply from the coordinate bridge.**  The three `TSV` facts are
derived from the star-index facts. -/
def ResolvedRetargetCoordinateBridgeSupply.toInnerApplicabilitySupply
    (B : ResolvedRetargetCoordinateBridgeSupply D G imageOf) :
    ResolvedRetargetInnerApplicabilitySupply D G imageOf where
  innerLeft := retargetInnerLeft imageOf
  freshB := B.freshB
  left_TSV_survivor := by
    intro s v _ hleft
    obtain ⟨i, hL, hveq⟩ := hleft
    exact hveq ▸ ⟨B.survival.left_star_mem_quotientGraph s i hL,
      B.survival.left_star_not_mem_quotientForest s i hL⟩
  left_TSV_fresh := by
    intro s v _ hleft
    obtain ⟨i, hL, hveq⟩ := hleft
    have hi : i.vertex ∉ G.vertices := B.freshA s i.η i.hη
    exact hveq ▸ hi
  right_TSV_quotientStar := by
    intro s v hin hnleft
    obtain ⟨j, hjeq⟩ := B.right_index s hin hnleft
    exact hjeq ▸ j.toStarVertex.2

end GaugeGeometry.QFT.Combinatorial
