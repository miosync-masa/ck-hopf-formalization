import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRetargetCoordinateWitnesses

/-!
# R-6c-body-44 — retarget coordinate facts: right_quotientStar from "TSV is not a quotient survivor"

Forty-fourth genuine-body step, reducing body-43's `right_quotientStar` to the cleaner "TSV is not a
quotient-forest survivor" classification, via the proved exhaustiveness of the two-stage graph vertices.

For any inner `v` (`v ∈ s.1.1.vertices`, hence `v ∈ G.vertices`), the two-stage vertex `TSV` lies in the
two-stage graph (`resolved_retarget_rhs_mem`), so `contractWithStars_vertex_cases` gives
`isContractSurvivingVertex quotientForest TSV ∨ isContractStarVertex quotientForest starB TSV`.  For a non-left
`v`, `TSV` is NOT a quotient survivor (`TSV_not_survivor`), so the disjunction resolves to the quotient-star
side — exactly `right_quotientStar`.

`survival` stays the body-10 `ResolvedLeftStarSurvivalSupply` (it IS the left-star-survives leaf; no further
coordinate content).

So body-43's coordinate witnesses flow from `{survival (body-10) + freshA + freshB + TSV_not_survivor}`, where
`TSV_not_survivor` (a non-left inner vertex's two-stage vertex is not a quotient survivor — the contrapositive
of body-11's two-stage-survivor split) is the clean classification fact; `right_quotientStar` is DERIVED.

Per the HALT, no `innerLeft` contrapositive proof-term / `Classical.choose` comparison is entered, and the star
recoveries are untouched.

Landed:

* `ResolvedRetargetCoordinateFactsSupply D G imageOf` — `survival` + `freshA` + `freshB` + `TSV_not_survivor`;
* `.toCoordinateWitnessSupply` — body-43's supply (with `right_quotientStar` derived via
  `contractWithStars_vertex_cases`).

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

/-- **R-6c-body-44 — the coordinate-facts supply.**  Body-10 left survival, the two star freshnesses, and the
right-route "not a quotient survivor" classification. -/
structure ResolvedRetargetCoordinateFactsSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- Body-10: left one-stage stars survive stage 2. -/
  survival : ResolvedLeftStarSurvivalSupply D G imageOf
  /-- The input outer forest's stars are fresh. -/
  freshA : ∀ (s : ResolvedCoassocSplitChoice D G), ∀ η ∈ s.1.1.elements,
    D.starOf G s.1.1 η ∉ G.vertices
  /-- The quotient forest's stars are fresh. -/
  freshB : ∀ (s : ResolvedCoassocSplitChoice D G),
    ∀ η ∈ (imageOf s).quotientForest.elements,
      D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest η
        ∉ (resolvedCoassocQuotientGraph (imageOf s)).vertices
  /-- RIGHT: a non-left inner vertex's two-stage vertex is NOT a quotient-forest survivor. -/
  TSV_not_survivor : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    v ∈ s.1.1.vertices → ¬ retargetInnerLeft imageOf s v →
    ¬ isContractSurvivingVertex (imageOf s).quotientForest
      ((imageOf s).quotientForest.retargetVertex
        (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
        (rightVertexDomain (imageOf s) v))

/-- **R-6c-body-44 — body-43's coordinate-witness supply from the facts.**  `right_quotientStar` is the
quotient-star side of `contractWithStars_vertex_cases`, resolved by `TSV_not_survivor`. -/
def ResolvedRetargetCoordinateFactsSupply.toCoordinateWitnessSupply
    (F : ResolvedRetargetCoordinateFactsSupply D G imageOf) :
    ResolvedRetargetCoordinateWitnessSupply D G imageOf where
  survival := F.survival
  freshA := F.freshA
  freshB := F.freshB
  right_quotientStar := by
    intro s v hin hnleft
    obtain ⟨γ, hγ, hvγ⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hin
    exact (contractWithStars_vertex_cases (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
      (resolved_retarget_rhs_mem s (γ.vertices_subset hvγ))).resolve_left
        (F.TSV_not_survivor s hin hnleft)

end GaugeGeometry.QFT.Combinatorial
