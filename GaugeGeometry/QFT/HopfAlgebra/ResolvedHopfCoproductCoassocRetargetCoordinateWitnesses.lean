import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRetargetCoordinateBridge

/-!
# R-6c-body-43 — retarget coordinate witnesses: right_index from the quotient-star fact

Forty-third genuine-body step, discharging body-41's `right_index` witness (a `TwoStageStarIndex` whose star
vertex is the two-stage vertex `TSV`) down to the plain quotient-star fact, and confirming `survival` is
already the body-10 leaf.

The `right_index` witness is EQUIVALENT to `isContractStarVertex (imageOf s).quotientForest starB TSV`: a
quotient star is by definition `TSV ∈ quotientForest.starVertices starB`, and `mem_starVertices` recovers a
component `δ ∈ quotientForest.elements` with `starB δ = TSV` — which is exactly a `TwoStageStarIndex ⟨δ, hδ⟩`
whose `toStarVertex.1` is `TSV`.  So the `∃ TwoStageStarIndex` witness form collapses (provably) to the plain
`isContractStarVertex` fact — the same fact body-40 already carries as `right_TSV_quotientStar`.

`survival` is `ResolvedLeftStarSurvivalSupply` (body-10) directly — no further witness content.

So body-41's coordinate bridge flows from `{survival (body-10) + freshA + freshB + right_quotientStar}`, where
`right_quotientStar` is the clean `isContractStarVertex` fact; `right_index` is DERIVED via the
`mem_starVertices` recovery.

Per the HALT, `right_index_of_quotientStar` is proved (the `mem_starVertices` recovery); the star recoveries are
untouched.

Landed:

* `right_index_of_quotientStar` — `isContractStarVertex quotientForest starB w → ∃ j : TwoStageStarIndex,
  j.toStarVertex.1 = w` (PROVED, `mem_starVertices`);
* `ResolvedRetargetCoordinateWitnessSupply D G imageOf` — `survival` + `freshA` + `freshB` +
  `right_quotientStar`;
* `.toCoordinateBridgeSupply` — body-41's bridge (with `right_index` derived).

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

/-- **R-6c-body-43 — a quotient star is a `TwoStageStarIndex`'s star vertex.**  `mem_starVertices` recovers the
quotient-forest component, giving the two-stage star index. -/
theorem right_index_of_quotientStar (s : ResolvedCoassocSplitChoice D G) {w : VertexId}
    (h : isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) w) :
    ∃ j : TwoStageStarIndex D G imageOf s, j.toStarVertex.1 = w := by
  obtain ⟨δ, hδ, hδeq⟩ := ResolvedAdmissibleSubgraph.mem_starVertices.mp h
  exact ⟨⟨δ, hδ⟩, hδeq⟩

/-- **R-6c-body-43 — the coordinate-witness supply.**  Body-10 left survival, the two star freshnesses, and the
right-route quotient-star fact (the clean `isContractStarVertex` form of `right_index`). -/
structure ResolvedRetargetCoordinateWitnessSupply (D : ResolvedCoproductProperForestData)
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
  /-- RIGHT: a non-left inner vertex's two-stage vertex is a quotient star. -/
  right_quotientStar : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    v ∈ s.1.1.vertices → ¬ retargetInnerLeft imageOf s v →
    isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
      ((imageOf s).quotientForest.retargetVertex
        (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
        (rightVertexDomain (imageOf s) v))

/-- **R-6c-body-43 — body-41's coordinate bridge from the witness supply.**  `right_index` is the
`mem_starVertices` recovery of `right_quotientStar`. -/
def ResolvedRetargetCoordinateWitnessSupply.toCoordinateBridgeSupply
    (W : ResolvedRetargetCoordinateWitnessSupply D G imageOf) :
    ResolvedRetargetCoordinateBridgeSupply D G imageOf where
  survival := W.survival
  freshA := W.freshA
  freshB := W.freshB
  right_index := by
    intro s v hin hnleft
    exact right_index_of_quotientStar s (W.right_quotientStar s hin hnleft)

end GaugeGeometry.QFT.Combinatorial
