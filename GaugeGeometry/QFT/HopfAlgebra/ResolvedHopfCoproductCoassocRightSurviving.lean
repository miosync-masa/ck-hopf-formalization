import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightCheapGeometry

/-!
# R-6c-heart-6a-6d-1 — RIGHT surviving transport supply (the non-star half)

Before the genuine `starToStar` bijection (6a-6d, the combinatorial heart), this isolates the
**non-star** half of `ResolvedContractStarMapSupply`: the surviving-vertex transport.

A vertex outside the input outer forest `A := s.1.1` survives both contraction routes — it is outside
`selectedOuter` (so it survives stage 1 into the quotient graph) and outside `quotientForest` (whose
vertices are all `A`-derived: stars + right-survivor / remnant vertices).  The two directions
`surviving_to` / `surviving_from` are exactly the fields `ResolvedContractStarMapSupply` asks for, at the
right instantiation `A = s.1.1`, `B = (imageOf s).quotientForest`.

The actual content (`selectedOuter.vertices ⊆ s.1.1.vertices` and `quotientForest.vertices` is `A`-derived)
runs through the promote / `Right ⊔ Remnant` structure and is genuine, so per the HALT it stays a supply
field — but a NAMED one, independent of the star bijection.

This supplies the non-star half of `ResolvedContractStarMapSupply`; combined later with the star bijection
(6a-6d) and the freshness supply (6a-6b), it assembles the full `ResolvedContractStarMapSupply`.

Per the HALT, `starToStar` / `starFromStar` are NOT built, `retargetVertex_eq` / `edge_domain_eq` are NOT
touched, and the vertex containment is NOT proved (kept as the two supply fields).

Landed:

* `ResolvedRightSurvivingSupply D G imageOf` — `surviving_to` / `surviving_from` per split choice, in
  `ResolvedContractStarMapSupply` shape.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-6d-1 — the right surviving-transport supply (non-star half).**  The two
surviving-vertex transport directions of `ResolvedContractStarMapSupply` for the right factor: a vertex
surviving the one-stage contraction of the input outer `s.1.1` survives the two-stage contraction of the
quotient forest, and conversely.  The vertex containment behind these (genuine, via promote /
`Right ⊔ Remnant`) is kept as the two fields. -/
structure ResolvedRightSurvivingSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- A surviving vertex of the one-stage contraction (`s.1.1`) survives the two-stage (`quotientForest`). -/
  surviving_to : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    isContractSurvivingVertex s.1.1 v → isContractSurvivingVertex (imageOf s).quotientForest v
  /-- A surviving vertex of the two-stage contraction (`quotientForest`) survives the one-stage (`s.1.1`). -/
  surviving_from : ∀ (s : ResolvedCoassocSplitChoice D G) {w : VertexId},
    isContractSurvivingVertex (imageOf s).quotientForest w → isContractSurvivingVertex s.1.1 w

end GaugeGeometry.QFT.Combinatorial
