import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightSurviving

/-!
# R-6c-heart-6a-6d-2 — RIGHT star bijection supply + the `StarMapSupply` combiner

The star half of `ResolvedContractStarMapSupply` — the bijection between the one-stage star vertices (input
outer `s.1.1`'s component stars) and the two-stage star vertices (the quotient forest's component stars) —
is isolated here as `ResolvedRightStarBijectionSupply`, together with the combiner that assembles the full
per-split-choice `ResolvedContractStarMapSupply` from the three named halves:

  **`ResolvedContractStarMapSupply` = star bijection (6a-6d-2) + surviving transport (6a-6d-1) + freshness
  (6a-6b).**

So the BIGGEST genuine piece is now precisely the concrete construction of `ResolvedRightStarBijectionSupply`
(from 5b-1 `componentPartition` + 5b-4 `Right ⊔ Remnant`) — everything else around it is wired.

Per the HALT, no concrete `starToStar` from `componentPartition`, no inverse-law proof, no perm
extension / `retargetVertex_eq`.

Landed:

* `ResolvedRightStarBijectionSupply D G imageOf` — `starToStar` / `starFromStar` + inverse laws per split
  choice, in `ResolvedContractStarMapSupply` shape;
* `.toStarMapSupply Surv Fresh s` — the combiner producing the full per-`s`
  `ResolvedContractStarMapSupply`.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-6d-2 — the right star-bijection supply (star half).**  The one-stage star vertices
(input outer `s.1.1`'s component stars) ↔ the two-stage star vertices (the quotient forest's component
stars), with the inverse laws.  The genuine combinatorial content (from `componentPartition` /
`Right ⊔ Remnant`) is kept as these fields. -/
structure ResolvedRightStarBijectionSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- One-stage star ↦ two-stage star. -/
  starToStar : ∀ s : ResolvedCoassocSplitChoice D G,
    {v : VertexId // isContractStarVertex s.1.1 (D.starOf G s.1.1) v} →
    {w : VertexId // isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) w}
  /-- Two-stage star ↦ one-stage star. -/
  starFromStar : ∀ s : ResolvedCoassocSplitChoice D G,
    {w : VertexId // isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) w} →
    {v : VertexId // isContractStarVertex s.1.1 (D.starOf G s.1.1) v}
  /-- The star map's left inverse law. -/
  star_left_inv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.LeftInverse (starFromStar s) (starToStar s)
  /-- The star map's right inverse law. -/
  star_right_inv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.RightInverse (starFromStar s) (starToStar s)

/-- **R-6c-heart-6a-6d-2 — the combiner.**  Assembles the full per-split-choice
`ResolvedContractStarMapSupply` from the star bijection (this supply), the surviving transport (6a-6d-1),
and the freshness (6a-6b). -/
noncomputable def ResolvedRightStarBijectionSupply.toStarMapSupply
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (Star : ResolvedRightStarBijectionSupply D G imageOf)
    (Surv : ResolvedRightSurvivingSupply D G imageOf)
    (Fresh : ResolvedRightStarFreshSupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) :
    ResolvedContractStarMapSupply s.1.1 (D.starOf G s.1.1) (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) where
  freshA := Fresh.freshA s
  freshB := Fresh.freshB s
  surviving_to := Surv.surviving_to s
  surviving_from := Surv.surviving_from s
  starToStar := Star.starToStar s
  starFromStar := Star.starFromStar s
  star_left_inv := Star.star_left_inv s
  star_right_inv := Star.star_right_inv s

end GaugeGeometry.QFT.Combinatorial
