import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightStarIndex
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightStarBijection

/-!
# R-6c-heart-6a-8b-1 — `starToStar` from index equivalences (subtype mud cleared)

Before constructing the index bijection `OneStageStarIndex ≃ TwoStageStarIndex`, this proves that — given
it, plus the two star-subtype ↔ index equivalences (recovery + no-collision of the star assignment) — the
whole `ResolvedRightStarBijectionSupply` follows, with the inverse laws FREE (composition of `Equiv`s).

So the BIGGEST shrinks to: the two star-subtype recoveries (`oneStarEquiv` / `twoStarEquiv` — each is
"`toStarVertex` is a bijection", i.e. recovery + distinct components have distinct stars) plus the genuine
`indexEquiv` (the `componentPartition` / `Right ⊔ Remnant` correspondence).  The bare-subtype bookkeeping
and the inverse-law proofs are discharged here once and for all.

Per the HALT, NO `indexEquiv` construction, NO recovery construction, NO `componentPartition` /
`Right ⊔ Remnant`.

Landed:

* `ResolvedRightStarIndexBijectionSupply D G imageOf` — `oneStarEquiv` / `twoStarEquiv` / `indexEquiv`;
* `.starEquiv s` — the composed star-vertex subtype equivalence;
* `.toStarBijectionSupply` — `ResolvedRightStarBijectionSupply`, inverse laws from the `Equiv`.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-8b-1 — the star index-bijection supply.**  The two star-vertex subtype ↔ index
equivalences (recovery + no-collision) and the genuine index equivalence. -/
structure ResolvedRightStarIndexBijectionSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- One-stage star vertices ≃ one-stage star indices (recovery + no-collision). -/
  oneStarEquiv : ∀ s : ResolvedCoassocSplitChoice D G,
    {v : VertexId // isContractStarVertex s.1.1 (D.starOf G s.1.1) v} ≃ OneStageStarIndex D G s
  /-- Two-stage star vertices ≃ two-stage star indices (recovery + no-collision). -/
  twoStarEquiv : ∀ s : ResolvedCoassocSplitChoice D G,
    {w : VertexId // isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) w}
      ≃ TwoStageStarIndex D G imageOf s
  /-- The genuine index equivalence (`componentPartition` / `Right ⊔ Remnant` correspondence). -/
  indexEquiv : ∀ s : ResolvedCoassocSplitChoice D G,
    OneStageStarIndex D G s ≃ TwoStageStarIndex D G imageOf s

/-- **R-6c-heart-6a-8b-1 — the composed star-vertex subtype equivalence.**  One-stage star vertex →
recover index → cross via `indexEquiv` → re-encode as two-stage star vertex. -/
def ResolvedRightStarIndexBijectionSupply.starEquiv
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (B : ResolvedRightStarIndexBijectionSupply D G imageOf) (s : ResolvedCoassocSplitChoice D G) :
    {v : VertexId // isContractStarVertex s.1.1 (D.starOf G s.1.1) v} ≃
      {w : VertexId // isContractStarVertex (imageOf s).quotientForest
        (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) w} :=
  (B.oneStarEquiv s).trans ((B.indexEquiv s).trans (B.twoStarEquiv s).symm)

/-- **R-6c-heart-6a-8b-1 — the star bijection supply from the index equivalences.**  Inverse laws are the
composed `Equiv`'s. -/
def ResolvedRightStarIndexBijectionSupply.toStarBijectionSupply
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (B : ResolvedRightStarIndexBijectionSupply D G imageOf) :
    ResolvedRightStarBijectionSupply D G imageOf where
  starToStar := fun s => B.starEquiv s
  starFromStar := fun s => (B.starEquiv s).symm
  star_left_inv := fun s => (B.starEquiv s).left_inv
  star_right_inv := fun s => (B.starEquiv s).right_inv

end GaugeGeometry.QFT.Combinatorial
