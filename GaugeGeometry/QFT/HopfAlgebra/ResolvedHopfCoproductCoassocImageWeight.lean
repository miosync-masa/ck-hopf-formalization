import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientTerm
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientBody

/-!
# R-6c-heart-3b — the easy image-side fields (innerRightTerm, discriminatorOf, imageWeightOf)

With `quotientForestOf` reduced to the full-grain σ-cover (heart-3), the remaining image-side fields
other than the selected-outer/promote body are light:

* **`innerRightTerm`** (the inner quotient-of-quotient gen, heart-1's only strict-summand supply) is
  the generator of the quotient subforest contracted in the quotient graph — `resolvedForestRightTerm
  z.quotientForest (D.starOf (quotientGraph z) z.quotientForest) (innerCD z)`.  The star is `D.starOf`
  on the quotient graph (available generically); only the doubly-contracted CD `innerCD` is genuine, so
  it reduces to **one supply field**.
* **`discriminatorOf`** is the resolved forest-by-star discriminator unfolded directly on the image —
  fully CONCRETE (a plain existential, no supply, no divergence-preservation instances).
* **`imageWeightOf`** is then the concrete `resolvedCoassocQuotientTerm` (heart-1) over the strict-summand
  supply, wired into a `ResolvedCoassocImageSideSupply` whose `quotient` comes from the heart-3
  full-grain quotient.

So after this file the ONLY abstract image-side input is the selected-outer/promote body (heart-4).

Landed:

* `resolvedCoassocQuotientGraph` — the quotient graph `selectedOuter.contractWithStars` of an image;
* `ResolvedCoassocInnerRightSupply D G` (+ `.innerRightTerm`, `.toStrictSummandSupply`) — `innerRightTerm`
  reduced to the single `innerCD` field;
* `resolvedCoassocDiscriminator` — the concrete forest-by-star discriminator on an image;
* `ResolvedCoassocInnerRightSupply.toImageSideSupply` — assembles a `ResolvedCoassocImageSideSupply` with
  concrete `imageWeightOf` (= `resolvedCoassocQuotientTerm`) and `discriminatorOf`, the heart-3 quotient,
  and a supplied selected-outer.

No facade, no flat term, no `forgetHopf`; the selected-outer/promote body and the `innerCD` proof are the
remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-3b — the quotient graph of an image.**  `selectedOuter.contractWithStars` — the graph
the quotient forest lives over (`z.quotientForest : ResolvedAdmissibleSubgraph (quotientGraph z)`). -/
noncomputable def resolvedCoassocQuotientGraph (z : ResolvedCoassocQuotientImage D G) :
    ResolvedFeynmanGraph :=
  z.selectedOuter.1.contractWithStars (D.starOf G z.selectedOuter.1)

/-- **R-6c-heart-3b — the inner-right supply.**  The genuine remaining datum for the strict summand's
inner factor: the connected-divergence of the quotient subforest doubly contracted (in the quotient
graph).  The star is `D.starOf` on the quotient graph (generic); only this CD is supplied. -/
structure ResolvedCoassocInnerRightSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) where
  /-- The doubly-contracted CD: the quotient subforest contracted in the quotient graph is
  connected-divergent (so its generator exists). -/
  innerCD : ∀ z : ResolvedCoassocQuotientImage D G,
    (z.quotientForest.contractWithStars
        (D.starOf (resolvedCoassocQuotientGraph z) z.quotientForest)).forget.toClass.IsConnectedDivergent

/-- **R-6c-heart-3b — the inner-right term.**  The generator of the quotient subforest contracted in the
quotient graph (the strict summand's inner-right factor) via `resolvedForestRightTerm`. -/
noncomputable def ResolvedCoassocInnerRightSupply.innerRightTerm
    (R : ResolvedCoassocInnerRightSupply D G) (z : ResolvedCoassocQuotientImage D G) : ResolvedHopfH :=
  resolvedForestRightTerm z.quotientForest
    (D.starOf (resolvedCoassocQuotientGraph z) z.quotientForest) (R.innerCD z)

/-- The heart-1 strict-summand supply from the inner-right supply. -/
noncomputable def ResolvedCoassocInnerRightSupply.toStrictSummandSupply
    (R : ResolvedCoassocInnerRightSupply D G) : ResolvedQuotientStrictSummandSupply D G where
  innerRightTerm := R.innerRightTerm

/-- **R-6c-heart-3b — the concrete forest-by-star discriminator.**  `resolvedIsForestByStar` unfolded
directly on an image: some quotient-forest component touches a selected-outer star.  Fully concrete (no
supply, no divergence-preservation instances). -/
def resolvedCoassocDiscriminator (z : ResolvedCoassocQuotientImage D G) : Prop :=
  ∃ δ ∈ z.quotientForest.elements,
    ¬ Disjoint δ.vertices (z.selectedOuter.1.starVertices (D.starOf G z.selectedOuter.1))

/-- **R-6c-heart-3b — image side with concrete `imageWeightOf` and `discriminatorOf`.**  Assembles a
`ResolvedCoassocImageSideSupply` whose image weight is the concrete `resolvedCoassocQuotientTerm` (heart-1)
and whose discriminator is the concrete forest-by-star, with the heart-3 full-grain quotient and a
supplied selected-outer.  Only the selected-outer/promote body remains abstract. -/
noncomputable def ResolvedCoassocInnerRightSupply.toImageSideSupply
    (R : ResolvedCoassocInnerRightSupply D G)
    (selected : ResolvedCoassocSelectedOuterImageSupply D G)
    (Sig : ResolvedCoassocSigmaDataSupply D G selected)
    (Full : ResolvedCoassocFullQuotientSupply D G selected Sig) :
    ResolvedCoassocImageSideSupply D G where
  selected := selected
  quotient := Full.toQuotientForestSupply
  imageWeightOf := R.toStrictSummandSupply.resolvedCoassocQuotientTerm
  discriminatorOf := resolvedCoassocDiscriminator

end GaugeGeometry.QFT.Combinatorial
