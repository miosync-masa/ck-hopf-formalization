import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightCheapGeometry

/-!
# R-6c-heart-6a-7a — RIGHT freshness from one canonical fresh-star property

`ResolvedRightStarFreshSupply` (6a-6b) asks for two freshness facts — `freshA` (input outer `s.1.1`'s
stars outside `G`) and `freshB` (quotient forest's stars outside the quotient graph).  Scout result: `D`
carries no freshness field, and the existing `ResolvedCoassocSigmaDataSupply.starFreshOf` is only about
`selectedOuter` (per split choice), so neither `freshA` nor `freshB` reads off it directly.

But both `freshA` and `freshB` are instances of the SAME canonical property: **`D.starOf G' A` sends each
component of `A` to a vertex outside `G'`**, for the relevant `(G', A)` pairs (`(G, s.1.1)` and
`(quotient graph, quotientForest)`).  So this file isolates that single universal property
`ResolvedCanonicalStarFreshSupply D` and derives the whole `ResolvedRightStarFreshSupply` from it — one
canonical freshness source, two holes closed.

Per the HALT, the canonical freshness itself is NOT proved (it is the one supply field — a property a
canonical star assignment has but `D` does not record); no `starToStar` / `surviving` / `edge` / `retarget`.

Landed:

* `ResolvedCanonicalStarFreshSupply D` — the one universal fresh-star property of `D`;
* `.toRightStarFreshSupply imageOf` — derive `ResolvedRightStarFreshSupply` (both `freshA` / `freshB` as
  instances).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

/-- **R-6c-heart-6a-7a — the canonical fresh-star property of `D`.**  For every graph and admissible
forest, `D.starOf` sends each component to a vertex outside the graph — the freshness a canonical star
assignment enjoys (but `ResolvedCoproductProperForestData` does not record). -/
structure ResolvedCanonicalStarFreshSupply (D : ResolvedCoproductProperForestData) where
  /-- `D.starOf G' A η` is fresh (outside `G'`) for each component `η` of `A`. -/
  starOf_fresh : ∀ (G' : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G')
    (η : ResolvedFeynmanSubgraph G'), η ∈ A.elements → D.starOf G' A η ∉ G'.vertices

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-7a — the right freshness supply from the canonical property.**  Both `freshA` and
`freshB` are instances of `starOf_fresh` at `(G, s.1.1)` and `(quotient graph, quotientForest)`. -/
def ResolvedCanonicalStarFreshSupply.toRightStarFreshSupply
    (F : ResolvedCanonicalStarFreshSupply D)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) :
    ResolvedRightStarFreshSupply D G imageOf where
  freshA := fun s η hη => F.starOf_fresh G s.1.1 η hη
  freshB := fun s η hη =>
    F.starOf_fresh (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest η hη

end GaugeGeometry.QFT.Combinatorial
