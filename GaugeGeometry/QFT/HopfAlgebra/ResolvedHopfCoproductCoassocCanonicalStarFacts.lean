import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteFreshConcrete

/-!
# R-6c-leaf-1 — canonical star facts (the RIGHT Mechanical group from ONE record)

First leaf-discharge step.  The RIGHT factor's `Mechanical` group (6a-9b) needs exactly two kinds of
canonical-star fact, both universal over `(G', A)`:

* `starOf_fresh` — the allocated star `D.starOf G' A η` lies outside `G'.vertices` (feeds `ResolvedCanonicalStarFreshSupply`, 6a-7a → `freshA`/`freshB`);
* `starOf_injective` — distinct components of `A` get distinct stars (feeds `ResolvedStarIndexRecoverSupply`, 6a-8b-2 → the two `oneRecover`/`twoRecover` → all recoveries).

Both are instances of the *same* canonical star-allocation properties at `(G, s.1.1)` and at
`(quotient graph, quotientForest)`.  Collecting them into ONE record `ResolvedCanonicalStarFacts D` lets the
whole `ResolvedThreeRouteMechanicalSupply` (Recover + canonicalFresh) be produced by a single adapter.

Per the HALT, the canonical star-allocation bodies are NOT proved (the two universal fields); no Transport /
Sector / Product leaves, no representative lift.

Landed:

* `ResolvedCanonicalStarFacts D` — `starOf_fresh` + `starOf_injective` (both `∀ G' A …`);
* `.toFreshSupply : ResolvedCanonicalStarFreshSupply D`;
* `.toRecoverSupply imageOf : ResolvedThreeRouteRecoverSupply D G imageOf`;
* `.toMechanicalSupply imageOf : ResolvedThreeRouteMechanicalSupply D G imageOf`.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-leaf-1 — the canonical star facts.**  The two universal star-allocation properties (freshness +
injectivity), from which the whole RIGHT `Mechanical` group is derived. -/
structure ResolvedCanonicalStarFacts (D : ResolvedCoproductProperForestData) where
  /-- The allocated star `D.starOf G' A η` is fresh (outside `G'`) for each component `η` of `A`. -/
  starOf_fresh : ∀ (G' : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G')
    (η : ResolvedFeynmanSubgraph G'), η ∈ A.elements → D.starOf G' A η ∉ G'.vertices
  /-- Distinct components of `A` get distinct stars. -/
  starOf_injective : ∀ (G' : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G')
    {η δ : ResolvedFeynmanSubgraph G'}, η ∈ A.elements → δ ∈ A.elements →
      D.starOf G' A η = D.starOf G' A δ → η = δ

/-- **R-6c-leaf-1 — the canonical fresh-star supply (6a-7a). -/
def ResolvedCanonicalStarFacts.toFreshSupply (F : ResolvedCanonicalStarFacts D) :
    ResolvedCanonicalStarFreshSupply D where
  starOf_fresh := F.starOf_fresh

/-- **R-6c-leaf-1 — the three-route star recoveries (6a-9a) from the injectivity fact.**  Both stages are
`starOf`-injectivity at `(G, s.1.1)` and at `(quotient graph, quotientForest)`. -/
def ResolvedCanonicalStarFacts.toRecoverSupply (F : ResolvedCanonicalStarFacts D)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) :
    ResolvedThreeRouteRecoverSupply D G imageOf where
  oneRecover := fun s => { star_injective_on_elements := F.starOf_injective G s.1.1 }
  twoRecover := fun s =>
    { star_injective_on_elements :=
        F.starOf_injective (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest }

/-- **R-6c-leaf-1 — the RIGHT `Mechanical` group (6a-9b) from the canonical star facts. -/
def ResolvedCanonicalStarFacts.toMechanicalSupply (F : ResolvedCanonicalStarFacts D)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) :
    ResolvedThreeRouteMechanicalSupply D G imageOf where
  Recover := F.toRecoverSupply imageOf
  canonicalFresh := F.toFreshSupply

/-- **R-6c-body-412 — the raw canonical star facts.**  The exact same two universal star-allocation properties
(freshness + injectivity), but stated over the `rightTerm`-free raw core `R` — the honest carrier of what the
correcting-permutation geometry consumes.  The `D`-facing `ResolvedCanonicalStarFacts` is kept (the 400-chain uses it);
this is the additive raw counterpart. -/
structure ResolvedCanonicalStarRawFacts (R : ResolvedCoproductProperForestRawData) where
  /-- The allocated star `R.starOf G' A η` is fresh (outside `G'`) for each component `η` of `A`. -/
  starOf_fresh : ∀ (G' : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G')
    (η : ResolvedFeynmanSubgraph G'), η ∈ A.elements → R.starOf G' A η ∉ G'.vertices
  /-- Distinct components of `A` get distinct stars. -/
  starOf_injective : ∀ (G' : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G')
    {η δ : ResolvedFeynmanSubgraph G'}, η ∈ A.elements → δ ∈ A.elements →
      R.starOf G' A η = R.starOf G' A δ → η = δ

/-- **R-6c-body-412 — the `D`→raw star-facts adapter** (definitional: `D.toRaw.starOf = D.starOf`). -/
def ResolvedCanonicalStarFacts.toRaw (F : ResolvedCanonicalStarFacts D) :
    ResolvedCanonicalStarRawFacts D.toRaw where
  starOf_fresh := F.starOf_fresh
  starOf_injective := F.starOf_injective

end GaugeGeometry.QFT.Combinatorial
