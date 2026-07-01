import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientStarCodomain

/-!
# R-6c-heart-6a-10d — codomain elements/disjoint from the concrete `Right ⊔ Remnant` forests

The 6a-10b codomain supply asks for `rightElements` / `remnantElements` (Finsets) with
`quotientForest.elements = right ∪ remnant` and disjointness.  This file expresses those element sets as the
`.elements` of the actual right-survivor / remnant admissible forests in the quotient graph (5b-2 / 5b-3,
assembled into `quotientForest = Right ⊔ Remnant` by 5b-4 `fullQuotientOf`), so the codomain data reduces to
the two genuine, light connectors:

* `quotientForest_elements_eq` — the quotient forest's components are exactly the right ⊔ remnant
  components (`fullQuotientOf.toImage`);
* `forests_disjoint` — right-survivors and remnants are disjoint (5b-4 cross-disjointness).

Per the HALT, `rightEquiv` / `forestEquiv` maps are NOT built, no survivor/remnant equality; the two
connectors are named supply fields (the genuine `Right ⊔ Remnant` facts).

Landed:

* `ResolvedCodomainConcreteSupply D G imageOf` — the right/remnant forests + the two connectors;
* `.toCodomainFullQuotientSupply` — the 6a-10b codomain supply.

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

/-- **R-6c-heart-6a-10d — the concrete codomain supply.**  The right-survivor / remnant admissible forests
in the quotient graph, with the `Right ⊔ Remnant` union and disjointness connectors. -/
structure ResolvedCodomainConcreteSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- The right-survivor forest in the quotient graph (5b-2). -/
  rightForest : ∀ s : ResolvedCoassocSplitChoice D G,
    ResolvedAdmissibleSubgraph (resolvedCoassocQuotientGraph (imageOf s))
  /-- The remnant forest in the quotient graph (5b-3). -/
  remnantForest : ∀ s : ResolvedCoassocSplitChoice D G,
    ResolvedAdmissibleSubgraph (resolvedCoassocQuotientGraph (imageOf s))
  /-- The quotient forest is `Right ⊔ Remnant` (5b-4 `fullQuotientOf.toImage`). -/
  quotientForest_elements_eq : ∀ s : ResolvedCoassocSplitChoice D G,
    (imageOf s).quotientForest.elements = (rightForest s).elements ∪ (remnantForest s).elements
  /-- Right-survivors and remnants are disjoint. -/
  forests_disjoint : ∀ s : ResolvedCoassocSplitChoice D G,
    Disjoint (rightForest s).elements (remnantForest s).elements

/-- **R-6c-heart-6a-10d — into the 6a-10b codomain supply. -/
def ResolvedCodomainConcreteSupply.toCodomainFullQuotientSupply
    (Co : ResolvedCodomainConcreteSupply D G imageOf) :
    ResolvedQuotientStarCodomainFullQuotientSupply D G imageOf where
  rightElements := fun s => (Co.rightForest s).elements
  remnantElements := fun s => (Co.remnantForest s).elements
  elements_eq := Co.quotientForest_elements_eq
  disjoint := Co.forests_disjoint

end GaugeGeometry.QFT.Combinatorial
