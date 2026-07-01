import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestSectorEquiv
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightSectorConcrete

/-!
# R-6c-heart-6a-10e-2 — forest sector maps + the full concrete sector → `QuotientStarSupply`

Mirror of 6a-10e-1 for the forest sector: `ForestPrimitiveIndex ≃ {δ ∈ remnantForest.elements}` (a
forest-choice occurrence ↦ its remnant component in the quotient forest, 5b-3 / 6a-5c-4c
`remnantComponent`).  Combined with the right sector (6a-10e-1), the concrete sector supply produces the
whole `ResolvedThreeRouteQuotientStarSupply` — closing the BIGGEST down to the two per-sector forward maps
(`survivorComponent` / `remnantComponent`) plus their inverse laws.

Per the HALT, `forestToComponent` / `componentToForest` and the inverse laws are supply fields; no remnant
component equality / injectivity; the concrete `survivorComponent` / `remnantComponent` forward maps are
the next step.

Landed:

* `ResolvedForestSectorConcreteSupply C` — the forest sector maps + inverse laws over `C.remnantForest`;
* `.toForestSectorEquivSupply` — into 6a-10c-3's forest sector supply;
* `ResolvedConcreteSectorEquivSupply C` — `Right` + `Forest`;
* `.toSectorEquivSupply` / `.toQuotientStarSupply` — through to the `ResolvedThreeRouteQuotientStarSupply`.

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

/-- **R-6c-heart-6a-10e-2 — the forest sector maps over the concrete remnant forest.** -/
structure ResolvedForestSectorConcreteSupply
    (C : ResolvedCodomainConcreteSupply D G imageOf) where
  /-- A forest-choice occurrence ↦ its remnant component in the quotient forest. -/
  forestToComponent : ∀ s : ResolvedCoassocSplitChoice D G,
    ForestPrimitiveIndex D G s → {δ // δ ∈ (C.remnantForest s).elements}
  /-- ... and back. -/
  componentToForest : ∀ s : ResolvedCoassocSplitChoice D G,
    {δ // δ ∈ (C.remnantForest s).elements} → ForestPrimitiveIndex D G s
  /-- Left inverse. -/
  left_inv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.LeftInverse (componentToForest s) (forestToComponent s)
  /-- Right inverse. -/
  right_inv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.RightInverse (componentToForest s) (forestToComponent s)

/-- **R-6c-heart-6a-10e-2 — into 6a-10c-3's forest sector equivalence supply.** -/
def ResolvedForestSectorConcreteSupply.toForestSectorEquivSupply
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    (M : ResolvedForestSectorConcreteSupply C) :
    ResolvedForestSectorEquivSupply C.toCodomainFullQuotientSupply where
  forestToComponent := M.forestToComponent
  componentToForest := M.componentToForest
  left_inv := M.left_inv
  right_inv := M.right_inv

/-- **R-6c-heart-6a-10e-2 — the full concrete sector supply. -/
structure ResolvedConcreteSectorEquivSupply
    (C : ResolvedCodomainConcreteSupply D G imageOf) where
  /-- The right sector (6a-10e-1). -/
  Right : ResolvedRightSectorConcreteSupply C
  /-- The forest sector (6a-10e-2). -/
  Forest : ResolvedForestSectorConcreteSupply C

/-- **R-6c-heart-6a-10e-2 — into 6a-10c-3's sector equivalence supply. -/
def ResolvedConcreteSectorEquivSupply.toSectorEquivSupply
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    (S : ResolvedConcreteSectorEquivSupply C) :
    ResolvedSectorEquivSupply C.toCodomainFullQuotientSupply where
  Right := S.Right.toRightSectorEquivSupply
  Forest := S.Forest.toForestSectorEquivSupply

/-- **R-6c-heart-6a-10e-2 — through to the quotient-star supply. -/
noncomputable def ResolvedConcreteSectorEquivSupply.toQuotientStarSupply
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    (S : ResolvedConcreteSectorEquivSupply C) :
    ResolvedThreeRouteQuotientStarSupply D G imageOf :=
  S.toSectorEquivSupply.toQuotientStarSectorEquivSupply.toQuotientStarSupply

end GaugeGeometry.QFT.Combinatorial
