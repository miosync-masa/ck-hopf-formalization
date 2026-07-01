import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightSectorEquiv
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientStarSector

/-!
# R-6c-heart-6a-10c-3 — the forest sector equivalence + the sector assembler

The forest half of the BIGGEST: `ForestPrimitiveIndex ≃ {δ ∈ remnantElements}` — a forest-choice occurrence
of the input outer forest maps to its remnant component in the quotient graph (5b-3 remnant / 6a-5c-4c
`remnantComponent`), and back.  Mirror of the right sector (6a-10c-2).

A small assembler then combines the right and forest sectors into 6a-10c-1's
`ResolvedQuotientStarSectorEquivSupply`, so `right sector + forest sector → QuotientStarSupply`.

Per the HALT, `forestToComponent` / `componentToForest` are NOT constructed (supply fields), no remnant
component equality / injectivity, right sector concrete untouched.

Landed:

* `ResolvedForestSectorEquivSupply C` — the forest sector maps + inverse laws;
* `.forestEquiv` — the forest sector `Equiv`;
* `ResolvedSectorEquivSupply C` — `Right` + `Forest`;
* `.toQuotientStarSectorEquivSupply` — the assembled 6a-10c-1 sector-equiv supply.

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

/-- **R-6c-heart-6a-10c-3 — the forest sector equivalence supply.**  The forest-choice ↔ remnant maps and
their inverse laws. -/
structure ResolvedForestSectorEquivSupply
    (C : ResolvedQuotientStarCodomainFullQuotientSupply D G imageOf) where
  /-- A forest-choice component maps to its quotient remnant element. -/
  forestToComponent : ∀ s : ResolvedCoassocSplitChoice D G,
    ForestPrimitiveIndex D G s → {δ // δ ∈ C.remnantElements s}
  /-- ... and back. -/
  componentToForest : ∀ s : ResolvedCoassocSplitChoice D G,
    {δ // δ ∈ C.remnantElements s} → ForestPrimitiveIndex D G s
  /-- Left inverse. -/
  left_inv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.LeftInverse (componentToForest s) (forestToComponent s)
  /-- Right inverse. -/
  right_inv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.RightInverse (componentToForest s) (forestToComponent s)

/-- **R-6c-heart-6a-10c-3 — the forest sector `Equiv`. -/
def ResolvedForestSectorEquivSupply.forestEquiv
    {C : ResolvedQuotientStarCodomainFullQuotientSupply D G imageOf}
    (F : ResolvedForestSectorEquivSupply C) (s : ResolvedCoassocSplitChoice D G) :
    ForestPrimitiveIndex D G s ≃ {δ // δ ∈ C.remnantElements s} where
  toFun := F.forestToComponent s
  invFun := F.componentToForest s
  left_inv := F.left_inv s
  right_inv := F.right_inv s

/-- **R-6c-heart-6a-10c-3 — the combined sector supply. -/
structure ResolvedSectorEquivSupply
    (C : ResolvedQuotientStarCodomainFullQuotientSupply D G imageOf) where
  /-- The right sector (6a-10c-2). -/
  Right : ResolvedRightSectorEquivSupply C
  /-- The forest sector (6a-10c-3). -/
  Forest : ResolvedForestSectorEquivSupply C

/-- **R-6c-heart-6a-10c-3 — into the 6a-10c-1 sector-equiv supply. -/
def ResolvedSectorEquivSupply.toQuotientStarSectorEquivSupply
    {C : ResolvedQuotientStarCodomainFullQuotientSupply D G imageOf}
    (S : ResolvedSectorEquivSupply C) : ResolvedQuotientStarSectorEquivSupply C where
  rightEquiv := fun s => S.Right.rightEquiv s
  forestEquiv := fun s => S.Forest.forestEquiv s

end GaugeGeometry.QFT.Combinatorial
