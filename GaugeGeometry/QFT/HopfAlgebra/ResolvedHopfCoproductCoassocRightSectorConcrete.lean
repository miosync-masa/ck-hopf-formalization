import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightSectorEquiv
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCodomainConcrete

/-!
# R-6c-heart-6a-10e-1 — right sector maps against the concrete right-survivor forest

The right sector equivalence (6a-10c-2) is here re-expressed against the **actual** right-survivor forest
(6a-10d `rightForest`): `RightPrimitiveIndex ≃ {δ ∈ rightForest.elements}`.  Since the 6a-10d codomain
supply sets `rightElements := rightForest.elements`, a right sector map supply over the concrete forest
feeds 6a-10c-2's `ResolvedRightSectorEquivSupply` by definitional equality — connecting the domain
right-primitives to the quotient right-survivor components (5b-2 `survivorComponent` / 6a-3a
`rightSurvivorComponentOf`), ready for the concrete forward map.

Per the HALT, `rightToComponent` / `componentToRight` and the inverse laws are supply fields (the concrete
`survivorComponent` construction is the next step); forest/remnant sector untouched.

Landed:

* `ResolvedRightSectorConcreteSupply C` — the right sector maps + inverse laws over `C.rightForest`;
* `.toRightSectorEquivSupply` — into 6a-10c-2's supply (over `C.toCodomainFullQuotientSupply`).

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

/-- **R-6c-heart-6a-10e-1 — the right sector maps over the concrete right-survivor forest.** -/
structure ResolvedRightSectorConcreteSupply
    (C : ResolvedCodomainConcreteSupply D G imageOf) where
  /-- A right-primitive component ↦ its right-survivor component in the quotient forest. -/
  rightToComponent : ∀ s : ResolvedCoassocSplitChoice D G,
    RightPrimitiveIndex D G s → {δ // δ ∈ (C.rightForest s).elements}
  /-- ... and back. -/
  componentToRight : ∀ s : ResolvedCoassocSplitChoice D G,
    {δ // δ ∈ (C.rightForest s).elements} → RightPrimitiveIndex D G s
  /-- Left inverse. -/
  left_inv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.LeftInverse (componentToRight s) (rightToComponent s)
  /-- Right inverse. -/
  right_inv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.RightInverse (componentToRight s) (rightToComponent s)

/-- **R-6c-heart-6a-10e-1 — into 6a-10c-2's right sector equivalence supply.** -/
def ResolvedRightSectorConcreteSupply.toRightSectorEquivSupply
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    (M : ResolvedRightSectorConcreteSupply C) :
    ResolvedRightSectorEquivSupply C.toCodomainFullQuotientSupply where
  rightToComponent := M.rightToComponent
  componentToRight := M.componentToRight
  left_inv := M.left_inv
  right_inv := M.right_inv

end GaugeGeometry.QFT.Combinatorial
