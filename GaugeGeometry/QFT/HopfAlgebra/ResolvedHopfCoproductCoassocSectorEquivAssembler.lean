import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestSectorConcrete
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorForwardConcrete

/-!
# R-6c-heart-6a-10g-1 — sector backward maps + the full sector-equiv assembler

The quotient-star forward maps are concrete (6a-10f-4: the actual `survivorComponent` / `remnantComponent`).
This file adds the backward maps and inverse laws (as supply fields), and assembles the whole
`ResolvedThreeRouteQuotientStarSupply` — closing the BIGGEST down to:

* `Forward` — the concrete forward maps (6a-10f, reducible to `hne` / `hcompl` / remnant supply + alignment +
  membership);
* `Backward` — `componentToRight` / `componentToForest` (recover the input-outer sector index from a
  quotient survivor / remnant component);
* the four inverse laws.

Per the HALT, the backward maps and inverse laws are supply fields (not constructed / proved); no
membership / alignment proofs.

Landed:

* `ResolvedSectorBackwardSupply C` — the two backward maps;
* `ResolvedSectorEquivAssemblerSupply C` — `Forward` + `Backward` + the four inverse laws;
* `.toRightSectorConcreteSupply` / `.toForestSectorConcreteSupply` / `.toConcreteSectorEquivSupply` /
  `.toQuotientStarSupply` — through to `ResolvedThreeRouteQuotientStarSupply`.

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

/-- **R-6c-heart-6a-10g-1 — the sector backward maps. -/
structure ResolvedSectorBackwardSupply
    (C : ResolvedCodomainConcreteSupply D G imageOf) where
  /-- A quotient right-survivor component ↦ its input-outer right-primitive. -/
  componentToRight : ∀ s : ResolvedCoassocSplitChoice D G,
    {δ // δ ∈ (C.rightForest s).elements} → RightPrimitiveIndex D G s
  /-- A quotient remnant component ↦ its input-outer forest-choice. -/
  componentToForest : ∀ s : ResolvedCoassocSplitChoice D G,
    {δ // δ ∈ (C.remnantForest s).elements} → ForestPrimitiveIndex D G s

/-- **R-6c-heart-6a-10g-1 — the full sector-equiv assembler supply. -/
structure ResolvedSectorEquivAssemblerSupply
    (C : ResolvedCodomainConcreteSupply D G imageOf) where
  /-- The concrete forward maps (6a-10f). -/
  Forward : ResolvedSectorForwardConcreteSupply C
  /-- The backward maps. -/
  Backward : ResolvedSectorBackwardSupply C
  /-- Right sector left inverse. -/
  right_left_inv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.LeftInverse (Backward.componentToRight s) (Forward.rightToComponent s)
  /-- Right sector right inverse. -/
  right_right_inv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.RightInverse (Backward.componentToRight s) (Forward.rightToComponent s)
  /-- Forest sector left inverse. -/
  forest_left_inv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.LeftInverse (Backward.componentToForest s) (Forward.forestToComponent s)
  /-- Forest sector right inverse. -/
  forest_right_inv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.RightInverse (Backward.componentToForest s) (Forward.forestToComponent s)

/-- **R-6c-heart-6a-10g-1 — into 6a-10e-1's right sector concrete supply. -/
def ResolvedSectorEquivAssemblerSupply.toRightSectorConcreteSupply
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    (A : ResolvedSectorEquivAssemblerSupply C) : ResolvedRightSectorConcreteSupply C where
  rightToComponent := A.Forward.rightToComponent
  componentToRight := A.Backward.componentToRight
  left_inv := A.right_left_inv
  right_inv := A.right_right_inv

/-- **R-6c-heart-6a-10g-1 — into 6a-10e-2's forest sector concrete supply. -/
def ResolvedSectorEquivAssemblerSupply.toForestSectorConcreteSupply
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    (A : ResolvedSectorEquivAssemblerSupply C) : ResolvedForestSectorConcreteSupply C where
  forestToComponent := A.Forward.forestToComponent
  componentToForest := A.Backward.componentToForest
  left_inv := A.forest_left_inv
  right_inv := A.forest_right_inv

/-- **R-6c-heart-6a-10g-1 — into 6a-10e-2's combined sector supply. -/
def ResolvedSectorEquivAssemblerSupply.toConcreteSectorEquivSupply
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    (A : ResolvedSectorEquivAssemblerSupply C) : ResolvedConcreteSectorEquivSupply C where
  Right := A.toRightSectorConcreteSupply
  Forest := A.toForestSectorConcreteSupply

/-- **R-6c-heart-6a-10g-1 — through to the quotient-star supply. -/
noncomputable def ResolvedSectorEquivAssemblerSupply.toQuotientStarSupply
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    (A : ResolvedSectorEquivAssemblerSupply C) :
    ResolvedThreeRouteQuotientStarSupply D G imageOf :=
  A.toConcreteSectorEquivSupply.toQuotientStarSupply

end GaugeGeometry.QFT.Combinatorial
