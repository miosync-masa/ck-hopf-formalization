import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientStarCodomain

/-!
# R-6c-heart-6a-10c-2 — the right sector equivalence (right-primitive ↔ right-survivor)

The right half of the BIGGEST: `RightPrimitiveIndex ≃ {δ ∈ rightElements}` — a right-primitive component of
the input outer forest maps to its right-survivor component in the quotient graph (5b-2 `survivorComponent`
/ 6a-3a `rightSurvivorComponentOf`), and back.

This file isolates the right sector as its own supply (`rightToComponent` / `componentToRight` + inverse
laws) and packages it as the `Equiv` that 6a-10c-1's `ResolvedQuotientStarSectorEquivSupply.rightEquiv`
wants — so the right and forest sectors can be attacked independently.

Per the HALT, `rightToComponent` / `componentToRight` are NOT constructed (supply fields), no
`survivorComponent` equality / injectivity, forest/remnant sector untouched.

Landed:

* `ResolvedRightSectorEquivSupply C` — the right sector maps + inverse laws;
* `.rightEquiv` — the assembled right sector `Equiv` (per split choice).

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

/-- **R-6c-heart-6a-10c-2 — the right sector equivalence supply.**  The right-primitive ↔ right-survivor
maps and their inverse laws. -/
structure ResolvedRightSectorEquivSupply
    (C : ResolvedQuotientStarCodomainFullQuotientSupply D G imageOf) where
  /-- A right-primitive component maps to its quotient right-survivor element. -/
  rightToComponent : ∀ s : ResolvedCoassocSplitChoice D G,
    RightPrimitiveIndex D G s → {δ // δ ∈ C.rightElements s}
  /-- ... and back. -/
  componentToRight : ∀ s : ResolvedCoassocSplitChoice D G,
    {δ // δ ∈ C.rightElements s} → RightPrimitiveIndex D G s
  /-- Left inverse. -/
  left_inv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.LeftInverse (componentToRight s) (rightToComponent s)
  /-- Right inverse. -/
  right_inv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.RightInverse (componentToRight s) (rightToComponent s)

/-- **R-6c-heart-6a-10c-2 — the right sector `Equiv`. -/
def ResolvedRightSectorEquivSupply.rightEquiv
    {C : ResolvedQuotientStarCodomainFullQuotientSupply D G imageOf}
    (R : ResolvedRightSectorEquivSupply C) (s : ResolvedCoassocSplitChoice D G) :
    RightPrimitiveIndex D G s ≃ {δ // δ ∈ C.rightElements s} where
  toFun := R.rightToComponent s
  invFun := R.componentToRight s
  left_inv := R.left_inv s
  right_inv := R.right_inv s

end GaugeGeometry.QFT.Combinatorial
