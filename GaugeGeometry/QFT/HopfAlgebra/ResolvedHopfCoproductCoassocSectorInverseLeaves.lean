import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorLeafBundle

/-!
# R-6c-leaf-24 — Sector inverse laws grouped → `SectorLeafBundle`

Nineteenth leaf-body discharge — grouping the four sector inverse laws.  The leaf-23 `ResolvedSectorLeafBundle`
carries the four `Function.Left/RightInverse` laws inline; leaf-19's `ResolvedSectorInverseLawSupply` already
groups exactly those four (over a `ResolvedSectorForwardConcreteSupply`).  Instantiating that group at
`F.toSectorForwardConcreteSupply` (for the deep forward assembler `F`) recovers the bundle's inline fields, so
the bundle assembles from `Forward + Backward + InverseLawSupply`.

The backward maps (`componentToRight` / `componentToForest`) are abstract supply fields, so the inverse laws
cannot be *proved* here (they were genuinely PROVED in the fix-3c series over the constructed maps); this file
only re-groups them into the bundle shape.

Per the HALT, the backward maps are not constructed and the inverse laws are not re-proved; Perm / Retarget
untouched.

Landed:

* `ResolvedSectorLeafBundle.ofInverseGroup` — the bundle from the deep forward `F` + the grouped inverse laws
  (leaf-19 `ResolvedSectorInverseLawSupply F.toSectorForwardConcreteSupply B`).

So `SectorLeafBundle = Forward + Backward + InverseLawSupply` (grouped) — and hence
`→ toQuotientStarSupply` (leaf-23).

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

/-- **R-6c-leaf-24 — the sector leaf bundle from the deep forward + the grouped inverse laws.**  The four
inline inverse fields are read off the grouped `ResolvedSectorInverseLawSupply` at `F.toSectorForwardConcreteSupply`. -/
def ResolvedSectorLeafBundle.ofInverseGroup
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    (F : ResolvedSectorForwardAssemblerSupply C) (B : ResolvedSectorBackwardSupply C)
    (I : ResolvedSectorInverseLawSupply F.toSectorForwardConcreteSupply B) :
    ResolvedSectorLeafBundle C where
  Forward := F
  Backward := B
  right_left_inv := I.right_left_inv
  right_right_inv := I.right_right_inv
  forest_left_inv := I.forest_left_inv
  forest_right_inv := I.forest_right_inv

end GaugeGeometry.QFT.Combinatorial
