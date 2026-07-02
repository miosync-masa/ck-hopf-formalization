import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorForwardLeaf

/-!
# R-6c-leaf-23 — Sector concrete leaf bundle (→ `QuotientStarSupply`)

Eighteenth leaf-body discharge — the final leaf-bundle form of the sector equivalence, mirroring the Product
and RIGHT leaf bundles.  Collects the deep forward assembler + backward maps + the four inverse laws into ONE
record and flows it all the way to `ResolvedThreeRouteQuotientStarSupply` (the BIGGEST correspondence the RIGHT
grand record consumes).

Builds on leaf-19/19b (the inventory + deep Forward split): here the four inverse laws are carried inline over
`Forward.toSectorForwardConcreteSupply`, and the derived chain
`toSectorEquivAssemblerSupply → toConcreteSectorEquivSupply → toQuotientStarSupply` is exposed.

Per the HALT, no backward-map / inverse-law proofs; Perm / Retarget untouched.

Landed:

* `ResolvedSectorLeafBundle C` — deep `Forward` + `Backward` + the four inverse laws;
* `.toSectorEquivAssemblerSupply` / `.toConcreteSectorEquivSupply` / `.toQuotientStarSupply`.

So the sector is now in the same leaf-bundle shape as Product / RIGHT.

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

/-- **R-6c-leaf-23 — the sector concrete leaf bundle.**  Deep forward assembler + backward maps + the four
inverse laws (over the assembled concrete forward). -/
structure ResolvedSectorLeafBundle (C : ResolvedCodomainConcreteSupply D G imageOf) where
  /-- The deep forward assembler (Local + Align + memberships, 6a-10f-4). -/
  Forward : ResolvedSectorForwardAssemblerSupply C
  /-- The backward maps. -/
  Backward : ResolvedSectorBackwardSupply C
  /-- Right sector left inverse. -/
  right_left_inv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.LeftInverse (Backward.componentToRight s)
      (Forward.toSectorForwardConcreteSupply.rightToComponent s)
  /-- Right sector right inverse. -/
  right_right_inv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.RightInverse (Backward.componentToRight s)
      (Forward.toSectorForwardConcreteSupply.rightToComponent s)
  /-- Forest sector left inverse. -/
  forest_left_inv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.LeftInverse (Backward.componentToForest s)
      (Forward.toSectorForwardConcreteSupply.forestToComponent s)
  /-- Forest sector right inverse. -/
  forest_right_inv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.RightInverse (Backward.componentToForest s)
      (Forward.toSectorForwardConcreteSupply.forestToComponent s)

/-- **R-6c-leaf-23 — into the full sector-equiv assembler. -/
noncomputable def ResolvedSectorLeafBundle.toSectorEquivAssemblerSupply
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    (B : ResolvedSectorLeafBundle C) : ResolvedSectorEquivAssemblerSupply C where
  Forward := B.Forward.toSectorForwardConcreteSupply
  Backward := B.Backward
  right_left_inv := B.right_left_inv
  right_right_inv := B.right_right_inv
  forest_left_inv := B.forest_left_inv
  forest_right_inv := B.forest_right_inv

/-- **R-6c-leaf-23 — into the combined concrete sector equivalence. -/
noncomputable def ResolvedSectorLeafBundle.toConcreteSectorEquivSupply
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    (B : ResolvedSectorLeafBundle C) : ResolvedConcreteSectorEquivSupply C :=
  B.toSectorEquivAssemblerSupply.toConcreteSectorEquivSupply

/-- **R-6c-leaf-23 — into the three-route quotient-star supply (the BIGGEST correspondence). -/
noncomputable def ResolvedSectorLeafBundle.toQuotientStarSupply
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    (B : ResolvedSectorLeafBundle C) : ResolvedThreeRouteQuotientStarSupply D G imageOf :=
  B.toSectorEquivAssemblerSupply.toQuotientStarSupply

end GaugeGeometry.QFT.Combinatorial
