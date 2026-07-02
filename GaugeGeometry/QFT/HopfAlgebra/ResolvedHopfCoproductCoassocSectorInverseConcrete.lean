import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorBackwardMaps
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorLeafInventory

/-!
# R-6c-leaf-32 — Sector inverse laws from backward choose-specs + forward injectivity

Twenty-seventh leaf-body discharge — the four sector inverse laws, PROVED (modulo forward injectivity).  With
the backward maps built from forward surjectivity (leaf-31, `componentTo*_spec : Forward ∘ Backward = id`):

* `right_right_inv` / `forest_right_inv` — `Function.RightInverse (componentTo…) (…toComponent)` is *exactly*
  `componentTo…_spec` (free, `choose_spec`);
* `right_left_inv` / `forest_left_inv` — `∀ x, componentTo… (…toComponent x) = x` from forward INJECTIVITY:
  `…toComponent (componentTo… (…toComponent x)) = …toComponent x` (the spec at `δ = …toComponent x`), then
  cancel the injective `…toComponent`.

So the four inverse-law leaves reduce to the TWO forward injectivities (plus the leaf-31 surjectivities behind
the backward maps).

Per the HALT, forward injectivity / surjectivity are supply fields; Perm / Retarget untouched.

Landed:

* `ResolvedSectorForwardInjectivitySupply C Forward` — `right_injective` + `forest_injective`;
* `.toSectorInverseLawSupply Backward` — the four inverse laws over `Backward.toSectorBackwardSupply`.

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

/-- **R-6c-leaf-32 — the sector forward-map injectivity supply.**  The forward maps are injective (the
`LeftInverse` half of the sector equivalence). -/
structure ResolvedSectorForwardInjectivitySupply
    (C : ResolvedCodomainConcreteSupply D G imageOf)
    (Forward : ResolvedSectorForwardConcreteSupply C) where
  /-- The right forward map is injective. -/
  right_injective : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.Injective (Forward.rightToComponent s)
  /-- The forest forward map is injective. -/
  forest_injective : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.Injective (Forward.forestToComponent s)

/-- **R-6c-leaf-32 — the four sector inverse laws from injectivity + the backward choose-specs. -/
def ResolvedSectorForwardInjectivitySupply.toSectorInverseLawSupply
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    {Forward : ResolvedSectorForwardConcreteSupply C}
    (Inj : ResolvedSectorForwardInjectivitySupply C Forward)
    (Backward : ResolvedSectorBackwardFromImageSupply C Forward) :
    ResolvedSectorInverseLawSupply Forward Backward.toSectorBackwardSupply where
  right_left_inv := fun s r =>
    Inj.right_injective s (Backward.componentToRight_spec s (Forward.rightToComponent s r))
  right_right_inv := fun s => Backward.componentToRight_spec s
  forest_left_inv := fun s f =>
    Inj.forest_injective s (Backward.componentToForest_spec s (Forward.forestToComponent s f))
  forest_right_inv := fun s => Backward.componentToForest_spec s

end GaugeGeometry.QFT.Combinatorial
