import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorInverseConcrete

/-!
# R-6c-leaf-33 — Sector forward injectivity from the forward-map injectivity

Twenty-eighth leaf-body discharge — reducing the sector forward injectivity (the `LeftInverse` side of the
inverse laws, leaf-32) to the plain forward-*map* injectivity.  The forward maps are subtype-valued
(`Forward.rightToComponent s i = ⟨Forward.rightForward s i, rightForward_mem⟩`), so `rightToComponent`
injective reduces mechanically (via `Subtype.val`) to `rightForward` injective — dropping the membership
wrapper.

The forward maps are the transported local survivor / remnant components
(`rightForward = transportSubgraphAlongGraphEq … ∘ Local.rightLocal = … ∘ rightSurvivorComponentOf ∘ toRightComponent`),
so `rightForward` injective connects to the Product injection results — right to `survivorInj` (leaf-8), forest
to `remnantInj` / `occurrence_inj` (leaf-9) — through the index / transport layers.  Those component-level
injectivities stay the supply fields here.

Per the HALT, `right_forward_injective` / `forest_forward_injective` are supply fields (the genuine component /
index injectivity); no surjectivity; Perm / Retarget untouched.

Landed:

* `ResolvedSectorForwardInjectivityConnector C Forward` — `right_forward_injective` + `forest_forward_injective`;
* `.toSectorForwardInjectivitySupply` — the forward injectivity (via `Subtype.val`).

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

/-- **R-6c-leaf-33 — the sector forward-map injectivity connector.**  Injectivity of the underlying forward
maps (before the membership wrapper). -/
structure ResolvedSectorForwardInjectivityConnector
    (C : ResolvedCodomainConcreteSupply D G imageOf)
    (Forward : ResolvedSectorForwardConcreteSupply C) where
  /-- The right forward map is injective. -/
  right_forward_injective : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.Injective (Forward.rightForward s)
  /-- The forest forward map is injective. -/
  forest_forward_injective : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.Injective (Forward.forestForward s)

/-- **R-6c-leaf-33 — the sector forward injectivity from the forward-map injectivity (via `Subtype.val`). -/
def ResolvedSectorForwardInjectivityConnector.toSectorForwardInjectivitySupply
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    {Forward : ResolvedSectorForwardConcreteSupply C}
    (M : ResolvedSectorForwardInjectivityConnector C Forward) :
    ResolvedSectorForwardInjectivitySupply C Forward where
  right_injective := fun s _ _ hij => M.right_forward_injective s (congrArg Subtype.val hij)
  forest_injective := fun s _ _ hij => M.forest_forward_injective s (congrArg Subtype.val hij)

end GaugeGeometry.QFT.Combinatorial
