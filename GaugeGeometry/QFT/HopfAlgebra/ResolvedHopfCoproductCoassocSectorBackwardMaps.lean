import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorEquivAssembler

/-!
# R-6c-leaf-31 — Sector backward maps from forward surjectivity

Twenty-sixth leaf-body discharge — the inverse half of the sector equivalence.  The forward maps
`Forward.rightToComponent` / `Forward.forestToComponent` (6a-10f) send an input-outer index to its Codomain
component; the backward maps `componentToRight` / `componentToForest` invert them.  The natural construction:
each Codomain component IS a forward image (the forests are the images of the forward maps — surjectivity),
so `componentToRight δ := Classical.choose` of the surjectivity witness.

The choose-specs (`Forward.rightToComponent s (componentToRight s δ) = δ`) are recorded — they are the
`Function.RightInverse` half of the sector inverse laws (the `LeftInverse` half then needs forward injectivity,
deferred).

Per the HALT, no inverse laws are proved (only the right-inverse specs, free from `choose_spec`); the
surjectivities (`right_surj` / `forest_surj` — that the forests are covered by the forward images) are supply
fields; Perm / Retarget untouched.

Landed:

* `ResolvedSectorBackwardFromImageSupply C Forward` — `right_surj` + `forest_surj`;
* `.componentToRight` / `.componentToForest` (via `Classical.choose`);
* `.componentToRight_spec` / `.componentToForest_spec` (the right-inverse specs);
* `.toSectorBackwardSupply : ResolvedSectorBackwardSupply C`.

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

/-- **R-6c-leaf-31 — the sector backward data.**  The forward maps are surjective onto the Codomain forests
(each component is a forward image). -/
structure ResolvedSectorBackwardFromImageSupply
    (C : ResolvedCodomainConcreteSupply D G imageOf)
    (Forward : ResolvedSectorForwardConcreteSupply C) where
  /-- Every right-forest component is a right-forward image. -/
  right_surj : ∀ (s : ResolvedCoassocSplitChoice D G) (δ : {x // x ∈ (C.rightForest s).elements}),
    ∃ r, Forward.rightToComponent s r = δ
  /-- Every remnant-forest component is a forest-forward image. -/
  forest_surj : ∀ (s : ResolvedCoassocSplitChoice D G) (δ : {x // x ∈ (C.remnantForest s).elements}),
    ∃ f, Forward.forestToComponent s f = δ

variable {C : ResolvedCodomainConcreteSupply D G imageOf}
  {Forward : ResolvedSectorForwardConcreteSupply C}

/-- **R-6c-leaf-31 — the right backward map (right-forest component ↦ input-outer right-primitive). -/
noncomputable def ResolvedSectorBackwardFromImageSupply.componentToRight
    (M : ResolvedSectorBackwardFromImageSupply C Forward) (s : ResolvedCoassocSplitChoice D G) :
    {x // x ∈ (C.rightForest s).elements} → RightPrimitiveIndex D G s :=
  fun δ => Classical.choose (M.right_surj s δ)

/-- **R-6c-leaf-31 — the forest backward map (remnant-forest component ↦ input-outer forest-choice). -/
noncomputable def ResolvedSectorBackwardFromImageSupply.componentToForest
    (M : ResolvedSectorBackwardFromImageSupply C Forward) (s : ResolvedCoassocSplitChoice D G) :
    {x // x ∈ (C.remnantForest s).elements} → ForestPrimitiveIndex D G s :=
  fun δ => Classical.choose (M.forest_surj s δ)

/-- **R-6c-leaf-31 — the right-inverse spec (`Forward ∘ Backward = id`). -/
theorem ResolvedSectorBackwardFromImageSupply.componentToRight_spec
    (M : ResolvedSectorBackwardFromImageSupply C Forward) (s : ResolvedCoassocSplitChoice D G)
    (δ : {x // x ∈ (C.rightForest s).elements}) :
    Forward.rightToComponent s (M.componentToRight s δ) = δ :=
  Classical.choose_spec (M.right_surj s δ)

/-- **R-6c-leaf-31 — the forest right-inverse spec (`Forward ∘ Backward = id`). -/
theorem ResolvedSectorBackwardFromImageSupply.componentToForest_spec
    (M : ResolvedSectorBackwardFromImageSupply C Forward) (s : ResolvedCoassocSplitChoice D G)
    (δ : {x // x ∈ (C.remnantForest s).elements}) :
    Forward.forestToComponent s (M.componentToForest s δ) = δ :=
  Classical.choose_spec (M.forest_surj s δ)

/-- **R-6c-leaf-31 — the sector backward supply from the surjectivities. -/
noncomputable def ResolvedSectorBackwardFromImageSupply.toSectorBackwardSupply
    (M : ResolvedSectorBackwardFromImageSupply C Forward) : ResolvedSectorBackwardSupply C where
  componentToRight := M.componentToRight
  componentToForest := M.componentToForest

end GaugeGeometry.QFT.Combinatorial
