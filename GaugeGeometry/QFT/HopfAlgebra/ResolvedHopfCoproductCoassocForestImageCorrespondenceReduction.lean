import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestSectorBridgeScout

/-!
# R-6c-body-220 — forest image correspondence reduction: reduced to `componentToForest` sound + complete

Two-hundred-and-twentieth genuine-body step, the mirror of body-219 for the forest G-side leaf: body-215's
`forest_image_correspondence` is reduced to the two `componentToForest` round-trip directions, so both G-side sector
correspondences (right and forest) now sit at the same `sound` / `complete` granularity.

## The reduction

`Finset.mem_image` gives `γ ∈ s.attach.image f ↔ ∃ δ ∈ s.attach, f δ = γ`, so `forest_image_correspondence` splits
into:

* **sound** — `δ ∈ forestDomain (fwdMap q) → forestChoiceSelected q (componentToForest δ)`: the `componentToForest`
  image of a star-touching component is a forest-choice parent;
* **complete** — `forestChoiceSelected q γ → ∃ δ ∈ forestDomain (fwdMap q), componentToForest δ = γ`: every
  forest-choice parent is a `componentToForest` image.

As on the right side (body-219), body-156's region `componentToForest` is an abstract field (only
`forestComponentCD` / `forestComponentDisjoint`), disconnected from the sector `componentToForest` (which lands in
`ForestPrimitiveIndex`), so both directions are fresh.  The `forestChoiceSelected q γ = ∃ hγ ∃ B, choiceAt q ⟨γ,hγ⟩ =
inr B` predicate keeps the existential `B` (unlike `rightPrimSelected`'s bare `inl false`), but `complete` only needs
to recover the *parent* `γ` — the `B` is forgotten — so the extra existential is inert at this layer.

`ResolvedForestImageCorrespondenceDecompositionSupply D S Region` fields body-156's construction and the two fresh
directions `forest_sound` / `forest_complete`.  Then `.forest_image_correspondence` is **proved** by term-mode
`Finset.mem_image.mp` / `.mpr` (the `@[simp]` form does not fire through `simp` due to the `DecidableEq` instance
mismatch — body-211/219's finding — but term-mode unifies the instance from the goal).
`.toForestRecoveredSectorDecompositionSupply` (given the wiring bridge `forestRecovered_eq`) produces body-215's
supply.

## Consequence — the two G-side sector correspondences at one granularity

```text
right   (219)  right_sound  / right_complete    componentToRight  round-trip ↔ inl false
forest  (220)  forest_sound / forest_complete   componentToForest round-trip ↔ inr B
```

Both G-side sector leaves are now the two `componentTo…` round-trip directions.  The survivor correspondence (the
`HEq` quotient side) remains; the deeper win (wiring the region maps to the sector inverse, collapsing all four
`sound` / `complete`) is deferred.

Per the HALT: the `componentToForest` round-trip body (soundness / completeness) is not entered; the sector inverse
is not wired; the forest `B` value is not touched; only the `mem_image` assembly is proved.

Landed:

* `ResolvedForestImageCorrespondenceDecompositionSupply D S Region` — body-156's construction + `sound` + `complete`;
* `.forest_image_correspondence` — body-215's leaf (PROVED from the two directions);
* `.toForestRecoveredSectorDecompositionSupply` — body-215's supply (given the wiring bridge).

Toolkit body (like body-219).  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **R-6c-body-220 — the forest image correspondence decomposition supply.**  Body-156's sector region construction
and the two fresh `componentToForest` round-trip directions (soundness / completeness). -/
structure ResolvedForestImageCorrespondenceDecompositionSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- Body-156's sector region construction. -/
  Construction : ResolvedRegionConstructionFromSectorSupply D S
  /-- Sound: a `componentToForest` image of a star-touching component is a forest-choice parent. -/
  forest_sound : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (δ : {x // x ∈ forestDomain (fwdMap S q)}),
    forestChoiceSelected q (Construction.componentToForest (fwdMap S q) δ)
  /-- Complete: every forest-choice parent is a `componentToForest` image. -/
  forest_complete : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : ResolvedFeynmanSubgraph G),
    forestChoiceSelected q γ →
    ∃ δ : {x // x ∈ forestDomain (fwdMap S q)}, Construction.componentToForest (fwdMap S q) δ = γ

namespace ResolvedForestImageCorrespondenceDecompositionSupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-220 — body-215's `forest_image_correspondence` from `sound` + `complete`.** -/
theorem forest_image_correspondence
    (F : ResolvedForestImageCorrespondenceDecompositionSupply D S Region)
    {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G) (γ : ResolvedFeynmanSubgraph G) :
    γ ∈ (forestDomain (fwdMap S q)).attach.image (F.Construction.componentToForest (fwdMap S q))
      ↔ forestChoiceSelected q γ := by
  constructor
  · intro h
    obtain ⟨δ, _, rfl⟩ := Finset.mem_image.mp h
    exact F.forest_sound q δ
  · intro hγ
    obtain ⟨δ, hδ⟩ := F.forest_complete q γ hγ
    exact Finset.mem_image.mpr ⟨δ, Finset.mem_attach _ _, hδ⟩

/-- **R-6c-body-220 — body-215's forest recovered sector decomposition supply** (given the wiring bridge). -/
def toForestRecoveredSectorDecompositionSupply
    (F : ResolvedForestImageCorrespondenceDecompositionSupply D S Region)
    (forestRecovered_eq : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
      (Region.Union.forestRecovered (fwdMap S q)).elements
        = (F.Construction.forestRecovered (fwdMap S q)).elements) :
    ResolvedForestRecoveredSectorDecompositionSupply D S Region where
  Construction := F.Construction
  forestRecovered_eq := fun {G} q => forestRecovered_eq q
  forest_image_correspondence := fun {G} q γ => F.forest_image_correspondence q γ

end ResolvedForestImageCorrespondenceDecompositionSupply

end GaugeGeometry.QFT.Combinatorial
