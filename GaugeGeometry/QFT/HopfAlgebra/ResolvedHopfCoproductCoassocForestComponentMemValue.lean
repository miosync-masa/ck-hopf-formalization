import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredPreimageValueMem

/-!
# R-6c-body-297 — `forestComponentMem` reduced to a pointwise parent-membership floor (PROVED)

Two-hundred-and-ninety-seventh genuine-body step — the value-root reduction of body-289's `forestComponentMem` leaf to
the minimal pointwise parent-membership floor `forest_parent_mem_value`.  The set-level statement `γ ∈ forestRecovered z
→ γ ∈ z.1.1.elements` is proved from the pointwise fact `componentToForest z δ ∈ z.1.1.elements` via the image structure
of `forestRecovered` (body-277).

## The reduction

`forestRecovered z`'s elements are `(forestDomain z).attach.image (componentToForest z)` (body-277,
`forestRecovered_elements_eq`, rfl).  So `γ ∈ forestRecovered z` gives `γ = componentToForest z δ` for some
`δ ∈ forestDomain z` (`Finset.mem_image`), and `forestComponentMem` reduces to
`componentToForest z δ ∈ z.1.1.elements`.

## Why the pointwise fact is a floor

The S-free region core (body-277, `RegionConstructionValue.lean:60`) fields `componentToForest` returning a BARE
`ResolvedFeynmanSubgraph G` — NOT a subtype of `z.1.1.elements` — with only `forestComponentCD` / `forestComponentDisjoint`
alongside; parent-in-`A` is not retained.  So `componentToForest z δ ∈ z.1.1.elements` (each recovered forest parent is a
component of the target outer `A`) is an honest component-level geometry leaf; it is NOT inferred from `forestComponentCD`
/ `forestComponentDisjoint`, and `componentToForest`'s bare-graph return does not encode it.

Per the HALT: `forestComponentMem` (the set leaf) is reduced to `forest_parent_mem_value` (the pointwise floor); the
`componentToForest` internal construction / sector inverse is NOT entered; generic `z`, no `Forward` / round-trip /
`forestTag_agrees`.  No `S` / `Forward` / legacy in any declaration type.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-297 — the forest-component membership supply** (value root).  Body-283's data + the pointwise
parent-membership floor (each recovered forest parent is a component of the target outer `A`). -/
structure ResolvedForestComponentMemValueSupply
    (F : ResolvedSelectedOuterFilteredMemSupply D) (V : ResolvedConcreteSummandValueSupply D) where
  /-- The membership supply (body-283). -/
  Data : ResolvedRecoveredPreimageValueMemSupply F V
  /-- The pointwise floor: a recovered forest parent `componentToForest z δ` is a component of `z.1.1`. -/
  forest_parent_mem_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z}),
    Data.Tags.Closure.Assembly.Region.componentToForest z δ ∈ z.1.1.elements

namespace ResolvedForestComponentMemValueSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-297 — body-289's `forestComponentMem` from the pointwise floor** (via the image structure). -/
theorem forestComponentMem (R : ResolvedForestComponentMemValueSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) (γ : ResolvedFeynmanSubgraph G)
    (h : γ ∈ (R.Data.Tags.Closure.Assembly.Region.forestRecovered z).elements) :
    γ ∈ z.1.1.elements := by
  rw [ResolvedRegionConstructionFromSectorValueSupply.forestRecovered_elements_eq] at h
  obtain ⟨δ, _, rfl⟩ := Finset.mem_image.mp h
  exact R.forest_parent_mem_value z δ

end ResolvedForestComponentMemValueSupply

end GaugeGeometry.QFT.Combinatorial
