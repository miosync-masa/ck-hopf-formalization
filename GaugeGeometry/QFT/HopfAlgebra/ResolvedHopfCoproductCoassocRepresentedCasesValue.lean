import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredPreimageValueMem

/-!
# R-6c-body-298 — `represented_cases` reduced to a pointwise forest-completeness floor (PROVED)

Two-hundred-and-ninety-eighth genuine-body step — the value-root reduction of body-289's `represented_cases` leaf to
the minimal pointwise forest-completeness floor `represented_forest_complete_value`.  The set-level statement
`γ ∈ z.1.1.elements → representedInQuotient z γ → γ ∈ forestRecovered z` is proved from the pointwise completeness fact
`∃ δ ∈ forestDomain z, componentToForest z δ = γ` via the image structure of `forestRecovered` (body-277).

## The reduction

`forestRecovered z`'s elements are `(forestDomain z).attach.image (componentToForest z)` (body-277,
`forestRecovered_elements_eq`, rfl).  So to place a represented `A`-component `γ` in `forestRecovered z` it suffices to
exhibit a `forestDomain z` component whose `componentToForest` image is `γ` — the completeness direction only, no `↔`.

## Why the pointwise fact is a floor

`representedInQuotient` is an opaque predicate (body-279, `ResolvedLeftResidualConstructionValueSupply`), and
`componentToForest` is an abstract map returning a bare `ResolvedFeynmanSubgraph G` (body-277); the S-free region core
carries NO law connecting the two.  So "a represented component has a `componentToForest` preimage" is an honest
component-level geometry leaf — the completeness half of `representedInQuotient` ⟷ `forestRecovered` image.

Per the HALT: `represented_cases` (the set leaf) is reduced to `represented_forest_complete_value` (the pointwise
completeness floor); no `↔` strengthening; the `componentToForest` / `representedInQuotient` internals are NOT entered;
generic `z`, no `forward_outer_value` / recovered-region coverage / round-trip (which would be self-circular), no
`Forward` / `forestTag`.  No `S` / `Forward` / legacy in any declaration type.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-298 — the represented-cases supply** (value root).  Body-283's data + the pointwise forest-completeness
floor (a represented `A`-component has a `componentToForest` preimage). -/
structure ResolvedRepresentedCasesValueSupply
    (F : ResolvedSelectedOuterFilteredMemSupply D) (V : ResolvedConcreteSummandValueSupply D) where
  /-- The membership supply (body-283). -/
  Data : ResolvedRecoveredPreimageValueMemSupply F V
  /-- The pointwise floor: a represented `A`-component `γ` is a `componentToForest` image (completeness only). -/
  represented_forest_complete_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : ResolvedFeynmanSubgraph G),
    γ ∈ z.1.1.elements → Data.Tags.Closure.Assembly.Left.representedInQuotient z γ →
    ∃ δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z},
      Data.Tags.Closure.Assembly.Region.componentToForest z δ = γ

namespace ResolvedRepresentedCasesValueSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-298 — body-289's `represented_cases` from the pointwise completeness floor** (via the image structure). -/
theorem represented_cases (R : ResolvedRepresentedCasesValueSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) (γ : ResolvedFeynmanSubgraph G)
    (hmem : γ ∈ z.1.1.elements)
    (hrep : R.Data.Tags.Closure.Assembly.Left.representedInQuotient z γ) :
    γ ∈ (R.Data.Tags.Closure.Assembly.Region.forestRecovered z).elements := by
  rw [ResolvedRegionConstructionFromSectorValueSupply.forestRecovered_elements_eq]
  obtain ⟨δ, hδ⟩ := R.represented_forest_complete_value z γ hmem hrep
  exact Finset.mem_image.mpr ⟨δ, Finset.mem_attach _ _, hδ⟩

end ResolvedRepresentedCasesValueSupply

end GaugeGeometry.QFT.Combinatorial
