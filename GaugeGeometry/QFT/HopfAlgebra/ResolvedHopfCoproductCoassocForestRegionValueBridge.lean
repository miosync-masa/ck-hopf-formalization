import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionConstructionFromSector
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteSummandValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestRegionSectorBridge

/-!
# R-6c-body-276 — forest region sector bridge, value-root version (PROVED)

Two-hundred-and-seventy-sixth genuine-body step — the remnant (forest) side of the sector bridge, the exact mirror of
body-275.  For `z = fwdMapFilteredValue F V q`, the forest-recovered region's components are exactly `q`'s forest-choice
components (`forestChoiceSelected q.1 γ`, the `inr` mirror of `rightPrimSelected`) — proved from the value-root
sound/complete round-trip via body-219's `Finset.mem_image` skeleton, over `fwdMapFilteredValue` alone (no `fwdMap S`,
no `Forward`, no legacy bridge, no sector-index inverse).

## Same honest construction leaves as body-275

As with the right side (Case c of the body-273/275 scout), the only `componentToForest` ↔ `forestChoiceSelected`
connection is the total-`fwdMap S q` assumed field (never proved).  So the value-root sound/complete are honest
construction leaves `forest_sound_value` / `forest_complete_value` over `fwdMapFilteredValue`, and the membership bridge
is *proved* from them.  Only parent-component sound/complete are needed — the exact `B` of the `inr B` choice is NOT
recovered here (`forestChoiceSelected` already existentially quantifies `B`); the choice-value agreement is handled
downstream by the occurrence/tag machinery.

## The bridge

`forestRecovered_forward_value_membership` proves

```text
γ ∈ (Construction.forestRecovered (fwdMapFilteredValue F V q)).elements  ↔  forestChoiceSelected q.1 γ
```

by `forestRecovered_elements_eq` (body-156, rfl) + `Finset.mem_image.mp/.mpr` fed by the two value-root leaves.

## Status pin

```text
right / forest value bridge complete
construction supply still indexed by phantom S
```

`S` is a phantom index on `Construction` (body-156 never reads `S`; body-273 scout) — but `S` is still a term of the
old inhabit-blocked bundle, so a declaration-level `S`-free re-key of `ResolvedRegionConstructionFromSectorSupply` is the
next front (body-277), before the left-residual + recovered-membership assembly (body-278).

Per the HALT: only the forest side is closed; the left residual and the recovered-membership assembly are NOT entered;
body-224's sector-index inverse is NOT reused.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-276 — the value-root forest region bridge supply.**  The mirror of body-275: the region construction
(body-156, `S` phantom) plus the value-root remnant sound/complete round-trip (the value image of body-219, over
`fwdMapFilteredValue`). -/
structure ResolvedForestRegionValueBridgeSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) (S : ResolvedConcreteSummandBundleSupply D) where
  /-- The region construction (body-156); `S` is a phantom index, never read. -/
  Construction : ResolvedRegionConstructionFromSectorSupply D S
  /-- Value-root remnant soundness: `componentToForest` lands in `q`'s forest-choice components. -/
  forest_sound_value : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredValue F V q)}),
    forestChoiceSelected q.1 (Construction.componentToForest (fwdMapFilteredValue F V q) δ)
  /-- Value-root remnant completeness: every forest-choice component is a `componentToForest` image. -/
  forest_complete_value : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : ResolvedFeynmanSubgraph G),
    forestChoiceSelected q.1 γ →
    ∃ δ : {x // x ∈ forestDomain (fwdMapFilteredValue F V q)},
      Construction.componentToForest (fwdMapFilteredValue F V q) δ = γ

namespace ResolvedForestRegionValueBridgeSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
  {S : ResolvedConcreteSummandBundleSupply D}

/-- **R-6c-body-276 — the value-root forest region membership bridge.**  `forestRecovered (fwdMapFilteredValue F V q)`'s
components are exactly `q`'s forest-choice (`inr`) components — body-219's `Finset.mem_image` proof, re-keyed. -/
theorem forestRecovered_forward_value_membership (B : ResolvedForestRegionValueBridgeSupply F V S)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) (γ : ResolvedFeynmanSubgraph G) :
    γ ∈ (B.Construction.forestRecovered (fwdMapFilteredValue F V q)).elements
      ↔ forestChoiceSelected q.1 γ := by
  rw [ResolvedRegionConstructionFromSectorSupply.forestRecovered_elements_eq]
  constructor
  · intro h
    obtain ⟨δ, _, rfl⟩ := Finset.mem_image.mp h
    exact B.forest_sound_value q δ
  · intro hγ
    obtain ⟨δ, hδ⟩ := B.forest_complete_value q γ hγ
    exact Finset.mem_image.mpr ⟨δ, Finset.mem_attach _ _, hδ⟩

end ResolvedForestRegionValueBridgeSupply

end GaugeGeometry.QFT.Combinatorial
