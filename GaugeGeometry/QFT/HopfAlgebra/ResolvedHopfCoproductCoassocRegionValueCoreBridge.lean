import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionConstructionValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteSummandValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightPrimitiveFactorComplete
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestRegionSectorBridge

/-!
# R-6c-body-278 — right / forest region bridges over the S-free core (PROVED)

Two-hundred-and-seventy-eighth genuine-body step — bodies 275/276 re-keyed onto the S-free region construction core
(body-277).  The `Construction` field is now `ResolvedRegionConstructionFromSectorValueSupply D` — **no `S` in the
declaration type at all**.  The two membership bridges are re-proved with the same `Finset.mem_image.mp/.mpr` skeleton.
After this the region sector layer is fully value-root canonical: no phantom `S`, no `Forward`, no legacy bridge, no
sector-index inverse.

## The two S-free canonical bridge records

```lean
structure ResolvedRightRegionValueCoreBridgeSupply (F) (V) where
  Construction : ResolvedRegionConstructionFromSectorValueSupply D   -- S-free (body-277)
  right_sound_value / right_complete_value                            -- honest construction leaves (body-219 image)

structure ResolvedForestRegionValueCoreBridgeSupply (F) (V) where
  Construction : ResolvedRegionConstructionFromSectorValueSupply D
  forest_sound_value / forest_complete_value
```

`rightRecovered_forward_value_membership` / `forestRecovered_forward_value_membership` prove the `inl false` / `inr B`
component characterizations, `↔`, over `fwdMapFilteredValue F V q` alone.

Per the HALT: only the S-free re-key of the right/forest bridges is done; `.toValueCore` is NOT used on the canonical
path (the old 275/276 supplies remain only as comparison records); the left residual (body-279) and the
recovered-membership assembly (body-280) are NOT entered.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-278 — the value-root right region bridge over the S-free core.**  `Construction` is S-free (body-277);
the survivor sound/complete round-trip are honest construction leaves over `fwdMapFilteredValue`. -/
structure ResolvedRightRegionValueCoreBridgeSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) where
  /-- The S-free region construction core (body-277). -/
  Construction : ResolvedRegionConstructionFromSectorValueSupply D
  /-- Value-root survivor soundness: `componentToRight` lands in `q`'s right-primitive components. -/
  right_sound_value : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (δ : {x // x ∈ rightDomain (fwdMapFilteredValue F V q)}),
    rightPrimSelected q.1 (Construction.componentToRight (fwdMapFilteredValue F V q) δ)
  /-- Value-root survivor completeness: every right-primitive component is a `componentToRight` image. -/
  right_complete_value : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : ResolvedFeynmanSubgraph G),
    rightPrimSelected q.1 γ →
    ∃ δ : {x // x ∈ rightDomain (fwdMapFilteredValue F V q)},
      Construction.componentToRight (fwdMapFilteredValue F V q) δ = γ

/-- **R-6c-body-278 — the value-root forest region bridge over the S-free core.**  The mirror: `Construction` is S-free;
the remnant sound/complete round-trip are honest construction leaves over `fwdMapFilteredValue`. -/
structure ResolvedForestRegionValueCoreBridgeSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) where
  /-- The S-free region construction core (body-277). -/
  Construction : ResolvedRegionConstructionFromSectorValueSupply D
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

/-- **R-6c-body-278 — the S-free right region membership bridge.**  Body-275's proof over the S-free core. -/
theorem ResolvedRightRegionValueCoreBridgeSupply.rightRecovered_forward_value_membership
    {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
    (B : ResolvedRightRegionValueCoreBridgeSupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) (γ : ResolvedFeynmanSubgraph G) :
    γ ∈ (B.Construction.rightRecovered (fwdMapFilteredValue F V q)).elements
      ↔ rightPrimSelected q.1 γ := by
  rw [ResolvedRegionConstructionFromSectorValueSupply.rightRecovered_elements_eq]
  constructor
  · intro h
    obtain ⟨δ, _, rfl⟩ := Finset.mem_image.mp h
    exact B.right_sound_value q δ
  · intro hγ
    obtain ⟨δ, hδ⟩ := B.right_complete_value q γ hγ
    exact Finset.mem_image.mpr ⟨δ, Finset.mem_attach _ _, hδ⟩

/-- **R-6c-body-278 — the S-free forest region membership bridge.**  Body-276's proof over the S-free core. -/
theorem ResolvedForestRegionValueCoreBridgeSupply.forestRecovered_forward_value_membership
    {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
    (B : ResolvedForestRegionValueCoreBridgeSupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) (γ : ResolvedFeynmanSubgraph G) :
    γ ∈ (B.Construction.forestRecovered (fwdMapFilteredValue F V q)).elements
      ↔ forestChoiceSelected q.1 γ := by
  rw [ResolvedRegionConstructionFromSectorValueSupply.forestRecovered_elements_eq]
  constructor
  · intro h
    obtain ⟨δ, _, rfl⟩ := Finset.mem_image.mp h
    exact B.forest_sound_value q δ
  · intro hγ
    obtain ⟨δ, hδ⟩ := B.forest_complete_value q γ hγ
    exact Finset.mem_image.mpr ⟨δ, Finset.mem_attach _ _, hδ⟩

end GaugeGeometry.QFT.Combinatorial
