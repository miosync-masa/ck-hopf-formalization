import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionConstructionFromSector
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteSummandValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightPrimitiveFactorComplete

/-!
# R-6c-body-275 — right region sector bridge, value-root version (PROVED)

Two-hundred-and-seventy-fifth genuine-body step — the survivor (right) side of the sector bridge, re-keyed to the value
root.  For `z = fwdMapFilteredValue F V q`, the right-recovered region's components are exactly `q`'s right-primitive
components (`rightPrimSelected q.1 γ`) — proved from the value-root sound/complete round-trip, using body-219's
`Finset.mem_image` skeleton, over `fwdMapFilteredValue` alone (no `fwdMap S`, no `Forward`, no legacy bridge).

## Why the round-trip is an honest construction leaf

The scout of body-273/275 established (Case c): the ONLY law connecting the region map `componentToRight` to
`rightPrimSelected q` is body-219's `right_sound` / `right_complete` pair, and it is (i) an **assumed structure field,
never proved** (`ResolvedRegionConstructionFromSectorSupply` is never instantiated — body-224), and (ii) keyed to the
total `fwdMap S q` **only**.  Re-keying by `rfl` on the outer is blocked by body-224's outer disconnect
(`fwdMap`'s outer is `(selectedOuterOf q).1`, a different `Finset` from `q.1.1`).  So the value-root sound/complete are
introduced here as honest construction leaves `right_sound_value` / `right_complete_value` — the value image of
body-219's fields, over `fwdMapFilteredValue F V q` — and the membership bridge is *proved* from them.

## The bridge

`rightRecovered_forward_value_membership` proves

```text
γ ∈ (Construction.rightRecovered (fwdMapFilteredValue F V q)).elements  ↔  rightPrimSelected q.1 γ
```

by `rightRecovered_elements_eq` (body-156, rfl) + `Finset.mem_image.mp/.mpr` fed by the two value-root leaves — exactly
body-219's `right_image_correspondence` proof, re-keyed.  `S` is a phantom index on `Construction` (body-156 never reads
`S`; body-273 scout); the map and the leaves use only `fwdMapFilteredValue F V q`.

Per the HALT: only the right side is closed; the forest side (`componentToForest` / `forestRecovered`) and the left
residual are NOT entered; body-224's sector-index inverse (outer/tag mismatch) is NOT reused — only the explicit
`componentToRight` ↔ `rightPrimSelected` round-trip.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-275 — the value-root right region bridge supply.**  Carries the region construction (body-156, `S`
phantom) plus the value-root survivor sound/complete round-trip (the value image of body-219, over
`fwdMapFilteredValue`). -/
structure ResolvedRightRegionValueBridgeSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) (S : ResolvedConcreteSummandBundleSupply D) where
  /-- The region construction (body-156); `S` is a phantom index, never read. -/
  Construction : ResolvedRegionConstructionFromSectorSupply D S
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

namespace ResolvedRightRegionValueBridgeSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
  {S : ResolvedConcreteSummandBundleSupply D}

/-- **R-6c-body-275 — the value-root right region membership bridge.**  `rightRecovered (fwdMapFilteredValue F V q)`'s
components are exactly `q`'s right-primitive (`inl false`) components — body-219's `Finset.mem_image` proof, re-keyed to
the value root. -/
theorem rightRecovered_forward_value_membership (B : ResolvedRightRegionValueBridgeSupply F V S)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) (γ : ResolvedFeynmanSubgraph G) :
    γ ∈ (B.Construction.rightRecovered (fwdMapFilteredValue F V q)).elements
      ↔ rightPrimSelected q.1 γ := by
  rw [ResolvedRegionConstructionFromSectorSupply.rightRecovered_elements_eq]
  constructor
  · intro h
    obtain ⟨δ, _, rfl⟩ := Finset.mem_image.mp h
    exact B.right_sound_value q δ
  · intro hγ
    obtain ⟨δ, hδ⟩ := B.right_complete_value q γ hγ
    exact Finset.mem_image.mpr ⟨δ, Finset.mem_attach _ _, hδ⟩

end ResolvedRightRegionValueBridgeSupply

end GaugeGeometry.QFT.Combinatorial
