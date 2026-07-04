import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientForestConstructor

/-!
# R-6c-body-112 — outer-mixing inverse scout: `invConstruct` is the flat inverse via sector backward maps

Hundred-and-twelfth genuine-body step, scouting the backward map `invConstruct : (A, B) ↦ (A', p)` — the LAST
genuinely-new construction (forward map + `quot_eq` are recovered from existing machinery, bodies 105/106/111).
The finding: `invConstruct` is the resolved analogue of the flat `forestComponentSplitPhiInverseConstruction.inv`
(`Coassoc` 27993), and its per-component reconstruction is exactly the existing sector backward maps
`ResolvedSectorBackwardFromImageSupply.componentToRight` / `componentToForest` (`SectorBackwardMaps` 57/63).

## The type and the flat template

`invConstruct : ForestBlockCodType D G → ForestBlockDomType D G`, i.e. `(A, B) ↦ (A', p)` — exactly the flat
`inv : forestQuotientForestSigma g → forestComponentSplitChoiceSigma g`.  The flat inverse construction bundles:

* `inv_mem` — the reconstructed `(A', p)` lands in the domain carrier;
* `right_inv` — `forward (inv r) = r` (`toFun ∘ invConstruct = id`);
* `left_inv` — `inv (forward q) = q` (`invConstruct ∘ toFun = id`);

matching the map data's `mixed_/forest_ right_inv` / `left_inv` fields.

## The per-component reconstruction (existing sector backward maps)

Given `(A, B)` with `A = leftOf ∪ promotedOf` and `B = rightSurvivor ∪ remnant` (bodies 105/109), the original
outer `A'` and choice `p` are recovered component-by-component, by the `star`-classification of `B`'s components:

* a REMNANT component of `B` (star-touching) ↦ a FOREST-choice component of `A'` — the existing
  `ResolvedSectorBackwardFromImageSupply.componentToForest s : {δ ∈ remnantForest s} → ForestPrimitiveIndex D G
  s` (via `forest_surj`), then `ForestPrimitiveIndex.toOccurrence` (`SectorIndexBridge` 53);
* a RIGHT-SURVIVOR component of `B` (star-avoiding) ↦ a RIGHT-PRIMITIVE component of `A'` — the existing
  `componentToRight s : {δ ∈ rightForest s} → RightPrimitiveIndex D G s` (via `right_surj`), then
  `RightPrimitiveIndex.toRightComponent` (`SectorIndexBridge` 44);
* a component of `A` NOT arising from the quotient (a `promotedOf` / `leftOf` piece) ↦ a LEFT-PRIMITIVE component
  of `A'`.

So `A' = ` (left-primitive pieces of `A`) ∪ (right-survivor pieces of `B` lifted back) ∪ (forest-choice pieces
reassembled from `promotedOf` ⊔ `remnant`), and `p` assigns each `A'`-component its `inl true` / `inl false` /
`inr Bᵧ` tag by which class it came from.  The two `_surj` fields are the surjectivity witnesses that make the
backward maps total; the specs `componentToRight_spec` / `componentToForest_spec` are the local right-inverses.

## The named inverse data

So the raid boss's last new datum is exactly the flat `forestComponentSplitPhiInverseConstruction` ported to the
resolved carrier, i.e.:

* `invConstruct` — the total backward map (from the sector backward maps + `A'` reassembly);
* `left_inv` / `right_inv` — the two inverse laws (the sector backward `_spec`s plus the forward/backward
  round-trips on the components);

with the per-component classification supplied by the EXISTING `ResolvedSectorBackwardFromImageSupply`
(`right_surj` / `forest_surj` / `componentToRight` / `componentToForest`) and the sector index bridge.  The map
data's four inverse fields (`mixed_/forest_ left_/right_inv`) are these two round-trips restricted to the two
classes.

Per the HALT: `invConstruct` is identified with the flat inverse construction and reduced to the existing sector
backward maps; the inverse laws are NOT proved (they remain the map data's fields); no reconstruction is
implemented; mixed/forest classification kept separate.

Landed:

* `ResolvedOuterMixingInverseType` — the backward-map type abbreviation (`(A, B) ↦ (A', p)`), documenting the
  flat-`inv` / sector-backward identification.

Scout/documentation body (like body-103/107–111), no new supply.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-112 — the outer-mixing backward-map type.**  `invConstruct : (A, B) ↦ (A', p)` — the resolved
analogue of the flat `forestComponentSplitPhiInverseConstruction.inv` (`forestQuotientForestSigma →
forestComponentSplitChoiceSigma`), reconstructed via the existing sector backward maps
(`ResolvedSectorBackwardFromImageSupply.componentToRight` / `componentToForest`). -/
abbrev ResolvedOuterMixingInverseType (D : ResolvedCoproductProperForestData) (G : ResolvedFeynmanGraph) :=
  ForestBlockCodType D G → ForestBlockDomType D G

end GaugeGeometry.QFT.Combinatorial
