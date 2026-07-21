import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRegionAssemblyForwardOcc
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSurvivorForestNonempty
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRemnantForwardOcc

/-!
# R-6c-body-509 — the four faithful geometry leaves over the single `TagsF` (PROVED)

Five-hundred-and-ninth genuine-body step — houter / forest_nonempty / survivor_mem / remnant_mem re-issued over body-508's
SINGLE `TagsF` owner (`canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc VBuild ValueGeometry E Split`), with NO
`OccRaw` and NO inline Tags rebuilding.  Each is the body-490/494/495 canonical wrapper with the old OccRaw-tags swapped for
`TagsF`; the forward socket appears only on the left/forest exact-B path (not here), and the remnant leaf reads body-507's
recovered-tag correspondence (no `ForwardOcc`).

## Issued

```text
canonicalMultiStar_alpha_houter_forwardOcc        (body-490 generic → TagsF)
canonicalMultiStar_alpha_forest_nonempty_forwardOcc  (shallow, Region = multiStarRegion)
canonicalMultiStar_alpha_survivor_mem_forwardOcc  (body-494 generic → TagsF, houterF + right anchor)
canonicalMultiStar_alpha_remnant_mem_forwardOcc   (body-507 recovered-tag → TagsF, hForest/hFT = rfl)
```

All four statements read the same `TagsF` application.  Step 4+ (raw quotient elements HEq / mixed exclusions / `DataF` /
`qz` / forward-quotient / `forestValueEqF` / round-trip / final quotEq wrapper) is the body-510 continuation (per the plan's
safe-stop — fixing the four leaves over the single owner is the sturdy checkpoint before the membership-cycle re-key).

Per the HALT/guards: old canonical Tags are NOT used; `TagsF` is NOT inline-rebuilt; the remnant leaf gets no `ForwardOcc`;
no cast into the legacy `OccRaw` chain; mixed pR/pL, `DataF`, `qz`, round-trip are NOT forced in here; the legacy
body-490/494/495 stay valid conditionals (NON-destructive); `quot_eq` / `legComplete` are NOT entered; strict `StarProm` /
`InnerStarRaw` stay ZERO; NO unconditional-coassoc claim.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
`promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
  (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
  (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
  (Split : ResolvedAlphaValueQuotientRegionSplitSupply
    (canonicalUniqueSelectedOuterFilteredMemSupply_of_measure VBuild.Measure E)
    VBuild.toCanonicalFilteredValue)

/-- **R-6c-body-509 — `houter`, over `TagsF`.** -/
theorem canonicalMultiStar_alpha_houter_forwardOcc {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G) :
    (resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
        ((canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc VBuild ValueGeometry E Split).recoveredPreimageAlphaValue z)
      = z.1.1 :=
  (canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc VBuild ValueGeometry E Split).multiStar_selectedOuterRawOf_alpha_eq
    (ValueGeometry.toCoreBuild.toValueCore.toDecontractionSupply
      (canonicalUniqueInnerRawCarrierClosureSupply ValueGeometry.toCoreBuild.toValueCore))
    canonicalUniqueStarFactsOfW' VBuild.Measure z rfl rfl
    (fun γ _ h' =>
      (ValueGeometry.toCoreBuild.toValueCore.toDecontractionSupply
        (canonicalUniqueInnerRawCarrierClosureSupply ValueGeometry.toCoreBuild.toValueCore)).promote_forestTag_elements
        canonicalUniqueStarFactsOfW' z ⟨γ.1, h'⟩)

/-- **R-6c-body-509 — `forest_nonempty`, over `TagsF`** (`Region = multiStarRegion`, shallow). -/
theorem canonicalMultiStar_alpha_forest_nonempty_forwardOcc {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G)
    (hz : resolvedIsForestImage z.1 z.2) :
    ((canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc VBuild ValueGeometry E
        Split).Closure.Assembly.Region.forestRecovered z).elements.Nonempty :=
  forestRecovered_nonempty_of_resolvedIsForestImage _ hz

/-- **R-6c-body-509 — `survivor_mem`, over `TagsF`** (houterF + the body-483 right anchor `rfl`). -/
theorem canonicalMultiStar_alpha_survivor_mem_forwardOcc {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G)
    (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
      ((canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc VBuild ValueGeometry E Split).recoveredPreimageAlphaValue z)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G z.1.1)))
    (hx : HEq x₁ x₂) :
    x₁ ∈ ((survivorSupply_of_measure VBuild.Measure G).rightSurvivorForest
        ((canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc VBuild ValueGeometry E Split).recoveredPreimageAlphaValue z)).elements
      ↔ x₂ ∈ rightDomain z :=
  (canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc VBuild ValueGeometry E Split).survivor_mem_alpha
    VBuild.Measure z (canonicalMultiStar_alpha_houter_forwardOcc VBuild ValueGeometry E Split z) rfl x₁ x₂ hx

/-- **R-6c-body-509 — `remnant_mem`, over `TagsF`** (body-507 recovered-tag correspondence; `hForest` / `hFT` are `rfl`;
no `ForwardOcc`). -/
theorem canonicalMultiStar_alpha_remnant_mem_forwardOcc {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G)
    (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
      ((canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc VBuild ValueGeometry E Split).recoveredPreimageAlphaValue z)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G z.1.1)))
    (hx : HEq x₁ x₂) :
    x₁ ∈ ((canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantForest
        ((canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc VBuild ValueGeometry E Split).recoveredPreimageAlphaValue z)).elements
      ↔ x₂ ∈ forestDomain z :=
  (canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc VBuild ValueGeometry E Split).remnant_mem_alpha_forwardOcc
    (ValueGeometry.toCoreBuild.toValueCore.toDecontractionSupply
      (canonicalUniqueInnerRawCarrierClosureSupply ValueGeometry.toCoreBuild.toValueCore))
    canonicalUniqueStarFactsOfW' VBuild.Measure
    canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
    (fun _ _ _ _ => rfl) (fun _ => rfl) z
    (canonicalMultiStar_alpha_houter_forwardOcc VBuild ValueGeometry E Split z) x₁ x₂ hx

end GaugeGeometry.QFT.Combinatorial
