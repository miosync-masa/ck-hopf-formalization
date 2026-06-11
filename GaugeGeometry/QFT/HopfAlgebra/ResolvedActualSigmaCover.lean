import GaugeGeometry.QFT.HopfAlgebra.ResolvedH58Bridge

/-!
# Final σ-cover data package (Track R-4-superfull)

The R-4-superfull architecture is complete up to **one** remaining construction: an
actual resolved σ-cover.  This file consolidates the remaining obligations into a single
package `ResolvedActualSigmaCover g`, and shows it delivers the concrete H5.8 sum-reindex
identity and the branch classifier.

What is **embedded in `FL`** (`ResolvedFiniteBranchMapLayer`) and so *not* duplicated
here: the layer's `cover` (branch-map surjectivity), `forest_inj`/`mixed_inj`, and the
forest/mixed image data carrying `componentCD`/`remnantCD`/disjointness/`avoidsStars`
(all baked in when `FL` is built from the forest/mixed image data via
`ResolvedBranchMapInstantiation.toLayer`).

What remains **external** (the package's own fields): the resolved→flat
`concreteIndexMaps` and the flat `splitTerm_agreement` (σ-cover data, Field Filling 6).

So the entire remaining R-4-superfull obstruction is: *construct one
`ResolvedActualSigmaCover g`*.
-/

set_option linter.unusedSectionVars false

open scoped TensorProduct

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ H : FeynmanGraph, DivergenceMeasure H]
         [∀ H : FeynmanGraph, IsPermInvariantDivergence H]
         [∀ H : FeynmanGraph, IsIsoInvariantDivergence H]
         [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)]
         [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
         [IsDivergencePreservedByAdmissibleForestContract]

/-- **The actual resolved σ-cover package.**  Consolidates the remaining R-4-superfull
obligations: the finite branch-map layer (carrying cover/injectivity/CD/disjoint), the
id-unique payload family, the resolved→flat index maps, and the flat split-term
agreement. -/
structure ResolvedActualSigmaCover (g : HopfGen) where
  /-- The id-unique payload family (supplies `EdgeIdsUnique`/`LegIdsUnique`). -/
  PFU : ResolvedHopfPayloadFamilyWithUniqueIds
  /-- The finite branch-map layer (carries cover/injectivity/CD/disjoint via its build). -/
  FL : ResolvedFiniteBranchMapLayer
  /-- Resolved→flat index maps + commutation squares. -/
  concreteIndexMaps : ResolvedH58ConcreteIndexMaps g FL
  /-- The flat split-term agreement (σ-cover data). -/
  splitTerm_agreement : ∀ s ∈ h58BridgeSplitChoiceIndex g,
    h58BridgeSplitChoiceTerm g s = h58BridgeQuotientTerm g (h58BridgeSplitPhi g s)

namespace ResolvedActualSigmaCover

variable {g : HopfGen} (S : ResolvedActualSigmaCover g)

/-- The full concrete bridge data assembled from the package. -/
def concreteData : ResolvedH58ConcreteData g S.FL :=
  S.concreteIndexMaps.toConcreteData S.splitTerm_agreement

/-- **The concrete resolved H5.8 sum-reindex** delivered by the package, with the actual
flat tensor terms. -/
theorem concrete_sum_reindex :
    ∑ z ∈ S.FL.imageCarrier, h58BridgeQuotientTerm g (S.concreteData.flatImageOf z) =
      (∑ q ∈ S.FL.forestCarrier, h58BridgeSplitChoiceTerm g (S.concreteData.forestSplitOf q)) +
      (∑ q ∈ S.FL.mixedCarrier, h58BridgeSplitChoiceTerm g (S.concreteData.mixedSplitOf q)) :=
  S.concreteData.concrete_sum_reindex

/-- The branch classifier delivered by the package (unique preimage in exactly one
branch). -/
def classifier : ResolvedIndexedBranchClassifier :=
  S.FL.layer.toClassifier

end ResolvedActualSigmaCover

/-! **Report.**  `ResolvedActualSigmaCover g` consolidates the four σ-cover-data-supply
obligations.  Dependency diagram:

```
ResolvedActualSigmaCover g
  ├─ FL : ResolvedFiniteBranchMapLayer        (carries cover, forest_inj, mixed_inj,
  │       └─ layer + carriers                  componentCD/remnantCD, disjoint, avoidsStars)
  ├─ concreteIndexMaps : ResolvedH58ConcreteIndexMaps g FL   (resolved→flat maps + comm)
  └─ splitTerm_agreement                       (flat σ-cover term agreement)

  .concreteData        = concreteIndexMaps.toConcreteData splitTerm_agreement
  .concrete_sum_reindex = the flat-term H5.8 split identity
  .classifier          = FL.layer.toClassifier
```

**Embedded vs external.**  `cover`, branch injectivity, and the image-data graph-work
(CD/disjoint/avoidsStars) are *inside* `FL` — supplied when `FL` is constructed from the
forest/mixed image data (`ResolvedForestImageData`/`ResolvedMixedImageData` →
`ResolvedBranchMapInstantiation.toLayer`).  The package adds only the resolved→flat index
maps and the flat term agreement.

**Remaining R-4-superfull obstruction (single statement):** *construct one
`ResolvedActualSigmaCover g`* — i.e. build the finite branch-map layer from an actual
resolved σ-cover (its forest/mixed image data) and supply the resolved→flat index maps +
flat term agreement.  All four are σ-cover data (non-facade); no abstract structure or new
mathematics remains. -/

end GaugeGeometry.QFT.Combinatorial
