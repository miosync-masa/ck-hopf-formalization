import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaLeftBridge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRightBridge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarRegionTagValue

/-!
# R-6c-body-488 — the six-bridge alpha region assembly + canonical alpha `Tags` (PROVED)

Four-hundred-and-eighty-eighth genuine-body step — stage 5 of the body-445 migration campaign.  The six sound/complete
bridges (right body-483, forest body-486, left body-487) are bundled into the body-475 assembly record, and the alpha
region tag supply (body-477) is issued canonically over `W'` — the body-341 converter mirrored to the alpha value root.

**Correction (honest):** the `Data` membership does NOT become concrete here; the mixed-membership leaves need the forward
identities, so `ResolvedRecoveredPreimageAlphaValueMemSupply` is body-489's work.

* `resolvedCanonicalMultiStarRegionAlphaBridgeAssembly` — the body-475 record, projection-only from the three canonical
  bridges (`Region := multiStarRegion M Fstar`, `Left := multiStarLeft` by the body-483/486/487 anchors);
* `multiStarRegionTagAlphaValueSupply` — the generic body-341 alpha tag converter (six raw bridge laws + `rrm` → alpha
  `Tags`); the three disjointnesses are `left_right_cross` / `left_forest_cross` / `right_forest_cross`, the exclusivities
  are body-338, the nonempty source is `Measure.toConnectedDivergentNonemptySupply`;
* `canonicalMultiStarRegionTagAlphaValueSupply` — the canonical specialization feeding the body-341 converter the assembly's
  six projections + `(canonicalUniquePureMultiStarCarrierClosureBundleSupply Core).recovered_raw_mem`;
* the projection anchors (`Tags.Closure.Assembly` is the assembly; `Construction` / `forestTag` read the same multi-star
  maps), all `rfl`, banked for body-489's `hRight` / `hForest` / `hFT`.

Per the HALT/guards: `houter` is NOT proved; the forward quotient identity is NOT built; `ResolvedRecoveredPreimageAlpha
ValueMemSupply` is NOT constructed; the body-461 corrected `hround` is NOT consumed; the forest value exact-`B` leaf is NOT
entered; strict `StarProm` / `InnerStarRaw` NOT restored; body-445 stays a valid conditional.  NOT the unconditional
theorem.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **R-6c-body-488 — the canonical six-bridge alpha region assembly** (body-475 record, projection-only). -/
noncomputable def resolvedCanonicalMultiStarRegionAlphaBridgeAssembly
    {Fmem : ResolvedSelectedOuterFilteredMemSupply canonicalUniqueSupportedCarrierProperSupply.toData}
    (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
    (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
    (OccRaw : ResolvedForestOccurrenceInversionValueSupply ValueGeometry.toCoreBuild.toValueCore)
    (Split : ResolvedAlphaValueQuotientRegionSplitSupply Fmem VBuild.toCanonicalFilteredValue) :
    ResolvedRecoveredRegionAlphaValueBridgeAssemblySupply Fmem VBuild.toCanonicalFilteredValue where
  Region := multiStarRegion
    (ValueGeometry.toCoreBuild.toValueCore.toDecontractionSupply
      (canonicalUniqueInnerRawCarrierClosureSupply ValueGeometry.toCoreBuild.toValueCore))
    canonicalUniqueStarFactsOfW'
  Left := multiStarLeft
  right_sound_value := (resolvedCanonicalMultiStarRightAlphaBridge VBuild ValueGeometry Split).right_sound_value
  right_complete_value := (resolvedCanonicalMultiStarRightAlphaBridge VBuild ValueGeometry Split).right_complete_value
  forest_sound_value := (resolvedCanonicalMultiStarForestAlphaBridge VBuild ValueGeometry Split).forest_sound_value
  forest_complete_value := (resolvedCanonicalMultiStarForestAlphaBridge VBuild ValueGeometry Split).forest_complete_value
  left_sound_value := (resolvedCanonicalMultiStarLeftAlphaBridge VBuild ValueGeometry OccRaw Split).left_sound_value
  left_complete_value := (resolvedCanonicalMultiStarLeftAlphaBridge VBuild ValueGeometry OccRaw Split).left_complete_value

/-- **R-6c-body-488 — the generic alpha region tag converter** (body-341 mirrored to the alpha value root).  The six raw
bridge laws + `rrm` build the alpha `Tags`; disjointness / exclusivity / nonempty are the existing multi-star geometry. -/
noncomputable def multiStarRegionTagAlphaValueSupply (M : ResolvedMultiStarDecontractionSupply D)
    (Fstar : ResolvedCanonicalStarFacts D) (Measure : ResolvedMeasureLeafSupply D)
    {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedFilteredConcreteSummandValueSupply D}
    (right_sound : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (δ : {x // x ∈ rightDomain (fwdMapFilteredAlphaValue Fmem V q)}),
      rightPrimSelected q.1 (rightReembed (fwdMapFilteredAlphaValue Fmem V q) δ))
    (right_complete : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (γ : ResolvedFeynmanSubgraph G), rightPrimSelected q.1 γ →
      ∃ δ : {x // x ∈ rightDomain (fwdMapFilteredAlphaValue Fmem V q)},
        rightReembed (fwdMapFilteredAlphaValue Fmem V q) δ = γ)
    (forest_sound : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem V q)}),
      forestChoiceSelected q.1 (M.parent (fwdMapFilteredAlphaValue Fmem V q) δ))
    (forest_complete : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (γ : ResolvedFeynmanSubgraph G), forestChoiceSelected q.1 γ →
      ∃ δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem V q)},
        M.parent (fwdMapFilteredAlphaValue Fmem V q) δ = γ)
    (left_sound : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (γ : ResolvedFeynmanSubgraph G), ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 γ →
      γ ∈ leftResidualTouched (fwdMapFilteredAlphaValue Fmem V q))
    (left_complete : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (γ : ResolvedFeynmanSubgraph G), γ ∈ leftResidualTouched (fwdMapFilteredAlphaValue Fmem V q) →
      ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 γ)
    (rrm : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      regionRawUnion M Fstar z ∈ D.carrier G) :
    ResolvedRegionTagAlphaValueSupply Fmem V where
  Closure :=
    { Assembly :=
        { Region := multiStarRegion M Fstar
          Left := multiStarLeft
          right_sound_value := right_sound
          right_complete_value := right_complete
          forest_sound_value := forest_sound
          forest_complete_value := forest_complete
          left_sound_value := left_sound
          left_complete_value := left_complete }
      selected := Fmem
      left_right_disjoint := fun z γ hγ δ hδ _ => left_right_cross z hγ hδ
      left_forest_disjoint := fun z γ hγ δ hδ _ => left_forest_cross M Fstar z hγ hδ
      right_forest_disjoint := fun z γ hγ δ hδ _ => right_forest_cross M z hγ hδ
      recovered_raw_mem := rrm }
  forestTag := fun z γ h => M.forestTag Fstar z ⟨γ.1, h⟩
  right_notMem_left := fun z γ hr =>
    right_notMem_left (fun H => Measure.toConnectedDivergentNonemptySupply H) z hr
  forest_notMem_left := fun z γ hf =>
    forest_notMem_left (fun H => Measure.toConnectedDivergentNonemptySupply H) M Fstar z hf
  forest_notMem_right := fun z γ hf =>
    forest_notMem_right (fun H => Measure.toConnectedDivergentNonemptySupply H) M Fstar z hf

/-- **R-6c-body-488 ∎ — the canonical alpha region tag supply over `W'`.**  The body-341 converter fed the six-bridge
assembly's projections + the pure `W'` carrier closure. -/
noncomputable def canonicalMultiStarRegionTagAlphaValueSupply
    {Fmem : ResolvedSelectedOuterFilteredMemSupply canonicalUniqueSupportedCarrierProperSupply.toData}
    (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
    (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
    (OccRaw : ResolvedForestOccurrenceInversionValueSupply ValueGeometry.toCoreBuild.toValueCore)
    (Split : ResolvedAlphaValueQuotientRegionSplitSupply Fmem VBuild.toCanonicalFilteredValue) :
    ResolvedRegionTagAlphaValueSupply Fmem VBuild.toCanonicalFilteredValue :=
  let A := resolvedCanonicalMultiStarRegionAlphaBridgeAssembly VBuild ValueGeometry OccRaw Split
  multiStarRegionTagAlphaValueSupply
    (ValueGeometry.toCoreBuild.toValueCore.toDecontractionSupply
      (canonicalUniqueInnerRawCarrierClosureSupply ValueGeometry.toCoreBuild.toValueCore))
    canonicalUniqueStarFactsOfW' VBuild.Measure
    A.right_sound_value A.right_complete_value A.forest_sound_value A.forest_complete_value
    A.left_sound_value A.left_complete_value
    (canonicalUniquePureMultiStarCarrierClosureBundleSupply
      ValueGeometry.toCoreBuild.toValueCore).recovered_raw_mem

/-- **R-6c-body-488 — projection anchor: the canonical tags' assembly is the six-bridge assembly** (`rfl`). -/
theorem canonicalMultiStarRegionTagAlphaValueSupply_assembly
    {Fmem : ResolvedSelectedOuterFilteredMemSupply canonicalUniqueSupportedCarrierProperSupply.toData}
    (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
    (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
    (OccRaw : ResolvedForestOccurrenceInversionValueSupply ValueGeometry.toCoreBuild.toValueCore)
    (Split : ResolvedAlphaValueQuotientRegionSplitSupply Fmem VBuild.toCanonicalFilteredValue) :
    (canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).Closure.Assembly
      = resolvedCanonicalMultiStarRegionAlphaBridgeAssembly VBuild ValueGeometry OccRaw Split :=
  rfl

/-- **R-6c-body-488 — wiring anchor: the tags' forest tag is the multi-star forest tag** (`rfl`). -/
theorem canonicalMultiStarRegionTagAlphaValueSupply_forestTag
    {Fmem : ResolvedSelectedOuterFilteredMemSupply canonicalUniqueSupportedCarrierProperSupply.toData}
    (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
    (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
    (OccRaw : ResolvedForestOccurrenceInversionValueSupply ValueGeometry.toCoreBuild.toValueCore)
    (Split : ResolvedAlphaValueQuotientRegionSplitSupply Fmem VBuild.toCanonicalFilteredValue)
    {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G)
    (γ : {x // x ∈ ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).Closure.unionOuterAlphaValue z).1.elements})
    (h : γ.1 ∈ ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).Closure.Assembly.Region.forestRecovered z).elements) :
    (canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).forestTag z γ h
      = (ValueGeometry.toCoreBuild.toValueCore.toDecontractionSupply
          (canonicalUniqueInnerRawCarrierClosureSupply ValueGeometry.toCoreBuild.toValueCore)).forestTag
          canonicalUniqueStarFactsOfW' z ⟨γ.1, h⟩ :=
  rfl

end GaugeGeometry.QFT.Combinatorial
