import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRegionAssembly
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaLeftBridgeForwardOcc

/-!
# R-6c-body-508 — the single canonical faithful owner: AssemblyF + TagsF (PROVED)

Five-hundred-and-eighth genuine-body step — issuing the OccRaw-free canonical region owner ONCE.  The body-488 six-bridge
assembly threads `OccRaw` through ONE component only — the LEFT bridge (right body-483 / forest body-486 are already
`OccRaw`-free).  So the faithful assembly `AssemblyF` swaps the left component to body-504's
`resolvedCanonicalMultiStarLeftAlphaBridge_forwardOcc` (which fixes `Fmem := canonicalUniqueSelectedOuterFilteredMem
Supply_of_measure VBuild.Measure E`), and `TagsF` feeds `AssemblyF`'s six projections into the generic body-488 tag
converter with the pure `W'` carrier closure.  No `OccRaw` argument.

## Issued (Step 2)

```text
resolvedCanonicalMultiStarRegionAlphaBridgeAssembly_forwardOcc   (right 483 / forest 486 / left 504)
canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc           (the single TagsF owner)
canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc_assembly  (rfl anchor: TagsF.Closure.Assembly = AssemblyF)
canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc_forestTag (rfl anchor: TagsF.forestTag = M.forestTag)
```

Every downstream theorem (houter / the three correspondence leaves / membership boundary / round-trip / final wrapper)
reads this SAME named `TagsF` — no inline Tags re-construction, no old-Tags/new-Tags mixing.  Step 3+ (houterF /
forest_nonemptyF / survivor_memF / remnant_memF / DataF / round-trip / final quotEq wrapper) is the body-509 continuation
(per the plan's safe-stop — the single owner is the foundation; the downstream threading is deferred rather than rushed,
the only real risk being double owner issuance).

Per the HALT/guards: old Tags are NOT used; `TagsF` is NOT inline-rebuilt; the recovered branch gets no `ForwardOcc`; no
cast into the legacy `OccRaw` chain; the legacy body-488 stays a valid conditional (NON-destructive); `quot_eq` /
`legComplete` are NOT entered; strict `StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc claim.  No facade, no
flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **R-6c-body-508 — the OccRaw-free six-bridge alpha region assembly.**  Right body-483 / forest body-486 unchanged;
LEFT swapped to body-504's faithful bridge.  `Fmem` is the canonical `FmemF`. -/
noncomputable def resolvedCanonicalMultiStarRegionAlphaBridgeAssembly_forwardOcc
    (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
    (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    (Split : ResolvedAlphaValueQuotientRegionSplitSupply
      (canonicalUniqueSelectedOuterFilteredMemSupply_of_measure VBuild.Measure E)
      VBuild.toCanonicalFilteredValue) :
    ResolvedRecoveredRegionAlphaValueBridgeAssemblySupply
      (canonicalUniqueSelectedOuterFilteredMemSupply_of_measure VBuild.Measure E)
      VBuild.toCanonicalFilteredValue where
  Region := multiStarRegion
    (ValueGeometry.toCoreBuild.toValueCore.toDecontractionSupply
      (canonicalUniqueInnerRawCarrierClosureSupply ValueGeometry.toCoreBuild.toValueCore))
    canonicalUniqueStarFactsOfW'
  Left := multiStarLeft
  right_sound_value := (resolvedCanonicalMultiStarRightAlphaBridge VBuild ValueGeometry Split).right_sound_value
  right_complete_value := (resolvedCanonicalMultiStarRightAlphaBridge VBuild ValueGeometry Split).right_complete_value
  forest_sound_value := (resolvedCanonicalMultiStarForestAlphaBridge VBuild ValueGeometry Split).forest_sound_value
  forest_complete_value := (resolvedCanonicalMultiStarForestAlphaBridge VBuild ValueGeometry Split).forest_complete_value
  left_sound_value :=
    (resolvedCanonicalMultiStarLeftAlphaBridge_forwardOcc VBuild ValueGeometry E Split).left_sound_value
  left_complete_value :=
    (resolvedCanonicalMultiStarLeftAlphaBridge_forwardOcc VBuild ValueGeometry E Split).left_complete_value

/-- **R-6c-body-508 ∎ — the SINGLE canonical faithful region tag owner `TagsF`.**  The body-488 generic converter fed
`AssemblyF`'s six projections + the pure `W'` carrier closure.  No `OccRaw`. -/
noncomputable def canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc
    (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
    (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    (Split : ResolvedAlphaValueQuotientRegionSplitSupply
      (canonicalUniqueSelectedOuterFilteredMemSupply_of_measure VBuild.Measure E)
      VBuild.toCanonicalFilteredValue) :
    ResolvedRegionTagAlphaValueSupply
      (canonicalUniqueSelectedOuterFilteredMemSupply_of_measure VBuild.Measure E)
      VBuild.toCanonicalFilteredValue :=
  let A := resolvedCanonicalMultiStarRegionAlphaBridgeAssembly_forwardOcc VBuild ValueGeometry E Split
  multiStarRegionTagAlphaValueSupply
    (ValueGeometry.toCoreBuild.toValueCore.toDecontractionSupply
      (canonicalUniqueInnerRawCarrierClosureSupply ValueGeometry.toCoreBuild.toValueCore))
    canonicalUniqueStarFactsOfW' VBuild.Measure
    A.right_sound_value A.right_complete_value A.forest_sound_value A.forest_complete_value
    A.left_sound_value A.left_complete_value
    (canonicalUniquePureMultiStarCarrierClosureBundleSupply
      ValueGeometry.toCoreBuild.toValueCore).recovered_raw_mem

/-- **R-6c-body-508 — rfl anchor: `TagsF`'s assembly is `AssemblyF`.** -/
theorem canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc_assembly
    (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
    (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    (Split : ResolvedAlphaValueQuotientRegionSplitSupply
      (canonicalUniqueSelectedOuterFilteredMemSupply_of_measure VBuild.Measure E)
      VBuild.toCanonicalFilteredValue) :
    (canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc VBuild ValueGeometry E Split).Closure.Assembly
      = resolvedCanonicalMultiStarRegionAlphaBridgeAssembly_forwardOcc VBuild ValueGeometry E Split :=
  rfl

/-- **R-6c-body-508 — rfl anchor: `TagsF`'s forest tag is `M.forestTag`.** -/
theorem canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc_forestTag
    (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
    (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    (Split : ResolvedAlphaValueQuotientRegionSplitSupply
      (canonicalUniqueSelectedOuterFilteredMemSupply_of_measure VBuild.Measure E)
      VBuild.toCanonicalFilteredValue)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G)
    (γ : {x : ResolvedFeynmanSubgraph G //
      x ∈ ((canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc VBuild ValueGeometry E Split).Closure.unionOuterAlphaValue
        z).1.elements})
    (h : γ.1 ∈ ((canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc VBuild ValueGeometry E
      Split).Closure.Assembly.Region.forestRecovered z).elements) :
    (canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc VBuild ValueGeometry E Split).forestTag z γ h
      = (ValueGeometry.toCoreBuild.toValueCore.toDecontractionSupply
          (canonicalUniqueInnerRawCarrierClosureSupply ValueGeometry.toCoreBuild.toValueCore)).forestTag
          canonicalUniqueStarFactsOfW' z ⟨γ.1, h⟩ :=
  rfl

end GaugeGeometry.QFT.Combinatorial
