import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaLeavesForwardOcc
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaForestValueEqForwardOcc
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaMembershipQz
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaQuotientMemComplete

/-!
# R-6c-body-510 — membership boundary + faithful roundtrip + OccRaw GONE (PROVED)

Five-hundred-and-tenth genuine-body step — the completion.  The single `TagsF` (body-508) and the four leaves (body-509)
are threaded through the body-491/492 membership boundary and the body-493/482 round-trip into an OccRaw-FREE closed
coassoc wrapper.  `DataF` is issued ONCE; everything downstream is its projection.

`coassoc_gen_of_canonicalMultiStar_alpha_quotEq_occurrence_discharged` — the native `W'` `Δᵣ`-coassociativity with `Fmem`,
`Split`, `survivorInj`, `survivorGen`, `quotient_mem`, AND `OccRaw` all GONE from the signature.  Remaining: `E` +
`CquotEq` (`Measure + quot_eq`) + `ValueGeometry` + `rep*`.

Per the HALT/guards: old Tags/Data are NOT cast to; `TagsF`/`DataF` are issued ONCE; the `p_L` proof uses no filtered
quotient before the elements HEq; the recovered branch gets no `ForwardOcc`; no legacy `OccRaw`-chain cast; the legacy
bodies stay valid conditionals; `quot_eq`/`legComplete` are NOT entered; strict `StarProm`/`InnerStarRaw` stay ZERO; this
is recorded as a CONDITIONAL theorem (the remaining `quot_eq`/`ValueGeometry`/model inputs), NOT unconditional.  No facade,
no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-510 — raw quotient elements HEq, over `TagsF`** (leaves fixed to body-509). -/
theorem canonicalMultiStar_alpha_quotient_elements_heq_forwardOcc {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G) :
    HEq (canonicalCorrectedQuotientRaw VBuild.Measure
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider canonicalUniqueStarFactsOfW'
        ((canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc VBuild ValueGeometry E Split).recoveredPreimageAlphaValue z)).elements
      z.2.1.elements :=
  canonicalCorrectedQuotient_elements_heq VBuild.Measure
    canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider canonicalUniqueStarFactsOfW'
    ((canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc VBuild ValueGeometry E Split).recoveredPreimageAlphaValue z) z
    (canonicalMultiStar_alpha_houter_forwardOcc VBuild ValueGeometry E Split z)
    (fun x₁ x₂ hx => canonicalMultiStar_alpha_survivor_mem_forwardOcc VBuild ValueGeometry E Split z x₁ x₂ hx)
    (fun x₁ x₂ hx => canonicalMultiStar_alpha_remnant_mem_forwardOcc VBuild ValueGeometry E Split z x₁ x₂ hx)

/-- **R-6c-body-510 — the `p_R` exclusion, over `TagsF`.** -/
theorem mixed_ne_pR_alpha_forwardOcc {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G) :
    ((canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc VBuild ValueGeometry E Split).recoveredPreimageAlphaValue z).2
      ≠ (fun _ _ => Sum.inl false) := by
  intro hpR
  have hempty := selectedOuterRawOf_eq_empty_of_eq_pR
    ((canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc VBuild ValueGeometry E Split).recoveredPreimageAlphaValue z) hpR
  rw [canonicalMultiStar_alpha_houter_forwardOcc VBuild ValueGeometry E Split z] at hempty
  have hne : (z.1.1).elements.Nonempty :=
    (canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider.carrier_isProperForest G z.1.1 z.1.2).1
  rw [hempty] at hne
  exact Finset.not_nonempty_empty hne

/-- **R-6c-body-510 — the `p_L` exclusion, over `TagsF`** (raw elements HEq before any filtered quotient). -/
theorem mixed_ne_pL_alpha_forwardOcc {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G) :
    ((canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc VBuild ValueGeometry E Split).recoveredPreimageAlphaValue z).2
      ≠ (fun _ _ => Sum.inl true) := by
  intro hpL
  have hg : ResolvedCoassocSplitChoice.selectedOuterContractGraph
        ((canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc VBuild ValueGeometry E Split).recoveredPreimageAlphaValue z)
      = z.1.1.contractWithStars (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G z.1.1) := by
    rw [ResolvedCoassocSplitChoice.selectedOuterContractGraph,
      canonicalMultiStar_alpha_houter_forwardOcc VBuild ValueGeometry E Split z]
  have hcard := finset_card_eq_of_heq (congrArg ResolvedFeynmanSubgraph hg)
    (canonicalMultiStar_alpha_quotient_elements_heq_forwardOcc VBuild ValueGeometry E Split z)
  set q := (canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc VBuild ValueGeometry E Split).recoveredPreimageAlphaValue z
    with hq
  have hR : ResolvedCoassocSplitChoice.rightComponents q = ∅ := by
    rw [ResolvedCoassocSplitChoice.rightComponents, Finset.filter_eq_empty_iff]
    intro γ _ hRP
    have hRP' : ResolvedCoassocSplitChoice.choiceAt q γ = Sum.inl false := hRP
    have hc : ResolvedCoassocSplitChoice.choiceAt q γ = Sum.inl true := by
      simp only [ResolvedCoassocSplitChoice.choiceAt, hpL]
    rw [hc] at hRP'
    exact absurd (Sum.inl.inj hRP') (by decide)
  have hF : ResolvedCoassocSplitChoice.forestComponents q = ∅ := by
    rw [ResolvedCoassocSplitChoice.forestComponents, Finset.filter_eq_empty_iff]
    intro γ _ hFC
    obtain ⟨B, hB⟩ := hFC
    have hc : ResolvedCoassocSplitChoice.choiceAt q γ = Sum.inl true := by
      simp only [ResolvedCoassocSplitChoice.choiceAt, hpL]
    rw [hc] at hB
    simp at hB
  have hempty : (canonicalCorrectedQuotientRaw VBuild.Measure
      canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider canonicalUniqueStarFactsOfW' q).elements = ∅ := by
    rw [canonicalCorrectedQuotientRaw]
    simp only [ResolvedAdmissibleSubgraph.union_elements,
      ResolvedRightSurvivorSupply.rightSurvivorForest_elements,
      ResolvedRemnantComponentSupply.remnantForest_elements, Finset.union_eq_empty,
      Finset.image_eq_empty, Finset.attach_eq_empty_iff]
    exact ⟨hR, hF⟩
  rw [hempty, Finset.card_empty] at hcard
  have hne : (z.2.1.elements).Nonempty :=
    (canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider.carrier_isProperForest _ z.2.1 z.2.2).1
  rw [← Finset.card_pos] at hne
  omega

/-- **R-6c-body-510 — the SINGLE `DataF` recovered-preimage membership owner** (leaves + exclusions fixed to
body-509/510). -/
noncomputable def canonicalMultiStarRecoveredPreimageAlphaValueMemSupply_forwardOcc :
    ResolvedRecoveredPreimageAlphaValueMemSupply
      (canonicalUniqueSelectedOuterFilteredMemSupply_of_measure VBuild.Measure E)
      VBuild.toCanonicalFilteredValue where
  Tags := canonicalMultiStarRegionTagAlphaValueSupply_forwardOcc VBuild ValueGeometry E Split
  forest_nonempty := fun {_G} z h =>
    canonicalMultiStar_alpha_forest_nonempty_forwardOcc VBuild ValueGeometry E Split z h
  mixed_ne_pR := fun {_G} z _ => mixed_ne_pR_alpha_forwardOcc VBuild ValueGeometry E Split z
  mixed_ne_pL := fun {_G} z _ => mixed_ne_pL_alpha_forwardOcc VBuild ValueGeometry E Split z

/-- **R-6c-body-510 — the filtered forward-quotient HEq, over `DataF`.** -/
theorem canonicalMultiStar_alpha_forward_quotient_forwardOcc {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G) :
    HEq (VBuild.toCanonicalFilteredValue.quotientForestRaw
        ((canonicalMultiStarRecoveredPreimageAlphaValueMemSupply_forwardOcc VBuild ValueGeometry E
          Split).recoveredFilteredPreimageAlphaValue z))
      z.2 :=
  heq_forestIdx _ z.2
    (canonicalMultiStar_alpha_houter_forwardOcc VBuild ValueGeometry E Split z)
    (canonicalMultiStar_alpha_quotient_elements_heq_forwardOcc VBuild ValueGeometry E Split z)

/-- **R-6c-body-510 — the full OccRaw-free canonical alpha round-trip leaf `RoundTripF`** (`DataF` bound once;
`forest_value_eq` reads body-505's forward socket, not `OccRaw`). -/
noncomputable def canonicalMultiStarAlphaRoundTripLeafSupply_forwardOcc :
    ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply
      (canonicalUniqueSelectedOuterFilteredMemSupply_of_measure VBuild.Measure E)
      VBuild.toCanonicalFilteredValue where
  Data := canonicalMultiStarRecoveredPreimageAlphaValueMemSupply_forwardOcc VBuild ValueGeometry E Split
  forward_outer_value := fun z => canonicalMultiStar_alpha_houter_forwardOcc VBuild ValueGeometry E Split z
  forward_quotient_value := fun z =>
    canonicalMultiStar_alpha_forward_quotient_forwardOcc VBuild ValueGeometry E Split z
  forest_value_eq := fun q γ hu B hmem hqB =>
    forest_value_eq_alpha_forwardOcc
      (ValueGeometry.toCoreBuild.toValueCore.toDecontractionSupply
        (canonicalUniqueInnerRawCarrierClosureSupply ValueGeometry.toCoreBuild.toValueCore))
      canonicalUniqueStarFactsOfW'
      (canonicalForwardForestOccurrenceInversionAlphaValueSupply VBuild ValueGeometry E)
      VBuild.Measure
      (canonicalMultiStarRecoveredPreimageAlphaValueMemSupply_forwardOcc VBuild ValueGeometry E Split)
      (fun {_G} _z => rfl) (fun {_G} _z _γ' _h _h' => rfl) q γ hu B hmem hqB

end GaugeGeometry.QFT.Combinatorial

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

/-- **R-6c-body-510 ∎ — canonical-`W'` native `Δᵣ`-coassociativity with `OccRaw` DISCHARGED.**  The body-482 wrapper fed
the single-owner OccRaw-free round-trip leaf `RoundTripF`.  `Fmem` / `Split` / `survivorInj` / `survivorGen` /
`quotient_mem` / `OccRaw` are ALL gone; the remaining explicit roots are `E` / `CquotEq` (`Measure + quot_eq`) /
`ValueGeometry` / `rep*`. -/
theorem coassoc_gen_of_canonicalMultiStar_alpha_quotEq_occurrence_discharged
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    (CquotEq : ResolvedCanonicalUniqueAlphaFilteredQuotEqConstructionSupply E)
    (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x))
    (x : ResolvedHopfGen) :
    canonicalUniqueSupportedCarrierProperSupply.toData.coassocLeft (MvPolynomial.X x)
      = canonicalUniqueSupportedCarrierProperSupply.toData.coassocRight (MvPolynomial.X x) :=
  coassoc_gen_of_canonical_unique_alpha_roundtrip
    (CquotEq.toAlphaNativeFilteredQuotientConstructionSupply E).toAlphaNativeFilteredValueConstructionSupply
    (canonicalMultiStarAlphaRoundTripLeafSupply_forwardOcc
      (CquotEq.toAlphaNativeFilteredQuotientConstructionSupply E).toAlphaNativeFilteredValueConstructionSupply
      ValueGeometry E
      (canonicalUniqueAlphaValueQuotientRegionSplitSupply
        (CquotEq.toAlphaNativeFilteredQuotientConstructionSupply E).toAlphaNativeFilteredValueConstructionSupply E))
    rep repCD rep_gen x

end GaugeGeometry.QFT.Combinatorial
