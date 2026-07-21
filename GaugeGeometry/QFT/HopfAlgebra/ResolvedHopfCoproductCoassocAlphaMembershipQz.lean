import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRawQuotientElementsHEq
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMixedNePRExclusion

/-!
# R-6c-body-492 — crossing the membership boundary: `p_R`/`p_L` exclusions → `qz` → filtered `ForestIdx` HEq (PROVED)

Four-hundred-and-ninety-second genuine-body step — the completion node of the type-cycle repair.  The body-491 raw
elements HEq (the escape) drives the two mixed exclusions membership-free, which — with the geometric `forest_nonempty` —
issue the canonical alpha membership supply, hence the genuine filtered witness `qz`; then the raw HEq is upgraded to the
filtered `ForestIdx` HEq `HEq (V.quotientForestRaw qz) z.2` DIRECTLY (no detour through the body-478 `Data`-dependent
theorem).

* `finset_card_eq_of_heq` — HEq of `Finset`s ⟹ equal card (`cases h; rfl`);
* `mixed_ne_pR_alpha` — `p_R` ⟹ empty selected outer (body-310) vs `houter` (body-490) + `z.1.2` carrier properness;
* `mixed_ne_pL_alpha` — `p_L` ⟹ empty raw quotient (body-468) vs body-491 card + `z.2.2` carrier properness (NO
  `V.quotientForestRaw` / `V.union_eq`);
* `canonicalMultiStarRecoveredPreimageAlphaValueMemSupply` — the canonical `ResolvedRecoveredPreimageAlphaValueMemSupply`
  (`forest_nonempty` geometric input + the two exclusions);
* `canonicalMultiStar_alpha_forward_quotient` — the filtered `ForestIdx` HEq on `qz := Data.recoveredFilteredPreimage
  AlphaValue z`, from `heq_forestIdx` (body-203) fed `houter` + the body-491 elements HEq (`(V.quotientForestRaw qz).1 =
  canonicalCorrectedQuotientRaw … qz.1` by DEFEQ).

Per the HALT/guards: the `p_L` proof does NOT use `V.quotientForestRaw` first; properness comes ONLY from `z.1.2` / `z.2.2`
live carrier membership; NO `IsProperForest → membership` back-flow; NO `V.union_eq` / fabricated witness; strict `StarProm`
/ `InnerStarRaw` stay ZERO; the forest exact-`B` leaf / the full AlphaRoundTrip assembly are left to the next body.  NOT the
unconditional theorem.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton /
floor-297.
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

universe u

/-- **R-6c-body-492 — HEq of `Finset`s over propositionally-equal element types collapses to equal cardinality.** -/
theorem finset_card_eq_of_heq {α β : Type u} (hab : α = β) {s : Finset α} {t : Finset β} (h : HEq s t) :
    s.card = t.card := by
  subst hab; rw [eq_of_heq h]

variable {D : ResolvedCoproductProperForestData}
  {Fmem : ResolvedSelectedOuterFilteredMemSupply canonicalUniqueSupportedCarrierProperSupply.toData}
  (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
  (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
  (OccRaw : ResolvedForestOccurrenceInversionValueSupply ValueGeometry.toCoreBuild.toValueCore)
  (Split : ResolvedAlphaValueQuotientRegionSplitSupply Fmem VBuild.toCanonicalFilteredValue)

/-- **R-6c-body-492 — the `p_R` exclusion.**  The recovered choice is never all-right-primitive: `p_R` empties the
selected outer (body-310), but `houter` (body-490) equates it with the proper-forest outer `z.1.1` (nonempty via `z.1.2`). -/
theorem mixed_ne_pR_alpha {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G) :
    ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z).2
      ≠ (fun _ _ => Sum.inl false) := by
  intro hpR
  have hempty := selectedOuterRawOf_eq_empty_of_eq_pR
    ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z) hpR
  rw [canonicalMultiStar_alpha_houter VBuild ValueGeometry OccRaw Split z] at hempty
  have hne : (z.1.1).elements.Nonempty :=
    (canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider.carrier_isProperForest G z.1.1 z.1.2).1
  rw [hempty] at hne
  exact Finset.not_nonempty_empty hne

/-- **R-6c-body-492 — the `p_L` exclusion.**  `p_L` empties the raw quotient (body-468), but the body-491 elements HEq
card-equates it with the proper-forest codomain `z.2.1` (positive via `z.2.2`).  NO `V.quotientForestRaw`. -/
theorem mixed_ne_pL_alpha {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G)
    (survivor_mem : ∀ (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
        ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z)))
      (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars
        (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G z.1.1))),
      HEq x₁ x₂ →
      (x₁ ∈ ((survivorSupply_of_measure VBuild.Measure G).rightSurvivorForest
          ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z)).elements
        ↔ x₂ ∈ rightDomain z))
    (remnant_mem : ∀ (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
        ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z)))
      (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars
        (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G z.1.1))),
      HEq x₁ x₂ →
      (x₁ ∈ ((canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantForest
          ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z)).elements
        ↔ x₂ ∈ forestDomain z)) :
    ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z).2
      ≠ (fun _ _ => Sum.inl true) := by
  intro hpL
  have hg : ResolvedCoassocSplitChoice.selectedOuterContractGraph
        ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z)
      = z.1.1.contractWithStars (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G z.1.1) := by
    rw [ResolvedCoassocSplitChoice.selectedOuterContractGraph,
      canonicalMultiStar_alpha_houter VBuild ValueGeometry OccRaw Split z]
  have hcard := finset_card_eq_of_heq (congrArg ResolvedFeynmanSubgraph hg)
    (canonicalMultiStar_alpha_quotient_elements_heq VBuild ValueGeometry OccRaw Split z survivor_mem remnant_mem)
  set q := (canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z
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

/-- **R-6c-body-492 — the canonical alpha recovered-preimage membership supply.**  `forest_nonempty` is the geometric
input; the two mixed exclusions are the body-492 theorems above. -/
noncomputable def canonicalMultiStarRecoveredPreimageAlphaValueMemSupply
    (forest_nonempty : ∀ {G : ResolvedFeynmanGraph}
      (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G),
      resolvedIsForestImage z.1 z.2 →
      ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).Closure.Assembly.Region.forestRecovered z).elements.Nonempty)
    (survivor_mem : ∀ {G : ResolvedFeynmanGraph}
      (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G)
      (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
        ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z)))
      (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars
        (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G z.1.1))),
      HEq x₁ x₂ →
      (x₁ ∈ ((survivorSupply_of_measure VBuild.Measure G).rightSurvivorForest
          ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z)).elements
        ↔ x₂ ∈ rightDomain z))
    (remnant_mem : ∀ {G : ResolvedFeynmanGraph}
      (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G)
      (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
        ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z)))
      (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars
        (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G z.1.1))),
      HEq x₁ x₂ →
      (x₁ ∈ ((canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantForest
          ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z)).elements
        ↔ x₂ ∈ forestDomain z)) :
    ResolvedRecoveredPreimageAlphaValueMemSupply Fmem VBuild.toCanonicalFilteredValue where
  Tags := canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split
  forest_nonempty := fun {_G} z h => forest_nonempty z h
  mixed_ne_pR := fun {_G} z _ => mixed_ne_pR_alpha VBuild ValueGeometry OccRaw Split z
  mixed_ne_pL := fun {_G} z _ =>
    mixed_ne_pL_alpha VBuild ValueGeometry OccRaw Split z (survivor_mem z) (remnant_mem z)

/-- **R-6c-body-492 ∎ — the filtered `ForestIdx` HEq, upgraded from the body-491 raw elements HEq.**  On the genuine
filtered witness `qz := Data.recoveredFilteredPreimageAlphaValue z`, `HEq (V.quotientForestRaw qz) z.2`, via
`heq_forestIdx` fed `houter` (body-490) + the body-491 elements HEq (`(V.quotientForestRaw qz).1 =
canonicalCorrectedQuotientRaw … qz.1` by DEFEQ). -/
theorem canonicalMultiStar_alpha_forward_quotient
    (forest_nonempty : ∀ {G : ResolvedFeynmanGraph}
      (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G),
      resolvedIsForestImage z.1 z.2 →
      ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).Closure.Assembly.Region.forestRecovered z).elements.Nonempty)
    (survivor_mem : ∀ {G : ResolvedFeynmanGraph}
      (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G)
      (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
        ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z)))
      (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars
        (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G z.1.1))),
      HEq x₁ x₂ →
      (x₁ ∈ ((survivorSupply_of_measure VBuild.Measure G).rightSurvivorForest
          ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z)).elements
        ↔ x₂ ∈ rightDomain z))
    (remnant_mem : ∀ {G : ResolvedFeynmanGraph}
      (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G)
      (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
        ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z)))
      (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars
        (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G z.1.1))),
      HEq x₁ x₂ →
      (x₁ ∈ ((canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantForest
          ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z)).elements
        ↔ x₂ ∈ forestDomain z))
    {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G) :
    HEq (VBuild.toCanonicalFilteredValue.quotientForestRaw
        ((canonicalMultiStarRecoveredPreimageAlphaValueMemSupply VBuild ValueGeometry OccRaw Split
          forest_nonempty survivor_mem remnant_mem).recoveredFilteredPreimageAlphaValue z))
      z.2 :=
  heq_forestIdx _ z.2
    (canonicalMultiStar_alpha_houter VBuild ValueGeometry OccRaw Split z)
    (canonicalMultiStar_alpha_quotient_elements_heq VBuild ValueGeometry OccRaw Split z
      (survivor_mem z) (remnant_mem z))

end GaugeGeometry.QFT.Combinatorial
