import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaHouter
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRawCorrectedRoundTrip
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientPartitionMulti

/-!
# R-6c-body-491 — the pre-membership raw quotient elements HEq (cycle cut) (PROVED)

Four-hundred-and-ninety-first genuine-body step — the decisive cut of the membership cycle.  The membership-free raw
quotient value `canonicalCorrectedQuotientRaw` (body-469) has its ELEMENTS heterogeneously equal to `z.2.1.elements`,
assembled from the alpha `houter` (body-490) + the survivor / remnant membership bridges, with the corrected remnant
round-trip available in raw form (body-489).  `V.quotientForestRaw` / `V.union_eq` are NEVER used; no filtered witness `qz`
is issued.

The membership bridges (`survivor_mem` / `remnant_mem`) are the irreducible geometric data (as in the total root's
body-206/208 and the alpha body-478 fields): the survivor forest of `s` corresponds to `rightDomain z` (the star-avoiding
half), the corrected remnant forest to `forestDomain z` (the star-touching half — where the body-489 raw `hround` supplies
the occurrence↔`δ` transport).  This body ASSEMBLES them with `houter` into the elements HEq via `heq_of_membership_split`,
splitting the left value by the DEFINITIONAL `canonicalCorrectedQuotientRaw = survivor ∪ remnant` and the right value by
`rightDomain_union_forestDomain`.

* `canonicalCorrectedQuotient_elements_heq` — the raw quotient elements HEq (generic `s` / `z` / bridges);
* `canonicalCorrectedQuotient_elements_card` — the `.elements.card` equality corollary (banked for body-492's `p_L`
  no-go);
* `canonicalMultiStar_alpha_quotient_elements_heq` — the canonical specialization at
  `s := Tags.recoveredPreimageAlphaValue z` with `houter := canonicalMultiStar_alpha_houter` (body-490).

Per the HALT/guards: `V.quotientForestRaw` / `V.union_eq` NOT used; no filtered `qz` issued; `ResolvedRecoveredPreimage
AlphaValueMemSupply` NOT assumed; NOT lifted to `heq_forestIdx`; the mixed `p_R` / `p_L` exclusions are NOT mixed in; strict
`StarProm` / `InnerStarRaw` NOT restored; body-445 stays a valid conditional.  NOT the unconditional theorem.  No facade,
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

variable {D : ResolvedCoproductProperForestData}
  (Measure : ResolvedMeasureLeafSupply D) (CarrierProper : ResolvedCarrierProperProvider D)
  (Fstar : ResolvedCanonicalStarFacts D)

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-- **R-6c-body-491 ∎ — the raw quotient elements HEq.**  The membership-free `canonicalCorrectedQuotientRaw`'s elements are
heterogeneously equal to `z.2.1.elements`, from `houter` + the survivor / remnant membership bridges. -/
theorem canonicalCorrectedQuotient_elements_heq {G : ResolvedFeynmanGraph}
    (s : ResolvedCoassocSplitChoice D G) (z : ForestBlockCodType D G)
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s = z.1.1)
    (survivor_mem : ∀ (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph s))
      (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
      HEq x₁ x₂ →
      (x₁ ∈ ((survivorSupply_of_measure Measure G).rightSurvivorForest s).elements ↔ x₂ ∈ rightDomain z))
    (remnant_mem : ∀ (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph s))
      (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
      HEq x₁ x₂ →
      (x₁ ∈ ((canonicalCorrectedRemnantComponentSupply Fstar CarrierProper).remnantForest s).elements
        ↔ x₂ ∈ forestDomain z)) :
    HEq (canonicalCorrectedQuotientRaw Measure CarrierProper Fstar s).elements z.2.1.elements := by
  refine heq_of_membership_split houter
    (Q := (canonicalCorrectedQuotientRaw Measure CarrierProper Fstar s).elements)
    (Z := z.2.1.elements)
    (surv := ((survivorSupply_of_measure Measure G).rightSurvivorForest s).elements)
    (rem := ((canonicalCorrectedRemnantComponentSupply Fstar CarrierProper).remnantForest s).elements)
    (rightDom := rightDomain z) (forestDom := forestDomain z)
    ?_ ?_
    (heq_finset_of_mem_iff houter survivor_mem)
    (heq_finset_of_mem_iff houter remnant_mem)
  · intro x
    show x ∈ (canonicalCorrectedQuotientRaw Measure CarrierProper Fstar s).elements ↔ _
    rw [canonicalCorrectedQuotientRaw, ResolvedAdmissibleSubgraph.union_elements]
    convert Finset.mem_union using 2
  · intro x
    simp only [rightDomain, forestDomain, Finset.mem_filter]
    tauto

/-- **R-6c-body-491 ∎ — the canonical specialization.**  The raw quotient elements HEq at `s := Tags.recoveredPreimage
AlphaValue z` with the body-490 `houter`; the survivor / remnant bridges remain the geometric inputs. -/
theorem canonicalMultiStar_alpha_quotient_elements_heq
    {Fmem : ResolvedSelectedOuterFilteredMemSupply canonicalUniqueSupportedCarrierProperSupply.toData}
    (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
    (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
    (OccRaw : ResolvedForestOccurrenceInversionValueSupply ValueGeometry.toCoreBuild.toValueCore)
    (Split : ResolvedAlphaValueQuotientRegionSplitSupply Fmem VBuild.toCanonicalFilteredValue)
    {G : ResolvedFeynmanGraph}
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
    HEq (canonicalCorrectedQuotientRaw VBuild.Measure
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider canonicalUniqueStarFactsOfW'
        ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z)).elements
      z.2.1.elements :=
  canonicalCorrectedQuotient_elements_heq VBuild.Measure
    canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider canonicalUniqueStarFactsOfW'
    ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z) z
    (canonicalMultiStar_alpha_houter VBuild ValueGeometry OccRaw Split z)
    survivor_mem remnant_mem

end GaugeGeometry.QFT.Combinatorial
