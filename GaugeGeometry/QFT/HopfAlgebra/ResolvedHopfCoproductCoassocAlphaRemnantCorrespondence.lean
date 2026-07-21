import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSurvivorForestNonempty
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRawCorrectedRoundTrip
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantCollection
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestTagPartition

/-!
# R-6c-body-495 — the final remnant correspondence: `remnant_mem` DERIVED, membership geometry front CLOSED (PROVED)

Four-hundred-and-ninety-fifth genuine-body step — the LAST membership geometry.  Body-359's remnant collection is mirrored
to the alpha / corrected-raw root: the corrected-remnant round-trip (body-489, raw + membership-free) supplies the
component `hround` (its `hConn` / `hPos` derived inline from `z.2`'s live carrier properness), the `OccInv` gives the
occurrence index transport, and the body-490 `houter` aligns the ambient — closing the two-direction `remnant_mem` membership
bridge, hence the collection HEq, hence the LAST geometric input of the canonical alpha round-trip leaf.

* `ResolvedRegionTagAlphaValueSupply.mem_forestComponents_iff_alpha` (body-348) — the forest-choice tag characterization;
* `ResolvedRegionTagAlphaValueSupply.remnant_mem_alpha` (body-359's inner bridge) — the two-direction membership bridge, the
  `hround` inlined from body-489;
* `canonicalMultiStar_alpha_remnant_mem` — the body-494-required `remnant_mem` at the canonical tags;
* `canonicalMultiStar_alpha_remnantForest_elements_heq` — the collection HEq corollary (`heq_finset_of_mem_iff`);
* `canonicalMultiStarAlphaRoundTripLeafSupply_closed` / `coassoc_gen_of_canonicalMultiStar_alpha_closed` — the round-trip
  leaf / native `W'` coassoc with EVERY geometry proof-leaf DERIVED (only `VBuild` / `ValueGeometry` / `OccRaw` / `Split` /
  `Fmem` construction inputs + `rep` remain).

Per the HALT/guards: the filtered `Data` / `qz` are NOT used in the remnant proof; nothing is back-computed from the forward
quotient HEq; the old uncorrected `Remnant` is NOT used; NO `corrected = uncorrected` graph equality; NO permutation
equality; `hConn` / `hPos` are NOT new leaves (derived from `z.2` properness); strict `StarProm` / `InnerStarRaw` stay ZERO;
body-445 stays a valid conditional.  NOT the unconditional theorem (the construction inputs remain).  No facade, no flat
term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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
set_option maxHeartbeats 1600000

namespace ResolvedRegionTagAlphaValueSupply

variable {Fmem : ResolvedSelectedOuterFilteredMemSupply D}
  {V : ResolvedFilteredConcreteSummandValueSupply D}

/-- **R-6c-body-495 — the forest-choice components of the reconstruction are the forest region** (body-348, alpha). -/
theorem mem_forestComponents_iff_alpha (T : ResolvedRegionTagAlphaValueSupply Fmem V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Closure.unionOuterAlphaValue z).1.elements}) :
    γ ∈ ResolvedCoassocSplitChoice.forestComponents (T.recoveredPreimageAlphaValue z)
      ↔ γ.1 ∈ (T.Closure.Assembly.Region.forestRecovered z).elements := by
  constructor
  · intro h
    rw [ResolvedCoassocSplitChoice.forestComponents] at h
    obtain ⟨B, hB⟩ := (Finset.mem_filter.mp h).2
    rcases (T.Closure.mem_unionOuterAlphaValue_iff z γ.1).mp γ.2 with hl | hr | hf
    · exact absurd (((T.choiceAt_recovered_alpha_eq z γ).trans (T.left_tag_alpha z γ hl)).symm.trans hB)
        Sum.inl_ne_inr
    · exact absurd (((T.choiceAt_recovered_alpha_eq z γ).trans (T.right_tag_alpha z γ hr)).symm.trans hB)
        Sum.inl_ne_inr
    · exact hf
  · intro h
    rw [ResolvedCoassocSplitChoice.forestComponents]
    refine Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, ?_⟩
    obtain ⟨B, hB⟩ := T.forest_tag_alpha z γ h
    exact ⟨B, (T.choiceAt_recovered_alpha_eq z γ).trans hB⟩

/-- **R-6c-body-495 — the remnant membership bridge** (body-359's inner bridge, alpha; `hround` inlined from body-489's raw
corrected round-trip). -/
theorem remnant_mem_alpha (M : ResolvedMultiStarDecontractionSupply D) (Fstar : ResolvedCanonicalStarFacts D)
    (S : ResolvedForestOccurrenceInversionSupply M) (CarrierProper : ResolvedCarrierProperProvider D)
    (T : ResolvedRegionTagAlphaValueSupply Fmem V) {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf
      (T.recoveredPreimageAlphaValue z) = z.1.1)
    (hForest : (T.Closure.Assembly.Region.forestRecovered z).elements
      = (M.forestRecoveredMulti Fstar z).elements)
    (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
      (T.recoveredPreimageAlphaValue z)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (hx : HEq x₁ x₂) :
    x₁ ∈ ((canonicalCorrectedRemnantComponentSupply Fstar CarrierProper).remnantForest
        (T.recoveredPreimageAlphaValue z)).elements
      ↔ x₂ ∈ forestDomain z := by
  have hround : ∀ (γ : {x : {y : ResolvedFeynmanSubgraph G //
        y ∈ (T.recoveredPreimageAlphaValue z).1.1.elements} // x ∈
        ResolvedCoassocSplitChoice.forestComponents (T.recoveredPreimageAlphaValue z)})
      (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) //
        x ∈ forestDomain z}),
      (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageAlphaValue z) γ).γ.1 = M.parent z δ →
      HEq (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageAlphaValue z) γ).B (M.innerIdx z δ) →
      HEq ((canonicalCorrectedRemnantComponentSupply Fstar CarrierProper).remnantComponent
        (T.recoveredPreimageAlphaValue z)
        (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageAlphaValue z) γ)) δ.1 := by
    intro γ δ hp hi
    have hConn : (touchedLocalComponent z δ.1).forget.IsConnected :=
      (touchedLocalComponent_isConnectedDivergent z δ.1
        (z.2.1.isConnectedDivergent δ.1 (Finset.mem_filter.mp δ.2).1)).1
    have hPos : 0 < (touchedLocalComponent z δ.1).internalEdges.card := by
      rw [touchedLocalComponent_internalEdges]
      exact (CarrierProper.carrier_isProperForest _ z.2.1 z.2.2).2.2.2.1 δ.1
        (Finset.mem_filter.mp δ.2).1
    exact canonicalCorrectedRemnantComponent_roundtrip_raw M z δ (T.recoveredPreimageAlphaValue z)
      (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageAlphaValue z) γ) Fstar
      hp hi hConn hPos houter
  constructor
  · intro hx₁
    rw [ResolvedRemnantComponentSupply.remnantForest_elements] at hx₁
    obtain ⟨γ, -, hγ⟩ := Finset.mem_image.mp hx₁
    have hfr : γ.1.1 ∈ (M.forestRecoveredMulti Fstar z).elements := by
      rw [← hForest]; exact (T.mem_forestComponents_iff_alpha z γ.1).mp γ.2
    have hp : M.parent z (M.forestSource Fstar z ⟨γ.1.1, hfr⟩) = γ.1.1 :=
      M.forestSource_spec Fstar z ⟨γ.1.1, hfr⟩
    have hi : HEq (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageAlphaValue z) γ).B
        (M.innerIdx z (M.forestSource Fstar z ⟨γ.1.1, hfr⟩)) :=
      (M.innerIdx_occurrence S z (M.forestSource Fstar z ⟨γ.1.1, hfr⟩) (T.recoveredPreimageAlphaValue z)
        (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageAlphaValue z) γ) hp).symm
    have hheq := hround γ (M.forestSource Fstar z ⟨γ.1.1, hfr⟩) hp.symm hi
    rw [hγ] at hheq
    have hx₂eq : x₂ = (M.forestSource Fstar z ⟨γ.1.1, hfr⟩).1 := eq_of_heq (hx.symm.trans hheq)
    rw [hx₂eq]; exact (M.forestSource Fstar z ⟨γ.1.1, hfr⟩).2
  · intro hx₂
    have hmemMulti : M.parent z ⟨x₂, hx₂⟩ ∈ (M.forestRecoveredMulti Fstar z).elements := by
      rw [M.forestRecoveredMulti_elements Fstar z]
      exact Finset.mem_image.mpr ⟨⟨x₂, hx₂⟩, Finset.mem_attach _ _, rfl⟩
    have hfrec : M.parent z ⟨x₂, hx₂⟩ ∈ (T.Closure.Assembly.Region.forestRecovered z).elements := by
      rw [hForest]; exact hmemMulti
    have hmemU : M.parent z ⟨x₂, hx₂⟩ ∈ (T.Closure.unionOuterAlphaValue z).1.elements :=
      (T.Closure.mem_unionOuterAlphaValue_iff z _).mpr (Or.inr (Or.inr hfrec))
    have hfc : (⟨M.parent z ⟨x₂, hx₂⟩, hmemU⟩ :
        {y : ResolvedFeynmanSubgraph G // y ∈ (T.recoveredPreimageAlphaValue z).1.1.elements})
        ∈ ResolvedCoassocSplitChoice.forestComponents (T.recoveredPreimageAlphaValue z) :=
      (T.mem_forestComponents_iff_alpha z ⟨M.parent z ⟨x₂, hx₂⟩, hmemU⟩).mpr hfrec
    set γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ (T.recoveredPreimageAlphaValue z).1.1.elements} //
        x ∈ ResolvedCoassocSplitChoice.forestComponents (T.recoveredPreimageAlphaValue z)} :=
      ⟨⟨M.parent z ⟨x₂, hx₂⟩, hmemU⟩, hfc⟩ with hγdef
    have hi : HEq (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageAlphaValue z) γ).B
        (M.innerIdx z ⟨x₂, hx₂⟩) :=
      (M.innerIdx_occurrence S z ⟨x₂, hx₂⟩ (T.recoveredPreimageAlphaValue z)
        (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageAlphaValue z) γ) rfl).symm
    have hheq := hround γ ⟨x₂, hx₂⟩ rfl hi
    have hx₁eq : x₁ = (canonicalCorrectedRemnantComponentSupply Fstar CarrierProper).remnantComponent
        (T.recoveredPreimageAlphaValue z)
        (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageAlphaValue z) γ) :=
      eq_of_heq (hx.trans hheq.symm)
    rw [hx₁eq, ResolvedRemnantComponentSupply.remnantForest_elements]
    exact Finset.mem_image.mpr ⟨γ, Finset.mem_attach _ _, rfl⟩

end ResolvedRegionTagAlphaValueSupply

variable {Fmem : ResolvedSelectedOuterFilteredMemSupply canonicalUniqueSupportedCarrierProperSupply.toData}
  (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
  (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
  (OccRaw : ResolvedForestOccurrenceInversionValueSupply ValueGeometry.toCoreBuild.toValueCore)
  (Split : ResolvedAlphaValueQuotientRegionSplitSupply Fmem VBuild.toCanonicalFilteredValue)

include VBuild ValueGeometry OccRaw Split

/-- **R-6c-body-495 — `remnant_mem`, DERIVED** (at the canonical tags; `M` / `OccInv` / `Fstar` / `CarrierProper` canonical,
`houter` = body-490, `hForest` = `rfl`). -/
theorem canonicalMultiStar_alpha_remnant_mem {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G)
    (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
      ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G z.1.1)))
    (hx : HEq x₁ x₂) :
    x₁ ∈ ((canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantForest
        ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z)).elements
      ↔ x₂ ∈ forestDomain z :=
  (canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).remnant_mem_alpha
    (ValueGeometry.toCoreBuild.toValueCore.toDecontractionSupply
      (canonicalUniqueInnerRawCarrierClosureSupply ValueGeometry.toCoreBuild.toValueCore))
    canonicalUniqueStarFactsOfW'
    (ValueGeometry.toCoreBuild.toValueCore.toForestOccurrenceInversionSupply
      (canonicalUniqueInnerRawCarrierClosureSupply ValueGeometry.toCoreBuild.toValueCore) OccRaw)
    canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
    z (canonicalMultiStar_alpha_houter VBuild ValueGeometry OccRaw Split z) rfl x₁ x₂ hx

/-- **R-6c-body-495 — the remnant collection HEq** (banked; `heq_finset_of_mem_iff` of the membership bridge). -/
theorem canonicalMultiStar_alpha_remnantForest_elements_heq {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G) :
    HEq ((canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantForest
        ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z)).elements
      (forestDomain z) :=
  heq_finset_of_mem_iff (canonicalMultiStar_alpha_houter VBuild ValueGeometry OccRaw Split z)
    (fun x₁ x₂ hx => canonicalMultiStar_alpha_remnant_mem VBuild ValueGeometry OccRaw Split z x₁ x₂ hx)

/-- **R-6c-body-495 — the CLOSED round-trip leaf** (every geometry proof-leaf DERIVED). -/
noncomputable def canonicalMultiStarAlphaRoundTripLeafSupply_closed :
    ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply Fmem VBuild.toCanonicalFilteredValue :=
  canonicalMultiStarAlphaRoundTripLeafSupply_of_remnant_mem VBuild ValueGeometry OccRaw Split
    (fun {_G} z x₁ x₂ hx => canonicalMultiStar_alpha_remnant_mem VBuild ValueGeometry OccRaw Split z x₁ x₂ hx)

/-- **R-6c-body-495 ∎ — native `W'` `Δᵣ`-coassociativity, ALL geometry proof-leaves DERIVED.**  Only the construction
inputs (`VBuild` / `ValueGeometry` / `OccRaw` / `Split` / `Fmem`) and the representatives (`rep` / `repCD` / `rep_gen`)
remain — the full alpha-native conditional replacement of body-445, with strict cross-ambient sockets ZERO. -/
theorem coassoc_gen_of_canonicalMultiStar_alpha_closed
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x))
    (x : ResolvedHopfGen) :
    canonicalUniqueSupportedCarrierProperSupply.toData.coassocLeft (MvPolynomial.X x)
      = canonicalUniqueSupportedCarrierProperSupply.toData.coassocRight (MvPolynomial.X x) :=
  coassoc_gen_of_canonicalMultiStar_alpha_of_remnant_mem VBuild ValueGeometry OccRaw Split
    (fun {_G} z x₁ x₂ hx => canonicalMultiStar_alpha_remnant_mem VBuild ValueGeometry OccRaw Split z x₁ x₂ hx)
    rep repCD rep_gen x

end GaugeGeometry.QFT.Combinatorial
