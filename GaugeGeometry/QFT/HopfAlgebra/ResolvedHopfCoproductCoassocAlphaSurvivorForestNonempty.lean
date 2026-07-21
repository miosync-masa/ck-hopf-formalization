import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaForestValueEq
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSurvivorCollection
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSurvivorTagPartition
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestNonemptyLeaf

/-!
# R-6c-body-494 — residual 3→1: `forest_nonempty` + `survivor_mem` DERIVED, only `remnant_mem` left (PROVED)

Four-hundred-and-ninety-fourth genuine-body step — collapsing the three residual geometry bridges to ONE.  `forest_
nonempty` is the shallow body-312 theorem at the canonical alpha `Region` (`rfl` wiring); `survivor_mem` is the body-345/
346/347 z-local survivor round-trip mirrored to the alpha tags (no `Data` / `qz` / quotient HEq, no corrected remnant
geometry); the remaining `remnant_mem` is banked as the single honest input.

* `canonicalMultiStar_alpha_forest_nonempty` — body-312 at the canonical `Region`;
* `ResolvedRegionTagAlphaValueSupply.mem_rightComponents_iff_alpha` (body-345) / `rightSurvivor_roundtrip_alpha`
  (body-346) / `survivor_mem_alpha` (body-347's inner membership bridge) — the z-local survivor correspondence;
* `canonicalMultiStar_alpha_survivor_mem` — the body-491/492-required survivor membership bridge, at the canonical tags
  (`houter` = body-490, `hRight` = the body-483 right-bridge anchor `rfl`);
* `canonicalMultiStarAlphaRoundTripLeafSupply_of_remnant_mem` / `coassoc_gen_of_canonicalMultiStar_alpha_of_remnant_mem` —
  the thin constructor / coassoc taking ONLY `remnant_mem`.

Per the HALT/guards: the body-492 `Data` / filtered `qz` are NOT used in the survivor proof; nothing is back-computed from
the forward quotient HEq; the survivor proof reads NO corrected remnant geometry; `forest_nonempty` is NOT re-wrapped as a
field; the body-489 raw `hround` is preserved for the body-495 remnant front; strict `StarProm` / `InnerStarRaw` stay ZERO;
body-445 stays a valid conditional.  NOT the unconditional theorem.  No facade, no flat term, no `forgetHopf`, no rep/perm,
and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-494 — the right-primitive components of the reconstruction are the right region** (body-345, alpha). -/
theorem mem_rightComponents_iff_alpha (T : ResolvedRegionTagAlphaValueSupply Fmem V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Closure.unionOuterAlphaValue z).1.elements}) :
    γ ∈ ResolvedCoassocSplitChoice.rightComponents (T.recoveredPreimageAlphaValue z)
      ↔ γ.1 ∈ (T.Closure.Assembly.Region.rightRecovered z).elements := by
  constructor
  · intro h
    rw [ResolvedCoassocSplitChoice.rightComponents] at h
    have hp : ResolvedCoassocSplitChoice.choiceAt (T.recoveredPreimageAlphaValue z) γ = Sum.inl false :=
      (Finset.mem_filter.mp h).2
    rcases (T.Closure.mem_unionOuterAlphaValue_iff z γ.1).mp γ.2 with hl | hr | hf
    · exact absurd (Sum.inl.inj
        (hp.symm.trans ((T.choiceAt_recovered_alpha_eq z γ).trans (T.left_tag_alpha z γ hl)))) (by decide)
    · exact hr
    · obtain ⟨B, hB⟩ := T.forest_tag_alpha z γ hf
      exact absurd (hp.symm.trans ((T.choiceAt_recovered_alpha_eq z γ).trans hB)) Sum.inl_ne_inr
  · intro h
    rw [ResolvedCoassocSplitChoice.rightComponents]
    refine Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, ?_⟩
    show ResolvedCoassocSplitChoice.choiceAt (T.recoveredPreimageAlphaValue z) γ = Sum.inl false
    rw [T.choiceAt_recovered_alpha_eq z γ]
    exact T.right_tag_alpha z γ h

/-- **R-6c-body-494 — the survivor round-trip** (body-346, alpha). -/
theorem rightSurvivor_roundtrip_alpha (Measure : ResolvedMeasureLeafSupply D)
    (T : ResolvedRegionTagAlphaValueSupply Fmem V) {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf
      (T.recoveredPreimageAlphaValue z) = z.1.1)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ rightDomain z})
    (γ : {y : {x : ResolvedFeynmanSubgraph G // x ∈ (T.recoveredPreimageAlphaValue z).1.1.elements} //
      y ∈ ResolvedCoassocSplitChoice.rightComponents (T.recoveredPreimageAlphaValue z)})
    (hγ : γ.1.1 = rightReembed z δ) :
    HEq ((survivorSupply_of_measure Measure G).survivorComponent (T.recoveredPreimageAlphaValue z) γ) δ.1 := by
  refine subgraph_heq_of_data
    (congrArg (fun A => A.contractWithStars (D.starOf G A)) houter) _ δ.1 ?_ ?_ ?_
  · show γ.1.1.vertices = δ.1.vertices
    rw [hγ]; exact rightReembed_vertices z δ
  · show γ.1.1.internalEdges = δ.1.internalEdges
    rw [hγ]; rfl
  · show γ.1.1.externalLegs = δ.1.externalLegs
    rw [hγ]; rfl

/-- **R-6c-body-494 — the survivor membership bridge** (body-347's inner bridge, alpha; the body-491/492-required shape). -/
theorem survivor_mem_alpha (Measure : ResolvedMeasureLeafSupply D)
    (T : ResolvedRegionTagAlphaValueSupply Fmem V) {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf
      (T.recoveredPreimageAlphaValue z) = z.1.1)
    (hRight : (T.Closure.Assembly.Region.rightRecovered z).elements
      = (rightDomain z).attach.image (rightReembed z))
    (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
      (T.recoveredPreimageAlphaValue z)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (hx : HEq x₁ x₂) :
    x₁ ∈ ((survivorSupply_of_measure Measure G).rightSurvivorForest
        (T.recoveredPreimageAlphaValue z)).elements
      ↔ x₂ ∈ rightDomain z := by
  constructor
  · intro hx₁
    rw [ResolvedRightSurvivorSupply.rightSurvivorForest_elements] at hx₁
    obtain ⟨γa, -, hγa⟩ := Finset.mem_image.mp hx₁
    have hrr : γa.1.1 ∈ (T.Closure.Assembly.Region.rightRecovered z).elements :=
      (T.mem_rightComponents_iff_alpha z γa.1).mp γa.2
    rw [hRight] at hrr
    obtain ⟨δa, -, hδa⟩ := Finset.mem_image.mp hrr
    have hheq := T.rightSurvivor_roundtrip_alpha Measure z houter δa γa hδa.symm
    rw [hγa] at hheq
    have hx₂eq : x₂ = δa.1 := eq_of_heq (hx.symm.trans hheq)
    rw [hx₂eq]; exact δa.2
  · intro hx₂
    have hrr : rightReembed z ⟨x₂, hx₂⟩ ∈ (T.Closure.Assembly.Region.rightRecovered z).elements := by
      rw [hRight]; exact Finset.mem_image.mpr ⟨⟨x₂, hx₂⟩, Finset.mem_attach _ _, rfl⟩
    have hmemU : rightReembed z ⟨x₂, hx₂⟩ ∈ (T.Closure.unionOuterAlphaValue z).1.elements :=
      (T.Closure.mem_unionOuterAlphaValue_iff z _).mpr (Or.inr (Or.inl hrr))
    have hright : (⟨rightReembed z ⟨x₂, hx₂⟩, hmemU⟩ :
        {x : ResolvedFeynmanSubgraph G // x ∈ (T.recoveredPreimageAlphaValue z).1.1.elements})
        ∈ ResolvedCoassocSplitChoice.rightComponents (T.recoveredPreimageAlphaValue z) :=
      (T.mem_rightComponents_iff_alpha z ⟨rightReembed z ⟨x₂, hx₂⟩, hmemU⟩).mpr hrr
    have hheq := T.rightSurvivor_roundtrip_alpha Measure z houter ⟨x₂, hx₂⟩
      ⟨⟨rightReembed z ⟨x₂, hx₂⟩, hmemU⟩, hright⟩ rfl
    have hx₁eq : x₁ = (survivorSupply_of_measure Measure G).survivorComponent
        (T.recoveredPreimageAlphaValue z) ⟨⟨rightReembed z ⟨x₂, hx₂⟩, hmemU⟩, hright⟩ :=
      eq_of_heq (hx.trans hheq.symm)
    rw [hx₁eq, ResolvedRightSurvivorSupply.rightSurvivorForest_elements]
    exact Finset.mem_image.mpr ⟨⟨⟨rightReembed z ⟨x₂, hx₂⟩, hmemU⟩, hright⟩,
      Finset.mem_attach _ _, rfl⟩

end ResolvedRegionTagAlphaValueSupply

variable {Fmem : ResolvedSelectedOuterFilteredMemSupply canonicalUniqueSupportedCarrierProperSupply.toData}
  (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
  (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
  (OccRaw : ResolvedForestOccurrenceInversionValueSupply ValueGeometry.toCoreBuild.toValueCore)
  (Split : ResolvedAlphaValueQuotientRegionSplitSupply Fmem VBuild.toCanonicalFilteredValue)

/-- **R-6c-body-494 — `forest_nonempty`, DERIVED** (body-312 at the canonical alpha `Region`, `rfl` wiring). -/
theorem canonicalMultiStar_alpha_forest_nonempty {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G)
    (hz : resolvedIsForestImage z.1 z.2) :
    ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).Closure.Assembly.Region.forestRecovered z).elements.Nonempty :=
  forestRecovered_nonempty_of_resolvedIsForestImage _ hz

/-- **R-6c-body-494 — `survivor_mem`, DERIVED** (the z-local survivor bridge at the canonical tags; `houter` = body-490,
`hRight` = the body-483 right-bridge anchor `rfl`). -/
theorem canonicalMultiStar_alpha_survivor_mem {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G)
    (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
      ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G z.1.1)))
    (hx : HEq x₁ x₂) :
    x₁ ∈ ((survivorSupply_of_measure VBuild.Measure G).rightSurvivorForest
        ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z)).elements
      ↔ x₂ ∈ rightDomain z :=
  (canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).survivor_mem_alpha
    VBuild.Measure z (canonicalMultiStar_alpha_houter VBuild ValueGeometry OccRaw Split z) rfl x₁ x₂ hx

/-- **R-6c-body-494 — the thin round-trip leaf constructor taking ONLY `remnant_mem`.** -/
noncomputable def canonicalMultiStarAlphaRoundTripLeafSupply_of_remnant_mem
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
    ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply Fmem VBuild.toCanonicalFilteredValue :=
  canonicalMultiStarAlphaRoundTripLeafSupply VBuild ValueGeometry OccRaw Split
    (fun {_G} z hz => canonicalMultiStar_alpha_forest_nonempty VBuild ValueGeometry OccRaw Split z hz)
    (fun {_G} z x₁ x₂ hx => canonicalMultiStar_alpha_survivor_mem VBuild ValueGeometry OccRaw Split z x₁ x₂ hx)
    remnant_mem

/-- **R-6c-body-494 ∎ — native `W'` coassociativity taking ONLY `remnant_mem`.** -/
theorem coassoc_gen_of_canonicalMultiStar_alpha_of_remnant_mem
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
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x))
    (x : ResolvedHopfGen) :
    canonicalUniqueSupportedCarrierProperSupply.toData.coassocLeft (MvPolynomial.X x)
      = canonicalUniqueSupportedCarrierProperSupply.toData.coassocRight (MvPolynomial.X x) :=
  coassoc_gen_of_canonical_unique_alpha_roundtrip VBuild
    (canonicalMultiStarAlphaRoundTripLeafSupply_of_remnant_mem VBuild ValueGeometry OccRaw Split remnant_mem)
    rep repCD rep_gen x

end GaugeGeometry.QFT.Combinatorial
