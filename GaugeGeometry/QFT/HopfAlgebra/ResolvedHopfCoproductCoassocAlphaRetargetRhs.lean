import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaContractFieldScope

/-!
# R-6c-body-525 — corrected retarget RHS coordinate + sector forward-value bank (PROVED)

Five-hundred-and-twenty-fifth genuine-body step — the verified foundation for the `retargetVertex_eq_on_G` coordinate
calculation.  Two banks:

1. **The RHS coordinate + membership** — the on-`G` retarget equation's RHS is the two-step domain coordinate
   `CQ.retargetVertex correctedStar (selectedOuterVertexDomain q v)`; `correctedRetargetRhs` names it and
   `correctedRetargetRhs_mem` places it in the corrected two-stage graph `G₂` (both `∀ v ∈ G.vertices`, NEVER `∀ v`).

2. **The sector forward-value lemmas** (the equiv-composition "type mountain") — `canonicalCorrectedQuotientStarVertexEquiv`
   evaluated on a right-primitive (resp. forest-choice) one-stage star is `correctedStar` of the corresponding
   survivor (resp. corrected-remnant) component.  Both close by unfolding the sector equiv chain
   (`quotientStarEquiv → quotientDomainEquiv → sumCongr → right/forest equiv → codomainEquiv.symm → two-stage recover.symm`)
   and `rfl` — the forward map never touches an image-witness `choose`.

The four correspondence-coordinate route lemmas + aggregate + socket discharge follow (next body) and reuse these directly.

Per the HALT/guards: `hv : v ∈ G.vertices` stays in the binder (NO `∀ v`); only the RHS coordinate + membership + the two
sector forward values are entered; the route lemmas / aggregate / socket are NOT inhabited; the inverse/`choose` side of the
sector equivs is NOT expanded; strict `StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc claim.  No facade, no
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
set_option maxHeartbeats 3200000

variable {G : ResolvedFeynmanGraph}
  (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G)

/-! ## Bank 1 — the RHS coordinate + membership -/

/-- **R-6c-body-525 — the corrected retarget RHS coordinate** (the two-step domain contraction). -/
noncomputable def correctedRetargetRhs
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (v : VertexId) : VertexId :=
  (canonicalCorrectedQuotientRaw Measure
      canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
      canonicalUniqueStarFactsOfW' q.1).retargetVertex
    (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
      (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
      (canonicalCorrectedQuotientRaw Measure
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
        canonicalUniqueStarFactsOfW' q.1))
    (selectedOuterVertexDomain q v)

/-- **R-6c-body-525 ∎ — the RHS coordinate lands in the corrected two-stage graph** (`∀ v ∈ G.vertices`). -/
theorem correctedRetargetRhs_mem
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    {v : VertexId} (hv : v ∈ G.vertices) :
    correctedRetargetRhs q Measure v
      ∈ ((canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1).contractWithStars
        (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
          (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
          (canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1))).vertices :=
  ResolvedAdmissibleSubgraph.retargetVertex_mem_contractWithStars_vertices _ _
    (ResolvedAdmissibleSubgraph.retargetVertex_mem_contractWithStars_vertices _ _ hv)

/-! ## Bank 2 — the sector forward-value lemmas -/

/-- **R-6c-body-525 ∎ — the right-primitive sector forward value.**  On a right one-stage star the quotient-star vertex
equiv is `correctedStar` of the right survivor component. -/
theorem canonicalCorrectedQuotientStarVertexEquiv_right
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    (i : OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1) (hR : i.isRight) :
    (canonicalCorrectedQuotientStarVertexEquiv Measure E q ⟨i, Or.inl hR⟩).1
      = canonicalUniqueSupportedCarrierProperSupply.toData.starOf
          (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
          (canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1)
          ((survivorSupply_of_measure Measure G).survivorComponent q.1
            (RightPrimitiveIndex.toRightComponent ⟨i, hR⟩)) := by
  simp only [canonicalCorrectedQuotientStarVertexEquiv, canonicalCorrectedQuotientStarEquiv,
    ResolvedCanonicalFilteredQuotientSectorEquivSupply.quotientStarEquiv,
    canonicalCorrectedQuotientSectorEquivSupply, Equiv.trans_apply, Equiv.sumCongr_apply,
    quotientDomainEquiv, Equiv.coe_fn_mk, dif_pos hR, Sum.map_inl,
    ResolvedCanonicalFilteredQuotientSectorEquivSupply.codomainEquiv,
    canonicalCorrectedRightSectorEquiv, Equiv.symm_trans_apply]
  rfl

/-- **R-6c-body-525 ∎ — the forest-choice sector forward value.**  On a forest one-stage star the quotient-star vertex
equiv is `correctedStar` of the corrected-remnant component. -/
theorem canonicalCorrectedQuotientStarVertexEquiv_forest
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    (i : OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1) (hF : i.isForest) :
    (canonicalCorrectedQuotientStarVertexEquiv Measure E q ⟨i, Or.inr hF⟩).1
      = canonicalUniqueSupportedCarrierProperSupply.toData.starOf
          (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
          (canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1)
          ((canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
              canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1
            (ResolvedCoassocSplitChoice.forestComponentOccurrence q.1
              (forestPrimitiveIndexEquivComponents q.1 ⟨i, hF⟩))) := by
  have hnR : ¬ i.isRight := fun hR => ResolvedCoassocSplitChoice.not_isForestChoice_of_isRightPrimitive hR hF
  simp only [canonicalCorrectedQuotientStarVertexEquiv, canonicalCorrectedQuotientStarEquiv,
    ResolvedCanonicalFilteredQuotientSectorEquivSupply.quotientStarEquiv,
    canonicalCorrectedQuotientSectorEquivSupply, Equiv.trans_apply, Equiv.sumCongr_apply,
    quotientDomainEquiv, Equiv.coe_fn_mk, dif_neg hnR, Sum.map_inr,
    ResolvedCanonicalFilteredQuotientSectorEquivSupply.codomainEquiv,
    canonicalCorrectedForestSectorEquiv, Equiv.symm_trans_apply]
  rfl

end GaugeGeometry.QFT.Combinatorial
