import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaTwoStageSurvivorPartition
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaStarVertexRecover
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocStarVertexMap
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterSubset

/-!
# R-6c-body-522 — corrected q-local three-route maps (PROVED)

Five-hundred-and-twenty-second genuine-body step — turning body-521's partition into the corrected q-local three-route
`toFun` / `invFun` between the one-stage contract graph `G₁ := q.1.1.1.contractWithStars` and the corrected two-stage
contract graph `G₂ := correctedQuotient.contractWithStars` (body-513's `G₁` / `G₂`), plus every branch value lemma.  The
INVERSE LAWS are the next body.  The legacy `i.vertex = v` identity interface is NEVER used; the left forward value is
`targetLeftStar q i`.

## Helpers (Step 1)

* `correctedQuotient_gvertices_subset_inputOuter` — a corrected-quotient vertex that is in `G` sits in the input outer
  (survivor components ⊆ input outer; remnant survivor part ⊆ `o.γ` ⊆ input outer; remnant star part is fresh, so not in
  `G`);
* `correctedOriginalSurvivor_to` — an input-outer surviving vertex is a corrected-quotient surviving vertex
  (`selectedOuterRawOf_vertices_subset` for the stage-1 membership, the subset lemma for the quotient-avoidance).

## Maps (Steps 2/3)

* `correctedThreeRouteToFun` — source star → left (`targetLeftStar`) / non-left (`canonicalCorrectedQuotientStarVertexEquiv`)
  / source survivor → identity;
* `correctedThreeRouteInvFun` — target star → `canonicalCorrectedQuotientStarVertexEquiv.symm` (one-stage star vertex) /
  target survivor → input-outer survivor (identity) or (via body-521) a left index's star vertex.

## Branch value lemmas (Step 4)

`..._toFun_original` / `_left` / `_nonleft` and `..._invFun_star` / `_originalSurvivor` / `_left`, plus the recovery anchors
(`canonicalOneStageStarRecover` / `canonicalCorrectedQuotientStarVertexEquiv` round-trips) — the body-523 inverse-law
inputs.

Per the HALT/guards: `sourceLeftStar = targetLeftStar` is NOT required; the legacy three-route supply /
`twoStageSurvivor_cases` is NOT inhabited; NO raw `∀ s`; NO local-permutation comparison; the correspondence /
`left_inv` / `right_inv` / global `σ` / field equalities are NOT entered (next body); strict `StarProm` / `InnerStarRaw`
stay ZERO; NO unconditional-coassoc claim.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
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

variable {G : ResolvedFeynmanGraph}
  (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G)

/-! ## Step 1 — the two containment helpers -/

/-- **R-6c-body-522 ∎ — a corrected-quotient vertex that is in `G` sits in the input outer.** -/
theorem correctedQuotient_gvertices_subset_inputOuter
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    {v : VertexId}
    (hvQ : v ∈ (canonicalCorrectedQuotientRaw Measure
      canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
      canonicalUniqueStarFactsOfW' q.1).vertices)
    (hvG : v ∈ G.vertices) :
    v ∈ q.1.1.1.vertices := by
  obtain ⟨δ, hδ, hvδ⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hvQ
  simp only [canonicalCorrectedQuotientRaw, ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union] at hδ
  rcases hδ with hR | hM
  · rw [ResolvedRightSurvivorSupply.rightSurvivorForest_elements] at hR
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hR
    have hvr : v ∈ r.1.1.vertices := hvδ
    exact ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨r.1.1, r.1.2, hvr⟩
  · rw [ResolvedRemnantComponentSupply.remnantForest_elements] at hM
    obtain ⟨γ, -, rfl⟩ := Finset.mem_image.mp hM
    set o := ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 γ with ho
    rw [show ((canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1 o).vertices
          = (o.B.1.contractWithStars (promotedOccurrenceStar q.1 o)).vertices
        from correctedRemnantComponent_vertices_eq_promoted q.1 o canonicalUniqueStarFactsOfW',
      ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hvδ
    rcases hvδ with hsurv | hstar
    · exact ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨o.γ.1, o.γ.2, (Finset.mem_sdiff.mp hsurv).1⟩
    · exfalso
      obtain ⟨b, hb, hbeq⟩ := ResolvedAdmissibleSubgraph.mem_starVertices.mp hstar
      have hfresh := canonicalUniqueStarFactsOfW'.starOf_fresh G
        ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf q.1)
        (o.γ.1.promote b) (promote_mem_selectedOuterRawOf_raw q.1 o hb)
      rw [← hbeq] at hvG
      exact hfresh hvG

/-- **R-6c-body-522 ∎ — an input-outer surviving vertex is a corrected-quotient surviving vertex.** -/
theorem correctedOriginalSurvivor_to
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    {v : VertexId} (h : isContractSurvivingVertex q.1.1.1 v) :
    isContractSurvivingVertex (canonicalCorrectedQuotientRaw Measure
      canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
      canonicalUniqueStarFactsOfW' q.1) v := by
  obtain ⟨hvG, hvI⟩ := h
  refine ⟨?_, ?_⟩
  · rw [ResolvedCoassocSplitChoice.selectedOuterContractGraph,
      ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union]
    refine Or.inl (Finset.mem_sdiff.mpr ⟨hvG, fun hvS => hvI (selectedOuterRawOf_vertices_subset q.1 hvS)⟩)
  · exact fun hvQ => hvI (correctedQuotient_gvertices_subset_inputOuter q Measure hvQ hvG)

/-! ## Steps 2/3 — the two maps -/

/-- **R-6c-body-522 ∎ — the corrected three-route forward map.**  Source star → left `targetLeftStar` / non-left quotient
star; source survivor → identity. -/
noncomputable def correctedThreeRouteToFun
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H) :
    {v : VertexId // v ∈ (q.1.1.1.contractWithStars
        (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices} →
    {w : VertexId // w ∈ ((canonicalCorrectedQuotientRaw Measure
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
        canonicalUniqueStarFactsOfW' q.1).contractWithStars
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1))).vertices} :=
  fun p =>
    if hstar : isContractStarVertex q.1.1.1
        (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) p.1 then
      if hL : (canonicalOneStageStarRecover q ⟨p.1, hstar⟩).isLeft then
        ⟨targetLeftStar q (canonicalOneStageStarRecover q ⟨p.1, hstar⟩),
          surviving_mem_contractWithStars _ _
            (correctedLeftStar_toSurvivor q Measure (canonicalOneStageStarRecover q ⟨p.1, hstar⟩) hL)⟩
      else
        ⟨(canonicalCorrectedQuotientStarVertexEquiv Measure E q
            ⟨canonicalOneStageStarRecover q ⟨p.1, hstar⟩,
              (canonicalOneStageStarRecover q ⟨p.1, hstar⟩).isLeft_or_hasQuotientStar.resolve_left hL⟩).1,
          star_mem_contractWithStars _ _
            (canonicalCorrectedQuotientStarVertexEquiv Measure E q
              ⟨canonicalOneStageStarRecover q ⟨p.1, hstar⟩,
                (canonicalOneStageStarRecover q ⟨p.1, hstar⟩).isLeft_or_hasQuotientStar.resolve_left hL⟩).2⟩
    else
      ⟨p.1, surviving_mem_contractWithStars _ _
        (correctedOriginalSurvivor_to q Measure
          ((contractWithStars_vertex_cases q.1.1.1
            (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) p.2).resolve_right hstar))⟩

/-- **R-6c-body-522 ∎ — the corrected three-route inverse map.**  Target star → the one-stage star vertex; target survivor
→ input-outer survivor (identity) or (via body-521) a left index's star vertex. -/
noncomputable def correctedThreeRouteInvFun
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H) :
    {w : VertexId // w ∈ ((canonicalCorrectedQuotientRaw Measure
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
        canonicalUniqueStarFactsOfW' q.1).contractWithStars
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1))).vertices} →
    {v : VertexId // v ∈ (q.1.1.1.contractWithStars
        (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices} :=
  fun p =>
    if hstar : isContractStarVertex (canonicalCorrectedQuotientRaw Measure
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
        canonicalUniqueStarFactsOfW' q.1)
        (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
          (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
          (canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1)) p.1 then
      ⟨((canonicalCorrectedQuotientStarVertexEquiv Measure E q).symm ⟨p.1, hstar⟩).1.vertex,
        star_mem_contractWithStars _ _
          ((canonicalCorrectedQuotientStarVertexEquiv Measure E q).symm ⟨p.1, hstar⟩).1.toStarVertex.2⟩
    else
      have hsurv : isContractSurvivingVertex (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1) p.1 :=
        (contractWithStars_vertex_cases _ _ p.2).resolve_right hstar
      if hO : isContractSurvivingVertex q.1.1.1 p.1 then
        ⟨p.1, surviving_mem_contractWithStars _ _ hO⟩
      else
        ⟨((correctedTwoStageSurvivor_cases q Measure hsurv).resolve_left hO).choose.vertex,
          star_mem_contractWithStars _ _
            ((correctedTwoStageSurvivor_cases q Measure hsurv).resolve_left hO).choose.toStarVertex.2⟩

/-! ## Step 4 — branch value lemmas -/

/-- **R-6c-body-522 — forward, source-survivor branch: identity.** -/
theorem correctedThreeRouteToFun_original
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    {v : VertexId} (hv : v ∈ (q.1.1.1.contractWithStars
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices)
    (hnotstar : ¬ isContractStarVertex q.1.1.1
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v) :
    (correctedThreeRouteToFun q Measure E ⟨v, hv⟩).1 = v := by
  simp only [correctedThreeRouteToFun, dif_neg hnotstar]

/-- **R-6c-body-522 — forward, left branch: `targetLeftStar`.** -/
theorem correctedThreeRouteToFun_left
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    {v : VertexId} (hv : v ∈ (q.1.1.1.contractWithStars
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices)
    (hstar : isContractStarVertex q.1.1.1
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v)
    (hL : (canonicalOneStageStarRecover q ⟨v, hstar⟩).isLeft) :
    (correctedThreeRouteToFun q Measure E ⟨v, hv⟩).1
      = targetLeftStar q (canonicalOneStageStarRecover q ⟨v, hstar⟩) := by
  simp only [correctedThreeRouteToFun, dif_pos hstar, dif_pos hL]

/-- **R-6c-body-522 — forward, non-left branch: the quotient-star vertex.** -/
theorem correctedThreeRouteToFun_nonleft
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    {v : VertexId} (hv : v ∈ (q.1.1.1.contractWithStars
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices)
    (hstar : isContractStarVertex q.1.1.1
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v)
    (hL : ¬ (canonicalOneStageStarRecover q ⟨v, hstar⟩).isLeft) :
    (correctedThreeRouteToFun q Measure E ⟨v, hv⟩).1
      = (canonicalCorrectedQuotientStarVertexEquiv Measure E q
          ⟨canonicalOneStageStarRecover q ⟨v, hstar⟩,
            (canonicalOneStageStarRecover q ⟨v, hstar⟩).isLeft_or_hasQuotientStar.resolve_left hL⟩).1 := by
  simp only [correctedThreeRouteToFun, dif_pos hstar, dif_neg hL]

/-- **R-6c-body-522 — inverse, target-star branch: the one-stage star vertex.** -/
theorem correctedThreeRouteInvFun_star
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    {w : VertexId} (hw : w ∈ ((canonicalCorrectedQuotientRaw Measure
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
        canonicalUniqueStarFactsOfW' q.1).contractWithStars
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1))).vertices)
    (hstar : isContractStarVertex (canonicalCorrectedQuotientRaw Measure
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
        canonicalUniqueStarFactsOfW' q.1)
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1)) w) :
    (correctedThreeRouteInvFun q Measure E ⟨w, hw⟩).1
      = ((canonicalCorrectedQuotientStarVertexEquiv Measure E q).symm ⟨w, hstar⟩).1.vertex := by
  simp only [correctedThreeRouteInvFun, dif_pos hstar]

/-- **R-6c-body-522 — inverse, target-survivor / input-outer branch: identity.** -/
theorem correctedThreeRouteInvFun_originalSurvivor
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    {w : VertexId} (hw : w ∈ ((canonicalCorrectedQuotientRaw Measure
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
        canonicalUniqueStarFactsOfW' q.1).contractWithStars
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1))).vertices)
    (hstar : ¬ isContractStarVertex (canonicalCorrectedQuotientRaw Measure
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
        canonicalUniqueStarFactsOfW' q.1)
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1)) w)
    (hO : isContractSurvivingVertex q.1.1.1 w) :
    (correctedThreeRouteInvFun q Measure E ⟨w, hw⟩).1 = w := by
  simp only [correctedThreeRouteInvFun, dif_neg hstar, dif_pos hO]

/-- **R-6c-body-522 — inverse, target-survivor / left branch: the chosen index's star vertex.** -/
theorem correctedThreeRouteInvFun_left
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    {w : VertexId} (hw : w ∈ ((canonicalCorrectedQuotientRaw Measure
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
        canonicalUniqueStarFactsOfW' q.1).contractWithStars
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1))).vertices)
    (hstar : ¬ isContractStarVertex (canonicalCorrectedQuotientRaw Measure
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
        canonicalUniqueStarFactsOfW' q.1)
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1)) w)
    (hO : ¬ isContractSurvivingVertex q.1.1.1 w) :
    (correctedThreeRouteInvFun q Measure E ⟨w, hw⟩).1
      = ((correctedTwoStageSurvivor_cases q Measure
          ((contractWithStars_vertex_cases _ _ hw).resolve_right hstar)).resolve_left hO).choose.vertex := by
  simp only [correctedThreeRouteInvFun, dif_neg hstar, dif_neg hO]

/-! ## Recovery anchors (for body-523) -/

/-- **R-6c-body-522 — the one-stage star recovery round-trip** (`recover (vertex i) = i`). -/
theorem canonicalOneStageStarRecover_apply
    (i : OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1) :
    canonicalOneStageStarRecover q i.toStarVertex = i :=
  (canonicalOneStageStarRecover q).apply_symm_apply i

/-- **R-6c-body-522 — the quotient-star vertex equiv round-trip** (`equiv.symm (equiv k) = k`). -/
theorem canonicalCorrectedQuotientStarVertexEquiv_symm_apply
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    (k : {i : OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1 // i.hasQuotientStar}) :
    (canonicalCorrectedQuotientStarVertexEquiv Measure E q).symm
        (canonicalCorrectedQuotientStarVertexEquiv Measure E q k) = k :=
  (canonicalCorrectedQuotientStarVertexEquiv Measure E q).symm_apply_apply k

end GaugeGeometry.QFT.Combinatorial
