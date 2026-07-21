import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaLeftStarRoute
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSplitDischarge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMeasureLeaves

/-!
# R-6c-body-520 — the corrected left target survives stage 2 (PROVED)

Five-hundred-and-twentieth genuine-body step — completing the body-519 corrected left route.  The corrected target star
`targetLeftStar q i = D.starOf G (selectedOuterRawOf q.1) i.η` (the SELECTED-outer star of a left index) is shown to be a
genuine STAGE-2 SURVIVING vertex of the corrected quotient: it lives in the stage-1 quotient graph (body-519's
`targetLeftStar_mem_selectedOuterContractGraph`) but in NONE of the corrected quotient's carrier components.

## Component-level exclusion, then the union aggregate

The two per-component exclusions are named theorems (reused by body-521's partition), then aggregated:

* **freshness (Step 1)** — `targetLeftStar_not_mem_G` : `targetLeftStar q i ∉ G.vertices`, straight from
  `Fstar.starOf_fresh` at body-519's `leftIndex_mem_selectedOuter`;
* **right-survivor exclusion (Step 2)** — a survivor component's vertices are `r.1.1.vertices ⊆ G.vertices`
  (`vertices_subset`), contradicting Step 1;
* **corrected-remnant exclusion (Step 3)** — `correctedRemnantComponent_vertices_eq_promoted` +
  `contractWithStars_vertices` splits into (A) the survivor part `⊆ o.γ.vertices ⊆ G.vertices` (Step 1 again) and (B) the
  promoted-star part, where `mem_starVertices` recovers `b ∈ o.B.elements` with
  `promotedOccurrenceStar q.1 o b = targetLeftStar q i`; the SELECTED-outer `starOf_injective` forces
  `o.γ.promote b = i.η`, but `o.γ.promote b ∈ promotedOf` and `i.η ∈ leftOf`, and the `hLP` `leftOf`/`promotedOf`
  element-disjointness (Measure-derived) closes it;
* **whole quotient exclusion (Step 4)** — `mem_vertices` recovers the owner component, `union_elements` dispatches it to
  the right-survivor or remnant sector, and the image witness feeds Step 2 / Step 3;
* **completion (Step 5)** — `correctedLeftStar_toSurvivor := ⟨body-519's contract-graph membership, Step 4⟩`, an
  `isContractSurvivingVertex` of the corrected quotient (over its ambient `selectedOuterContractGraph q.1`).

The star/star contradiction is body-464-like but simpler: the SAME selected-outer allocator's injectivity identifies the
left component with a promoted component, and the selection disjointness finishes.  `sourceLeftStar` NEVER appears; the
target vertex is the selected-outer star itself.

Per the HALT/guards: `sourceLeftStar = targetLeftStar` is NOT required; the legacy `ResolvedLeftStarSurvivalSupply` is NOT
inhabited; NO correcting-permutation comparison; no raw `∀ s`; body-464's remnant/remnant disjointness is NOT reused; the
graph-level cross disjointness is NOT routed through to fabricate a vertex witness; two-stage completeness / the full vertex
correspondence / global `σ` / whole-graph field equalities / `quot_eq` are NOT entered; strict `StarProm` / `InnerStarRaw`
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

/-- **R-6c-body-520 ∎ — Step 1, the corrected target star is fresh (outside `G`).** -/
theorem targetLeftStar_not_mem_G
    (i : OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1) (hL : i.isLeft) :
    targetLeftStar q i ∉ G.vertices :=
  canonicalUniqueStarFactsOfW'.starOf_fresh G
    ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf q.1)
    i.η (leftIndex_mem_selectedOuter q i hL)

/-- **R-6c-body-520 ∎ — Step 2, the corrected target avoids every right-survivor component.** -/
theorem targetLeftStar_not_mem_rightSurvivorComponent
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (i : OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1) (hL : i.isLeft)
    (r : {x : {y : ResolvedFeynmanSubgraph G // y ∈ q.1.1.1.elements} //
        x ∈ ResolvedCoassocSplitChoice.rightComponents q.1}) :
    targetLeftStar q i ∉ ((survivorSupply_of_measure Measure G).survivorComponent q.1 r).vertices := by
  intro hv
  have hvr : targetLeftStar q i ∈ r.1.1.vertices := hv
  exact targetLeftStar_not_mem_G q i hL (r.1.1.vertices_subset hvr)

/-- **R-6c-body-520 ∎ — Step 3, the corrected target avoids every corrected-remnant component.** -/
theorem targetLeftStar_not_mem_correctedRemnantComponent
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (i : OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1) (hL : i.isLeft)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1) :
    targetLeftStar q i ∉ ((canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1 o).vertices := by
  intro hv
  rw [show ((canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1 o).vertices
        = (o.B.1.contractWithStars (promotedOccurrenceStar q.1 o)).vertices
      from correctedRemnantComponent_vertices_eq_promoted q.1 o canonicalUniqueStarFactsOfW',
    ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hv
  rcases hv with hsurv | hstar
  · -- survivor part: the target lies in `o.γ.vertices ⊆ G.vertices`, contradicting freshness.
    exact targetLeftStar_not_mem_G q i hL (o.γ.1.vertices_subset (Finset.mem_sdiff.mp hsurv).1)
  · -- promoted-star part: selected-outer injectivity meets left/promoted disjointness.
    obtain ⟨b, hb, hbeq⟩ := ResolvedAdmissibleSubgraph.mem_starVertices.mp hstar
    have hpromMem : o.γ.1.promote b
        ∈ ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
          q.1).elements := promote_mem_selectedOuterRawOf_raw q.1 o hb
    have hηMem : i.η
        ∈ ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
          q.1).elements := leftIndex_mem_selectedOuter q i hL
    have hstareq : canonicalUniqueSupportedCarrierProperSupply.toData.starOf G
          ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
            q.1) (o.γ.1.promote b)
        = canonicalUniqueSupportedCarrierProperSupply.toData.starOf G
          ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
            q.1) i.η := hbeq
    have hγeq : o.γ.1.promote b = i.η :=
      canonicalUniqueStarFactsOfW'.starOf_injective G
        ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
          q.1) hpromMem hηMem hstareq
    have hpromPromoted : o.γ.1.promote b
        ∈ ((resolvedPromotedOfSupply canonicalUniqueSupportedCarrierProperSupply.toData G).promotedOf q.1).elements := by
      rw [ResolvedPromotedOfSupply.promotedOf_elements]
      unfold ResolvedCoassocSplitChoice.promotedElements
      refine Finset.mem_biUnion.mpr ⟨o.γ, Finset.mem_attach _ _, ?_⟩
      rw [ResolvedCoassocSplitChoice.promotedComponentElements_inr q.1 o.hchoice]
      simp only [ResolvedAdmissibleSubgraph.promote_elements, Finset.mem_image]
      exact ⟨b, hb, rfl⟩
    have hηLeft : i.η
        ∈ ((resolvedConcreteLeftSelectionSupply canonicalUniqueSupportedCarrierProperSupply.toData G).leftOf
          q.1).elements := by
      rw [resolved_leftOf_elements_eq]
      exact Finset.mem_filter.mpr ⟨i.hη,
        (ResolvedCoassocSplitChoice.isLeftPrimitive_iff_leftSelectedConcrete q.1 i.toComponent).mp hL⟩
    exact Finset.disjoint_left.mp
      ((Measure.toInputOuterElementNonemptySupply (G := G)).hLP q.1) hηLeft (hγeq ▸ hpromPromoted)

/-- **R-6c-body-520 ∎ — Step 4, the corrected target is in NONE of the corrected quotient's components.** -/
theorem targetLeftStar_not_mem_correctedQuotient
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (i : OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1) (hL : i.isLeft) :
    targetLeftStar q i ∉ (canonicalCorrectedQuotientRaw Measure
      canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
      canonicalUniqueStarFactsOfW' q.1).vertices := by
  intro hv
  rw [ResolvedAdmissibleSubgraph.mem_vertices] at hv
  obtain ⟨δ, hδ, hvδ⟩ := hv
  simp only [canonicalCorrectedQuotientRaw, ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union] at hδ
  rcases hδ with hR | hM
  · rw [ResolvedRightSurvivorSupply.rightSurvivorForest_elements] at hR
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hR
    exact targetLeftStar_not_mem_rightSurvivorComponent q Measure i hL r hvδ
  · rw [ResolvedRemnantComponentSupply.remnantForest_elements] at hM
    obtain ⟨γ, -, rfl⟩ := Finset.mem_image.mp hM
    exact targetLeftStar_not_mem_correctedRemnantComponent q Measure i hL
      (ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 γ) hvδ

/-- **R-6c-body-520 ∎ — Step 5, the corrected left route completed: the target is a stage-2 SURVIVING vertex.** -/
theorem correctedLeftStar_toSurvivor
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (i : OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1) (hL : i.isLeft) :
    isContractSurvivingVertex (canonicalCorrectedQuotientRaw Measure
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
        canonicalUniqueStarFactsOfW' q.1)
      (targetLeftStar q i) :=
  ⟨targetLeftStar_mem_selectedOuterContractGraph q i hL,
    targetLeftStar_not_mem_correctedQuotient q Measure i hL⟩

end GaugeGeometry.QFT.Combinatorial
