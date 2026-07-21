import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaLeftStarSurvive

/-!
# R-6c-body-521 — corrected two-stage survivor partition (PROVED)

Five-hundred-and-twenty-first genuine-body step — the mathematical center of the `quot_eq` campaign.  The corrected left
route (body-519/520) is turned into a full PARTITION of the corrected quotient's surviving vertices, honest to the canonical
allocator: a surviving vertex of the corrected quotient is EITHER an input-outer surviving vertex OR the corrected
`targetLeftStar` of a left one-stage index.  The legacy `i.vertex = v` identity interface is NEVER used.

The reverse direction is split into two coverage lemmas (reused pieces), then assembled — not proved in one shot:

* **`inputOuter_survivor_mem_correctedQuotient`** — the ORIGINAL-vertex coverage: a vertex in `q.1.1.1.vertices` but NOT in
  `selectedOuterRawOf q.1` lands in the corrected quotient.  Its owner input-outer component is classified left /right/forest;
  the LEFT case is impossible (a left component sits in the selected outer), the RIGHT case routes through the survivor
  component, and the FOREST case uses the corrected remnant's SURVIVOR vertices (`v ∈ o.γ.vertices \ o.B.vertices`).
* **`selectedOuterStar_not_mem_correctedQuotient_isLeft`** — the STAR coverage: a selected-outer star that is NOT in the
  corrected quotient must be a LEFT star (its component is `leftOf`); a `promotedOf` star, by contrast, IS in the corrected
  quotient (the remnant's promoted-STAR vertices), contradicting the hypothesis.
* **`correctedTwoStageSurvivor_cases`** — splits `h.1 : v ∈ selectedOuterContractGraph.vertices` via
  `contractWithStars_vertices`; the survivor branch feeds the original-vertex coverage (`by_contra` + `h.2`), the star branch
  feeds the star coverage.

So the corrected remnant fills BOTH sides of the stage-2 survivor partition: its survivor vertices for the original branch,
its promoted-star vertices for the star branch.  This discards the old three-route identity-left interface entirely.

Per the HALT/guards: `sourceLeftStar = targetLeftStar` is NOT required; the legacy `twoStageSurvivor_cases` /
`ResolvedLeftStarSurvivalSupply` is NOT inhabited; NO raw `∀ s`; NO local-permutation comparison; the full correspondence /
inverse laws / global `σ` / whole-graph field equalities / `quot_eq` are NOT entered; strict `StarProm` / `InnerStarRaw` stay
ZERO; NO unconditional-coassoc claim.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` /
singleton / floor-297.
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

/-- **R-6c-body-521 ∎ — original-vertex coverage.**  An input-outer vertex not in the selected outer lands in the corrected
quotient. -/
theorem inputOuter_survivor_mem_correctedQuotient
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    {v : VertexId} (hvA : v ∈ q.1.1.1.vertices)
    (hvS : v ∉ ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
      q.1).vertices) :
    v ∈ (canonicalCorrectedQuotientRaw Measure
      canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
      canonicalUniqueStarFactsOfW' q.1).vertices := by
  obtain ⟨γ, hγ, hvγ⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hvA
  rcases ResolvedCoassocSplitChoice.isLeftPrimitive_or_isRightPrimitive_or_isForestChoice q.1 ⟨γ, hγ⟩ with
    hLeft | hRight | hForest
  · -- LEFT: γ ∈ leftOf ⊆ selectedOuter, so v ∈ selectedOuter.vertices — contradiction with hvS.
    exfalso
    have hlsc : ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 γ :=
      (ResolvedCoassocSplitChoice.isLeftPrimitive_iff_leftSelectedConcrete q.1 ⟨γ, hγ⟩).mp hLeft
    have hγOuter : γ ∈ ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData
        G).selectedOuterRawOf q.1).elements := by
      simp only [ResolvedForestPromoteSupply.selectedOuterRawOf, ResolvedAdmissibleSubgraph.union_elements,
        Finset.mem_union]
      refine Or.inl ?_
      show γ ∈ ((resolvedConcreteLeftSelectionSupply canonicalUniqueSupportedCarrierProperSupply.toData G).leftOf
        q.1).elements
      rw [resolved_leftOf_elements_eq]
      exact Finset.mem_filter.mpr ⟨hγ, hlsc⟩
    exact hvS (ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨γ, hγOuter, hvγ⟩)
  · -- RIGHT: v lives in the survivor component of the right primitive.
    have hrmem : (⟨γ, hγ⟩ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
        ∈ ResolvedCoassocSplitChoice.rightComponents q.1 :=
      Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hRight⟩
    set r : {x : {y : ResolvedFeynmanSubgraph G // y ∈ q.1.1.1.elements} //
        x ∈ ResolvedCoassocSplitChoice.rightComponents q.1} := ⟨⟨γ, hγ⟩, hrmem⟩ with hr
    have hvsurv : v ∈ ((survivorSupply_of_measure Measure G).survivorComponent q.1 r).vertices := hvγ
    have hδR : (survivorSupply_of_measure Measure G).survivorComponent q.1 r
        ∈ ((survivorSupply_of_measure Measure G).rightSurvivorForest q.1).elements := by
      rw [ResolvedRightSurvivorSupply.rightSurvivorForest_elements]
      exact Finset.mem_image.mpr ⟨r, Finset.mem_attach _ _, rfl⟩
    refine ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨_, ?_, hvsurv⟩
    simp only [canonicalCorrectedQuotientRaw, ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union]
    exact Or.inl hδR
  · -- FOREST: v is in the corrected remnant's SURVIVOR vertices (`o.γ.vertices \ o.B.vertices`).
    have hfmem : (⟨γ, hγ⟩ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
        ∈ ResolvedCoassocSplitChoice.forestComponents q.1 :=
      Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hForest⟩
    set o := ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 ⟨⟨γ, hγ⟩, hfmem⟩ with ho
    -- v is not in the chosen sub-forest's vertices (else it would land in the selected outer).
    have hvBnot : v ∉ o.B.1.vertices := by
      intro hvB
      obtain ⟨b, hb, hvb⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hvB
      have hpromMem : o.γ.1.promote b ∈ ((resolvedConcreteForestPromoteSupply
          canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf q.1).elements :=
        promote_mem_selectedOuterRawOf_raw q.1 o hb
      have hvpromote : v ∈ (o.γ.1.promote b).vertices := by
        rw [ResolvedFeynmanSubgraph.promote_vertices]; exact hvb
      exact hvS (ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨o.γ.1.promote b, hpromMem, hvpromote⟩)
    have hvδ : v ∈ ((canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1 o).vertices := by
      rw [show ((canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
              canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1 o).vertices
            = (o.B.1.contractWithStars (promotedOccurrenceStar q.1 o)).vertices
          from correctedRemnantComponent_vertices_eq_promoted q.1 o canonicalUniqueStarFactsOfW',
        ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union]
      exact Or.inl (Finset.mem_sdiff.mpr ⟨hvγ, hvBnot⟩)
    have hδM : (canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1 o
        ∈ ((canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantForest q.1).elements := by
      rw [ResolvedRemnantComponentSupply.remnantForest_elements]
      exact Finset.mem_image.mpr ⟨⟨⟨γ, hγ⟩, hfmem⟩, Finset.mem_attach _ _, rfl⟩
    refine ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨_, ?_, hvδ⟩
    simp only [canonicalCorrectedQuotientRaw, ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union]
    exact Or.inr hδM

/-- **R-6c-body-521 ∎ — star coverage.**  A selected-outer star that is not in the corrected quotient is the corrected
`targetLeftStar` of a LEFT one-stage index (a `promotedOf` star would BE in the quotient). -/
theorem selectedOuterStar_not_mem_correctedQuotient_isLeft
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (δ : ResolvedFeynmanSubgraph G)
    (hδ : δ ∈ ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData
      G).selectedOuterRawOf q.1).elements)
    (hnot : canonicalUniqueSupportedCarrierProperSupply.toData.starOf G
        ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf q.1) δ
      ∉ (canonicalCorrectedQuotientRaw Measure
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
        canonicalUniqueStarFactsOfW' q.1).vertices) :
    ∃ i : OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1,
      i.isLeft ∧ targetLeftStar q i = canonicalUniqueSupportedCarrierProperSupply.toData.starOf G
        ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf q.1)
        δ := by
  simp only [ResolvedForestPromoteSupply.selectedOuterRawOf, ResolvedAdmissibleSubgraph.union_elements,
    Finset.mem_union] at hδ
  rcases hδ with hLeft | hProm
  · -- leftOf: the genuine left witness.
    obtain ⟨hδOuter, hlsc⟩ := Finset.mem_filter.mp
      (show δ ∈ q.1.1.1.elements.filter (fun x => ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 x) from hLeft)
    exact ⟨⟨δ, hδOuter⟩,
      (ResolvedCoassocSplitChoice.isLeftPrimitive_iff_leftSelectedConcrete q.1 ⟨δ, hδOuter⟩).mpr hlsc, rfl⟩
  · -- promotedOf: the star IS in the quotient (remnant promoted star), contradicting `hnot`.
    exfalso
    have hProm' : δ ∈ ResolvedCoassocSplitChoice.promotedElements q.1 := hProm
    obtain ⟨γ, hγP⟩ := ResolvedCoassocSplitChoice.mem_promotedElements hProm'
    rcases hc : ResolvedCoassocSplitChoice.choiceAt q.1 γ with b | Bγ
    · rw [ResolvedCoassocSplitChoice.promotedComponentElements_inl q.1 hc] at hγP
      exact absurd hγP (by simp)
    · rw [ResolvedCoassocSplitChoice.promotedComponentElements_inr q.1 hc] at hγP
      simp only [ResolvedAdmissibleSubgraph.promote_elements, Finset.mem_image] at hγP
      obtain ⟨b, hb, hbeq⟩ := hγP
      have hfc : γ ∈ ResolvedCoassocSplitChoice.forestComponents q.1 :=
        Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, ⟨Bγ, hc⟩⟩
      set o := ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 ⟨γ, hfc⟩ with ho
      have hoB : o.B = Bγ := Sum.inr.inj (o.hchoice.symm.trans hc)
      have hb' : b ∈ o.B.1.elements := by rw [hoB]; exact hb
      have hstar_in : canonicalUniqueSupportedCarrierProperSupply.toData.starOf G
            ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
              q.1) δ
          ∈ ((canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1 o).vertices := by
        rw [show ((canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
                canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1 o).vertices
              = (o.B.1.contractWithStars (promotedOccurrenceStar q.1 o)).vertices
            from correctedRemnantComponent_vertices_eq_promoted q.1 o canonicalUniqueStarFactsOfW',
          ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union]
        refine Or.inr (ResolvedAdmissibleSubgraph.mem_starVertices.mpr ⟨b, hb', ?_⟩)
        show canonicalUniqueSupportedCarrierProperSupply.toData.starOf G
            ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
              q.1) (o.γ.1.promote b)
          = canonicalUniqueSupportedCarrierProperSupply.toData.starOf G
            ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
              q.1) δ
        exact congrArg _ hbeq
      have hδM : (canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1 o
          ∈ ((canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantForest q.1).elements := by
        rw [ResolvedRemnantComponentSupply.remnantForest_elements]
        exact Finset.mem_image.mpr ⟨⟨γ, hfc⟩, Finset.mem_attach _ _, rfl⟩
      refine hnot (ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨_, ?_, hstar_in⟩)
      simp only [canonicalCorrectedQuotientRaw, ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union]
      exact Or.inr hδM

/-- **R-6c-body-521 ∎ — the corrected two-stage survivor partition.**  A surviving vertex of the corrected quotient is an
input-outer surviving vertex OR the corrected `targetLeftStar` of a left one-stage index.  The legacy `i.vertex = v` is
NEVER used. -/
theorem correctedTwoStageSurvivor_cases
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    {v : VertexId}
    (h : isContractSurvivingVertex (canonicalCorrectedQuotientRaw Measure
      canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
      canonicalUniqueStarFactsOfW' q.1) v) :
    isContractSurvivingVertex q.1.1.1 v ∨
      ∃ i : OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1,
        i.isLeft ∧ targetLeftStar q i = v := by
  obtain ⟨h1, h2⟩ := h
  rw [ResolvedCoassocSplitChoice.selectedOuterContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at h1
  rcases h1 with hSurv | hStar
  · -- survivor branch: v ∈ G.vertices \ selectedOuter.vertices.
    obtain ⟨hvG, hvS⟩ := Finset.mem_sdiff.mp hSurv
    refine Or.inl ⟨hvG, ?_⟩
    intro hvA
    exact h2 (inputOuter_survivor_mem_correctedQuotient q Measure hvA hvS)
  · -- star branch: v is a selected-outer star; feed the star coverage.
    obtain ⟨δ, hδ, hstar⟩ := ResolvedAdmissibleSubgraph.mem_starVertices.mp hStar
    obtain ⟨i, hiL, hieq⟩ := selectedOuterStar_not_mem_correctedQuotient_isLeft q Measure δ hδ (hstar ▸ h2)
    exact Or.inr ⟨i, hiL, hieq.trans hstar⟩

end GaugeGeometry.QFT.Combinatorial
