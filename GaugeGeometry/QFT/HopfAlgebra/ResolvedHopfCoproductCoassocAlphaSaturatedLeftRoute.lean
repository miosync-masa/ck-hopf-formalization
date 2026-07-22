import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSaturatedSectorEquiv
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaStarVertexRecover
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaLeftStarRoute
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaLeftStarSurvive
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaTwoStageSurvivorPartition

/-!
# R-6c-body-543 — the `W″` star-vertex recovery + corrected left route + two-stage survivor partition (PROVED)

Five-hundred-and-forty-third genuine-body step — the SECOND of the `W″` re-key campaign (542 image + sector / **543
star-recovery + corrected-left + partition** / 544 three-route / 545 global-`σ` + field + `quot_eq` / 546 occurrence +
round-trip + final wrapper).  This body re-issues bodies 518–521 from `W′` to `W″`, reading the single construction owner
`R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E` (body-541) only at the top star-vertex equivalence (so it can
consume body-542's `R`-keyed `canonicalLegSaturatedCorrectedQuotientStarEquiv R q`); the individual recoveries / left-route
theorems / partition lemmas stay parametrized by an explicit `Measure` exactly as the `W′` templates.

**NEW GEOMETRY = ZERO.**  The star geometry is body-518–521's, re-issued in the `W″` owner's coordinates.  Every
substitution is mechanical: `canonicalUniqueSupportedCarrierProperSupply → canonicalLegSaturatedCarrierProperSupply`,
`canonicalUniqueStarFactsOfW' → canonicalLegSaturatedStarFacts`, and — ONLY in the top star-vertex composition —
`canonicalCorrectedQuotientStarEquiv Measure E q → canonicalLegSaturatedCorrectedQuotientStarEquiv R q` (body-542).  All the
D-generic helpers (`resolvedStarVertexEquivIndex`, `oneStageStarIndexEquivSubtype`, `isContractStarVertex`,
`isContractSurvivingVertex`, `OneStageStarIndex` + `.η`/`.isLeft`/`.hasQuotientStar`/`.toComponent`,
`resolvedConcreteForestPromoteSupply`/`.selectedOuterRawOf`, `resolvedConcreteLeftSelectionSupply`/`.leftOf`,
`resolved_leftOf_elements_eq`, `isLeftPrimitive_iff_leftSelectedConcrete`, `contractWithStars_vertices`, `mem_starVertices`,
`selectedOuterContractGraph`, `survivorSupply_of_measure`, `canonicalCorrectedRemnantComponentSupply`,
`canonicalCorrectedQuotientRaw`) apply UNCHANGED with the `W″` `Measure` / `Fstar` / `CarrierProper`.

## Deliverables

* **Step 1 — star-vertex recoveries** (`canonicalLegSaturatedOneStageStarRecover`,
  `canonicalLegSaturatedCorrectedTwoStageStarRecover`, and the top
  `canonicalLegSaturatedCorrectedQuotientStarVertexEquiv R q` reading body-542's `R`-keyed star equiv).
* **Step 2 — corrected left route foundation** (`legSaturatedSourceLeftStar` / `legSaturatedTargetLeftStar` and
  `legSaturated_leftIndex_mem_selectedOuter` / `legSaturated_targetLeftStar_mem_selectedOuterContractGraph` /
  `legSaturated_correctedLeftTarget_injective`).  ★`legSaturatedSourceLeftStar` is NEVER asserted equal to
  `legSaturatedTargetLeftStar`.★
* **Step 3 — corrected left target survives stage 2** (`legSaturated_targetLeftStar_not_mem_G` /
  `..._rightSurvivorComponent` / `..._correctedRemnantComponent` / `..._correctedQuotient` /
  `legSaturated_correctedLeftStar_toSurvivor`).
* **Step 4 — corrected two-stage survivor partition** (`legSaturated_inputOuter_survivor_mem_correctedQuotient` /
  `legSaturated_selectedOuterStar_not_mem_correctedQuotient_isLeft` / the headline
  `canonicalLegSaturatedCorrectedTwoStageSurvivor_cases`).  ★The final form uses `legSaturatedTargetLeftStar q i = v`,
  NEVER the legacy `i.vertex`-identity form.★
* **Step 5 — branch anchors for body-544** (`canonicalLegSaturatedOneStageStarRecover_vertex` /
  `canonicalLegSaturatedOneStageStarRecover_apply` / `canonicalLegSaturatedCorrectedQuotientStarVertexEquiv_symm_apply`,
  all from the GENERIC `Equiv` inverse laws).

Per the HALT/guards: NO three-route maps / inverses / correspondence / global `σ` / `quot_eq` (bodies 544–546); NO `W′`↔`W″`
`q` adapter / cast; local permutations are NOT compared; no strict sockets; `R.quotient_mem` is NOT read; the D-generic
helpers are reused directly with the `W″` `Measure` / `Fstar` / `CarrierProper` and NO `W′` decl is modified; strict
`StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc claim.  No facade, no flat term, no `forgetHopf`, no
rep/perm.
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

/-! ## Step 1 — the `W″` star-vertex recoveries (body-518 re-key). -/

/-- **R-6c-body-543 ∎ — the `W″` one-stage star-vertex recovery.**  `{v // contract star of the input outer} ≃
OneStageStarIndex`. -/
noncomputable def canonicalLegSaturatedOneStageStarRecover {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G) :
    {v : VertexId // isContractStarVertex q.1.1.1
        (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v}
      ≃ OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1 :=
  (resolvedStarVertexEquivIndex q.1.1.1
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)
      (fun γ₁ h₁ γ₂ h₂ heq =>
        canonicalLegSaturatedStarFacts.starOf_injective G q.1.1.1 h₁ h₂ heq)).trans
    (oneStageStarIndexEquivSubtype q.1).symm

/-- **R-6c-body-543 ∎ — the `W″` corrected two-stage star-vertex recovery.**  `{w // contract star of the corrected
quotient} ≃ corrected quotient components` — directly on the q-local subtype, no `TwoStageStarIndex`. -/
noncomputable def canonicalLegSaturatedCorrectedTwoStageStarRecover
    (Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G) :
    {w : VertexId // isContractStarVertex
        (canonicalCorrectedQuotientRaw Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1)
        (canonicalLegSaturatedCarrierProperSupply.toData.starOf
          (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
          (canonicalCorrectedQuotientRaw Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
            canonicalLegSaturatedStarFacts q.1)) w}
      ≃ {δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) //
          δ ∈ (canonicalCorrectedQuotientRaw Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
            canonicalLegSaturatedStarFacts q.1).elements} :=
  resolvedStarVertexEquivIndex
    (canonicalCorrectedQuotientRaw Measure
      canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
      canonicalLegSaturatedStarFacts q.1)
    (canonicalLegSaturatedCarrierProperSupply.toData.starOf
      (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
      (canonicalCorrectedQuotientRaw Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
        canonicalLegSaturatedStarFacts q.1))
    (fun γ₁ h₁ γ₂ h₂ heq =>
      canonicalLegSaturatedStarFacts.starOf_injective
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1) h₁ h₂ heq)

/-- **R-6c-body-543 ∎ — the completed `W″` quotient-star VERTEX equivalence** (non-left star ↦ its corrected-quotient
star vertex), reading body-542's `R`-keyed star equiv (`R.Measure` for the two-stage recovery). -/
noncomputable def canonicalLegSaturatedCorrectedQuotientStarVertexEquiv
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G) :
    {i : OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1 // i.hasQuotientStar}
      ≃ {w : VertexId // isContractStarVertex
          (canonicalCorrectedQuotientRaw R.Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
            canonicalLegSaturatedStarFacts q.1)
          (canonicalLegSaturatedCarrierProperSupply.toData.starOf
            (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
            (canonicalCorrectedQuotientRaw R.Measure
              canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
              canonicalLegSaturatedStarFacts q.1)) w} :=
  (canonicalLegSaturatedCorrectedQuotientStarEquiv R q).trans
    (canonicalLegSaturatedCorrectedTwoStageStarRecover R.Measure q).symm

/-! ## Step 2 — the `W″` corrected left route foundation (body-519 re-key). -/

variable {G : ResolvedFeynmanGraph}
  (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G)

/-- **R-6c-body-543 — the input-outer star** (the legacy identity route's source). -/
noncomputable def legSaturatedSourceLeftStar
    (i : OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1) : VertexId :=
  canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1 i.η

/-- **R-6c-body-543 — the selected-outer star** (the corrected route's target; NOT assumed equal to
`legSaturatedSourceLeftStar`). -/
noncomputable def legSaturatedTargetLeftStar
    (i : OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1) : VertexId :=
  canonicalLegSaturatedCarrierProperSupply.toData.starOf G
    ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf q.1)
    i.η

/-- **R-6c-body-543 ∎ — a left index's component is in the selected outer.** -/
theorem legSaturated_leftIndex_mem_selectedOuter
    (i : OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1) (hL : i.isLeft) :
    i.η ∈ ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
      q.1).elements := by
  have hlsc : ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 i.η :=
    (ResolvedCoassocSplitChoice.isLeftPrimitive_iff_leftSelectedConcrete q.1 i.toComponent).mp hL
  simp only [ResolvedForestPromoteSupply.selectedOuterRawOf, ResolvedAdmissibleSubgraph.union_elements,
    Finset.mem_union]
  left
  show i.η ∈ ((resolvedConcreteLeftSelectionSupply canonicalLegSaturatedCarrierProperSupply.toData G).leftOf q.1).elements
  rw [resolved_leftOf_elements_eq]
  exact Finset.mem_filter.mpr ⟨i.hη, hlsc⟩

/-- **R-6c-body-543 ∎ — the corrected target star is a stage-1 quotient-graph vertex.**  NO equality with
`legSaturatedSourceLeftStar`. -/
theorem legSaturated_targetLeftStar_mem_selectedOuterContractGraph
    (i : OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1) (hL : i.isLeft) :
    legSaturatedTargetLeftStar q i ∈ (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1).vertices := by
  rw [ResolvedCoassocSplitChoice.selectedOuterContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union]
  exact Or.inr (ResolvedAdmissibleSubgraph.mem_starVertices.mpr
    ⟨i.η, legSaturated_leftIndex_mem_selectedOuter q i hL, rfl⟩)

/-- **R-6c-body-543 ∎ — the corrected left target is injective** (on left indices). -/
theorem legSaturated_correctedLeftTarget_injective
    (i j : OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1)
    (hLi : i.isLeft) (hLj : j.isLeft)
    (heq : legSaturatedTargetLeftStar q i = legSaturatedTargetLeftStar q j) : i = j := by
  have hη : i.η = j.η :=
    canonicalLegSaturatedStarFacts.starOf_injective G
      ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf q.1)
      (legSaturated_leftIndex_mem_selectedOuter q i hLi) (legSaturated_leftIndex_mem_selectedOuter q j hLj) heq
  obtain ⟨ηi, hηi⟩ := i
  obtain ⟨ηj, hηj⟩ := j
  cases hη
  rfl

/-! ## Step 3 — the corrected left target survives stage 2 (body-520 re-key). -/

/-- **R-6c-body-543 ∎ — Step 1, the corrected target star is fresh (outside `G`).** -/
theorem legSaturated_targetLeftStar_not_mem_G
    (i : OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1) (hL : i.isLeft) :
    legSaturatedTargetLeftStar q i ∉ G.vertices :=
  canonicalLegSaturatedStarFacts.starOf_fresh G
    ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf q.1)
    i.η (legSaturated_leftIndex_mem_selectedOuter q i hL)

/-- **R-6c-body-543 ∎ — Step 2, the corrected target avoids every right-survivor component.** -/
theorem legSaturated_targetLeftStar_not_mem_rightSurvivorComponent
    (Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData)
    (i : OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1) (hL : i.isLeft)
    (r : {x : {y : ResolvedFeynmanSubgraph G // y ∈ q.1.1.1.elements} //
        x ∈ ResolvedCoassocSplitChoice.rightComponents q.1}) :
    legSaturatedTargetLeftStar q i ∉ ((survivorSupply_of_measure Measure G).survivorComponent q.1 r).vertices := by
  intro hv
  have hvr : legSaturatedTargetLeftStar q i ∈ r.1.1.vertices := hv
  exact legSaturated_targetLeftStar_not_mem_G q i hL (r.1.1.vertices_subset hvr)

/-- **R-6c-body-543 ∎ — Step 3, the corrected target avoids every corrected-remnant component.** -/
theorem legSaturated_targetLeftStar_not_mem_correctedRemnantComponent
    (Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData)
    (i : OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1) (hL : i.isLeft)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1) :
    legSaturatedTargetLeftStar q i ∉ ((canonicalCorrectedRemnantComponentSupply canonicalLegSaturatedStarFacts
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1 o).vertices := by
  intro hv
  rw [show ((canonicalCorrectedRemnantComponentSupply canonicalLegSaturatedStarFacts
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1 o).vertices
        = (o.B.1.contractWithStars (promotedOccurrenceStar q.1 o)).vertices
      from correctedRemnantComponent_vertices_eq_promoted q.1 o canonicalLegSaturatedStarFacts,
    ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hv
  rcases hv with hsurv | hstar
  · -- survivor part: the target lies in `o.γ.vertices ⊆ G.vertices`, contradicting freshness.
    exact legSaturated_targetLeftStar_not_mem_G q i hL (o.γ.1.vertices_subset (Finset.mem_sdiff.mp hsurv).1)
  · -- promoted-star part: selected-outer injectivity meets left/promoted disjointness.
    obtain ⟨b, hb, hbeq⟩ := ResolvedAdmissibleSubgraph.mem_starVertices.mp hstar
    have hpromMem : o.γ.1.promote b
        ∈ ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
          q.1).elements := promote_mem_selectedOuterRawOf_raw q.1 o hb
    have hηMem : i.η
        ∈ ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
          q.1).elements := legSaturated_leftIndex_mem_selectedOuter q i hL
    have hstareq : canonicalLegSaturatedCarrierProperSupply.toData.starOf G
          ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
            q.1) (o.γ.1.promote b)
        = canonicalLegSaturatedCarrierProperSupply.toData.starOf G
          ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
            q.1) i.η := hbeq
    have hγeq : o.γ.1.promote b = i.η :=
      canonicalLegSaturatedStarFacts.starOf_injective G
        ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
          q.1) hpromMem hηMem hstareq
    have hpromPromoted : o.γ.1.promote b
        ∈ ((resolvedPromotedOfSupply canonicalLegSaturatedCarrierProperSupply.toData G).promotedOf q.1).elements := by
      rw [ResolvedPromotedOfSupply.promotedOf_elements]
      unfold ResolvedCoassocSplitChoice.promotedElements
      refine Finset.mem_biUnion.mpr ⟨o.γ, Finset.mem_attach _ _, ?_⟩
      rw [ResolvedCoassocSplitChoice.promotedComponentElements_inr q.1 o.hchoice]
      simp only [ResolvedAdmissibleSubgraph.promote_elements, Finset.mem_image]
      exact ⟨b, hb, rfl⟩
    have hηLeft : i.η
        ∈ ((resolvedConcreteLeftSelectionSupply canonicalLegSaturatedCarrierProperSupply.toData G).leftOf
          q.1).elements := by
      rw [resolved_leftOf_elements_eq]
      exact Finset.mem_filter.mpr ⟨i.hη,
        (ResolvedCoassocSplitChoice.isLeftPrimitive_iff_leftSelectedConcrete q.1 i.toComponent).mp hL⟩
    exact Finset.disjoint_left.mp
      ((Measure.toInputOuterElementNonemptySupply (G := G)).hLP q.1) hηLeft (hγeq ▸ hpromPromoted)

/-- **R-6c-body-543 ∎ — Step 4, the corrected target is in NONE of the corrected quotient's components.** -/
theorem legSaturated_targetLeftStar_not_mem_correctedQuotient
    (Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData)
    (i : OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1) (hL : i.isLeft) :
    legSaturatedTargetLeftStar q i ∉ (canonicalCorrectedQuotientRaw Measure
      canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
      canonicalLegSaturatedStarFacts q.1).vertices := by
  intro hv
  rw [ResolvedAdmissibleSubgraph.mem_vertices] at hv
  obtain ⟨δ, hδ, hvδ⟩ := hv
  simp only [canonicalCorrectedQuotientRaw, ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union] at hδ
  rcases hδ with hR | hM
  · rw [ResolvedRightSurvivorSupply.rightSurvivorForest_elements] at hR
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hR
    exact legSaturated_targetLeftStar_not_mem_rightSurvivorComponent q Measure i hL r hvδ
  · rw [ResolvedRemnantComponentSupply.remnantForest_elements] at hM
    obtain ⟨γ, -, rfl⟩ := Finset.mem_image.mp hM
    exact legSaturated_targetLeftStar_not_mem_correctedRemnantComponent q Measure i hL
      (ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 γ) hvδ

/-- **R-6c-body-543 ∎ — Step 5, the corrected left route completed: the target is a stage-2 SURVIVING vertex.** -/
theorem legSaturated_correctedLeftStar_toSurvivor
    (Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData)
    (i : OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1) (hL : i.isLeft) :
    isContractSurvivingVertex (canonicalCorrectedQuotientRaw Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
        canonicalLegSaturatedStarFacts q.1)
      (legSaturatedTargetLeftStar q i) :=
  ⟨legSaturated_targetLeftStar_mem_selectedOuterContractGraph q i hL,
    legSaturated_targetLeftStar_not_mem_correctedQuotient q Measure i hL⟩

/-! ## Step 4 — the corrected two-stage survivor partition (body-521 re-key). -/

/-- **R-6c-body-543 ∎ — original-vertex coverage.**  An input-outer vertex not in the selected outer lands in the
corrected quotient. -/
theorem legSaturated_inputOuter_survivor_mem_correctedQuotient
    (Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData)
    {v : VertexId} (hvA : v ∈ q.1.1.1.vertices)
    (hvS : v ∉ ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
      q.1).vertices) :
    v ∈ (canonicalCorrectedQuotientRaw Measure
      canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
      canonicalLegSaturatedStarFacts q.1).vertices := by
  obtain ⟨γ, hγ, hvγ⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hvA
  rcases ResolvedCoassocSplitChoice.isLeftPrimitive_or_isRightPrimitive_or_isForestChoice q.1 ⟨γ, hγ⟩ with
    hLeft | hRight | hForest
  · -- LEFT: γ ∈ leftOf ⊆ selectedOuter, so v ∈ selectedOuter.vertices — contradiction with hvS.
    exfalso
    have hlsc : ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 γ :=
      (ResolvedCoassocSplitChoice.isLeftPrimitive_iff_leftSelectedConcrete q.1 ⟨γ, hγ⟩).mp hLeft
    have hγOuter : γ ∈ ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData
        G).selectedOuterRawOf q.1).elements := by
      simp only [ResolvedForestPromoteSupply.selectedOuterRawOf, ResolvedAdmissibleSubgraph.union_elements,
        Finset.mem_union]
      refine Or.inl ?_
      show γ ∈ ((resolvedConcreteLeftSelectionSupply canonicalLegSaturatedCarrierProperSupply.toData G).leftOf
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
          canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf q.1).elements :=
        promote_mem_selectedOuterRawOf_raw q.1 o hb
      have hvpromote : v ∈ (o.γ.1.promote b).vertices := by
        rw [ResolvedFeynmanSubgraph.promote_vertices]; exact hvb
      exact hvS (ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨o.γ.1.promote b, hpromMem, hvpromote⟩)
    have hvδ : v ∈ ((canonicalCorrectedRemnantComponentSupply canonicalLegSaturatedStarFacts
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1 o).vertices := by
      rw [show ((canonicalCorrectedRemnantComponentSupply canonicalLegSaturatedStarFacts
              canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1 o).vertices
            = (o.B.1.contractWithStars (promotedOccurrenceStar q.1 o)).vertices
          from correctedRemnantComponent_vertices_eq_promoted q.1 o canonicalLegSaturatedStarFacts,
        ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union]
      exact Or.inl (Finset.mem_sdiff.mpr ⟨hvγ, hvBnot⟩)
    have hδM : (canonicalCorrectedRemnantComponentSupply canonicalLegSaturatedStarFacts
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1 o
        ∈ ((canonicalCorrectedRemnantComponentSupply canonicalLegSaturatedStarFacts
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider).remnantForest q.1).elements := by
      rw [ResolvedRemnantComponentSupply.remnantForest_elements]
      exact Finset.mem_image.mpr ⟨⟨⟨γ, hγ⟩, hfmem⟩, Finset.mem_attach _ _, rfl⟩
    refine ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨_, ?_, hvδ⟩
    simp only [canonicalCorrectedQuotientRaw, ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union]
    exact Or.inr hδM

/-- **R-6c-body-543 ∎ — star coverage.**  A selected-outer star that is not in the corrected quotient is the corrected
`legSaturatedTargetLeftStar` of a LEFT one-stage index (a `promotedOf` star would BE in the quotient). -/
theorem legSaturated_selectedOuterStar_not_mem_correctedQuotient_isLeft
    (Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData)
    (δ : ResolvedFeynmanSubgraph G)
    (hδ : δ ∈ ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData
      G).selectedOuterRawOf q.1).elements)
    (hnot : canonicalLegSaturatedCarrierProperSupply.toData.starOf G
        ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf q.1) δ
      ∉ (canonicalCorrectedQuotientRaw Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
        canonicalLegSaturatedStarFacts q.1).vertices) :
    ∃ i : OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1,
      i.isLeft ∧ legSaturatedTargetLeftStar q i = canonicalLegSaturatedCarrierProperSupply.toData.starOf G
        ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf q.1)
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
      have hstar_in : canonicalLegSaturatedCarrierProperSupply.toData.starOf G
            ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
              q.1) δ
          ∈ ((canonicalCorrectedRemnantComponentSupply canonicalLegSaturatedStarFacts
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1 o).vertices := by
        rw [show ((canonicalCorrectedRemnantComponentSupply canonicalLegSaturatedStarFacts
                canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1 o).vertices
              = (o.B.1.contractWithStars (promotedOccurrenceStar q.1 o)).vertices
            from correctedRemnantComponent_vertices_eq_promoted q.1 o canonicalLegSaturatedStarFacts,
          ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union]
        refine Or.inr (ResolvedAdmissibleSubgraph.mem_starVertices.mpr ⟨b, hb', ?_⟩)
        show canonicalLegSaturatedCarrierProperSupply.toData.starOf G
            ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
              q.1) (o.γ.1.promote b)
          = canonicalLegSaturatedCarrierProperSupply.toData.starOf G
            ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
              q.1) δ
        exact congrArg _ hbeq
      have hδM : (canonicalCorrectedRemnantComponentSupply canonicalLegSaturatedStarFacts
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1 o
          ∈ ((canonicalCorrectedRemnantComponentSupply canonicalLegSaturatedStarFacts
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider).remnantForest q.1).elements := by
        rw [ResolvedRemnantComponentSupply.remnantForest_elements]
        exact Finset.mem_image.mpr ⟨⟨γ, hfc⟩, Finset.mem_attach _ _, rfl⟩
      refine hnot (ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨_, ?_, hstar_in⟩)
      simp only [canonicalCorrectedQuotientRaw, ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union]
      exact Or.inr hδM

/-- **R-6c-body-543 ∎ — the corrected two-stage survivor partition.**  A surviving vertex of the corrected quotient is an
input-outer surviving vertex OR the corrected `legSaturatedTargetLeftStar` of a left one-stage index.  The legacy
the legacy `i.vertex`-identity form is NEVER used. -/
theorem canonicalLegSaturatedCorrectedTwoStageSurvivor_cases
    (Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData)
    {v : VertexId}
    (h : isContractSurvivingVertex (canonicalCorrectedQuotientRaw Measure
      canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
      canonicalLegSaturatedStarFacts q.1) v) :
    isContractSurvivingVertex q.1.1.1 v ∨
      ∃ i : OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1,
        i.isLeft ∧ legSaturatedTargetLeftStar q i = v := by
  obtain ⟨h1, h2⟩ := h
  rw [ResolvedCoassocSplitChoice.selectedOuterContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at h1
  rcases h1 with hSurv | hStar
  · -- survivor branch: v ∈ G.vertices \ selectedOuter.vertices.
    obtain ⟨hvG, hvS⟩ := Finset.mem_sdiff.mp hSurv
    refine Or.inl ⟨hvG, ?_⟩
    intro hvA
    exact h2 (legSaturated_inputOuter_survivor_mem_correctedQuotient q Measure hvA hvS)
  · -- star branch: v is a selected-outer star; feed the star coverage.
    obtain ⟨δ, hδ, hstar⟩ := ResolvedAdmissibleSubgraph.mem_starVertices.mp hStar
    obtain ⟨i, hiL, hieq⟩ := legSaturated_selectedOuterStar_not_mem_correctedQuotient_isLeft q Measure δ hδ (hstar ▸ h2)
    exact Or.inr ⟨i, hiL, hieq.trans hstar⟩

/-! ## Step 5 — branch anchors for body-544 (generic `Equiv` inverse laws, `W″` re-key). -/

/-- **R-6c-body-543 — the one-stage star recovery's vertex.**  `(recover w).vertex = w.1`. -/
theorem canonicalLegSaturatedOneStageStarRecover_vertex
    (w : {v : VertexId // isContractStarVertex q.1.1.1
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v}) :
    (canonicalLegSaturatedOneStageStarRecover q w).vertex = w.1 :=
  congrArg Subtype.val
    (show (canonicalLegSaturatedOneStageStarRecover q w).toStarVertex = w
      from (canonicalLegSaturatedOneStageStarRecover q).symm_apply_apply w)

/-- **R-6c-body-543 — the one-stage star recovery round-trip** (`recover (vertex i) = i`). -/
theorem canonicalLegSaturatedOneStageStarRecover_apply
    (i : OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1) :
    canonicalLegSaturatedOneStageStarRecover q i.toStarVertex = i :=
  (canonicalLegSaturatedOneStageStarRecover q).apply_symm_apply i

/-- **R-6c-body-543 — the quotient-star vertex equiv round-trip** (`equiv.symm (equiv k) = k`), reading `R`. -/
theorem canonicalLegSaturatedCorrectedQuotientStarVertexEquiv_symm_apply
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    (k : {i : OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1 // i.hasQuotientStar}) :
    (canonicalLegSaturatedCorrectedQuotientStarVertexEquiv R q).symm
        (canonicalLegSaturatedCorrectedQuotientStarVertexEquiv R q k) = k :=
  (canonicalLegSaturatedCorrectedQuotientStarVertexEquiv R q).symm_apply_apply k

end GaugeGeometry.QFT.Combinatorial
