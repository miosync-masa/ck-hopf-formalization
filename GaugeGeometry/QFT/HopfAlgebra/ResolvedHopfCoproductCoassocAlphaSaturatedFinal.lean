import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSaturatedQuotEq
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSaturatedConstructionRoot
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaNativeFilteredValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSurvivorDischarge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSplitDischarge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaBijectionSide
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaParentSection
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaOccurrenceInversionInhabit
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaLeftBridgeForwardOcc
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRegionAssemblyForwardOcc
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaLeavesForwardOcc
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaOccurrenceDischarged

/-!
# R-6c-body-546 — the `W″` re-key TERMINUS (PROVED)

Five-hundred-and-forty-sixth genuine-body step — the terminus of the `W″` re-key campaign.  A single owner
`R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E` (body-541) is threaded through the entire alpha assembly
chain, re-keying bodies ~483–510's `W′`-canonical wrappers (which were keyed to the `W′` supported-carrier / star-facts /
`VBuild`) to the `W″` carrier `canonicalLegSaturatedCarrierProperSupply` / `canonicalLegSaturatedStarFacts`, reading
only `R`.

The value / split / parent / occurrence / bridge / tag / round-trip wrappers all read the SAME upstream owners
(`R.Core` / `R.ClosureBundle` / `R.Fmem` / `R.quotient_mem` / `R.quot_eq` / `R.M` / `R.V`), each issued EXACTLY ONCE.

## Owner chain (single-issuance invariant)

* `R := ⟨Measure, Parent⟩ : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E` — built ONCE.
* `R.Core` (541) / `R.ClosureBundle` (541) / `R.Fmem` (541) / `R.quotient_mem` (541) / `R.quot_eq` (545) — single-owner
  projections; read, never rebuilt.
* `R.M := R.Core.toDecontractionSupply R.ClosureBundle.Closure` — issued ONCE.
* `R.V` — the filtered value supply, issued ONCE (Step 1).

## Substitution key (each `W′` canonical wrapper → `W″`)

```text
W′ value-geometry de-contraction supply   ↦  R.M
W′ value-geometry core                     ↦  R.Core
W′ star facts                              ↦  canonicalLegSaturatedStarFacts
W′ VBuild measure                          ↦  R.Measure
W′ VBuild selected-outer filtered mem      ↦  R.Fmem
W′ VBuild canonical filtered value         ↦  R.V
W′ supported carrier                       ↦  canonicalLegSaturatedCarrierProperSupply
```

Per the HALT/guards: `Fmem` / `Split` / `quotient_mem` / `quot_eq` / `OccRaw` are NOT re-introduced as sockets (they are
`R`'s derived projections); NO `W′` ValueGeometry / LegModel / OccRaw / final-wrapper is cast; NO `W′` carrier is read;
strict `StarProm` / `InnerStarRaw` stay ZERO; no local-permutation comparison; no `∀ v` retarget equality; the
input-outer left star is never asserted equal to the selected-outer left star.  No facade, no flat term, no `forgetHopf`,
no rep/perm.
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

/-! ## Step 1 — the single-owner filtered value `R.V`. -/

/-- **R-6c-body-546 — the `W″` reduced alpha filtered-quotient construction root, from `R`.**  `Measure := R.Measure`;
`Quotient` = `R.quotient_mem` (541) + `R.quot_eq` (545). -/
noncomputable def ResolvedCanonicalLegSaturatedAlphaConstructionSupply.toAlphaNativeFilteredQuotientConstructionSupply
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    ResolvedAlphaNativeFilteredQuotientConstructionSupply
      canonicalLegSaturatedCarrierProperSupply.toData
      canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
      canonicalLegSaturatedStarFacts where
  Measure := R.Measure
  Quotient :=
    { quotient_mem := fun q => R.quotient_mem q
      quot_eq := fun q => R.quot_eq q }

/-- **R-6c-body-546 — the `W″` alpha-native filtered value construction root (body-498 converter).** -/
noncomputable def ResolvedCanonicalLegSaturatedAlphaConstructionSupply.VBuild
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    ResolvedAlphaNativeFilteredValueConstructionSupply
      canonicalLegSaturatedCarrierProperSupply.toData
      canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
      canonicalLegSaturatedStarFacts :=
  R.toAlphaNativeFilteredQuotientConstructionSupply.toAlphaNativeFilteredValueConstructionSupply

/-- **R-6c-body-546 — the SINGLE filtered value owner `R.V` (body-471 projection).** -/
noncomputable def ResolvedCanonicalLegSaturatedAlphaConstructionSupply.V
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    ResolvedFilteredConcreteSummandValueSupply canonicalLegSaturatedCarrierProperSupply.toData :=
  R.VBuild.toFilteredConcreteSummandValueSupply
    canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider canonicalLegSaturatedStarFacts

/-- **R-6c-body-546 — bank: `R.V.Measure = R.Measure`** (`rfl`). -/
theorem ResolvedCanonicalLegSaturatedAlphaConstructionSupply.V_measure
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    R.V.Measure = R.Measure :=
  rfl

/-! ## Step 2 — the single-owner de-contraction supply `R.M`. -/

/-- **R-6c-body-546 — the SINGLE de-contraction supply owner `R.M`.**  `R.Core.toDecontractionSupply
`R.ClosureBundle.Closure`, issued ONCE. -/
noncomputable def ResolvedCanonicalLegSaturatedAlphaConstructionSupply.M
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    ResolvedMultiStarDecontractionSupply canonicalLegSaturatedCarrierProperSupply.toData :=
  R.Core.toDecontractionSupply R.ClosureBundle.Closure

/-! ## Step 3 — the `W″` alpha region-split `Split` (body-497 re-key). -/

/-- **R-6c-body-546 — the `W″` alpha `Split` supply.**  The generic body-497 constructor at the `W″` star-facts /
carrier / value owners; `Fmem := R.Fmem`. -/
noncomputable def canonicalLegSaturatedAlphaValueQuotientRegionSplitSupply
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    ResolvedAlphaValueQuotientRegionSplitSupply R.Fmem R.V :=
  canonicalAlphaValueQuotientRegionSplitSupply
    canonicalLegSaturatedStarFacts
    canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
    R.VBuild
    R.Fmem

/-! ## Step 4 — the `W″` corrected-parent geometry + forward occurrence-inversion (bodies 484/485/502/503 re-key). -/

/-- **R-6c-body-546 — the `W″` block-local id supply** (body-445 mirror; `W″` membership → `W′` → id-uniqueness). -/
def canonicalLegSaturatedFilteredForestBlockIds :
    ResolvedFilteredForestBlockUniqueIdSupply canonicalLegSaturatedCarrierProperSupply.toData where
  edgeIdsUnique := fun {_G} q => edgeIdsUnique_of_carrier_mem (canonicalLegSaturatedCarrier_mem_W' q.1.1.2)
  legIdsUnique := fun {_G} q => legIdsUnique_of_carrier_mem (canonicalLegSaturatedCarrier_mem_W' q.1.1.2)

variable {Fmem : ResolvedSelectedOuterFilteredMemSupply canonicalLegSaturatedCarrierProperSupply.toData}

/-- **R-6c-body-546 — the corrected touched-collection theorem, re-keyed** (body-484). -/
theorem legSaturatedTouchedOuterComponents_of_corrected_occurrence_alpha
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem R.V q)})
    (hδ : HEq (R.V.Remnant.remnant.remnantComponent q.1 o) δ.1) :
    touchedOuterComponents (fwdMapFilteredAlphaValue Fmem R.V q) δ.1
      = (ResolvedAdmissibleSubgraph.promote o.γ.1 o.B.1).elements := by
  have hcr : (canonicalCorrectedRemnantReembedSupply q.1 canonicalLegSaturatedStarFacts).correctedRemnantComponent o
      = δ.1 := eq_of_heq hδ
  have hδv : δ.1.vertices
      = (o.γ.1.toResolvedFeynmanGraph.vertices \ o.B.1.vertices)
        ∪ o.B.1.starVertices (promotedOccurrenceStar q.1 o) := by
    rw [← hcr, correctedRemnantComponent_vertices_eq_promoted q.1 o canonicalLegSaturatedStarFacts,
      ResolvedAdmissibleSubgraph.contractWithStars_vertices]
  apply Finset.ext
  intro A
  simp only [mem_touchedOuterComponents, ResolvedAdmissibleSubgraph.promote_elements,
    Finset.mem_image]
  constructor
  · rintro ⟨hAmem, hstar⟩
    rw [hδv] at hstar
    rcases Finset.mem_union.mp hstar with hout | hstarv
    · exfalso
      rw [Finset.mem_sdiff] at hout
      exact canonicalLegSaturatedStarFacts.starOf_fresh G _ A hAmem (o.γ.1.vertices_subset hout.1)
    · rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hstarv
      obtain ⟨b, hb, hbstar⟩ := hstarv
      have hpmem : o.γ.1.promote b
          ∈ (fwdMapFilteredAlphaValue Fmem R.V q).1.1.elements :=
        promote_mem_selectedOuterRawOf_raw q.1 o hb
      exact ⟨b, hb, canonicalLegSaturatedStarFacts.starOf_injective G _ hpmem hAmem hbstar⟩
  · rintro ⟨b, hb, rfl⟩
    have hpmem : o.γ.1.promote b
        ∈ (fwdMapFilteredAlphaValue Fmem R.V q).1.1.elements :=
      promote_mem_selectedOuterRawOf_raw q.1 o hb
    refine ⟨hpmem, ?_⟩
    rw [hδv]
    exact Finset.mem_union.mpr
      (Or.inr (ResolvedAdmissibleSubgraph.mem_starVertices.mpr ⟨b, hb, rfl⟩))

/-- **R-6c-body-546 — the corrected edge preimage is the occurrence's complement edges** (body-485). -/
theorem legSaturated_quotientEdgePreimage_eq_occurrence_complement_alpha
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem R.V q)})
    (hδ : HEq (R.V.Remnant.remnant.remnantComponent q.1 o) δ.1) :
    quotientEdgePreimage (touchedOuterForest (fwdMapFilteredAlphaValue Fmem R.V q) δ.1)
        (canonicalLegSaturatedCarrierProperSupply.toData.starOf G
          (fwdMapFilteredAlphaValue Fmem R.V q).1.1)
        (touchedLocalComponent (fwdMapFilteredAlphaValue Fmem R.V q) δ.1)
      = o.B.1.complementEdges := by
  have he := legSaturatedTouchedOuterComponents_of_corrected_occurrence_alpha R q o δ hδ
  have hcr : (canonicalCorrectedRemnantReembedSupply q.1 canonicalLegSaturatedStarFacts).correctedRemnantComponent o
      = δ.1 := eq_of_heq hδ
  have hδint : δ.1.internalEdges
      = (o.B.1.contractWithStars (promotedOccurrenceStar q.1 o)).internalEdges := by
    rw [← hcr]; exact (promotedCorrectedSource_internalEdges canonicalLegSaturatedStarFacts q.1 o).symm
  have hM₁ : quotientEdgePreimage
        (touchedOuterForest (fwdMapFilteredAlphaValue Fmem R.V q) δ.1)
        (canonicalLegSaturatedCarrierProperSupply.toData.starOf G
          (fwdMapFilteredAlphaValue Fmem R.V q).1.1)
        (touchedLocalComponent (fwdMapFilteredAlphaValue Fmem R.V q) δ.1)
      ≤ G.internalEdges := by
    refine le_trans (quotientEdgePreimage_le _ _ _) ?_
    rw [ResolvedAdmissibleSubgraph.complementEdges]; exact tsub_le_self
  have hM₂ : o.B.1.complementEdges ≤ G.internalEdges := by
    rw [ResolvedAdmissibleSubgraph.complementEdges]
    exact le_trans tsub_le_self o.γ.1.internalEdges_le
  refine (touchedOuterForest (fwdMapFilteredAlphaValue Fmem R.V q) δ.1).retarget_residual_edges_injective
    (canonicalLegSaturatedFilteredForestBlockIds.edgeIdsUnique q)
    (canonicalLegSaturatedCarrierProperSupply.toData.starOf G
      (fwdMapFilteredAlphaValue Fmem R.V q).1.1) hM₁ hM₂ ?_
  rw [quotientEdgePreimage_map, touchedLocalComponent_internalEdges,
    Multiset.map_congr rfl (fun e _ => promoted_retargetEdge_eq_inner_alpha q o δ he e),
    ← ResolvedAdmissibleSubgraph.contractWithStars_internalEdges]
  exact hδint

/-- **R-6c-body-546 — the corrected internal-edges projection** (body-485). -/
theorem legSaturated_parent_remnantComponent_internalEdges_alpha
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem R.V q)})
    (hδ : HEq (R.V.Remnant.remnant.remnantComponent q.1 o) δ.1) :
    (R.Core.parent (fwdMapFilteredAlphaValue Fmem R.V q) δ).internalEdges
      = o.γ.1.internalEdges := by
  have he := legSaturatedTouchedOuterComponents_of_corrected_occurrence_alpha R q o δ hδ
  show (touchedOuterForest (fwdMapFilteredAlphaValue Fmem R.V q) δ.1).internalEdges
      + quotientEdgePreimage
          (touchedOuterForest (fwdMapFilteredAlphaValue Fmem R.V q) δ.1)
          (canonicalLegSaturatedCarrierProperSupply.toData.starOf G
            (fwdMapFilteredAlphaValue Fmem R.V q).1.1)
          (touchedLocalComponent (fwdMapFilteredAlphaValue Fmem R.V q) δ.1)
      = o.γ.1.internalEdges
  rw [legSaturated_quotientEdgePreimage_eq_occurrence_complement_alpha R q o δ hδ]
  have ht : (touchedOuterForest (fwdMapFilteredAlphaValue Fmem R.V q) δ.1).internalEdges
      = o.B.1.internalEdges := by
    have h1 : (touchedOuterForest (fwdMapFilteredAlphaValue Fmem R.V q) δ.1).internalEdges
        = (ResolvedAdmissibleSubgraph.promote o.γ.1 o.B.1).internalEdges := by
      unfold ResolvedAdmissibleSubgraph.internalEdges
      rw [touchedOuterForest_elements, he]
    rw [h1, promote_internalEdges_eq]
  rw [ht, ResolvedAdmissibleSubgraph.complementEdges]
  exact add_tsub_cancel_of_le
    (resolvedAdmissibleSubgraph_internalEdges_le_of_pairwise o.B.1 o.B.1.isPairwiseDisjoint)

/-- **R-6c-body-546 — the corrected external-legs projection** (body-485). -/
theorem legSaturated_parent_remnantComponent_externalLegs_alpha
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem R.V q)})
    (hδ : HEq (R.V.Remnant.remnant.remnantComponent q.1 o) δ.1) :
    (R.Core.parent (fwdMapFilteredAlphaValue Fmem R.V q) δ).externalLegs
      = o.γ.1.externalLegs := by
  have he := legSaturatedTouchedOuterComponents_of_corrected_occurrence_alpha R q o δ hδ
  have hcr : (canonicalCorrectedRemnantReembedSupply q.1 canonicalLegSaturatedStarFacts).correctedRemnantComponent o
      = δ.1 := eq_of_heq hδ
  have hδleg : δ.1.externalLegs
      = (o.B.1.contractWithStars (promotedOccurrenceStar q.1 o)).externalLegs := by
    rw [← hcr]; exact (promotedCorrectedSource_externalLegs canonicalLegSaturatedStarFacts q.1 o).symm
  show (R.Core.legLift
      (fwdMapFilteredAlphaValue Fmem R.V q) δ).legs = o.γ.1.externalLegs
  refine (touchedOuterForest (fwdMapFilteredAlphaValue Fmem R.V q) δ.1).retarget_residual_legs_injective
    (canonicalLegSaturatedFilteredForestBlockIds.legIdsUnique q)
    (canonicalLegSaturatedCarrierProperSupply.toData.starOf G
      (fwdMapFilteredAlphaValue Fmem R.V q).1.1)
    (R.Core.legLift
      (fwdMapFilteredAlphaValue Fmem R.V q) δ).legs_le o.γ.1.externalLegs_le ?_
  rw [(R.Core.legLift
        (fwdMapFilteredAlphaValue Fmem R.V q) δ).map_eq,
    touchedLocalComponent_externalLegs,
    Multiset.map_congr rfl (fun ℓ _ => promoted_retargetExternalLeg_eq_inner_alpha q o δ he ℓ)]
  exact hδleg

/-- **R-6c-body-546 — the corrected vertices projection** (body-485). -/
theorem legSaturated_parent_remnantComponent_vertices_alpha
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem R.V q)})
    (hδ : HEq (R.V.Remnant.remnant.remnantComponent q.1 o) δ.1) :
    (R.Core.parent (fwdMapFilteredAlphaValue Fmem R.V q) δ).vertices
      = o.γ.1.vertices := by
  have hEdges := legSaturated_parent_remnantComponent_internalEdges_alpha R q o δ hδ
  have hγConn := (q.1.1.1.isConnectedDivergent o.γ.1 o.γ.2).1
  have hγPos := (canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider.carrier_isProperForest
    G q.1.1.1 q.1.1.2).2.2.2.1 o.γ.1 o.γ.2
  have hParentConn : (R.Core.parent
      (fwdMapFilteredAlphaValue Fmem R.V q) δ).forget.IsConnected :=
    (R.Core.parentCD
      (fwdMapFilteredAlphaValue Fmem R.V q) δ).1
  have hParentPos : 0 < (R.Core.parent
      (fwdMapFilteredAlphaValue Fmem R.V q) δ).internalEdges.card := by
    rw [hEdges]; exact hγPos
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨e, he, hend⟩ :=
      resolvedSubgraph_vertex_incident_edge_of_connected_pos hParentConn hParentPos hv
    rw [hEdges] at he
    obtain ⟨hs, ht⟩ := o.γ.1.edges_supported e he
    rcases hend with h | h
    · rw [← h]; exact hs
    · rw [← h]; exact ht
  · intro v hv
    obtain ⟨e, he, hend⟩ :=
      resolvedSubgraph_vertex_incident_edge_of_connected_pos hγConn hγPos hv
    rw [← hEdges] at he
    obtain ⟨hs, ht⟩ := (R.Core.parent
      (fwdMapFilteredAlphaValue Fmem R.V q) δ).edges_supported e he
    rcases hend with h | h
    · rw [← h]; exact hs
    · rw [← h]; exact ht

/-- **R-6c-body-546 — the corrected parent equality** (body-485). -/
theorem legSaturated_parent_remnantComponent_of_multiStar_alpha_geometry
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem R.V q)})
    (hδ : HEq (R.V.Remnant.remnant.remnantComponent q.1 o) δ.1) :
    R.Core.parent (fwdMapFilteredAlphaValue Fmem R.V q) δ = o.γ.1 :=
  parent_remnantComponent_of_data R.Core _ δ o.γ.1
    (legSaturated_parent_remnantComponent_vertices_alpha R q o δ hδ)
    (legSaturated_parent_remnantComponent_internalEdges_alpha R q o δ hδ)
    (legSaturated_parent_remnantComponent_externalLegs_alpha R q o δ hδ)

/-- **R-6c-body-546 — the canonical promoted-collection identity** (body-502). -/
theorem legSaturated_promoted_innerIdx_elements_eq_promoted_B_alpha
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x : ResolvedFeynmanSubgraph
        ((fwdMapFilteredAlphaValue Fmem R.V q).1.1.contractWithStars
          (canonicalLegSaturatedCarrierProperSupply.toData.starOf G
            (fwdMapFilteredAlphaValue Fmem R.V q).1.1)) //
      x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem R.V q)})
    (hδ : HEq (R.V.Remnant.remnant.remnantComponent q.1 o) δ.1) :
    (ResolvedAdmissibleSubgraph.promote
        (R.M.parent (fwdMapFilteredAlphaValue Fmem R.V q) δ)
        (R.M.innerIdx (fwdMapFilteredAlphaValue Fmem R.V q) δ).1).elements
      = (ResolvedAdmissibleSubgraph.promote o.γ.1 o.B.1).elements :=
  (promote_innerRaw_elements (fwdMapFilteredAlphaValue Fmem R.V q) δ.1
    (R.M.legLift (fwdMapFilteredAlphaValue Fmem R.V q) δ)
    (R.M.hE (fwdMapFilteredAlphaValue Fmem R.V q))
    (R.M.hL (fwdMapFilteredAlphaValue Fmem R.V q))).trans
    (legSaturatedTouchedOuterComponents_of_corrected_occurrence_alpha R q o δ hδ)

/-- **R-6c-body-546 — the canonical faithful forward occurrence-inversion socket, CONSTRUCTED** (body-503). -/
noncomputable def canonicalLegSaturatedForwardForestOccurrenceInversionAlphaValueSupply
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    ResolvedForwardForestOccurrenceInversionAlphaValueSupply R.M R.Fmem R.V where
  occurrence_inner_idx_alpha := fun {G} q δ o hparent => by
    have hmem : δ.1 ∈ (R.V.Remnant.remnant.remnantForest q.1).elements :=
      ((canonicalLegSaturatedAlphaValueQuotientRegionSplitSupply R).forestDomain_value_mem_alpha q δ.1).mp δ.2
    rw [ResolvedRemnantComponentSupply.remnantForest_elements] at hmem
    obtain ⟨γ', -, hγ'⟩ := Finset.mem_image.mp hmem
    set o' := ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 γ' with ho'
    have hδ' : HEq (R.V.Remnant.remnant.remnantComponent q.1 o') δ.1 :=
      heq_of_eq hγ'
    have hpar' : R.Core.parent
          (fwdMapFilteredAlphaValue R.Fmem R.V q) δ = o'.γ.1 :=
      legSaturated_parent_remnantComponent_of_multiStar_alpha_geometry R q o' δ hδ'
    have hoeq : o = o' := ForestChoiceOccurrence.eq_of_parent_eq (hparent.symm.trans hpar')
    have hprom := legSaturated_promoted_innerIdx_elements_eq_promoted_B_alpha R q o' δ hδ'
    have helem := promote_elements_cancel hpar' hprom
    exact hoeq.symm ▸ heq_forestIdx_of_graph_eq _ o'.B
      (congrArg ResolvedFeynmanSubgraph.toResolvedFeynmanGraph hpar') helem

/-! ## Step 5 — the six-bridge region assembly (bodies 483/486/504 re-key). -/

/-- **R-6c-body-546 — the `W″` alpha RIGHT bridge** (body-483). -/
noncomputable def resolvedCanonicalLegSaturatedRightAlphaBridge
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    ResolvedRightRegionAlphaValueCoreBridgeSupply R.Fmem R.V :=
  resolvedMultiStarRightAlphaBridge R.M
    canonicalLegSaturatedStarFacts R.Measure
    (canonicalLegSaturatedAlphaValueQuotientRegionSplitSupply R)
    (fun _s _γ => rfl)

/-- **R-6c-body-546 — the `W″` alpha FOREST bridge** (body-486, parent datum = the re-keyed body-485 theorem). -/
noncomputable def resolvedCanonicalLegSaturatedForestAlphaBridge
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    ResolvedForestRegionAlphaValueCoreBridgeSupply R.Fmem R.V :=
  resolvedMultiStarForestAlphaBridge R.M
    canonicalLegSaturatedStarFacts
    (canonicalLegSaturatedAlphaValueQuotientRegionSplitSupply R)
    (fun q o δ hδ =>
      legSaturated_parent_remnantComponent_of_multiStar_alpha_geometry R q o δ hδ)

/-- **R-6c-body-546 — the `W″` alpha LEFT bridge, OccRaw-FREE** (body-504, faithful `ForwardOcc`). -/
noncomputable def resolvedCanonicalLegSaturatedLeftAlphaBridge_forwardOcc
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    ResolvedLeftResidualAlphaValueCoreBridgeSupply R.Fmem R.V :=
  R.M.resolvedMultiStarLeftAlphaBridge_forwardOcc
    (canonicalLegSaturatedForwardForestOccurrenceInversionAlphaValueSupply R)
    R.Measure (canonicalLegSaturatedAlphaValueQuotientRegionSplitSupply R)
    (fun q o δ hδ =>
      legSaturated_parent_remnantComponent_of_multiStar_alpha_geometry R q o δ hδ)

/-- **R-6c-body-546 — the `W″` OccRaw-free six-bridge region assembly** (body-508 mirror). -/
noncomputable def resolvedCanonicalLegSaturatedRegionAlphaBridgeAssembly
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    ResolvedRecoveredRegionAlphaValueBridgeAssemblySupply R.Fmem R.V where
  Region := multiStarRegion R.M canonicalLegSaturatedStarFacts
  Left := multiStarLeft
  right_sound_value := (resolvedCanonicalLegSaturatedRightAlphaBridge R).right_sound_value
  right_complete_value := (resolvedCanonicalLegSaturatedRightAlphaBridge R).right_complete_value
  forest_sound_value := (resolvedCanonicalLegSaturatedForestAlphaBridge R).forest_sound_value
  forest_complete_value := (resolvedCanonicalLegSaturatedForestAlphaBridge R).forest_complete_value
  left_sound_value := (resolvedCanonicalLegSaturatedLeftAlphaBridge_forwardOcc R).left_sound_value
  left_complete_value := (resolvedCanonicalLegSaturatedLeftAlphaBridge_forwardOcc R).left_complete_value

/-! ## Step 6 — the SINGLE `W″` faithful region tag owner `TagsF` (body-508 converter). -/

/-- **R-6c-body-546 — the SINGLE canonical faithful region tag owner `TagsF`.**  The body-488 generic converter fed the
six-bridge assembly's projections + `R.ClosureBundle.recovered_raw_mem`.  No `OccRaw`. -/
noncomputable def canonicalLegSaturatedRegionTagAlphaValueSupply
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    ResolvedRegionTagAlphaValueSupply R.Fmem R.V :=
  let A := resolvedCanonicalLegSaturatedRegionAlphaBridgeAssembly R
  multiStarRegionTagAlphaValueSupply R.M
    canonicalLegSaturatedStarFacts R.Measure
    A.right_sound_value A.right_complete_value A.forest_sound_value A.forest_complete_value
    A.left_sound_value A.left_complete_value
    R.ClosureBundle.recovered_raw_mem

/-- **R-6c-body-546 — rfl anchor: `TagsF`'s assembly is the six-bridge assembly.** -/
theorem canonicalLegSaturatedRegionTagAlphaValueSupply_assembly
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    (canonicalLegSaturatedRegionTagAlphaValueSupply R).Closure.Assembly
      = resolvedCanonicalLegSaturatedRegionAlphaBridgeAssembly R :=
  rfl

/-! ## Step 7 — the four faithful geometry leaves over the single `TagsF` (body-509 re-key). -/

/-- **R-6c-body-546 — `houter`, over `TagsF`** (body-509). -/
theorem legSaturated_alpha_houter
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G) :
    (resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
        ((canonicalLegSaturatedRegionTagAlphaValueSupply R).recoveredPreimageAlphaValue z)
      = z.1.1 :=
  (canonicalLegSaturatedRegionTagAlphaValueSupply R).multiStar_selectedOuterRawOf_alpha_eq
    R.M canonicalLegSaturatedStarFacts R.Measure z rfl rfl
    (fun γ _ h' => R.M.promote_forestTag_elements canonicalLegSaturatedStarFacts z ⟨γ.1, h'⟩)

/-- **R-6c-body-546 — `forest_nonempty`, over `TagsF`** (body-509). -/
theorem legSaturated_alpha_forest_nonempty
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (hz : resolvedIsForestImage z.1 z.2) :
    ((canonicalLegSaturatedRegionTagAlphaValueSupply R).Closure.Assembly.Region.forestRecovered z).elements.Nonempty :=
  forestRecovered_nonempty_of_resolvedIsForestImage _ hz

/-- **R-6c-body-546 — `survivor_mem`, over `TagsF`** (body-509). -/
theorem legSaturated_alpha_survivor_mem
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
      ((canonicalLegSaturatedRegionTagAlphaValueSupply R).recoveredPreimageAlphaValue z)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)))
    (hx : HEq x₁ x₂) :
    x₁ ∈ ((survivorSupply_of_measure R.Measure G).rightSurvivorForest
        ((canonicalLegSaturatedRegionTagAlphaValueSupply R).recoveredPreimageAlphaValue z)).elements
      ↔ x₂ ∈ rightDomain z :=
  (canonicalLegSaturatedRegionTagAlphaValueSupply R).survivor_mem_alpha
    R.Measure z (legSaturated_alpha_houter R z) rfl x₁ x₂ hx

/-- **R-6c-body-546 — `remnant_mem`, over `TagsF`** (body-509). -/
theorem legSaturated_alpha_remnant_mem
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
      ((canonicalLegSaturatedRegionTagAlphaValueSupply R).recoveredPreimageAlphaValue z)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)))
    (hx : HEq x₁ x₂) :
    x₁ ∈ ((canonicalCorrectedRemnantComponentSupply canonicalLegSaturatedStarFacts
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider).remnantForest
        ((canonicalLegSaturatedRegionTagAlphaValueSupply R).recoveredPreimageAlphaValue z)).elements
      ↔ x₂ ∈ forestDomain z :=
  (canonicalLegSaturatedRegionTagAlphaValueSupply R).remnant_mem_alpha_forwardOcc
    R.M canonicalLegSaturatedStarFacts R.Measure
    canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
    (fun _ _ _ _ => rfl) (fun _ => rfl) z
    (legSaturated_alpha_houter R z) x₁ x₂ hx

/-! ## Step 8 — the membership boundary + `DataF` (body-510 re-key). -/

/-- **R-6c-body-546 — raw quotient elements HEq, over `TagsF`** (body-510). -/
theorem legSaturated_alpha_quotient_elements_heq
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G) :
    HEq (canonicalCorrectedQuotientRaw R.Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider canonicalLegSaturatedStarFacts
        ((canonicalLegSaturatedRegionTagAlphaValueSupply R).recoveredPreimageAlphaValue z)).elements
      z.2.1.elements :=
  canonicalCorrectedQuotient_elements_heq R.Measure
    canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider canonicalLegSaturatedStarFacts
    ((canonicalLegSaturatedRegionTagAlphaValueSupply R).recoveredPreimageAlphaValue z) z
    (legSaturated_alpha_houter R z)
    (fun x₁ x₂ hx => legSaturated_alpha_survivor_mem R z x₁ x₂ hx)
    (fun x₁ x₂ hx => legSaturated_alpha_remnant_mem R z x₁ x₂ hx)

/-- **R-6c-body-546 — the `p_R` exclusion, over `TagsF`** (body-510). -/
theorem legSaturated_mixed_ne_pR
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G) :
    ((canonicalLegSaturatedRegionTagAlphaValueSupply R).recoveredPreimageAlphaValue z).2
      ≠ (fun _ _ => Sum.inl false) := by
  intro hpR
  have hempty := selectedOuterRawOf_eq_empty_of_eq_pR
    ((canonicalLegSaturatedRegionTagAlphaValueSupply R).recoveredPreimageAlphaValue z) hpR
  rw [legSaturated_alpha_houter R z] at hempty
  have hne : (z.1.1).elements.Nonempty :=
    (canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider.carrier_isProperForest G z.1.1 z.1.2).1
  rw [hempty] at hne
  exact Finset.not_nonempty_empty hne

/-- **R-6c-body-546 — the `p_L` exclusion, over `TagsF`** (body-510; raw elements HEq before any filtered quotient). -/
theorem legSaturated_mixed_ne_pL
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G) :
    ((canonicalLegSaturatedRegionTagAlphaValueSupply R).recoveredPreimageAlphaValue z).2
      ≠ (fun _ _ => Sum.inl true) := by
  intro hpL
  have hg : ResolvedCoassocSplitChoice.selectedOuterContractGraph
        ((canonicalLegSaturatedRegionTagAlphaValueSupply R).recoveredPreimageAlphaValue z)
      = z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1) := by
    rw [ResolvedCoassocSplitChoice.selectedOuterContractGraph,
      legSaturated_alpha_houter R z]
  have hcard := finset_card_eq_of_heq (congrArg ResolvedFeynmanSubgraph hg)
    (legSaturated_alpha_quotient_elements_heq R z)
  set q := (canonicalLegSaturatedRegionTagAlphaValueSupply R).recoveredPreimageAlphaValue z
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
  have hempty : (canonicalCorrectedQuotientRaw R.Measure
      canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider canonicalLegSaturatedStarFacts q).elements = ∅ := by
    rw [canonicalCorrectedQuotientRaw]
    simp only [ResolvedAdmissibleSubgraph.union_elements,
      ResolvedRightSurvivorSupply.rightSurvivorForest_elements,
      ResolvedRemnantComponentSupply.remnantForest_elements, Finset.union_eq_empty,
      Finset.image_eq_empty, Finset.attach_eq_empty_iff]
    exact ⟨hR, hF⟩
  rw [hempty, Finset.card_empty] at hcard
  have hne : (z.2.1.elements).Nonempty :=
    (canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider.carrier_isProperForest _ z.2.1 z.2.2).1
  rw [← Finset.card_pos] at hne
  omega

/-- **R-6c-body-546 — the SINGLE `DataF` recovered-preimage membership owner** (body-510). -/
noncomputable def canonicalLegSaturatedRecoveredPreimageAlphaValueMemSupply
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    ResolvedRecoveredPreimageAlphaValueMemSupply R.Fmem R.V where
  Tags := canonicalLegSaturatedRegionTagAlphaValueSupply R
  forest_nonempty := fun {_G} z h => legSaturated_alpha_forest_nonempty R z h
  mixed_ne_pR := fun {_G} z _ => legSaturated_mixed_ne_pR R z
  mixed_ne_pL := fun {_G} z _ => legSaturated_mixed_ne_pL R z

/-! ## Step 9 — the OccRaw-free canonical alpha round-trip leaf `RoundTripF` (body-510 re-key). -/

/-- **R-6c-body-546 — the filtered forward-quotient HEq, over `DataF`** (body-510). -/
theorem legSaturated_alpha_forward_quotient
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G) :
    HEq (R.V.quotientForestRaw
        ((canonicalLegSaturatedRecoveredPreimageAlphaValueMemSupply R).recoveredFilteredPreimageAlphaValue z))
      z.2 :=
  heq_forestIdx _ z.2
    (legSaturated_alpha_houter R z)
    (legSaturated_alpha_quotient_elements_heq R z)

/-- **R-6c-body-546 — the full OccRaw-free canonical alpha round-trip leaf `RoundTripF`** (body-510). -/
noncomputable def canonicalLegSaturatedAlphaRoundTripLeafSupply
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply R.Fmem R.V where
  Data := canonicalLegSaturatedRecoveredPreimageAlphaValueMemSupply R
  forward_outer_value := fun z => legSaturated_alpha_houter R z
  forward_quotient_value := fun z => legSaturated_alpha_forward_quotient R z
  forest_value_eq := fun q γ hu B hmem hqB =>
    forest_value_eq_alpha_forwardOcc R.M canonicalLegSaturatedStarFacts
      (canonicalLegSaturatedForwardForestOccurrenceInversionAlphaValueSupply R)
      R.Measure
      (canonicalLegSaturatedRecoveredPreimageAlphaValueMemSupply R)
      (fun {_G} _z => rfl) (fun {_G} _z _γ' _h _h' => rfl) q γ hu B hmem hqB

/-! ## Step 10 — the final `W″` native `Δᵣ`-coassociativity (`Measure` / `E` / `Parent` / `rep*`). -/

/-- **R-6c-body-546 ∎ — the `W″` re-key TERMINUS.**  A single owner `R := ⟨Measure, Parent⟩` is threaded through the entire
alpha assembly; the round-trip leaf `RoundTripF` feeds the D-generic body-481 entry.  `Fmem` / `Split` / `quotient_mem` /
`quot_eq` / `OccRaw` are GONE (derived projections of `R`); `LegModel` / `ValueGeometry` are GONE (absorbed into `W″`
membership at bodies 533/540/541); strict `StarProm` / `InnerStarRaw` are ZERO.  The remaining explicit model residual is
`Measure` / `E` / `Parent` / `rep*`. -/
theorem coassoc_gen_of_canonicalLegSaturated_alpha
    (Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    (Parent : ResolvedCanonicalLegSaturatedDecontractionCDSupply)
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x))
    (x : ResolvedHopfGen) :
    canonicalLegSaturatedCarrierProperSupply.toData.coassocLeft (MvPolynomial.X x)
      = canonicalLegSaturatedCarrierProperSupply.toData.coassocRight (MvPolynomial.X x) :=
  coassoc_gen_of_recovered_preimage_alpha_value
    (canonicalLegSaturatedAlphaRoundTripLeafSupply
      (⟨Measure, Parent⟩ : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E))
    canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider.carrier_isProperForest
    rep repCD rep_gen x

end GaugeGeometry.QFT.Combinatorial
