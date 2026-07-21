import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaCorrectedTouched
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocParentVerticesConcrete
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocParentRemnantSectionValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedCorrectedSource

/-!
# R-6c-body-485 — the corrected parent three projections + parent equality (StarProm's last chain) (PROVED)

Four-hundred-and-eighty-fifth genuine-body step — the three parent/remnant projections (internal edges / external legs /
vertices) and the parent equality, over the canonical alpha `VBuild`'s CORRECTED remnant, closing WITHOUT strict
`StarProm`.  The corrected remnant's internal-edges / external-legs are the PROMOTED-star contraction's (body-456), and
the touched map equalities are body-484's corrected retarget bridges — so `promoted_star_agrees` vanishes from the parent
reconstruction chain entirely.  After this, strict `StarProm` is dead across the whole parent path.

* `quotientEdgePreimage_eq_occurrence_complement_alpha` — body-387 stage 3, over the corrected remnant + live
  `Ids.edgeIdsUnique`;
* `parent_remnantComponent_internalEdges_alpha` — body-387 stage 4 (the additive `touchedOuterForest.I + preimage =
  promote(B).I + B.complementEdges = o.γ.I`), NO new geometry;
* `parent_remnantComponent_externalLegs_alpha` — body-388, over `Core.legLift.map_eq` + live `Ids.legIdsUnique`;
* `parent_remnantComponent_vertices_alpha` — body-389 (internalEdges + no-isolated-vertex, both directions;
  `CarrierProper.carrier_isProperForest` + `Core.parentCD`); the external-legs equality is NOT consumed;
* `parent_remnantComponent_of_multiStar_alpha_geometry` — the parent equality via `parent_remnantComponent_of_data`
  (`ResolvedFeynmanSubgraph.ext`);
* `ResolvedParentRemnantSectionAlphaValueSupply` + `canonicalParentRemnantSectionAlphaValue` — the minimal section supply
  banked for the next body's forest bridge (canonical inhabitant = the theorem above).

Per the HALT/guards: the forest sound/complete bridge is NOT assembled; the left bridge / `OccRaw` are NOT entered; the
body-461 recovered round-trip is NOT used; corrected permutations are NOT compared to each other; global ID uniqueness is
NOT required (only the block-local live `Ids`); strict `StarProm` / `InnerStarRaw` / `Wiring` are NOT reintroduced;
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

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {Fmem : ResolvedSelectedOuterFilteredMemSupply canonicalUniqueSupportedCarrierProperSupply.toData}
  (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
  (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)

/-- **R-6c-body-485 — the corrected edge preimage is the occurrence's complement edges** (body-387 stage 3). -/
theorem quotientEdgePreimage_eq_occurrence_complement_alpha
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q)})
    (hδ : HEq (VBuild.toCanonicalFilteredValue.Remnant.remnant.remnantComponent q.1 o) δ.1) :
    quotientEdgePreimage (touchedOuterForest (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ.1)
        (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G
          (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q).1.1)
        (touchedLocalComponent (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ.1)
      = o.B.1.complementEdges := by
  have he := touchedOuterComponents_of_corrected_occurrence_alpha VBuild q o δ hδ
  have hcr : (canonicalCorrectedRemnantReembedSupply q.1 canonicalUniqueStarFactsOfW').correctedRemnantComponent o
      = δ.1 := eq_of_heq hδ
  have hδint : δ.1.internalEdges
      = (o.B.1.contractWithStars (promotedOccurrenceStar q.1 o)).internalEdges := by
    rw [← hcr]; exact (promotedCorrectedSource_internalEdges canonicalUniqueStarFactsOfW' q.1 o).symm
  have hM₁ : quotientEdgePreimage
        (touchedOuterForest (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ.1)
        (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G
          (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q).1.1)
        (touchedLocalComponent (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ.1)
      ≤ G.internalEdges := by
    refine le_trans (quotientEdgePreimage_le _ _ _) ?_
    rw [ResolvedAdmissibleSubgraph.complementEdges]; exact tsub_le_self
  have hM₂ : o.B.1.complementEdges ≤ G.internalEdges := by
    rw [ResolvedAdmissibleSubgraph.complementEdges]
    exact le_trans tsub_le_self o.γ.1.internalEdges_le
  refine (touchedOuterForest (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ.1).retarget_residual_edges_injective
    (canonicalUniqueFilteredForestBlockIds.edgeIdsUnique q)
    (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G
      (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q).1.1) hM₁ hM₂ ?_
  rw [quotientEdgePreimage_map, touchedLocalComponent_internalEdges,
    Multiset.map_congr rfl (fun e _ => promoted_retargetEdge_eq_inner_alpha q o δ he e),
    ← ResolvedAdmissibleSubgraph.contractWithStars_internalEdges]
  exact hδint

/-- **R-6c-body-485 — the corrected internal-edges projection** (body-387 stage 4). -/
theorem parent_remnantComponent_internalEdges_alpha
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q)})
    (hδ : HEq (VBuild.toCanonicalFilteredValue.Remnant.remnant.remnantComponent q.1 o) δ.1) :
    (ValueGeometry.toCoreBuild.toValueCore.parent
        (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ).internalEdges
      = o.γ.1.internalEdges := by
  have he := touchedOuterComponents_of_corrected_occurrence_alpha VBuild q o δ hδ
  show (touchedOuterForest (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ.1).internalEdges
      + quotientEdgePreimage
          (touchedOuterForest (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ.1)
          (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G
            (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q).1.1)
          (touchedLocalComponent (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ.1)
      = o.γ.1.internalEdges
  rw [quotientEdgePreimage_eq_occurrence_complement_alpha VBuild q o δ hδ]
  have ht : (touchedOuterForest (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ.1).internalEdges
      = o.B.1.internalEdges := by
    have h1 : (touchedOuterForest (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ.1).internalEdges
        = (ResolvedAdmissibleSubgraph.promote o.γ.1 o.B.1).internalEdges := by
      unfold ResolvedAdmissibleSubgraph.internalEdges
      rw [touchedOuterForest_elements, he]
    rw [h1, promote_internalEdges_eq]
  rw [ht, ResolvedAdmissibleSubgraph.complementEdges]
  exact add_tsub_cancel_of_le
    (resolvedAdmissibleSubgraph_internalEdges_le_of_pairwise o.B.1 o.B.1.isPairwiseDisjoint)

/-- **R-6c-body-485 — the corrected external-legs projection** (body-388). -/
theorem parent_remnantComponent_externalLegs_alpha
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q)})
    (hδ : HEq (VBuild.toCanonicalFilteredValue.Remnant.remnant.remnantComponent q.1 o) δ.1) :
    (ValueGeometry.toCoreBuild.toValueCore.parent
        (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ).externalLegs
      = o.γ.1.externalLegs := by
  have he := touchedOuterComponents_of_corrected_occurrence_alpha VBuild q o δ hδ
  have hcr : (canonicalCorrectedRemnantReembedSupply q.1 canonicalUniqueStarFactsOfW').correctedRemnantComponent o
      = δ.1 := eq_of_heq hδ
  have hδleg : δ.1.externalLegs
      = (o.B.1.contractWithStars (promotedOccurrenceStar q.1 o)).externalLegs := by
    rw [← hcr]; exact (promotedCorrectedSource_externalLegs canonicalUniqueStarFactsOfW' q.1 o).symm
  show (ValueGeometry.toCoreBuild.toValueCore.legLift
      (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ).legs = o.γ.1.externalLegs
  refine (touchedOuterForest (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ.1).retarget_residual_legs_injective
    (canonicalUniqueFilteredForestBlockIds.legIdsUnique q)
    (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G
      (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q).1.1)
    (ValueGeometry.toCoreBuild.toValueCore.legLift
      (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ).legs_le o.γ.1.externalLegs_le ?_
  rw [(ValueGeometry.toCoreBuild.toValueCore.legLift
        (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ).map_eq,
    touchedLocalComponent_externalLegs,
    Multiset.map_congr rfl (fun ℓ _ => promoted_retargetExternalLeg_eq_inner_alpha q o δ he ℓ)]
  exact hδleg

/-- **R-6c-body-485 — the corrected vertices projection** (body-389; internalEdges + no-isolated-vertex). -/
theorem parent_remnantComponent_vertices_alpha
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q)})
    (hδ : HEq (VBuild.toCanonicalFilteredValue.Remnant.remnant.remnantComponent q.1 o) δ.1) :
    (ValueGeometry.toCoreBuild.toValueCore.parent
        (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ).vertices
      = o.γ.1.vertices := by
  have hEdges := parent_remnantComponent_internalEdges_alpha VBuild ValueGeometry q o δ hδ
  have hγConn := (q.1.1.1.isConnectedDivergent o.γ.1 o.γ.2).1
  have hγPos := (canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider.carrier_isProperForest
    G q.1.1.1 q.1.1.2).2.2.2.1 o.γ.1 o.γ.2
  have hParentConn : (ValueGeometry.toCoreBuild.toValueCore.parent
      (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ).forget.IsConnected :=
    (ValueGeometry.toCoreBuild.toValueCore.parentCD
      (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ).1
  have hParentPos : 0 < (ValueGeometry.toCoreBuild.toValueCore.parent
      (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ).internalEdges.card := by
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
    obtain ⟨hs, ht⟩ := (ValueGeometry.toCoreBuild.toValueCore.parent
      (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ).edges_supported e he
    rcases hend with h | h
    · rw [← h]; exact hs
    · rw [← h]; exact ht

/-- **R-6c-body-485 ∎ — the corrected parent equality** (`ResolvedFeynmanSubgraph.ext` of the three projections). -/
theorem parent_remnantComponent_of_multiStar_alpha_geometry
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q)})
    (hδ : HEq (VBuild.toCanonicalFilteredValue.Remnant.remnant.remnantComponent q.1 o) δ.1) :
    ValueGeometry.toCoreBuild.toValueCore.parent
        (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ = o.γ.1 :=
  parent_remnantComponent_of_data ValueGeometry.toCoreBuild.toValueCore _ δ o.γ.1
    (parent_remnantComponent_vertices_alpha VBuild ValueGeometry q o δ hδ)
    (parent_remnantComponent_internalEdges_alpha VBuild ValueGeometry q o δ hδ)
    (parent_remnantComponent_externalLegs_alpha VBuild ValueGeometry q o δ hδ)

/-- **R-6c-body-485 — the minimal alpha parent/remnant section supply** (banked for the next body's forest bridge). -/
structure ResolvedParentRemnantSectionAlphaValueSupply
    (Core : ResolvedMultiStarDecontractionValueCoreSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (Fmem : ResolvedSelectedOuterFilteredMemSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (V : ResolvedFilteredConcreteSummandValueSupply canonicalUniqueSupportedCarrierProperSupply.toData) where
  /-- The de-contracted parent of a corrected remnant component is the occurrence's source outer. -/
  parent_remnantComponent : ∀ {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem V q)}),
    HEq (V.Remnant.remnant.remnantComponent q.1 o) δ.1 →
    Core.parent (fwdMapFilteredAlphaValue Fmem V q) δ = o.γ.1

/-- **R-6c-body-485 — the canonical inhabitant of the alpha parent section** (the theorem above). -/
noncomputable def canonicalParentRemnantSectionAlphaValue :
    ResolvedParentRemnantSectionAlphaValueSupply ValueGeometry.toCoreBuild.toValueCore Fmem
      VBuild.toCanonicalFilteredValue where
  parent_remnantComponent := fun q o δ hδ =>
    parent_remnantComponent_of_multiStar_alpha_geometry VBuild ValueGeometry q o δ hδ

end GaugeGeometry.QFT.Combinatorial
