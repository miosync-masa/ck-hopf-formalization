import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSaturatedLeftRoute
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSaturatedSectorEquiv
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaThreeRouteMaps
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaThreeRouteInverse
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaContractGlobalPerm

/-!
# R-6c-body-544 — the `W″` corrected q-local three-route maps / inverses + whole-vertex correspondence (PROVED)

Five-hundred-and-forty-fourth genuine-body step — the THIRD of the `W″` re-key campaign (542 image + sector / 543
star-recovery + left + partition / **544 three-route + correspondence** / 545 global-`σ` + field + `quot_eq` / 546
occurrence + round-trip + final wrapper).  This body re-issues bodies 522–523 from `W′` to `W″`, reading the single
construction owner `R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E` (body-541); the maps / branch values /
inverses / correspondence read `R` and use `R.Measure` internally (the two containment helpers stay parametrized by an
explicit `Measure` exactly as the body-543 lemmas).

**NEW GEOMETRY = ZERO.**  The three-route bijection is body-522–523's, re-issued in the `W″` owner's coordinates.  Every
substitution is mechanical: the `W′` carrier / star-facts names are replaced by `canonicalLegSaturatedCarrierProperSupply`
and `canonicalLegSaturatedStarFacts`, and the body-543 re-keyed dependencies
(`canonicalOneStageStarRecover → canonicalLegSaturatedOneStageStarRecover`,
`canonicalCorrectedQuotientStarVertexEquiv Measure E q → canonicalLegSaturatedCorrectedQuotientStarVertexEquiv R q`,
`targetLeftStar → legSaturatedTargetLeftStar`, `correctedLeftStar_toSurvivor q Measure →
legSaturated_correctedLeftStar_toSurvivor q R.Measure`, `correctedTwoStageSurvivor_cases q Measure →
canonicalLegSaturatedCorrectedTwoStageSurvivor_cases q R.Measure`, `correctedLeftTarget_injective →
legSaturated_correctedLeftTarget_injective`, `targetLeftStar_not_mem_G → legSaturated_targetLeftStar_not_mem_G`,
the recovery anchors `canonicalLegSaturatedOneStageStarRecover_vertex` / `_apply` /
`canonicalLegSaturatedCorrectedQuotientStarVertexEquiv_symm_apply`).  All the D-generic helpers
(`surviving_mem_contractWithStars`, `star_mem_contractWithStars`, `contractWithStars_vertex_cases`,
`contract_surviving_not_star`, `OneStageStarIndex.vertex` / `.toStarVertex` / `.isLeft_or_hasQuotientStar`,
`ResolvedCoassocSplitChoice.not_isRightPrimitive_of_isLeftPrimitive` /
`not_isForestChoice_of_isLeftPrimitive`) apply UNCHANGED.

## Deliverables

* **Step 1 — two containment helpers** (`legSaturated_correctedQuotient_gvertices_subset_inputOuter` /
  `legSaturated_correctedOriginalSurvivor_to`).
* **Step 2 — the two maps** (`legSaturatedCorrectedThreeRouteToFun` / `legSaturatedCorrectedThreeRouteInvFun`, reading
  `R`).
* **Step 3 — six branch value lemmas** (`..._toFun_original` / `_left` / `_nonleft` and `..._invFun_star` /
  `_originalSurvivor` / `_left`).
* **Step 4 — six inverse-route lemmas** (`..._leftInv_original` / `_left` / `_nonleft` and `..._rightInv_star` /
  `_original` / `_left`).  The LEFT route's crux is `legSaturated_correctedLeftTarget_injective`.
* **Step 5 — the two dispatchers** (`legSaturatedCorrectedThreeRoute_left_inv` / `_right_inv`).
* **Step 6 — the correspondence + supply + inhabitant** (`canonicalLegSaturatedCorrectedContractVertexCorrespondence`,
  the re-keyed `ResolvedCanonicalLegSaturatedFilteredContractCorrespondenceSupply R`, and
  `canonicalLegSaturatedCorrectedContractCorrespondenceSupply R` — body-545 reads ONLY this supply).

Per the HALT/guards: the input-outer star `legSaturatedSourceLeftStar` is NEVER asserted equal to the selected-outer star
`legSaturatedTargetLeftStar`; the legacy vertex-identity interface for `i` is NEVER used; the maps are NOT unfolded inside
the correspondence proof (the dispatchers are used);
NO `W′` correspondence supply is cast; `R.quotient_mem` / `quot_eq` are NOT read; NO local-permutation comparison; NO
strict sockets; NO `W′` decl is modified; global `σ` / the three whole-graph field equalities are NOT entered (bodies
545–546); strict `StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc claim.  No facade, no flat term, no
`forgetHopf`, no rep/perm.
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
  (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G)

/-! ## Step 1 — the two containment helpers (body-522 re-key). -/

/-- **R-6c-body-544 ∎ — a corrected-quotient vertex that is in `G` sits in the input outer.** -/
theorem legSaturated_correctedQuotient_gvertices_subset_inputOuter
    (Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData)
    {v : VertexId}
    (hvQ : v ∈ (canonicalCorrectedQuotientRaw Measure
      canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
      canonicalLegSaturatedStarFacts q.1).vertices)
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
    rw [show ((canonicalCorrectedRemnantComponentSupply canonicalLegSaturatedStarFacts
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1 o).vertices
          = (o.B.1.contractWithStars (promotedOccurrenceStar q.1 o)).vertices
        from correctedRemnantComponent_vertices_eq_promoted q.1 o canonicalLegSaturatedStarFacts,
      ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hvδ
    rcases hvδ with hsurv | hstar
    · exact ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨o.γ.1, o.γ.2, (Finset.mem_sdiff.mp hsurv).1⟩
    · exfalso
      obtain ⟨b, hb, hbeq⟩ := ResolvedAdmissibleSubgraph.mem_starVertices.mp hstar
      have hfresh := canonicalLegSaturatedStarFacts.starOf_fresh G
        ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf q.1)
        (o.γ.1.promote b) (promote_mem_selectedOuterRawOf_raw q.1 o hb)
      rw [← hbeq] at hvG
      exact hfresh hvG

/-- **R-6c-body-544 ∎ — an input-outer surviving vertex is a corrected-quotient surviving vertex.** -/
theorem legSaturated_correctedOriginalSurvivor_to
    (Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData)
    {v : VertexId} (h : isContractSurvivingVertex q.1.1.1 v) :
    isContractSurvivingVertex (canonicalCorrectedQuotientRaw Measure
      canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
      canonicalLegSaturatedStarFacts q.1) v := by
  obtain ⟨hvG, hvI⟩ := h
  refine ⟨?_, ?_⟩
  · rw [ResolvedCoassocSplitChoice.selectedOuterContractGraph,
      ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union]
    refine Or.inl (Finset.mem_sdiff.mpr ⟨hvG, fun hvS => hvI (selectedOuterRawOf_vertices_subset q.1 hvS)⟩)
  · exact fun hvQ => hvI (legSaturated_correctedQuotient_gvertices_subset_inputOuter q Measure hvQ hvG)

/-! ## Step 2 — the two maps (body-522 re-key, reading `R`). -/

/-- **R-6c-body-544 ∎ — the corrected three-route forward map.**  Source star → left `legSaturatedTargetLeftStar` /
non-left quotient star; source survivor → identity. -/
noncomputable def legSaturatedCorrectedThreeRouteToFun
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    {v : VertexId // v ∈ (q.1.1.1.contractWithStars
        (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices} →
    {w : VertexId // w ∈ ((canonicalCorrectedQuotientRaw R.Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
        canonicalLegSaturatedStarFacts q.1).contractWithStars
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1))).vertices} :=
  fun p =>
    if hstar : isContractStarVertex q.1.1.1
        (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) p.1 then
      if hL : (canonicalLegSaturatedOneStageStarRecover q ⟨p.1, hstar⟩).isLeft then
        ⟨legSaturatedTargetLeftStar q (canonicalLegSaturatedOneStageStarRecover q ⟨p.1, hstar⟩),
          surviving_mem_contractWithStars _ _
            (legSaturated_correctedLeftStar_toSurvivor q R.Measure
              (canonicalLegSaturatedOneStageStarRecover q ⟨p.1, hstar⟩) hL)⟩
      else
        ⟨(canonicalLegSaturatedCorrectedQuotientStarVertexEquiv R q
            ⟨canonicalLegSaturatedOneStageStarRecover q ⟨p.1, hstar⟩,
              (canonicalLegSaturatedOneStageStarRecover q ⟨p.1, hstar⟩).isLeft_or_hasQuotientStar.resolve_left hL⟩).1,
          star_mem_contractWithStars _ _
            (canonicalLegSaturatedCorrectedQuotientStarVertexEquiv R q
              ⟨canonicalLegSaturatedOneStageStarRecover q ⟨p.1, hstar⟩,
                (canonicalLegSaturatedOneStageStarRecover q ⟨p.1, hstar⟩).isLeft_or_hasQuotientStar.resolve_left hL⟩).2⟩
    else
      ⟨p.1, surviving_mem_contractWithStars _ _
        (legSaturated_correctedOriginalSurvivor_to q R.Measure
          ((contractWithStars_vertex_cases q.1.1.1
            (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) p.2).resolve_right hstar))⟩

/-- **R-6c-body-544 ∎ — the corrected three-route inverse map.**  Target star → the one-stage star vertex; target
survivor → input-outer survivor (identity) or (via body-543) a left index's star vertex. -/
noncomputable def legSaturatedCorrectedThreeRouteInvFun
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    {w : VertexId // w ∈ ((canonicalCorrectedQuotientRaw R.Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
        canonicalLegSaturatedStarFacts q.1).contractWithStars
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1))).vertices} →
    {v : VertexId // v ∈ (q.1.1.1.contractWithStars
        (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices} :=
  fun p =>
    if hstar : isContractStarVertex (canonicalCorrectedQuotientRaw R.Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
        canonicalLegSaturatedStarFacts q.1)
        (canonicalLegSaturatedCarrierProperSupply.toData.starOf
          (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
          (canonicalCorrectedQuotientRaw R.Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
            canonicalLegSaturatedStarFacts q.1)) p.1 then
      ⟨((canonicalLegSaturatedCorrectedQuotientStarVertexEquiv R q).symm ⟨p.1, hstar⟩).1.vertex,
        star_mem_contractWithStars _ _
          ((canonicalLegSaturatedCorrectedQuotientStarVertexEquiv R q).symm ⟨p.1, hstar⟩).1.toStarVertex.2⟩
    else
      have hsurv : isContractSurvivingVertex (canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1) p.1 :=
        (contractWithStars_vertex_cases _ _ p.2).resolve_right hstar
      if hO : isContractSurvivingVertex q.1.1.1 p.1 then
        ⟨p.1, surviving_mem_contractWithStars _ _ hO⟩
      else
        ⟨((canonicalLegSaturatedCorrectedTwoStageSurvivor_cases q R.Measure hsurv).resolve_left hO).choose.vertex,
          star_mem_contractWithStars _ _
            ((canonicalLegSaturatedCorrectedTwoStageSurvivor_cases q R.Measure hsurv).resolve_left
              hO).choose.toStarVertex.2⟩

/-! ## Step 3 — the six branch value lemmas (body-522 re-key). -/

/-- **R-6c-body-544 — forward, source-survivor branch: identity.** -/
theorem legSaturatedCorrectedThreeRouteToFun_original
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    {v : VertexId} (hv : v ∈ (q.1.1.1.contractWithStars
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices)
    (hnotstar : ¬ isContractStarVertex q.1.1.1
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v) :
    (legSaturatedCorrectedThreeRouteToFun q R ⟨v, hv⟩).1 = v := by
  simp only [legSaturatedCorrectedThreeRouteToFun, dif_neg hnotstar]

/-- **R-6c-body-544 — forward, left branch: `legSaturatedTargetLeftStar`.** -/
theorem legSaturatedCorrectedThreeRouteToFun_left
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    {v : VertexId} (hv : v ∈ (q.1.1.1.contractWithStars
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices)
    (hstar : isContractStarVertex q.1.1.1
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v)
    (hL : (canonicalLegSaturatedOneStageStarRecover q ⟨v, hstar⟩).isLeft) :
    (legSaturatedCorrectedThreeRouteToFun q R ⟨v, hv⟩).1
      = legSaturatedTargetLeftStar q (canonicalLegSaturatedOneStageStarRecover q ⟨v, hstar⟩) := by
  simp only [legSaturatedCorrectedThreeRouteToFun, dif_pos hstar, dif_pos hL]

/-- **R-6c-body-544 — forward, non-left branch: the quotient-star vertex.** -/
theorem legSaturatedCorrectedThreeRouteToFun_nonleft
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    {v : VertexId} (hv : v ∈ (q.1.1.1.contractWithStars
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices)
    (hstar : isContractStarVertex q.1.1.1
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v)
    (hL : ¬ (canonicalLegSaturatedOneStageStarRecover q ⟨v, hstar⟩).isLeft) :
    (legSaturatedCorrectedThreeRouteToFun q R ⟨v, hv⟩).1
      = (canonicalLegSaturatedCorrectedQuotientStarVertexEquiv R q
          ⟨canonicalLegSaturatedOneStageStarRecover q ⟨v, hstar⟩,
            (canonicalLegSaturatedOneStageStarRecover q ⟨v, hstar⟩).isLeft_or_hasQuotientStar.resolve_left hL⟩).1 := by
  simp only [legSaturatedCorrectedThreeRouteToFun, dif_pos hstar, dif_neg hL]

/-- **R-6c-body-544 — inverse, target-star branch: the one-stage star vertex.** -/
theorem legSaturatedCorrectedThreeRouteInvFun_star
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    {w : VertexId} (hw : w ∈ ((canonicalCorrectedQuotientRaw R.Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
        canonicalLegSaturatedStarFacts q.1).contractWithStars
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1))).vertices)
    (hstar : isContractStarVertex (canonicalCorrectedQuotientRaw R.Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
        canonicalLegSaturatedStarFacts q.1)
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1)) w) :
    (legSaturatedCorrectedThreeRouteInvFun q R ⟨w, hw⟩).1
      = ((canonicalLegSaturatedCorrectedQuotientStarVertexEquiv R q).symm ⟨w, hstar⟩).1.vertex := by
  simp only [legSaturatedCorrectedThreeRouteInvFun, dif_pos hstar]

/-- **R-6c-body-544 — inverse, target-survivor / input-outer branch: identity.** -/
theorem legSaturatedCorrectedThreeRouteInvFun_originalSurvivor
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    {w : VertexId} (hw : w ∈ ((canonicalCorrectedQuotientRaw R.Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
        canonicalLegSaturatedStarFacts q.1).contractWithStars
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1))).vertices)
    (hstar : ¬ isContractStarVertex (canonicalCorrectedQuotientRaw R.Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
        canonicalLegSaturatedStarFacts q.1)
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1)) w)
    (hO : isContractSurvivingVertex q.1.1.1 w) :
    (legSaturatedCorrectedThreeRouteInvFun q R ⟨w, hw⟩).1 = w := by
  simp only [legSaturatedCorrectedThreeRouteInvFun, dif_neg hstar, dif_pos hO]

/-- **R-6c-body-544 — inverse, target-survivor / left branch: the chosen index's star vertex.** -/
theorem legSaturatedCorrectedThreeRouteInvFun_left
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    {w : VertexId} (hw : w ∈ ((canonicalCorrectedQuotientRaw R.Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
        canonicalLegSaturatedStarFacts q.1).contractWithStars
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1))).vertices)
    (hstar : ¬ isContractStarVertex (canonicalCorrectedQuotientRaw R.Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
        canonicalLegSaturatedStarFacts q.1)
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1)) w)
    (hO : ¬ isContractSurvivingVertex q.1.1.1 w) :
    (legSaturatedCorrectedThreeRouteInvFun q R ⟨w, hw⟩).1
      = ((canonicalLegSaturatedCorrectedTwoStageSurvivor_cases q R.Measure
          ((contractWithStars_vertex_cases _ _ hw).resolve_right hstar)).resolve_left hO).choose.vertex := by
  simp only [legSaturatedCorrectedThreeRouteInvFun, dif_neg hstar, dif_neg hO]

/-! ## Step 4 — the six inverse-route lemmas (body-523 re-key). -/

/-- **R-6c-body-544 — left inverse, source-survivor route.** -/
theorem legSaturatedCorrectedThreeRoute_leftInv_original
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    {v : VertexId} (hv : v ∈ (q.1.1.1.contractWithStars
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices)
    (hstar : ¬ isContractStarVertex q.1.1.1
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v) :
    legSaturatedCorrectedThreeRouteInvFun q R (legSaturatedCorrectedThreeRouteToFun q R ⟨v, hv⟩) = ⟨v, hv⟩ := by
  apply Subtype.ext
  have hO : isContractSurvivingVertex q.1.1.1 v :=
    (contractWithStars_vertex_cases _ _ hv).resolve_right hstar
  have htoF : (legSaturatedCorrectedThreeRouteToFun q R ⟨v, hv⟩).1 = v :=
    legSaturatedCorrectedThreeRouteToFun_original q R hv hstar
  have hnotstarT : ¬ isContractStarVertex (canonicalCorrectedQuotientRaw R.Measure
      canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider canonicalLegSaturatedStarFacts q.1)
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider canonicalLegSaturatedStarFacts q.1))
      (legSaturatedCorrectedThreeRouteToFun q R ⟨v, hv⟩).1 := by
    rw [htoF]
    exact fun hs => contract_surviving_not_star _ _
      (canonicalLegSaturatedStarFacts.starOf_fresh _ _) (legSaturated_correctedOriginalSurvivor_to q R.Measure hO) hs
  have hOT : isContractSurvivingVertex q.1.1.1 (legSaturatedCorrectedThreeRouteToFun q R ⟨v, hv⟩).1 := by
    rw [htoF]; exact hO
  exact (legSaturatedCorrectedThreeRouteInvFun_originalSurvivor q R
    (legSaturatedCorrectedThreeRouteToFun q R ⟨v, hv⟩).2 hnotstarT hOT).trans htoF

/-- **R-6c-body-544 — left inverse, left route** (the corrected step: `j = i` by
`legSaturated_correctedLeftTarget_injective`). -/
theorem legSaturatedCorrectedThreeRoute_leftInv_left
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    {v : VertexId} (hv : v ∈ (q.1.1.1.contractWithStars
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices)
    (hstar : isContractStarVertex q.1.1.1
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v)
    (hL : (canonicalLegSaturatedOneStageStarRecover q ⟨v, hstar⟩).isLeft) :
    legSaturatedCorrectedThreeRouteInvFun q R (legSaturatedCorrectedThreeRouteToFun q R ⟨v, hv⟩) = ⟨v, hv⟩ := by
  apply Subtype.ext
  have htoF : (legSaturatedCorrectedThreeRouteToFun q R ⟨v, hv⟩).1
      = legSaturatedTargetLeftStar q (canonicalLegSaturatedOneStageStarRecover q ⟨v, hstar⟩) :=
    legSaturatedCorrectedThreeRouteToFun_left q R hv hstar hL
  have hnotstarT : ¬ isContractStarVertex (canonicalCorrectedQuotientRaw R.Measure
      canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider canonicalLegSaturatedStarFacts q.1)
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider canonicalLegSaturatedStarFacts q.1))
      (legSaturatedCorrectedThreeRouteToFun q R ⟨v, hv⟩).1 := by
    rw [htoF]
    exact fun hs => contract_surviving_not_star _ _
      (canonicalLegSaturatedStarFacts.starOf_fresh _ _)
      (legSaturated_correctedLeftStar_toSurvivor q R.Measure (canonicalLegSaturatedOneStageStarRecover q ⟨v, hstar⟩) hL) hs
  have hnotO : ¬ isContractSurvivingVertex q.1.1.1 (legSaturatedCorrectedThreeRouteToFun q R ⟨v, hv⟩).1 := by
    rw [htoF]
    exact fun hO => legSaturated_targetLeftStar_not_mem_G q (canonicalLegSaturatedOneStageStarRecover q ⟨v, hstar⟩) hL hO.1
  have h1 := legSaturatedCorrectedThreeRouteInvFun_left q R
    (legSaturatedCorrectedThreeRouteToFun q R ⟨v, hv⟩).2 hnotstarT hnotO
  have hjspec := ((canonicalLegSaturatedCorrectedTwoStageSurvivor_cases q R.Measure
    ((contractWithStars_vertex_cases _ _ (legSaturatedCorrectedThreeRouteToFun q R ⟨v, hv⟩).2).resolve_right
      hnotstarT)).resolve_left hnotO).choose_spec
  have hji := legSaturated_correctedLeftTarget_injective q _ (canonicalLegSaturatedOneStageStarRecover q ⟨v, hstar⟩)
    hjspec.1 hL (hjspec.2.trans htoF)
  exact (h1.trans (congrArg OneStageStarIndex.vertex hji)).trans
    (canonicalLegSaturatedOneStageStarRecover_vertex q ⟨v, hstar⟩)

/-- **R-6c-body-544 — left inverse, non-left route.** -/
theorem legSaturatedCorrectedThreeRoute_leftInv_nonleft
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    {v : VertexId} (hv : v ∈ (q.1.1.1.contractWithStars
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices)
    (hstar : isContractStarVertex q.1.1.1
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v)
    (hL : ¬ (canonicalLegSaturatedOneStageStarRecover q ⟨v, hstar⟩).isLeft) :
    legSaturatedCorrectedThreeRouteInvFun q R (legSaturatedCorrectedThreeRouteToFun q R ⟨v, hv⟩) = ⟨v, hv⟩ := by
  apply Subtype.ext
  have htoF := legSaturatedCorrectedThreeRouteToFun_nonleft q R hv hstar hL
  have hstarT : isContractStarVertex (canonicalCorrectedQuotientRaw R.Measure
      canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider canonicalLegSaturatedStarFacts q.1)
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider canonicalLegSaturatedStarFacts q.1))
      (legSaturatedCorrectedThreeRouteToFun q R ⟨v, hv⟩).1 := by
    rw [htoF]
    exact (canonicalLegSaturatedCorrectedQuotientStarVertexEquiv R q
      ⟨canonicalLegSaturatedOneStageStarRecover q ⟨v, hstar⟩,
        (canonicalLegSaturatedOneStageStarRecover q ⟨v, hstar⟩).isLeft_or_hasQuotientStar.resolve_left hL⟩).2
  have h1 := legSaturatedCorrectedThreeRouteInvFun_star q R
    (legSaturatedCorrectedThreeRouteToFun q R ⟨v, hv⟩).2 hstarT
  have hsymm : (canonicalLegSaturatedCorrectedQuotientStarVertexEquiv R q).symm
      ⟨(legSaturatedCorrectedThreeRouteToFun q R ⟨v, hv⟩).1, hstarT⟩
      = ⟨canonicalLegSaturatedOneStageStarRecover q ⟨v, hstar⟩,
          (canonicalLegSaturatedOneStageStarRecover q ⟨v, hstar⟩).isLeft_or_hasQuotientStar.resolve_left hL⟩ := by
    rw [show (⟨(legSaturatedCorrectedThreeRouteToFun q R ⟨v, hv⟩).1, hstarT⟩ :
          {w : VertexId // isContractStarVertex (canonicalCorrectedQuotientRaw R.Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider canonicalLegSaturatedStarFacts q.1)
            (canonicalLegSaturatedCarrierProperSupply.toData.starOf
              (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
              (canonicalCorrectedQuotientRaw R.Measure
                canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
                canonicalLegSaturatedStarFacts q.1)) w})
        = canonicalLegSaturatedCorrectedQuotientStarVertexEquiv R q
          ⟨canonicalLegSaturatedOneStageStarRecover q ⟨v, hstar⟩,
            (canonicalLegSaturatedOneStageStarRecover q ⟨v, hstar⟩).isLeft_or_hasQuotientStar.resolve_left hL⟩
      from Subtype.ext htoF]
    exact canonicalLegSaturatedCorrectedQuotientStarVertexEquiv_symm_apply q R _
  rw [h1, hsymm]
  exact canonicalLegSaturatedOneStageStarRecover_vertex q ⟨v, hstar⟩

/-- **R-6c-body-544 ∎ — the left inverse.** -/
theorem legSaturatedCorrectedThreeRoute_left_inv
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    Function.LeftInverse (legSaturatedCorrectedThreeRouteInvFun q R)
      (legSaturatedCorrectedThreeRouteToFun q R) := by
  rintro ⟨v, hv⟩
  by_cases hstar : isContractStarVertex q.1.1.1
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v
  · by_cases hL : (canonicalLegSaturatedOneStageStarRecover q ⟨v, hstar⟩).isLeft
    · exact legSaturatedCorrectedThreeRoute_leftInv_left q R hv hstar hL
    · exact legSaturatedCorrectedThreeRoute_leftInv_nonleft q R hv hstar hL
  · exact legSaturatedCorrectedThreeRoute_leftInv_original q R hv hstar

/-- **R-6c-body-544 — right inverse, target-star route.** -/
theorem legSaturatedCorrectedThreeRoute_rightInv_star
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    {w : VertexId} (hw : w ∈ ((canonicalCorrectedQuotientRaw R.Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
        canonicalLegSaturatedStarFacts q.1).contractWithStars
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1))).vertices)
    (hstar : isContractStarVertex (canonicalCorrectedQuotientRaw R.Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider canonicalLegSaturatedStarFacts q.1)
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider canonicalLegSaturatedStarFacts q.1)) w) :
    legSaturatedCorrectedThreeRouteToFun q R (legSaturatedCorrectedThreeRouteInvFun q R ⟨w, hw⟩) = ⟨w, hw⟩ := by
  apply Subtype.ext
  have hinv : (legSaturatedCorrectedThreeRouteInvFun q R ⟨w, hw⟩).1
      = ((canonicalLegSaturatedCorrectedQuotientStarVertexEquiv R q).symm ⟨w, hstar⟩).1.vertex :=
    legSaturatedCorrectedThreeRouteInvFun_star q R hw hstar
  have hstarS : isContractStarVertex q.1.1.1
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)
      (legSaturatedCorrectedThreeRouteInvFun q R ⟨w, hw⟩).1 := by
    rw [hinv]
    exact ((canonicalLegSaturatedCorrectedQuotientStarVertexEquiv R q).symm ⟨w, hstar⟩).1.toStarVertex.2
  have hrec : canonicalLegSaturatedOneStageStarRecover q
        ⟨(legSaturatedCorrectedThreeRouteInvFun q R ⟨w, hw⟩).1, hstarS⟩
      = ((canonicalLegSaturatedCorrectedQuotientStarVertexEquiv R q).symm ⟨w, hstar⟩).1 := by
    rw [show (⟨(legSaturatedCorrectedThreeRouteInvFun q R ⟨w, hw⟩).1, hstarS⟩ :
          {x : VertexId // isContractStarVertex q.1.1.1
            (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) x})
        = ((canonicalLegSaturatedCorrectedQuotientStarVertexEquiv R q).symm ⟨w, hstar⟩).1.toStarVertex
      from Subtype.ext hinv]
    exact canonicalLegSaturatedOneStageStarRecover_apply q _
  have hnotL : ¬ (canonicalLegSaturatedOneStageStarRecover q
      ⟨(legSaturatedCorrectedThreeRouteInvFun q R ⟨w, hw⟩).1, hstarS⟩).isLeft := by
    rw [hrec]
    exact fun hLk => ((canonicalLegSaturatedCorrectedQuotientStarVertexEquiv R q).symm ⟨w, hstar⟩).2.elim
      (fun hR => ResolvedCoassocSplitChoice.not_isRightPrimitive_of_isLeftPrimitive hLk hR)
      (fun hF => ResolvedCoassocSplitChoice.not_isForestChoice_of_isLeftPrimitive hLk hF)
  have htoF := legSaturatedCorrectedThreeRouteToFun_nonleft q R
    (legSaturatedCorrectedThreeRouteInvFun q R ⟨w, hw⟩).2 hstarS hnotL
  have hk : (⟨canonicalLegSaturatedOneStageStarRecover q
          ⟨(legSaturatedCorrectedThreeRouteInvFun q R ⟨w, hw⟩).1, hstarS⟩,
        (canonicalLegSaturatedOneStageStarRecover q
          ⟨(legSaturatedCorrectedThreeRouteInvFun q R ⟨w, hw⟩).1,
          hstarS⟩).isLeft_or_hasQuotientStar.resolve_left hnotL⟩
        : {i : OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1 // i.hasQuotientStar})
      = (canonicalLegSaturatedCorrectedQuotientStarVertexEquiv R q).symm ⟨w, hstar⟩ := Subtype.ext hrec
  have happly : canonicalLegSaturatedCorrectedQuotientStarVertexEquiv R q
      ((canonicalLegSaturatedCorrectedQuotientStarVertexEquiv R q).symm ⟨w, hstar⟩) = ⟨w, hstar⟩ :=
    (canonicalLegSaturatedCorrectedQuotientStarVertexEquiv R q).apply_symm_apply ⟨w, hstar⟩
  rw [htoF, hk, happly]

/-- **R-6c-body-544 — right inverse, target-survivor / input-outer route.** -/
theorem legSaturatedCorrectedThreeRoute_rightInv_original
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    {w : VertexId} (hw : w ∈ ((canonicalCorrectedQuotientRaw R.Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
        canonicalLegSaturatedStarFacts q.1).contractWithStars
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1))).vertices)
    (hstar : ¬ isContractStarVertex (canonicalCorrectedQuotientRaw R.Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider canonicalLegSaturatedStarFacts q.1)
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider canonicalLegSaturatedStarFacts q.1)) w)
    (hO : isContractSurvivingVertex q.1.1.1 w) :
    legSaturatedCorrectedThreeRouteToFun q R (legSaturatedCorrectedThreeRouteInvFun q R ⟨w, hw⟩) = ⟨w, hw⟩ := by
  apply Subtype.ext
  have hinv : (legSaturatedCorrectedThreeRouteInvFun q R ⟨w, hw⟩).1 = w :=
    legSaturatedCorrectedThreeRouteInvFun_originalSurvivor q R hw hstar hO
  have hnotstarS : ¬ isContractStarVertex q.1.1.1
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)
      (legSaturatedCorrectedThreeRouteInvFun q R ⟨w, hw⟩).1 := by
    rw [hinv]
    exact fun hs => contract_surviving_not_star _ _
      (canonicalLegSaturatedStarFacts.starOf_fresh _ _) hO hs
  exact (legSaturatedCorrectedThreeRouteToFun_original q R
    (legSaturatedCorrectedThreeRouteInvFun q R ⟨w, hw⟩).2 hnotstarS).trans hinv

/-- **R-6c-body-544 — right inverse, target-survivor / left route.** -/
theorem legSaturatedCorrectedThreeRoute_rightInv_left
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    {w : VertexId} (hw : w ∈ ((canonicalCorrectedQuotientRaw R.Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
        canonicalLegSaturatedStarFacts q.1).contractWithStars
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1))).vertices)
    (hstar : ¬ isContractStarVertex (canonicalCorrectedQuotientRaw R.Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider canonicalLegSaturatedStarFacts q.1)
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider canonicalLegSaturatedStarFacts q.1)) w)
    (hO : ¬ isContractSurvivingVertex q.1.1.1 w) :
    legSaturatedCorrectedThreeRouteToFun q R (legSaturatedCorrectedThreeRouteInvFun q R ⟨w, hw⟩) = ⟨w, hw⟩ := by
  apply Subtype.ext
  have hinv := legSaturatedCorrectedThreeRouteInvFun_left q R hw hstar hO
  have hjspec := ((canonicalLegSaturatedCorrectedTwoStageSurvivor_cases q R.Measure
    ((contractWithStars_vertex_cases _ _ hw).resolve_right hstar)).resolve_left hO).choose_spec
  have hstarS : isContractStarVertex q.1.1.1
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)
      (legSaturatedCorrectedThreeRouteInvFun q R ⟨w, hw⟩).1 := by
    rw [hinv]
    exact ((canonicalLegSaturatedCorrectedTwoStageSurvivor_cases q R.Measure
      ((contractWithStars_vertex_cases _ _ hw).resolve_right hstar)).resolve_left hO).choose.toStarVertex.2
  have hrec : canonicalLegSaturatedOneStageStarRecover q
        ⟨(legSaturatedCorrectedThreeRouteInvFun q R ⟨w, hw⟩).1, hstarS⟩
      = ((canonicalLegSaturatedCorrectedTwoStageSurvivor_cases q R.Measure
        ((contractWithStars_vertex_cases _ _ hw).resolve_right hstar)).resolve_left hO).choose := by
    rw [show (⟨(legSaturatedCorrectedThreeRouteInvFun q R ⟨w, hw⟩).1, hstarS⟩ :
          {x : VertexId // isContractStarVertex q.1.1.1
            (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) x})
        = ((canonicalLegSaturatedCorrectedTwoStageSurvivor_cases q R.Measure
          ((contractWithStars_vertex_cases _ _ hw).resolve_right hstar)).resolve_left hO).choose.toStarVertex
      from Subtype.ext hinv]
    exact canonicalLegSaturatedOneStageStarRecover_apply q _
  have hL : (canonicalLegSaturatedOneStageStarRecover q
      ⟨(legSaturatedCorrectedThreeRouteInvFun q R ⟨w, hw⟩).1, hstarS⟩).isLeft := by
    rw [hrec]; exact hjspec.1
  have htoF := legSaturatedCorrectedThreeRouteToFun_left q R
    (legSaturatedCorrectedThreeRouteInvFun q R ⟨w, hw⟩).2 hstarS hL
  rw [htoF, hrec]
  exact hjspec.2

/-- **R-6c-body-544 ∎ — the right inverse.** -/
theorem legSaturatedCorrectedThreeRoute_right_inv
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    Function.RightInverse (legSaturatedCorrectedThreeRouteInvFun q R)
      (legSaturatedCorrectedThreeRouteToFun q R) := by
  rintro ⟨w, hw⟩
  by_cases hstar : isContractStarVertex (canonicalCorrectedQuotientRaw R.Measure
      canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider canonicalLegSaturatedStarFacts q.1)
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider canonicalLegSaturatedStarFacts q.1)) w
  · exact legSaturatedCorrectedThreeRoute_rightInv_star q R hw hstar
  · by_cases hO : isContractSurvivingVertex q.1.1.1 w
    · exact legSaturatedCorrectedThreeRoute_rightInv_original q R hw hstar hO
    · exact legSaturatedCorrectedThreeRoute_rightInv_left q R hw hstar hO

/-! ## Step 6 — the correspondence + supply + inhabitant (body-523 / body-513 re-key). -/

/-- **R-6c-body-544 ∎ — the corrected `W″` whole-vertex correspondence.** -/
noncomputable def canonicalLegSaturatedCorrectedContractVertexCorrespondence
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    ResolvedContractTwiceVertexCorrespondence
      (q.1.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1))
      ((canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1).contractWithStars
        (canonicalLegSaturatedCarrierProperSupply.toData.starOf
          (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
          (canonicalCorrectedQuotientRaw R.Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
            canonicalLegSaturatedStarFacts q.1))) where
  toFun := legSaturatedCorrectedThreeRouteToFun q R
  invFun := legSaturatedCorrectedThreeRouteInvFun q R
  left_inv := legSaturatedCorrectedThreeRoute_left_inv q R
  right_inv := legSaturatedCorrectedThreeRoute_right_inv q R

/-- **R-6c-body-544 — the `W″` whole-vertex correspondence socket** (body-513's socket, re-keyed to `R`; body-545
reads ONLY this supply to issue the global `σ` once). -/
structure ResolvedCanonicalLegSaturatedFilteredContractCorrespondenceSupply
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) where
  /-- The whole-vertex bijection between `q`'s outer contract-with-stars and the corrected quotient's. -/
  correspondence : ∀ {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G),
    ResolvedContractTwiceVertexCorrespondence
      (q.1.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1))
      ((canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1).contractWithStars
        (canonicalLegSaturatedCarrierProperSupply.toData.starOf
          (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
          (canonicalCorrectedQuotientRaw R.Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
            canonicalLegSaturatedStarFacts q.1)))

/-- **R-6c-body-544 ∎ — the `W″` whole-vertex correspondence socket, INHABITED** (the SOLE residual of the global `σ`,
closed; body-545 reads ONLY this). -/
noncomputable def canonicalLegSaturatedCorrectedContractCorrespondenceSupply
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    ResolvedCanonicalLegSaturatedFilteredContractCorrespondenceSupply R where
  correspondence := fun {_G} q => canonicalLegSaturatedCorrectedContractVertexCorrespondence q R

end GaugeGeometry.QFT.Combinatorial
