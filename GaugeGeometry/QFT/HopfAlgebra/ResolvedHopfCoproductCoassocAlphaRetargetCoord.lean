import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRetargetRhs
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedRetargetAgreement

/-!
# R-6c-body-526 — corrected retarget coordinates on `G` + socket field discharge (PROVED)

Five-hundred-and-twenty-sixth genuine-body step — closing `retargetVertex_eq_on_G` (body-524's first residual field) as a
canonical theorem.  The binder `hvG : v ∈ G.vertices` is kept throughout; NO unrestricted `∀ v` version, and
`sourceLeftStar = targetLeftStar` appears NOWHERE.

The route is: show `correspondence.toFun ⟨inputRetarget v, _⟩ = ⟨correctedRetargetRhs v, _⟩` for each of the four
component classes, then `left_inv` turns it into the inverse coordinate; finally `contractStarPerm_on_vertices` (body-513)
converts to the global `σ` coordinate.

* `correctedThreeRoute_toFun_left_inv_val` — the common inverse helper (`toFun src = dst → (invFun dst).1 = src.1`);
* `correctedRetarget_route_original/_left/_right/_forest` — the four correspondence-coordinate route lemmas
  (identity / `targetLeftStar` via body-520's `targetLeftStar_not_mem_correctedQuotient` / body-525's `_right` survivor star
  / body-525's `_forest` remnant star via body-459's `promoted_retargetVertex_eq_selectedOuter`);
* `correctedRetarget_corr_on_G` — the aggregate (`by_cases` + `isLeftPrimitive_or_isRightPrimitive_or_isForestChoice`);
* `canonicalCorrected_retargetVertex_eq_on_G` — the socket field, `= contractStarPerm q (correctedRetargetRhs v)`.

Per the HALT/guards: `hvG : v ∈ G.vertices` stays in every signature; `internalEdges_domain` / the socket inhabitant /
whole-graph field equalities / `quot_eq` / any unrestricted retarget theorem / `sourceLeftStar = targetLeftStar` / local
permutation comparison are NOT entered; strict `StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc claim.  No
facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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
  (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
  (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)

/-! ## The common inverse helper -/

/-- **R-6c-body-526 — the inverse helper** (`toFun src = dst → (invFun dst).1 = src.1`). -/
theorem correctedThreeRoute_toFun_left_inv_val
    {src : {v : VertexId // v ∈ (q.1.1.1.contractWithStars
        (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices}}
    {dst : {w : VertexId // w ∈ ((canonicalCorrectedQuotientRaw Measure
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
        canonicalUniqueStarFactsOfW' q.1).contractWithStars
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1))).vertices}}
    (h : correctedThreeRouteToFun q Measure E src = dst) :
    (correctedThreeRouteInvFun q Measure E dst).1 = src.1 := by
  rw [← h, correctedThreeRoute_left_inv q Measure E src]

/-! ## The four correspondence-coordinate route lemmas -/

/-- **R-6c-body-526 — original-survivor route.** -/
theorem correctedRetarget_route_original
    {v : VertexId} (hvA : v ∉ q.1.1.1.vertices) (hvG : v ∈ G.vertices) :
    q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v
      = (correctedThreeRouteInvFun q Measure E
          ⟨correctedRetargetRhs q Measure v, correctedRetargetRhs_mem q Measure hvG⟩).1 := by
  have hIR : q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v = v :=
    ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ hvA
  have hmemG1 : q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v
      ∈ (q.1.1.1.contractWithStars (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices :=
    ResolvedAdmissibleSubgraph.retargetVertex_mem_contractWithStars_vertices _ _ hvG
  have hnotstar : ¬ isContractStarVertex q.1.1.1
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)
      (q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v) := by
    rw [hIR]
    intro hstar
    obtain ⟨γ, hγ, heq⟩ := ResolvedAdmissibleSubgraph.mem_starVertices.mp hstar
    exact canonicalUniqueStarFactsOfW'.starOf_fresh G q.1.1.1 γ hγ (heq ▸ hvG)
  have hRhs : correctedRetargetRhs q Measure v = v := by
    have hsel : selectedOuterVertexDomain q v = v :=
      ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _
        (fun h => hvA (selectedOuterRawOf_vertices_subset q.1 h))
    unfold correctedRetargetRhs
    rw [hsel]
    exact ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _
      (correctedOriginalSurvivor_to q Measure ⟨hvG, hvA⟩).2
  have htoF : correctedThreeRouteToFun q Measure E
      ⟨q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v, hmemG1⟩
      = ⟨correctedRetargetRhs q Measure v, correctedRetargetRhs_mem q Measure hvG⟩ := by
    apply Subtype.ext
    rw [correctedThreeRouteToFun_original q Measure E hmemG1 hnotstar]
    exact (hIR.trans hRhs.symm)
  exact (correctedThreeRoute_toFun_left_inv_val q Measure E htoF).symm

/-- **R-6c-body-526 — corrected left route** (`sourceLeftStar = targetLeftStar` NEVER used). -/
theorem correctedRetarget_route_left
    (i : OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1) (hL : i.isLeft)
    {v : VertexId} (hv : v ∈ i.η.vertices) (hvG : v ∈ G.vertices) :
    q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v
      = (correctedThreeRouteInvFun q Measure E
          ⟨correctedRetargetRhs q Measure v, correctedRetargetRhs_mem q Measure hvG⟩).1 := by
  have hmemG1 : q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v
      ∈ (q.1.1.1.contractWithStars (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices :=
    ResolvedAdmissibleSubgraph.retargetVertex_mem_contractWithStars_vertices _ _ hvG
  have hIR : q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v = i.vertex :=
    retargetVertex_eq_star_of_mem_element q.1.1.1 _ i.hη hv
  have hstar : isContractStarVertex q.1.1.1
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)
      (q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v) := by
    rw [hIR]; exact i.toStarVertex.2
  have hrec : canonicalOneStageStarRecover q
      ⟨q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v, hstar⟩ = i := by
    rw [show (⟨q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v, hstar⟩ :
          {x : VertexId // isContractStarVertex q.1.1.1
            (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) x}) = i.toStarVertex
      from Subtype.ext hIR]
    exact canonicalOneStageStarRecover_apply q i
  have hL' : (canonicalOneStageStarRecover q
      ⟨q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v, hstar⟩).isLeft := by
    rw [hrec]; exact hL
  have hRhs : correctedRetargetRhs q Measure v = targetLeftStar q i := by
    have hsel : selectedOuterVertexDomain q v = targetLeftStar q i :=
      retargetVertex_eq_star_of_mem_element _ _ (leftIndex_mem_selectedOuter q i hL) hv
    unfold correctedRetargetRhs
    rw [hsel]
    exact ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _
      (targetLeftStar_not_mem_correctedQuotient q Measure i hL)
  have htoF : correctedThreeRouteToFun q Measure E
      ⟨q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v, hmemG1⟩
      = ⟨correctedRetargetRhs q Measure v, correctedRetargetRhs_mem q Measure hvG⟩ := by
    apply Subtype.ext
    rw [correctedThreeRouteToFun_left q Measure E hmemG1 hstar hL', hrec]
    exact hRhs.symm
  exact (correctedThreeRoute_toFun_left_inv_val q Measure E htoF).symm

/-- **R-6c-body-526 — right route** (body-525's `_right` survivor star). -/
theorem correctedRetarget_route_right
    (i : OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1) (hR : i.isRight)
    {v : VertexId} (hv : v ∈ i.η.vertices) (hvG : v ∈ G.vertices) :
    q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v
      = (correctedThreeRouteInvFun q Measure E
          ⟨correctedRetargetRhs q Measure v, correctedRetargetRhs_mem q Measure hvG⟩).1 := by
  have hmemG1 : q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v
      ∈ (q.1.1.1.contractWithStars (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices :=
    ResolvedAdmissibleSubgraph.retargetVertex_mem_contractWithStars_vertices _ _ hvG
  have hIR : q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v = i.vertex :=
    retargetVertex_eq_star_of_mem_element q.1.1.1 _ i.hη hv
  have hstar : isContractStarVertex q.1.1.1
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)
      (q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v) := by
    rw [hIR]; exact i.toStarVertex.2
  have hrec : canonicalOneStageStarRecover q
      ⟨q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v, hstar⟩ = i := by
    rw [show (⟨q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v, hstar⟩ :
          {x : VertexId // isContractStarVertex q.1.1.1
            (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) x}) = i.toStarVertex
      from Subtype.ext hIR]
    exact canonicalOneStageStarRecover_apply q i
  have hnotL : ¬ (canonicalOneStageStarRecover q
      ⟨q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v, hstar⟩).isLeft := by
    rw [hrec]; exact fun hLi => ResolvedCoassocSplitChoice.not_isRightPrimitive_of_isLeftPrimitive hLi hR
  have hRhs : correctedRetargetRhs q Measure v
      = canonicalUniqueSupportedCarrierProperSupply.toData.starOf
          (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
          (canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1)
          ((survivorSupply_of_measure Measure G).survivorComponent q.1
            (RightPrimitiveIndex.toRightComponent ⟨i, hR⟩)) := by
    have hsel : selectedOuterVertexDomain q v = v :=
      ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _
        (Finset.disjoint_left.mp
          (ResolvedCoassocSplitChoice.isRightPrimitive_disjoint_vertices_selectedOuterRaw hR ⟨v, hv⟩) hv)
    have hsurvMem : (survivorSupply_of_measure Measure G).survivorComponent q.1
        (RightPrimitiveIndex.toRightComponent ⟨i, hR⟩)
        ∈ (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1).elements := by
      simp only [canonicalCorrectedQuotientRaw, ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union]
      refine Or.inl ?_
      rw [ResolvedRightSurvivorSupply.rightSurvivorForest_elements]
      exact Finset.mem_image.mpr ⟨RightPrimitiveIndex.toRightComponent ⟨i, hR⟩, Finset.mem_attach _ _, rfl⟩
    unfold correctedRetargetRhs
    rw [hsel]
    exact retargetVertex_eq_star_of_mem_element _ _ hsurvMem hv
  have htoF : correctedThreeRouteToFun q Measure E
      ⟨q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v, hmemG1⟩
      = ⟨correctedRetargetRhs q Measure v, correctedRetargetRhs_mem q Measure hvG⟩ := by
    apply Subtype.ext
    rw [correctedThreeRouteToFun_nonleft q Measure E hmemG1 hstar hnotL,
      show (⟨canonicalOneStageStarRecover q
          ⟨q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v, hstar⟩,
          (canonicalOneStageStarRecover q
            ⟨q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v,
              hstar⟩).isLeft_or_hasQuotientStar.resolve_left hnotL⟩
          : {j : OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1 // j.hasQuotientStar})
        = ⟨i, Or.inl hR⟩ from Subtype.ext hrec,
      canonicalCorrectedQuotientStarVertexEquiv_right q Measure E i hR]
    exact hRhs.symm
  exact (correctedThreeRoute_toFun_left_inv_val q Measure E htoF).symm

/-- **R-6c-body-526 — forest route** (body-525's `_forest` remnant star + body-459 `promoted_retargetVertex_eq_selectedOuter`). -/
theorem correctedRetarget_route_forest
    (i : OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1) (hF : i.isForest)
    {v : VertexId} (hv : v ∈ i.η.vertices) (hvG : v ∈ G.vertices) :
    q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v
      = (correctedThreeRouteInvFun q Measure E
          ⟨correctedRetargetRhs q Measure v, correctedRetargetRhs_mem q Measure hvG⟩).1 := by
  set o := ResolvedCoassocSplitChoice.forestComponentOccurrence q.1
    (forestPrimitiveIndexEquivComponents q.1 ⟨i, hF⟩) with ho
  have hvγ : v ∈ o.γ.1.vertices := hv
  have hmemG1 : q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v
      ∈ (q.1.1.1.contractWithStars (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices :=
    ResolvedAdmissibleSubgraph.retargetVertex_mem_contractWithStars_vertices _ _ hvG
  have hIR : q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v = i.vertex :=
    retargetVertex_eq_star_of_mem_element q.1.1.1 _ i.hη hv
  have hstar : isContractStarVertex q.1.1.1
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)
      (q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v) := by
    rw [hIR]; exact i.toStarVertex.2
  have hrec : canonicalOneStageStarRecover q
      ⟨q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v, hstar⟩ = i := by
    rw [show (⟨q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v, hstar⟩ :
          {x : VertexId // isContractStarVertex q.1.1.1
            (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) x}) = i.toStarVertex
      from Subtype.ext hIR]
    exact canonicalOneStageStarRecover_apply q i
  have hnotL : ¬ (canonicalOneStageStarRecover q
      ⟨q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v, hstar⟩).isLeft := by
    rw [hrec]; exact fun hLi => ResolvedCoassocSplitChoice.not_isForestChoice_of_isLeftPrimitive hLi hF
  have hRhs : correctedRetargetRhs q Measure v
      = canonicalUniqueSupportedCarrierProperSupply.toData.starOf
          (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
          (canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1)
          ((canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
              canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1 o) := by
    have hsel : selectedOuterVertexDomain q v = o.B.1.retargetVertex (promotedOccurrenceStar q.1 o) v :=
      (promoted_retargetVertex_eq_selectedOuter q.1 o hvγ).symm
    have hremMem : (canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1 o
        ∈ (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1).elements := by
      simp only [canonicalCorrectedQuotientRaw, ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union]
      refine Or.inr ?_
      rw [ResolvedRemnantComponentSupply.remnantForest_elements]
      exact Finset.mem_image.mpr ⟨forestPrimitiveIndexEquivComponents q.1 ⟨i, hF⟩, Finset.mem_attach _ _, rfl⟩
    unfold correctedRetargetRhs
    rw [hsel]
    refine retargetVertex_eq_star_of_mem_element _ _ hremMem ?_
    rw [show ((canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1 o).vertices
          = (o.B.1.contractWithStars (promotedOccurrenceStar q.1 o)).vertices
        from correctedRemnantComponent_vertices_eq_promoted q.1 o canonicalUniqueStarFactsOfW']
    exact ResolvedAdmissibleSubgraph.retargetVertex_mem_contractWithStars_vertices _ _ hvγ
  have htoF : correctedThreeRouteToFun q Measure E
      ⟨q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v, hmemG1⟩
      = ⟨correctedRetargetRhs q Measure v, correctedRetargetRhs_mem q Measure hvG⟩ := by
    apply Subtype.ext
    rw [correctedThreeRouteToFun_nonleft q Measure E hmemG1 hstar hnotL,
      show (⟨canonicalOneStageStarRecover q
          ⟨q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v, hstar⟩,
          (canonicalOneStageStarRecover q
            ⟨q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v,
              hstar⟩).isLeft_or_hasQuotientStar.resolve_left hnotL⟩
          : {j : OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1 // j.hasQuotientStar})
        = ⟨i, Or.inr hF⟩ from Subtype.ext hrec,
      canonicalCorrectedQuotientStarVertexEquiv_forest q Measure E i hF]
    exact hRhs.symm
  exact (correctedThreeRoute_toFun_left_inv_val q Measure E htoF).symm

/-! ## The aggregate + socket field -/

/-- **R-6c-body-526 ∎ — the aggregate coordinate identity** (`by_cases` + component classification). -/
theorem correctedRetarget_corr_on_G {v : VertexId} (hvG : v ∈ G.vertices) :
    q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v
      = (correctedThreeRouteInvFun q Measure E
          ⟨correctedRetargetRhs q Measure v, correctedRetargetRhs_mem q Measure hvG⟩).1 := by
  by_cases hvA : v ∈ q.1.1.1.vertices
  · obtain ⟨γ, hγ, hvγ⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hvA
    rcases ResolvedCoassocSplitChoice.isLeftPrimitive_or_isRightPrimitive_or_isForestChoice q.1 ⟨γ, hγ⟩ with
      hL | hR | hF
    · exact correctedRetarget_route_left q Measure E ⟨γ, hγ⟩ hL hvγ hvG
    · exact correctedRetarget_route_right q Measure E ⟨γ, hγ⟩ hR hvγ hvG
    · exact correctedRetarget_route_forest q Measure E ⟨γ, hγ⟩ hF hvγ hvG
  · exact correctedRetarget_route_original q Measure E hvA hvG

/-- **R-6c-body-526 ∎ — the socket field, discharged**: the on-`G` retarget-vertex equation to the global `σ`. -/
theorem canonicalCorrected_retargetVertex_eq_on_G {v : VertexId} (hvG : v ∈ G.vertices) :
    q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v
      = (canonicalCorrectedContractCorrespondenceSupply Measure E).contractStarPerm q
        ((canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1).retargetVertex
          (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
            (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
            (canonicalCorrectedQuotientRaw Measure
              canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
              canonicalUniqueStarFactsOfW' q.1))
          (selectedOuterVertexDomain q v)) := by
  rw [correctedRetarget_corr_on_G q Measure E hvG]
  exact (ResolvedCanonicalFilteredContractCorrespondenceSupply.contractStarPerm_on_vertices
    (canonicalCorrectedContractCorrespondenceSupply Measure E) q (correctedRetargetRhs q Measure v)
    (correctedRetargetRhs_mem q Measure hvG)).symm

end GaugeGeometry.QFT.Combinatorial
