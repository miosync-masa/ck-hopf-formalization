import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaThreeRouteMaps
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaContractGlobalPerm

/-!
# R-6c-body-523 — corrected three-route inverse laws + correspondence inhabitant (PROVED)

Five-hundred-and-twenty-third genuine-body step — closing body-522's `toFun` / `invFun` into a genuine bijection and
INHABITING body-513's whole-vertex correspondence socket.  The maps are never unfolded; only the branch value lemmas and
the recovery anchors are used.  The one genuinely new corrected step is the LEFT route: the index `j` that body-521's
partition chooses is sent back to the source index `i` by body-520's `correctedLeftTarget_injective`.

## Step 0 — the missing recovery anchor

`canonicalOneStageStarRecover_vertex` — `(recover w).vertex = w.1` (the recovery's `symm` is `toStarVertex`, up to defeq).

## Steps 1/2 — the two inverse laws, six routes

`..._leftInv_original` / `_left` / `_nonleft` and `..._rightInv_star` / `_original` / `_left`, then the dispatchers
`correctedThreeRoute_left_inv` / `_right_inv` (`Function.LeftInverse` / `RightInverse`).  Freshness separates surviving
vertices from stars (`contract_surviving_not_star`), `targetLeftStar_not_mem_G` separates left targets from input
survivors, and `hasQuotientStar` excludes `isLeft` on the star routes.

## Steps 3/4 — the correspondence and the socket

`canonicalCorrectedContractVertexCorrespondence` — the `ResolvedContractTwiceVertexCorrespondence`;
`canonicalCorrectedContractCorrespondenceSupply` — body-513's `ResolvedCanonicalFilteredContractCorrespondenceSupply`,
INHABITED (the SOLE residual of the global `σ`, closed).

Per the HALT/guards: `sourceLeftStar = targetLeftStar` is NOT required; the legacy three-route supply /
`twoStageSurvivor_cases` is NOT inhabited; the maps are NOT unfolded in proofs; global `σ` / the three whole-graph field
equalities / `quot_eq` are NOT entered (next body); strict `StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc
claim.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-! ## Step 0 — the recovery anchor -/

/-- **R-6c-body-523 ∎ — the one-stage star recovery's vertex.**  `(recover w).vertex = w.1`. -/
theorem canonicalOneStageStarRecover_vertex
    (w : {v : VertexId // isContractStarVertex q.1.1.1
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v}) :
    (canonicalOneStageStarRecover q w).vertex = w.1 :=
  congrArg Subtype.val
    (show (canonicalOneStageStarRecover q w).toStarVertex = w
      from (canonicalOneStageStarRecover q).symm_apply_apply w)

/-! ## Step 1 — the left inverse (`inv ∘ to = id`) -/

/-- **R-6c-body-523 — left inverse, source-survivor route.** -/
theorem correctedThreeRoute_leftInv_original
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    {v : VertexId} (hv : v ∈ (q.1.1.1.contractWithStars
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices)
    (hstar : ¬ isContractStarVertex q.1.1.1
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v) :
    correctedThreeRouteInvFun q Measure E (correctedThreeRouteToFun q Measure E ⟨v, hv⟩) = ⟨v, hv⟩ := by
  apply Subtype.ext
  have hO : isContractSurvivingVertex q.1.1.1 v :=
    (contractWithStars_vertex_cases _ _ hv).resolve_right hstar
  have htoF : (correctedThreeRouteToFun q Measure E ⟨v, hv⟩).1 = v :=
    correctedThreeRouteToFun_original q Measure E hv hstar
  have hnotstarT : ¬ isContractStarVertex (canonicalCorrectedQuotientRaw Measure
      canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider canonicalUniqueStarFactsOfW' q.1)
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider canonicalUniqueStarFactsOfW' q.1))
      (correctedThreeRouteToFun q Measure E ⟨v, hv⟩).1 := by
    rw [htoF]
    exact fun hs => contract_surviving_not_star _ _
      (canonicalUniqueStarFactsOfW'.starOf_fresh _ _) (correctedOriginalSurvivor_to q Measure hO) hs
  have hOT : isContractSurvivingVertex q.1.1.1 (correctedThreeRouteToFun q Measure E ⟨v, hv⟩).1 := by
    rw [htoF]; exact hO
  exact (correctedThreeRouteInvFun_originalSurvivor q Measure E
    (correctedThreeRouteToFun q Measure E ⟨v, hv⟩).2 hnotstarT hOT).trans htoF

/-- **R-6c-body-523 — left inverse, left route** (the new corrected step: `j = i` by `correctedLeftTarget_injective`). -/
theorem correctedThreeRoute_leftInv_left
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    {v : VertexId} (hv : v ∈ (q.1.1.1.contractWithStars
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices)
    (hstar : isContractStarVertex q.1.1.1
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v)
    (hL : (canonicalOneStageStarRecover q ⟨v, hstar⟩).isLeft) :
    correctedThreeRouteInvFun q Measure E (correctedThreeRouteToFun q Measure E ⟨v, hv⟩) = ⟨v, hv⟩ := by
  apply Subtype.ext
  have htoF : (correctedThreeRouteToFun q Measure E ⟨v, hv⟩).1
      = targetLeftStar q (canonicalOneStageStarRecover q ⟨v, hstar⟩) :=
    correctedThreeRouteToFun_left q Measure E hv hstar hL
  have hnotstarT : ¬ isContractStarVertex (canonicalCorrectedQuotientRaw Measure
      canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider canonicalUniqueStarFactsOfW' q.1)
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider canonicalUniqueStarFactsOfW' q.1))
      (correctedThreeRouteToFun q Measure E ⟨v, hv⟩).1 := by
    rw [htoF]
    exact fun hs => contract_surviving_not_star _ _
      (canonicalUniqueStarFactsOfW'.starOf_fresh _ _)
      (correctedLeftStar_toSurvivor q Measure (canonicalOneStageStarRecover q ⟨v, hstar⟩) hL) hs
  have hnotO : ¬ isContractSurvivingVertex q.1.1.1 (correctedThreeRouteToFun q Measure E ⟨v, hv⟩).1 := by
    rw [htoF]
    exact fun hO => targetLeftStar_not_mem_G q (canonicalOneStageStarRecover q ⟨v, hstar⟩) hL hO.1
  have h1 := correctedThreeRouteInvFun_left q Measure E
    (correctedThreeRouteToFun q Measure E ⟨v, hv⟩).2 hnotstarT hnotO
  have hjspec := ((correctedTwoStageSurvivor_cases q Measure
    ((contractWithStars_vertex_cases _ _ (correctedThreeRouteToFun q Measure E ⟨v, hv⟩).2).resolve_right
      hnotstarT)).resolve_left hnotO).choose_spec
  have hji := correctedLeftTarget_injective q _ (canonicalOneStageStarRecover q ⟨v, hstar⟩)
    hjspec.1 hL (hjspec.2.trans htoF)
  exact (h1.trans (congrArg OneStageStarIndex.vertex hji)).trans (canonicalOneStageStarRecover_vertex q ⟨v, hstar⟩)

/-- **R-6c-body-523 — left inverse, non-left route.** -/
theorem correctedThreeRoute_leftInv_nonleft
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    {v : VertexId} (hv : v ∈ (q.1.1.1.contractWithStars
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices)
    (hstar : isContractStarVertex q.1.1.1
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v)
    (hL : ¬ (canonicalOneStageStarRecover q ⟨v, hstar⟩).isLeft) :
    correctedThreeRouteInvFun q Measure E (correctedThreeRouteToFun q Measure E ⟨v, hv⟩) = ⟨v, hv⟩ := by
  apply Subtype.ext
  have htoF := correctedThreeRouteToFun_nonleft q Measure E hv hstar hL
  have hstarT : isContractStarVertex (canonicalCorrectedQuotientRaw Measure
      canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider canonicalUniqueStarFactsOfW' q.1)
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider canonicalUniqueStarFactsOfW' q.1))
      (correctedThreeRouteToFun q Measure E ⟨v, hv⟩).1 := by
    rw [htoF]
    exact (canonicalCorrectedQuotientStarVertexEquiv Measure E q
      ⟨canonicalOneStageStarRecover q ⟨v, hstar⟩,
        (canonicalOneStageStarRecover q ⟨v, hstar⟩).isLeft_or_hasQuotientStar.resolve_left hL⟩).2
  have h1 := correctedThreeRouteInvFun_star q Measure E
    (correctedThreeRouteToFun q Measure E ⟨v, hv⟩).2 hstarT
  have hsymm : (canonicalCorrectedQuotientStarVertexEquiv Measure E q).symm
      ⟨(correctedThreeRouteToFun q Measure E ⟨v, hv⟩).1, hstarT⟩
      = ⟨canonicalOneStageStarRecover q ⟨v, hstar⟩,
          (canonicalOneStageStarRecover q ⟨v, hstar⟩).isLeft_or_hasQuotientStar.resolve_left hL⟩ := by
    rw [show (⟨(correctedThreeRouteToFun q Measure E ⟨v, hv⟩).1, hstarT⟩ :
          {w : VertexId // isContractStarVertex (canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider canonicalUniqueStarFactsOfW' q.1)
            (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
              (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
              (canonicalCorrectedQuotientRaw Measure
                canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
                canonicalUniqueStarFactsOfW' q.1)) w})
        = canonicalCorrectedQuotientStarVertexEquiv Measure E q
          ⟨canonicalOneStageStarRecover q ⟨v, hstar⟩,
            (canonicalOneStageStarRecover q ⟨v, hstar⟩).isLeft_or_hasQuotientStar.resolve_left hL⟩
      from Subtype.ext htoF]
    exact canonicalCorrectedQuotientStarVertexEquiv_symm_apply q Measure E _
  rw [h1, hsymm]
  exact canonicalOneStageStarRecover_vertex q ⟨v, hstar⟩

/-- **R-6c-body-523 ∎ — the left inverse.** -/
theorem correctedThreeRoute_left_inv
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H) :
    Function.LeftInverse (correctedThreeRouteInvFun q Measure E) (correctedThreeRouteToFun q Measure E) := by
  rintro ⟨v, hv⟩
  by_cases hstar : isContractStarVertex q.1.1.1
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v
  · by_cases hL : (canonicalOneStageStarRecover q ⟨v, hstar⟩).isLeft
    · exact correctedThreeRoute_leftInv_left q Measure E hv hstar hL
    · exact correctedThreeRoute_leftInv_nonleft q Measure E hv hstar hL
  · exact correctedThreeRoute_leftInv_original q Measure E hv hstar

/-! ## Step 2 — the right inverse (`to ∘ inv = id`) -/

/-- **R-6c-body-523 — right inverse, target-star route.** -/
theorem correctedThreeRoute_rightInv_star
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
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider canonicalUniqueStarFactsOfW' q.1)
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider canonicalUniqueStarFactsOfW' q.1)) w) :
    correctedThreeRouteToFun q Measure E (correctedThreeRouteInvFun q Measure E ⟨w, hw⟩) = ⟨w, hw⟩ := by
  apply Subtype.ext
  have hinv : (correctedThreeRouteInvFun q Measure E ⟨w, hw⟩).1
      = ((canonicalCorrectedQuotientStarVertexEquiv Measure E q).symm ⟨w, hstar⟩).1.vertex :=
    correctedThreeRouteInvFun_star q Measure E hw hstar
  have hstarS : isContractStarVertex q.1.1.1
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)
      (correctedThreeRouteInvFun q Measure E ⟨w, hw⟩).1 := by
    rw [hinv]
    exact ((canonicalCorrectedQuotientStarVertexEquiv Measure E q).symm ⟨w, hstar⟩).1.toStarVertex.2
  have hrec : canonicalOneStageStarRecover q
        ⟨(correctedThreeRouteInvFun q Measure E ⟨w, hw⟩).1, hstarS⟩
      = ((canonicalCorrectedQuotientStarVertexEquiv Measure E q).symm ⟨w, hstar⟩).1 := by
    rw [show (⟨(correctedThreeRouteInvFun q Measure E ⟨w, hw⟩).1, hstarS⟩ :
          {x : VertexId // isContractStarVertex q.1.1.1
            (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) x})
        = ((canonicalCorrectedQuotientStarVertexEquiv Measure E q).symm ⟨w, hstar⟩).1.toStarVertex
      from Subtype.ext hinv]
    exact canonicalOneStageStarRecover_apply q _
  have hnotL : ¬ (canonicalOneStageStarRecover q
      ⟨(correctedThreeRouteInvFun q Measure E ⟨w, hw⟩).1, hstarS⟩).isLeft := by
    rw [hrec]
    exact fun hLk => ((canonicalCorrectedQuotientStarVertexEquiv Measure E q).symm ⟨w, hstar⟩).2.elim
      (fun hR => ResolvedCoassocSplitChoice.not_isRightPrimitive_of_isLeftPrimitive hLk hR)
      (fun hF => ResolvedCoassocSplitChoice.not_isForestChoice_of_isLeftPrimitive hLk hF)
  have htoF := correctedThreeRouteToFun_nonleft q Measure E
    (correctedThreeRouteInvFun q Measure E ⟨w, hw⟩).2 hstarS hnotL
  have hk : (⟨canonicalOneStageStarRecover q ⟨(correctedThreeRouteInvFun q Measure E ⟨w, hw⟩).1, hstarS⟩,
        (canonicalOneStageStarRecover q ⟨(correctedThreeRouteInvFun q Measure E ⟨w, hw⟩).1,
          hstarS⟩).isLeft_or_hasQuotientStar.resolve_left hnotL⟩
        : {i : OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1 // i.hasQuotientStar})
      = (canonicalCorrectedQuotientStarVertexEquiv Measure E q).symm ⟨w, hstar⟩ := Subtype.ext hrec
  have happly : canonicalCorrectedQuotientStarVertexEquiv Measure E q
      ((canonicalCorrectedQuotientStarVertexEquiv Measure E q).symm ⟨w, hstar⟩) = ⟨w, hstar⟩ :=
    (canonicalCorrectedQuotientStarVertexEquiv Measure E q).apply_symm_apply ⟨w, hstar⟩
  rw [htoF, hk, happly]

/-- **R-6c-body-523 — right inverse, target-survivor / input-outer route.** -/
theorem correctedThreeRoute_rightInv_original
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
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider canonicalUniqueStarFactsOfW' q.1)
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider canonicalUniqueStarFactsOfW' q.1)) w)
    (hO : isContractSurvivingVertex q.1.1.1 w) :
    correctedThreeRouteToFun q Measure E (correctedThreeRouteInvFun q Measure E ⟨w, hw⟩) = ⟨w, hw⟩ := by
  apply Subtype.ext
  have hinv : (correctedThreeRouteInvFun q Measure E ⟨w, hw⟩).1 = w :=
    correctedThreeRouteInvFun_originalSurvivor q Measure E hw hstar hO
  have hnotstarS : ¬ isContractStarVertex q.1.1.1
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)
      (correctedThreeRouteInvFun q Measure E ⟨w, hw⟩).1 := by
    rw [hinv]
    exact fun hs => contract_surviving_not_star _ _
      (canonicalUniqueStarFactsOfW'.starOf_fresh _ _) hO hs
  exact (correctedThreeRouteToFun_original q Measure E
    (correctedThreeRouteInvFun q Measure E ⟨w, hw⟩).2 hnotstarS).trans hinv

/-- **R-6c-body-523 — right inverse, target-survivor / left route.** -/
theorem correctedThreeRoute_rightInv_left
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
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider canonicalUniqueStarFactsOfW' q.1)
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider canonicalUniqueStarFactsOfW' q.1)) w)
    (hO : ¬ isContractSurvivingVertex q.1.1.1 w) :
    correctedThreeRouteToFun q Measure E (correctedThreeRouteInvFun q Measure E ⟨w, hw⟩) = ⟨w, hw⟩ := by
  apply Subtype.ext
  have hinv := correctedThreeRouteInvFun_left q Measure E hw hstar hO
  have hjspec := ((correctedTwoStageSurvivor_cases q Measure
    ((contractWithStars_vertex_cases _ _ hw).resolve_right hstar)).resolve_left hO).choose_spec
  have hstarS : isContractStarVertex q.1.1.1
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)
      (correctedThreeRouteInvFun q Measure E ⟨w, hw⟩).1 := by
    rw [hinv]
    exact ((correctedTwoStageSurvivor_cases q Measure
      ((contractWithStars_vertex_cases _ _ hw).resolve_right hstar)).resolve_left hO).choose.toStarVertex.2
  have hrec : canonicalOneStageStarRecover q
        ⟨(correctedThreeRouteInvFun q Measure E ⟨w, hw⟩).1, hstarS⟩
      = ((correctedTwoStageSurvivor_cases q Measure
        ((contractWithStars_vertex_cases _ _ hw).resolve_right hstar)).resolve_left hO).choose := by
    rw [show (⟨(correctedThreeRouteInvFun q Measure E ⟨w, hw⟩).1, hstarS⟩ :
          {x : VertexId // isContractStarVertex q.1.1.1
            (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) x})
        = ((correctedTwoStageSurvivor_cases q Measure
          ((contractWithStars_vertex_cases _ _ hw).resolve_right hstar)).resolve_left hO).choose.toStarVertex
      from Subtype.ext hinv]
    exact canonicalOneStageStarRecover_apply q _
  have hL : (canonicalOneStageStarRecover q
      ⟨(correctedThreeRouteInvFun q Measure E ⟨w, hw⟩).1, hstarS⟩).isLeft := by
    rw [hrec]; exact hjspec.1
  have htoF := correctedThreeRouteToFun_left q Measure E
    (correctedThreeRouteInvFun q Measure E ⟨w, hw⟩).2 hstarS hL
  rw [htoF, hrec]
  exact hjspec.2

/-- **R-6c-body-523 ∎ — the right inverse.** -/
theorem correctedThreeRoute_right_inv
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H) :
    Function.RightInverse (correctedThreeRouteInvFun q Measure E) (correctedThreeRouteToFun q Measure E) := by
  rintro ⟨w, hw⟩
  by_cases hstar : isContractStarVertex (canonicalCorrectedQuotientRaw Measure
      canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider canonicalUniqueStarFactsOfW' q.1)
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider canonicalUniqueStarFactsOfW' q.1)) w
  · exact correctedThreeRoute_rightInv_star q Measure E hw hstar
  · by_cases hO : isContractSurvivingVertex q.1.1.1 w
    · exact correctedThreeRoute_rightInv_original q Measure E hw hstar hO
    · exact correctedThreeRoute_rightInv_left q Measure E hw hstar hO

/-! ## Steps 3/4 — the correspondence and the body-513 socket -/

/-- **R-6c-body-523 ∎ — the corrected whole-vertex correspondence.** -/
noncomputable def canonicalCorrectedContractVertexCorrespondence
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H) :
    ResolvedContractTwiceVertexCorrespondence
      (q.1.1.1.contractWithStars (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1))
      ((canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1).contractWithStars
        (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
          (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
          (canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1))) where
  toFun := correctedThreeRouteToFun q Measure E
  invFun := correctedThreeRouteInvFun q Measure E
  left_inv := correctedThreeRoute_left_inv q Measure E
  right_inv := correctedThreeRoute_right_inv q Measure E

/-- **R-6c-body-523 ∎ — body-513's whole-vertex correspondence socket, INHABITED** (the SOLE residual of the global `σ`,
closed). -/
noncomputable def canonicalCorrectedContractCorrespondenceSupply
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H) :
    ResolvedCanonicalFilteredContractCorrespondenceSupply Measure E where
  correspondence := fun {_G} q => canonicalCorrectedContractVertexCorrespondence q Measure E

end GaugeGeometry.QFT.Combinatorial
