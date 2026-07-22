import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSaturatedThreeRoute
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSaturatedConstructionRoot
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaContractGlobalPerm
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRetargetRhs
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRetargetCoord
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaContractFieldScope
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaQuotientExactResidual
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaQuotEqDischarged
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocContractTwiceQuotEq
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocContractTwiceShared
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocVertexSetEq
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaQuotientMemSaturated

/-!
# R-6c-body-545 — the `W″` global `σ` (once) + on-`G` field equality + `quot_eq` (PROVED)

Five-hundred-and-forty-fifth genuine-body step — the FOURTH of the `W″` re-key campaign (542 image + sector / 543
star-recovery + left + partition / 544 three-route + correspondence / **545 global-`σ` + field + `quot_eq`** / 546
occurrence + round-trip + final wrapper, the terminus).  This is the LARGEST connection point: it re-keys the `W′`-pinned
bodies 513 (global `σ`), 525 (RHS coordinate + sector forward values), 526 (on-`G` retarget coordinate) and 524 (whole-graph
field scope) to the single construction owner `R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E`, reading only
body-544's completed correspondence supply, and DERIVES `R.quot_eq`.

**NEW GEOMETRY = ZERO.**  Every step is a mechanical re-key of the `W′` templates in the `W″` owner's coordinates.  The
`W′` carrier / star-facts names are replaced by `canonicalLegSaturatedCarrierProperSupply` / `canonicalLegSaturatedStarFacts`,
the correspondence supply by `canonicalLegSaturatedCorrectedContractCorrespondenceSupply R` (body-544), and the sector /
star-recovery / left / partition dependencies by their body-542/543 re-keyed names.  The D-generic count / residual algebra
(bodies 500/527/528) is applied directly; the body-528 reverse inclusion is re-keyed because its `W′` statement is pinned to
the `W′` carrier (its uniqueness gate is bridged through `canonicalLegSaturatedCarrier_mem_W'`, body-533).

## Deliverables

* **Step 1 — global `σ`, once** (`canonicalLegSaturatedGlobalPermExtension` / `canonicalLegSaturatedContractStarPerm` /
  `..._on_vertices` / `..._inv_on_vertices`), the ONE finite extension of body-544's correspondence.
* **Step 2 — corrected RHS coordinates** (`legSaturatedSelectedOuterVertexDomain` / `legSaturatedCorrectedRetargetRhs` /
  `_mem` and the sector forward values `canonicalLegSaturatedCorrectedQuotientStarVertexEquiv_right` / `_forest`).
* **Step 3 — four retarget routes + the on-`G` equation** (`legSaturated_retarget_route_original` / `_left` / `_right` /
  `_forest`, the aggregate `legSaturated_retarget_corr_on_G`, and `canonicalLegSaturated_retargetVertex_eq_on_G`).
  ★Every retarget field keeps `hvG : v ∈ G.vertices`; NEVER an unrestricted `∀ v` retarget equality.★
* **Step 4 — exact internal-edge domain** (`canonicalLegSaturatedCorrected_internalEdges_domain`, via the re-keyed exact
  residual `legSaturatedCorrectedQuotientRaw_internalEdges_eq_inputResidual`).
* **Step 5 — three whole-graph fields** (`canonicalLegSaturatedContract_vertices_eq` / `_internalEdges_eq` /
  `_externalLegs_eq`, endpoints gated by `ambientSupportOfW''`).
* **Step 6 — the contract class equality** (`canonicalLegSaturatedContract_class_eq`).
* **Step 7 — `quot_eq` DERIVED** (`ResolvedCanonicalLegSaturatedAlphaConstructionSupply.quot_eq`, via body-110's
  `resolved_rightTerm_eq_of_class_eq` — a DERIVED theorem in `R`'s namespace, NOT a new socket field).

After body-546 the final coassoc signature becomes `Measure` / `E` / `Parent` / `rep*`.

Per the HALT/guards: the input-outer star `legSaturatedSourceLeftStar` is NEVER asserted equal to the selected-outer star
`legSaturatedTargetLeftStar`; no unrestricted `∀ v` retarget equality is introduced; the global `σ` is issued ONCE from the
correspondence (no local permutations are composed); no `W′` class / `quot_eq` theorem is cast; `R.Measure` /
`R.quotient_mem` / body-544's correspondence supply are the only owners read; NO round-trip / coassoc wrapper (body-546); NO
new socket beyond the re-keyed defs; strict `StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc claim.  No
facade, no flat term, no `forgetHopf`, no rep/perm.
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

/-! ## Step 1 — the global `σ`, once (body-513 re-key, reading body-544's correspondence supply). -/

/-- **R-6c-body-545 — the global permutation extension, built ONCE from body-544's correspondence** (body-18 engine). -/
noncomputable def canonicalLegSaturatedGlobalPermExtension
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    VertexPermExtension ((canonicalLegSaturatedCorrectedContractCorrespondenceSupply R).correspondence q) :=
  (finsetSubtypePermExtension _ _
      ((canonicalLegSaturatedCorrectedContractCorrespondenceSupply R).correspondence q).toEquiv).toVertexPermExtension
    ((canonicalLegSaturatedCorrectedContractCorrespondenceSupply R).correspondence q)

/-- **R-6c-body-545 ∎ — the global star permutation** (the ONE `σ`). -/
noncomputable def canonicalLegSaturatedContractStarPerm
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    Equiv.Perm VertexId :=
  (canonicalLegSaturatedGlobalPermExtension q R).starPerm

/-- **R-6c-body-545 — orientation on `G₂.vertices`** (`σ w = corr.invFun ⟨w, hw⟩`). -/
theorem canonicalLegSaturatedContractStarPerm_on_vertices
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    (w : VertexId)
    (hw : w ∈ ((canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1).contractWithStars
        (canonicalLegSaturatedCarrierProperSupply.toData.starOf
          (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
          (canonicalCorrectedQuotientRaw R.Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
            canonicalLegSaturatedStarFacts q.1))).vertices) :
    canonicalLegSaturatedContractStarPerm q R w
      = (((canonicalLegSaturatedCorrectedContractCorrespondenceSupply R).correspondence q).invFun ⟨w, hw⟩).1 :=
  (canonicalLegSaturatedGlobalPermExtension q R).on_vertices w hw

/-- **R-6c-body-545 — inverse orientation on `G₁.vertices`** (`σ.symm v = corr.toFun ⟨v, hv⟩`). -/
theorem canonicalLegSaturatedContractStarPerm_inv_on_vertices
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    (v : VertexId)
    (hv : v ∈ (q.1.1.1.contractWithStars
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices) :
    (canonicalLegSaturatedContractStarPerm q R).symm v
      = (((canonicalLegSaturatedCorrectedContractCorrespondenceSupply R).correspondence q).toFun ⟨v, hv⟩).1 :=
  (canonicalLegSaturatedGlobalPermExtension q R).inv_on_vertices v hv

/-! ## Step 2 — the corrected RHS coordinates (body-525 re-key). -/

/-- **R-6c-body-545 — the intermediate one-step vertex domain** (`selectedOuterRawOf.retargetVertex`). -/
noncomputable def legSaturatedSelectedOuterVertexDomain (v : VertexId) : VertexId :=
  ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
      q.1).retargetVertex
    (canonicalLegSaturatedCarrierProperSupply.toData.starOf G
      ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf q.1))
    v

/-- **R-6c-body-545 — the corrected retarget RHS coordinate** (the two-step domain contraction). -/
noncomputable def legSaturatedCorrectedRetargetRhs
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) (v : VertexId) : VertexId :=
  (canonicalCorrectedQuotientRaw R.Measure
      canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
      canonicalLegSaturatedStarFacts q.1).retargetVertex
    (canonicalLegSaturatedCarrierProperSupply.toData.starOf
      (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
      (canonicalCorrectedQuotientRaw R.Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
        canonicalLegSaturatedStarFacts q.1))
    (legSaturatedSelectedOuterVertexDomain q v)

/-- **R-6c-body-545 ∎ — the RHS coordinate lands in the corrected two-stage graph** (`∀ v ∈ G.vertices`). -/
theorem legSaturatedCorrectedRetargetRhs_mem
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) {v : VertexId} (hv : v ∈ G.vertices) :
    legSaturatedCorrectedRetargetRhs q R v
      ∈ ((canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1).contractWithStars
        (canonicalLegSaturatedCarrierProperSupply.toData.starOf
          (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
          (canonicalCorrectedQuotientRaw R.Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
            canonicalLegSaturatedStarFacts q.1))).vertices :=
  ResolvedAdmissibleSubgraph.retargetVertex_mem_contractWithStars_vertices _ _
    (ResolvedAdmissibleSubgraph.retargetVertex_mem_contractWithStars_vertices _ _ hv)

/-- **R-6c-body-545 ∎ — the right-primitive sector forward value.** -/
theorem canonicalLegSaturatedCorrectedQuotientStarVertexEquiv_right
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    (i : OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1) (hR : i.isRight) :
    (canonicalLegSaturatedCorrectedQuotientStarVertexEquiv R q ⟨i, Or.inl hR⟩).1
      = canonicalLegSaturatedCarrierProperSupply.toData.starOf
          (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
          (canonicalCorrectedQuotientRaw R.Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
            canonicalLegSaturatedStarFacts q.1)
          ((survivorSupply_of_measure R.Measure G).survivorComponent q.1
            (RightPrimitiveIndex.toRightComponent ⟨i, hR⟩)) := by
  simp only [canonicalLegSaturatedCorrectedQuotientStarVertexEquiv, canonicalLegSaturatedCorrectedQuotientStarEquiv,
    ResolvedCanonicalLegSaturatedFilteredQuotientSectorEquivSupply.quotientStarEquiv,
    canonicalLegSaturatedCorrectedQuotientSectorEquivSupply, Equiv.trans_apply, Equiv.sumCongr_apply,
    quotientDomainEquiv, Equiv.coe_fn_mk, dif_pos hR, Sum.map_inl,
    ResolvedCanonicalLegSaturatedFilteredQuotientSectorEquivSupply.codomainEquiv,
    canonicalLegSaturatedRightSectorEquiv, Equiv.symm_trans_apply]
  rfl

/-- **R-6c-body-545 ∎ — the forest-choice sector forward value.** -/
theorem canonicalLegSaturatedCorrectedQuotientStarVertexEquiv_forest
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    (i : OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1) (hF : i.isForest) :
    (canonicalLegSaturatedCorrectedQuotientStarVertexEquiv R q ⟨i, Or.inr hF⟩).1
      = canonicalLegSaturatedCarrierProperSupply.toData.starOf
          (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
          (canonicalCorrectedQuotientRaw R.Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
            canonicalLegSaturatedStarFacts q.1)
          ((canonicalCorrectedRemnantComponentSupply canonicalLegSaturatedStarFacts
              canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1
            (ResolvedCoassocSplitChoice.forestComponentOccurrence q.1
              (legSaturatedForestPrimitiveIndexEquivComponents q.1 ⟨i, hF⟩))) := by
  have hnR : ¬ i.isRight := fun hR => ResolvedCoassocSplitChoice.not_isForestChoice_of_isRightPrimitive hR hF
  simp only [canonicalLegSaturatedCorrectedQuotientStarVertexEquiv, canonicalLegSaturatedCorrectedQuotientStarEquiv,
    ResolvedCanonicalLegSaturatedFilteredQuotientSectorEquivSupply.quotientStarEquiv,
    canonicalLegSaturatedCorrectedQuotientSectorEquivSupply, Equiv.trans_apply, Equiv.sumCongr_apply,
    quotientDomainEquiv, Equiv.coe_fn_mk, dif_neg hnR, Sum.map_inr,
    ResolvedCanonicalLegSaturatedFilteredQuotientSectorEquivSupply.codomainEquiv,
    canonicalLegSaturatedForestSectorEquiv, Equiv.symm_trans_apply]
  rfl

/-! ## Step 3 — the four retarget routes + on-`G` equation (body-526 re-key). -/

/-- **R-6c-body-545 — the inverse helper** (`toFun src = dst → (invFun dst).1 = src.1`). -/
theorem legSaturatedCorrectedThreeRoute_toFun_left_inv_val
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    {src : {v : VertexId // v ∈ (q.1.1.1.contractWithStars
        (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices}}
    {dst : {w : VertexId // w ∈ ((canonicalCorrectedQuotientRaw R.Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
        canonicalLegSaturatedStarFacts q.1).contractWithStars
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1))).vertices}}
    (h : legSaturatedCorrectedThreeRouteToFun q R src = dst) :
    (legSaturatedCorrectedThreeRouteInvFun q R dst).1 = src.1 := by
  rw [← h, legSaturatedCorrectedThreeRoute_left_inv q R src]

/-- **R-6c-body-545 — original-survivor route. -/
theorem legSaturated_retarget_route_original
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    {v : VertexId} (hvA : v ∉ q.1.1.1.vertices) (hvG : v ∈ G.vertices) :
    q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v
      = (legSaturatedCorrectedThreeRouteInvFun q R
          ⟨legSaturatedCorrectedRetargetRhs q R v, legSaturatedCorrectedRetargetRhs_mem q R hvG⟩).1 := by
  have hIR : q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v = v :=
    ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ hvA
  have hmemG1 : q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v
      ∈ (q.1.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices :=
    ResolvedAdmissibleSubgraph.retargetVertex_mem_contractWithStars_vertices _ _ hvG
  have hnotstar : ¬ isContractStarVertex q.1.1.1
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)
      (q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v) := by
    rw [hIR]
    intro hstar
    obtain ⟨γ, hγ, heq⟩ := ResolvedAdmissibleSubgraph.mem_starVertices.mp hstar
    exact canonicalLegSaturatedStarFacts.starOf_fresh G q.1.1.1 γ hγ (heq ▸ hvG)
  have hRhs : legSaturatedCorrectedRetargetRhs q R v = v := by
    have hsel : legSaturatedSelectedOuterVertexDomain q v = v :=
      ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _
        (fun h => hvA (selectedOuterRawOf_vertices_subset q.1 h))
    unfold legSaturatedCorrectedRetargetRhs
    rw [hsel]
    exact ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _
      (legSaturated_correctedOriginalSurvivor_to q R.Measure ⟨hvG, hvA⟩).2
  have htoF : legSaturatedCorrectedThreeRouteToFun q R
      ⟨q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v, hmemG1⟩
      = ⟨legSaturatedCorrectedRetargetRhs q R v, legSaturatedCorrectedRetargetRhs_mem q R hvG⟩ := by
    apply Subtype.ext
    rw [legSaturatedCorrectedThreeRouteToFun_original q R hmemG1 hnotstar]
    exact (hIR.trans hRhs.symm)
  exact (legSaturatedCorrectedThreeRoute_toFun_left_inv_val q R htoF).symm

/-- **R-6c-body-545 — corrected left route** (the source/target left-star coincidence is NEVER invoked). -/
theorem legSaturated_retarget_route_left
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    (i : OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1) (hL : i.isLeft)
    {v : VertexId} (hv : v ∈ i.η.vertices) (hvG : v ∈ G.vertices) :
    q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v
      = (legSaturatedCorrectedThreeRouteInvFun q R
          ⟨legSaturatedCorrectedRetargetRhs q R v, legSaturatedCorrectedRetargetRhs_mem q R hvG⟩).1 := by
  have hmemG1 : q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v
      ∈ (q.1.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices :=
    ResolvedAdmissibleSubgraph.retargetVertex_mem_contractWithStars_vertices _ _ hvG
  have hIR : q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v = i.vertex :=
    retargetVertex_eq_star_of_mem_element q.1.1.1 _ i.hη hv
  have hstar : isContractStarVertex q.1.1.1
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)
      (q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v) := by
    rw [hIR]; exact i.toStarVertex.2
  have hrec : canonicalLegSaturatedOneStageStarRecover q
      ⟨q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v, hstar⟩ = i := by
    rw [show (⟨q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v, hstar⟩ :
          {x : VertexId // isContractStarVertex q.1.1.1
            (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) x}) = i.toStarVertex
      from Subtype.ext hIR]
    exact canonicalLegSaturatedOneStageStarRecover_apply q i
  have hL' : (canonicalLegSaturatedOneStageStarRecover q
      ⟨q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v, hstar⟩).isLeft := by
    rw [hrec]; exact hL
  have hRhs : legSaturatedCorrectedRetargetRhs q R v = legSaturatedTargetLeftStar q i := by
    have hsel : legSaturatedSelectedOuterVertexDomain q v = legSaturatedTargetLeftStar q i :=
      retargetVertex_eq_star_of_mem_element _ _ (legSaturated_leftIndex_mem_selectedOuter q i hL) hv
    unfold legSaturatedCorrectedRetargetRhs
    rw [hsel]
    exact ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _
      (legSaturated_targetLeftStar_not_mem_correctedQuotient q R.Measure i hL)
  have htoF : legSaturatedCorrectedThreeRouteToFun q R
      ⟨q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v, hmemG1⟩
      = ⟨legSaturatedCorrectedRetargetRhs q R v, legSaturatedCorrectedRetargetRhs_mem q R hvG⟩ := by
    apply Subtype.ext
    rw [legSaturatedCorrectedThreeRouteToFun_left q R hmemG1 hstar hL', hrec]
    exact hRhs.symm
  exact (legSaturatedCorrectedThreeRoute_toFun_left_inv_val q R htoF).symm

/-- **R-6c-body-545 — right route** (body-545's `_right` survivor star). -/
theorem legSaturated_retarget_route_right
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    (i : OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1) (hR : i.isRight)
    {v : VertexId} (hv : v ∈ i.η.vertices) (hvG : v ∈ G.vertices) :
    q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v
      = (legSaturatedCorrectedThreeRouteInvFun q R
          ⟨legSaturatedCorrectedRetargetRhs q R v, legSaturatedCorrectedRetargetRhs_mem q R hvG⟩).1 := by
  have hmemG1 : q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v
      ∈ (q.1.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices :=
    ResolvedAdmissibleSubgraph.retargetVertex_mem_contractWithStars_vertices _ _ hvG
  have hIR : q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v = i.vertex :=
    retargetVertex_eq_star_of_mem_element q.1.1.1 _ i.hη hv
  have hstar : isContractStarVertex q.1.1.1
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)
      (q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v) := by
    rw [hIR]; exact i.toStarVertex.2
  have hrec : canonicalLegSaturatedOneStageStarRecover q
      ⟨q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v, hstar⟩ = i := by
    rw [show (⟨q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v, hstar⟩ :
          {x : VertexId // isContractStarVertex q.1.1.1
            (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) x}) = i.toStarVertex
      from Subtype.ext hIR]
    exact canonicalLegSaturatedOneStageStarRecover_apply q i
  have hnotL : ¬ (canonicalLegSaturatedOneStageStarRecover q
      ⟨q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v, hstar⟩).isLeft := by
    rw [hrec]; exact fun hLi => ResolvedCoassocSplitChoice.not_isRightPrimitive_of_isLeftPrimitive hLi hR
  have hRhs : legSaturatedCorrectedRetargetRhs q R v
      = canonicalLegSaturatedCarrierProperSupply.toData.starOf
          (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
          (canonicalCorrectedQuotientRaw R.Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
            canonicalLegSaturatedStarFacts q.1)
          ((survivorSupply_of_measure R.Measure G).survivorComponent q.1
            (RightPrimitiveIndex.toRightComponent ⟨i, hR⟩)) := by
    have hsel : legSaturatedSelectedOuterVertexDomain q v = v :=
      ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _
        (Finset.disjoint_left.mp
          (ResolvedCoassocSplitChoice.isRightPrimitive_disjoint_vertices_selectedOuterRaw hR ⟨v, hv⟩) hv)
    have hsurvMem : (survivorSupply_of_measure R.Measure G).survivorComponent q.1
        (RightPrimitiveIndex.toRightComponent ⟨i, hR⟩)
        ∈ (canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1).elements := by
      simp only [canonicalCorrectedQuotientRaw, ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union]
      refine Or.inl ?_
      rw [ResolvedRightSurvivorSupply.rightSurvivorForest_elements]
      exact Finset.mem_image.mpr ⟨RightPrimitiveIndex.toRightComponent ⟨i, hR⟩, Finset.mem_attach _ _, rfl⟩
    unfold legSaturatedCorrectedRetargetRhs
    rw [hsel]
    exact retargetVertex_eq_star_of_mem_element _ _ hsurvMem hv
  have htoF : legSaturatedCorrectedThreeRouteToFun q R
      ⟨q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v, hmemG1⟩
      = ⟨legSaturatedCorrectedRetargetRhs q R v, legSaturatedCorrectedRetargetRhs_mem q R hvG⟩ := by
    apply Subtype.ext
    rw [legSaturatedCorrectedThreeRouteToFun_nonleft q R hmemG1 hstar hnotL,
      show (⟨canonicalLegSaturatedOneStageStarRecover q
          ⟨q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v, hstar⟩,
          (canonicalLegSaturatedOneStageStarRecover q
            ⟨q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v,
              hstar⟩).isLeft_or_hasQuotientStar.resolve_left hnotL⟩
          : {j : OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1 // j.hasQuotientStar})
        = ⟨i, Or.inl hR⟩ from Subtype.ext hrec,
      canonicalLegSaturatedCorrectedQuotientStarVertexEquiv_right q R i hR]
    exact hRhs.symm
  exact (legSaturatedCorrectedThreeRoute_toFun_left_inv_val q R htoF).symm

/-- **R-6c-body-545 — forest route** (body-545's `_forest` remnant star + body-459 `promoted_retargetVertex_eq_selectedOuter`). -/
theorem legSaturated_retarget_route_forest
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    (i : OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1) (hF : i.isForest)
    {v : VertexId} (hv : v ∈ i.η.vertices) (hvG : v ∈ G.vertices) :
    q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v
      = (legSaturatedCorrectedThreeRouteInvFun q R
          ⟨legSaturatedCorrectedRetargetRhs q R v, legSaturatedCorrectedRetargetRhs_mem q R hvG⟩).1 := by
  set o := ResolvedCoassocSplitChoice.forestComponentOccurrence q.1
    (legSaturatedForestPrimitiveIndexEquivComponents q.1 ⟨i, hF⟩) with ho
  have hvγ : v ∈ o.γ.1.vertices := hv
  have hmemG1 : q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v
      ∈ (q.1.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices :=
    ResolvedAdmissibleSubgraph.retargetVertex_mem_contractWithStars_vertices _ _ hvG
  have hIR : q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v = i.vertex :=
    retargetVertex_eq_star_of_mem_element q.1.1.1 _ i.hη hv
  have hstar : isContractStarVertex q.1.1.1
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)
      (q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v) := by
    rw [hIR]; exact i.toStarVertex.2
  have hrec : canonicalLegSaturatedOneStageStarRecover q
      ⟨q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v, hstar⟩ = i := by
    rw [show (⟨q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v, hstar⟩ :
          {x : VertexId // isContractStarVertex q.1.1.1
            (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) x}) = i.toStarVertex
      from Subtype.ext hIR]
    exact canonicalLegSaturatedOneStageStarRecover_apply q i
  have hnotL : ¬ (canonicalLegSaturatedOneStageStarRecover q
      ⟨q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v, hstar⟩).isLeft := by
    rw [hrec]; exact fun hLi => ResolvedCoassocSplitChoice.not_isForestChoice_of_isLeftPrimitive hLi hF
  have hRhs : legSaturatedCorrectedRetargetRhs q R v
      = canonicalLegSaturatedCarrierProperSupply.toData.starOf
          (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
          (canonicalCorrectedQuotientRaw R.Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
            canonicalLegSaturatedStarFacts q.1)
          ((canonicalCorrectedRemnantComponentSupply canonicalLegSaturatedStarFacts
              canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1 o) := by
    have hsel : legSaturatedSelectedOuterVertexDomain q v = o.B.1.retargetVertex (promotedOccurrenceStar q.1 o) v :=
      (promoted_retargetVertex_eq_selectedOuter q.1 o hvγ).symm
    have hremMem : (canonicalCorrectedRemnantComponentSupply canonicalLegSaturatedStarFacts
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1 o
        ∈ (canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1).elements := by
      simp only [canonicalCorrectedQuotientRaw, ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union]
      refine Or.inr ?_
      rw [ResolvedRemnantComponentSupply.remnantForest_elements]
      exact Finset.mem_image.mpr ⟨legSaturatedForestPrimitiveIndexEquivComponents q.1 ⟨i, hF⟩,
        Finset.mem_attach _ _, rfl⟩
    unfold legSaturatedCorrectedRetargetRhs
    rw [hsel]
    refine retargetVertex_eq_star_of_mem_element _ _ hremMem ?_
    rw [show ((canonicalCorrectedRemnantComponentSupply canonicalLegSaturatedStarFacts
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1 o).vertices
          = (o.B.1.contractWithStars (promotedOccurrenceStar q.1 o)).vertices
        from correctedRemnantComponent_vertices_eq_promoted q.1 o canonicalLegSaturatedStarFacts]
    exact ResolvedAdmissibleSubgraph.retargetVertex_mem_contractWithStars_vertices _ _ hvγ
  have htoF : legSaturatedCorrectedThreeRouteToFun q R
      ⟨q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v, hmemG1⟩
      = ⟨legSaturatedCorrectedRetargetRhs q R v, legSaturatedCorrectedRetargetRhs_mem q R hvG⟩ := by
    apply Subtype.ext
    rw [legSaturatedCorrectedThreeRouteToFun_nonleft q R hmemG1 hstar hnotL,
      show (⟨canonicalLegSaturatedOneStageStarRecover q
          ⟨q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v, hstar⟩,
          (canonicalLegSaturatedOneStageStarRecover q
            ⟨q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v,
              hstar⟩).isLeft_or_hasQuotientStar.resolve_left hnotL⟩
          : {j : OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1 // j.hasQuotientStar})
        = ⟨i, Or.inr hF⟩ from Subtype.ext hrec,
      canonicalLegSaturatedCorrectedQuotientStarVertexEquiv_forest q R i hF]
    exact hRhs.symm
  exact (legSaturatedCorrectedThreeRoute_toFun_left_inv_val q R htoF).symm

/-- **R-6c-body-545 ∎ — the aggregate coordinate identity** (`by_cases` + component classification). -/
theorem legSaturated_retarget_corr_on_G
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    {v : VertexId} (hvG : v ∈ G.vertices) :
    q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v
      = (legSaturatedCorrectedThreeRouteInvFun q R
          ⟨legSaturatedCorrectedRetargetRhs q R v, legSaturatedCorrectedRetargetRhs_mem q R hvG⟩).1 := by
  by_cases hvA : v ∈ q.1.1.1.vertices
  · obtain ⟨γ, hγ, hvγ⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hvA
    rcases ResolvedCoassocSplitChoice.isLeftPrimitive_or_isRightPrimitive_or_isForestChoice q.1 ⟨γ, hγ⟩ with
      hL | hR | hF
    · exact legSaturated_retarget_route_left q R ⟨γ, hγ⟩ hL hvγ hvG
    · exact legSaturated_retarget_route_right q R ⟨γ, hγ⟩ hR hvγ hvG
    · exact legSaturated_retarget_route_forest q R ⟨γ, hγ⟩ hF hvγ hvG
  · exact legSaturated_retarget_route_original q R hvA hvG

/-- **R-6c-body-545 ∎ — the on-`G` retarget-vertex equation to the global `σ`.**  ★`hvG : v ∈ G.vertices` kept; no `∀ v`.★ -/
theorem canonicalLegSaturated_retargetVertex_eq_on_G
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    {v : VertexId} (hvG : v ∈ G.vertices) :
    q.1.1.1.retargetVertex (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) v
      = canonicalLegSaturatedContractStarPerm q R
        ((canonicalCorrectedQuotientRaw R.Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
            canonicalLegSaturatedStarFacts q.1).retargetVertex
          (canonicalLegSaturatedCarrierProperSupply.toData.starOf
            (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
            (canonicalCorrectedQuotientRaw R.Measure
              canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
              canonicalLegSaturatedStarFacts q.1))
          (legSaturatedSelectedOuterVertexDomain q v)) := by
  rw [legSaturated_retarget_corr_on_G q R hvG]
  exact (canonicalLegSaturatedContractStarPerm_on_vertices q R (legSaturatedCorrectedRetargetRhs q R v)
    (legSaturatedCorrectedRetargetRhs_mem q R hvG)).symm

/-! ## Step 4 — the exact internal-edge domain (body-528 reverse inclusion + body-529 domain re-key). -/

/-- **R-6c-body-545 ∎ — the reverse inclusion** `R.map f ≤ Q.internalEdges` (body-528 Step 3 re-key; the uniqueness gate is
bridged through `canonicalLegSaturatedCarrier_mem_W'`). -/
theorem legSaturatedCorrectedQuotientRaw_inputResidual_le_internalEdges
    (Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData) :
    (q.1.1.1.internalEdges
        - ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
            q.1).internalEdges).map
        (((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
            q.1).retargetEdge
          (canonicalLegSaturatedCarrierProperSupply.toData.starOf G
            ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
              q.1)))
      ≤ (canonicalCorrectedQuotientRaw Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1).internalEdges := by
  set S := (resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
    q.1 with hSdef
  set f := S.retargetEdge (canonicalLegSaturatedCarrierProperSupply.toData.starOf G S) with hfdef
  have hId : G.EdgeIdsUnique := edgeIdsUnique_of_carrier_mem (canonicalLegSaturatedCarrier_mem_W' q.1.1.2)
  rw [Multiset.le_iff_count]
  intro e'
  by_cases hc : Multiset.count e' ((q.1.1.1.internalEdges - S.internalEdges).map f) = 0
  · omega
  · obtain ⟨e, heR, rfl⟩ := Multiset.mem_map.mp (Multiset.count_pos.mp (Nat.pos_of_ne_zero hc))
    have heA : e ∈ q.1.1.1.internalEdges := Multiset.mem_of_le (Multiset.sub_le_self _ _) heR
    have heG : e ∈ G.internalEdges := Multiset.mem_of_le q.1.1.1.internalEdges_le heA
    have hmap : Multiset.count (f e) ((q.1.1.1.internalEdges - S.internalEdges).map f)
        = Multiset.count e (q.1.1.1.internalEdges - S.internalEdges) :=
      count_map_eq_count_of_injOn_mem
        (ResolvedAdmissibleSubgraph.retargetEdge_injOn_internalEdges hId S _)
        (fun a ha => Multiset.mem_of_le q.1.1.1.internalEdges_le
          (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha)) heG
    rw [hmap]
    obtain ⟨γ, hγ, heγ⟩ := resolvedAdmissible_mem_internalEdges'.mp heA
    have hownerA : Multiset.count e q.1.1.1.internalEdges = Multiset.count e γ.internalEdges :=
      ResolvedAdmissibleSubgraph.count_internalEdges_eq_of_mem_component hγ heγ
    rcases ResolvedCoassocSplitChoice.isLeftPrimitive_or_isRightPrimitive_or_isForestChoice q.1 ⟨γ, hγ⟩ with
      hL | hR | hF
    · rw [Multiset.count_sub]
      have hSA : Multiset.count e S.internalEdges = Multiset.count e q.1.1.1.internalEdges :=
        selectedOuter_count_eq_left q.1 ⟨γ, hγ⟩ hL heγ
      omega
    · set r : {x : {y : ResolvedFeynmanSubgraph G // y ∈ q.1.1.1.elements} //
          x ∈ ResolvedCoassocSplitChoice.rightComponents q.1} :=
        ⟨⟨γ, hγ⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hR⟩⟩ with hr
      have hS0 : Multiset.count e S.internalEdges = 0 := selectedOuter_count_eq_zero_right q.1 r heγ
      have hsurvEq : ((survivorSupply_of_measure Measure G).survivorComponent q.1 r).internalEdges
          = γ.internalEdges.map f := survivorComponent_internalEdges_eq_inputMap Measure q.1 r
      have hsurvMem : (survivorSupply_of_measure Measure G).survivorComponent q.1 r
          ∈ (canonicalCorrectedQuotientRaw Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
            canonicalLegSaturatedStarFacts q.1).elements := by
        simp only [canonicalCorrectedQuotientRaw, ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union]
        refine Or.inl ?_
        rw [ResolvedRightSurvivorSupply.rightSurvivorForest_elements]
        exact Finset.mem_image.mpr ⟨r, Finset.mem_attach _ _, rfl⟩
      have hfeMem : f e ∈ ((survivorSupply_of_measure Measure G).survivorComponent q.1 r).internalEdges := by
        rw [hsurvEq]; exact Multiset.mem_map.mpr ⟨e, heγ, rfl⟩
      have hownerQ : Multiset.count (f e) (canonicalCorrectedQuotientRaw Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
            canonicalLegSaturatedStarFacts q.1).internalEdges
          = Multiset.count (f e) ((survivorSupply_of_measure Measure G).survivorComponent q.1 r).internalEdges :=
        ResolvedAdmissibleSubgraph.count_internalEdges_eq_of_mem_component hsurvMem hfeMem
      have hmapcount : Multiset.count (f e) (γ.internalEdges.map f) = Multiset.count e γ.internalEdges :=
        count_map_eq_count_of_injOn_mem
          (ResolvedAdmissibleSubgraph.retargetEdge_injOn_internalEdges hId S _)
          (fun a ha => Multiset.mem_of_le q.1.1.1.internalEdges_le
            (Multiset.mem_of_le (ResolvedAdmissibleSubgraph.internalEdges_le_of_mem q.1.1.1 hγ) ha)) heG
      rw [Multiset.count_sub, hownerQ, hsurvEq, hmapcount]
      omega
    · have hfmem : (⟨γ, hγ⟩ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
          ∈ ResolvedCoassocSplitChoice.forestComponents q.1 :=
        Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hF⟩
      set o := ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 ⟨⟨γ, hγ⟩, hfmem⟩ with ho
      have heγo : e ∈ o.γ.1.internalEdges := heγ
      have hSocc : Multiset.count e S.internalEdges = Multiset.count e o.B.1.internalEdges :=
        selectedOuter_count_eq_forestOccurrence q.1 o heγo
      have hownerA' : Multiset.count e q.1.1.1.internalEdges = Multiset.count e o.γ.1.internalEdges :=
        ResolvedAdmissibleSubgraph.count_internalEdges_eq_of_mem_component o.γ.2 heγo
      have hcompl : Multiset.count e o.B.1.complementEdges
          = Multiset.count e o.γ.1.internalEdges - Multiset.count e o.B.1.internalEdges := by
        show Multiset.count e (o.γ.1.toResolvedFeynmanGraph.internalEdges - o.B.1.internalEdges) = _
        rw [Multiset.count_sub, ResolvedFeynmanSubgraph.toResolvedFeynmanGraph_internalEdges]
      have heBc : e ∈ o.B.1.complementEdges := by
        rw [← Multiset.count_pos, hcompl]
        have heRpos : 0 < Multiset.count e (q.1.1.1.internalEdges - S.internalEdges) :=
          hmap ▸ Nat.pos_of_ne_zero hc
        rw [Multiset.count_sub] at heRpos
        omega
      have hremEq : ((canonicalCorrectedRemnantReembedSupply q.1 canonicalLegSaturatedStarFacts).correctedRemnantComponent
            o).internalEdges = o.B.1.complementEdges.map f :=
        correctedRemnantComponent_internalEdges_eq_inputMap canonicalLegSaturatedStarFacts q.1 o
      have hremMem : (canonicalCorrectedRemnantReembedSupply q.1 canonicalLegSaturatedStarFacts).correctedRemnantComponent o
          ∈ (canonicalCorrectedQuotientRaw Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
            canonicalLegSaturatedStarFacts q.1).elements := by
        simp only [canonicalCorrectedQuotientRaw, ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union]
        refine Or.inr ?_
        rw [ResolvedRemnantComponentSupply.remnantForest_elements]
        exact Finset.mem_image.mpr ⟨⟨⟨γ, hγ⟩, hfmem⟩, Finset.mem_attach _ _, rfl⟩
      have hfeMem : f e ∈ ((canonicalCorrectedRemnantReembedSupply q.1
          canonicalLegSaturatedStarFacts).correctedRemnantComponent o).internalEdges := by
        rw [hremEq]; exact Multiset.mem_map.mpr ⟨e, heBc, rfl⟩
      have hownerQ : Multiset.count (f e) (canonicalCorrectedQuotientRaw Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
            canonicalLegSaturatedStarFacts q.1).internalEdges
          = Multiset.count (f e) ((canonicalCorrectedRemnantReembedSupply q.1
              canonicalLegSaturatedStarFacts).correctedRemnantComponent o).internalEdges :=
        ResolvedAdmissibleSubgraph.count_internalEdges_eq_of_mem_component hremMem hfeMem
      have hmapcount : Multiset.count (f e) (o.B.1.complementEdges.map f) = Multiset.count e o.B.1.complementEdges :=
        count_map_eq_count_of_injOn_mem
          (ResolvedAdmissibleSubgraph.retargetEdge_injOn_internalEdges hId S _)
          (fun a ha => Multiset.mem_of_le q.1.1.1.internalEdges_le
            (Multiset.mem_of_le (ResolvedAdmissibleSubgraph.internalEdges_le_of_mem q.1.1.1 o.γ.2)
              (by have h := ResolvedAdmissibleSubgraph.mem_internalEdges_of_mem_complementEdges ha
                  rwa [ResolvedFeynmanSubgraph.toResolvedFeynmanGraph_internalEdges] at h))) heG
      rw [Multiset.count_sub, hownerQ, hremEq, hmapcount, hcompl]
      omega

/-- **R-6c-body-545 ∎ — the exact residual equality** `Q.internalEdges = R.map f` (body-500 `≤` + the re-keyed `≥`). -/
theorem legSaturatedCorrectedQuotientRaw_internalEdges_eq_inputResidual
    (Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData) :
    (canonicalCorrectedQuotientRaw Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
        canonicalLegSaturatedStarFacts q.1).internalEdges
      = (q.1.1.1.internalEdges
          - ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
              q.1).internalEdges).map
          (((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
              q.1).retargetEdge
            (canonicalLegSaturatedCarrierProperSupply.toData.starOf G
              ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
                q.1))) :=
  le_antisymm
    (canonicalCorrectedQuotientRaw_internalEdges_le_inputResidual Measure
      canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider canonicalLegSaturatedStarFacts q.1)
    (legSaturatedCorrectedQuotientRaw_inputResidual_le_internalEdges q Measure)

/-- **R-6c-body-545 ∎ — the edge-domain field** `A.complementEdges.map f = Q.complementEdges` (body-529 re-key). -/
theorem canonicalLegSaturatedCorrected_internalEdges_domain
    (Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData) :
    q.1.1.1.complementEdges.map (fun e => e.retarget (legSaturatedSelectedOuterVertexDomain q))
      = (canonicalCorrectedQuotientRaw Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1).complementEdges := by
  have hSA : ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
      q.1).internalEdges ≤ q.1.1.1.internalEdges := selectedOuter_internalEdges_le_inputOuter q.1
  have hAG : q.1.1.1.internalEdges ≤ G.internalEdges := q.1.1.1.internalEdges_le
  have hSG : ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
      q.1).internalEdges ≤ G.internalEdges := hSA.trans hAG
  have hQ : (canonicalCorrectedQuotientRaw Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
        canonicalLegSaturatedStarFacts q.1).internalEdges
      = (q.1.1.1.internalEdges
          - ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
              q.1).internalEdges).map
          (((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
              q.1).retargetEdge
            (canonicalLegSaturatedCarrierProperSupply.toData.starOf G
              ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
                q.1))) :=
    legSaturatedCorrectedQuotientRaw_internalEdges_eq_inputResidual q Measure
  show (G.internalEdges - q.1.1.1.internalEdges).map
        (((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
            q.1).retargetEdge
          (canonicalLegSaturatedCarrierProperSupply.toData.starOf G
            ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
              q.1)))
      = (canonicalCorrectedQuotientRaw Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1).complementEdges
  rw [show (canonicalCorrectedQuotientRaw Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1).complementEdges
        = ((G.internalEdges
              - ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
                  q.1).internalEdges).map
            (((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
                q.1).retargetEdge
              (canonicalLegSaturatedCarrierProperSupply.toData.starOf G
                ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
                  q.1))))
          - (canonicalCorrectedQuotientRaw Measure
              canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
              canonicalLegSaturatedStarFacts q.1).internalEdges
      from rfl,
    hQ, multiset_map_sub_of_le _ hAG, multiset_map_sub_of_le _ hSG, multiset_map_sub_of_le _ hSA]
  exact (multiset_sub_sub_cancel_common (Multiset.map_le_map hSA) (Multiset.map_le_map hAG)).symm

/-! ## Step 5 — the three whole-graph fields (body-524 re-key, endpoints gated by `ambientSupportOfW''`). -/

/-- **R-6c-body-545 ∎ — the whole-graph vertices field equality**, straight from the correspondence. -/
theorem canonicalLegSaturatedContract_vertices_eq
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    (q.1.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices
      = (((canonicalCorrectedQuotientRaw R.Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
            canonicalLegSaturatedStarFacts q.1).contractWithStars
          (canonicalLegSaturatedCarrierProperSupply.toData.starOf
            (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
            (canonicalCorrectedQuotientRaw R.Measure
              canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
              canonicalLegSaturatedStarFacts q.1))).mapPerm
        (canonicalLegSaturatedContractStarPerm q R)).vertices :=
  vertices_eq_of_perm_extension (canonicalLegSaturatedGlobalPermExtension q R)

/-- **R-6c-body-545 — the leg domain is definitional** (`contractWithStars_externalLegs`). -/
theorem legSaturated_selectedOuter_leg_domain_eq :
    G.externalLegs.map (fun ℓ => ℓ.retarget (legSaturatedSelectedOuterVertexDomain q))
      = (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1).externalLegs := by
  rw [ResolvedCoassocSplitChoice.selectedOuterContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_externalLegs]
  rfl

/-- **R-6c-body-545 — the complement-edge endpoint lift** (on-`G` equation on both endpoints). -/
theorem legSaturated_retargetEdge_eq_of_mem_complement
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    {e : ResolvedFeynmanEdge} (he : e ∈ q.1.1.1.complementEdges) :
    q.1.1.1.retargetEdge (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) e
      = ResolvedFeynmanEdge.map (canonicalLegSaturatedContractStarPerm q R)
        ((canonicalCorrectedQuotientRaw R.Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
            canonicalLegSaturatedStarFacts q.1).retargetEdge
          (canonicalLegSaturatedCarrierProperSupply.toData.starOf
            (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
            (canonicalCorrectedQuotientRaw R.Measure
              canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
              canonicalLegSaturatedStarFacts q.1))
          (e.retarget (legSaturatedSelectedOuterVertexDomain q))) := by
  obtain ⟨hs, ht⟩ := ambientSupportOfW''.edges_supported_of_mem q.1.1.2 e
    (Multiset.mem_of_le (Multiset.sub_le_self _ _) he)
  simp only [ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.map, ResolvedFeynmanEdge.retarget]
  rw [canonicalLegSaturated_retargetVertex_eq_on_G q R hs, canonicalLegSaturated_retargetVertex_eq_on_G q R ht]

/-- **R-6c-body-545 — the external-leg endpoint lift** (on-`G` equation on the attachment). -/
theorem legSaturated_retargetLeg_eq
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E)
    {ℓ : ResolvedExternalLeg} (hℓ : ℓ ∈ G.externalLegs) :
    q.1.1.1.retargetExternalLeg (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1) ℓ
      = ResolvedExternalLeg.map (canonicalLegSaturatedContractStarPerm q R)
        ((canonicalCorrectedQuotientRaw R.Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
            canonicalLegSaturatedStarFacts q.1).retargetExternalLeg
          (canonicalLegSaturatedCarrierProperSupply.toData.starOf
            (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
            (canonicalCorrectedQuotientRaw R.Measure
              canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
              canonicalLegSaturatedStarFacts q.1))
          (ℓ.retarget (legSaturatedSelectedOuterVertexDomain q))) := by
  have ha := ambientSupportOfW''.legs_supported_of_mem q.1.1.2 ℓ hℓ
  simp only [ResolvedAdmissibleSubgraph.retargetExternalLeg, ResolvedExternalLeg.map, ResolvedExternalLeg.retarget]
  rw [canonicalLegSaturated_retargetVertex_eq_on_G q R ha]

/-- **R-6c-body-545 — the whole-graph internal-edges field equality**, from the edge domain + the endpoint lift. -/
theorem canonicalLegSaturatedContract_internalEdges_eq
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    (q.1.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)).internalEdges
      = (((canonicalCorrectedQuotientRaw R.Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
            canonicalLegSaturatedStarFacts q.1).contractWithStars
          (canonicalLegSaturatedCarrierProperSupply.toData.starOf
            (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
            (canonicalCorrectedQuotientRaw R.Measure
              canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
              canonicalLegSaturatedStarFacts q.1))).mapPerm
        (canonicalLegSaturatedContractStarPerm q R)).internalEdges := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_internalEdges]
  show q.1.1.1.complementEdges.map (q.1.1.1.retargetEdge _)
      = ((_ : ResolvedAdmissibleSubgraph _).complementEdges.map (_ : ResolvedFeynmanEdge → ResolvedFeynmanEdge)).map
        (ResolvedFeynmanEdge.map _)
  rw [← canonicalLegSaturatedCorrected_internalEdges_domain q R.Measure, Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl (fun e he => legSaturated_retargetEdge_eq_of_mem_complement q R he)

/-- **R-6c-body-545 — the whole-graph external-legs field equality**, from the leg domain + the endpoint lift. -/
theorem canonicalLegSaturatedContract_externalLegs_eq
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    (q.1.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)).externalLegs
      = (((canonicalCorrectedQuotientRaw R.Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
            canonicalLegSaturatedStarFacts q.1).contractWithStars
          (canonicalLegSaturatedCarrierProperSupply.toData.starOf
            (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
            (canonicalCorrectedQuotientRaw R.Measure
              canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
              canonicalLegSaturatedStarFacts q.1))).mapPerm
        (canonicalLegSaturatedContractStarPerm q R)).externalLegs := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_externalLegs]
  simp only [ResolvedFeynmanGraph.mapPerm]
  rw [ResolvedAdmissibleSubgraph.contractWithStars_externalLegs, ← legSaturated_selectedOuter_leg_domain_eq q,
    Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl (fun ℓ hℓ => legSaturated_retargetLeg_eq q R hℓ)

/-! ## Step 6 — the contract class equality. -/

/-- **R-6c-body-545 ∎ — the contract-twice class equality** (the shared `mapPerm` engine + the three whole fields). -/
theorem canonicalLegSaturatedContract_class_eq
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    (q.1.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G q.1.1.1)).toResolvedClass
      = ((canonicalCorrectedQuotientRaw R.Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
            canonicalLegSaturatedStarFacts q.1).contractWithStars
          (canonicalLegSaturatedCarrierProperSupply.toData.starOf
            (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
            (canonicalCorrectedQuotientRaw R.Measure
              canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
              canonicalLegSaturatedStarFacts q.1))).toResolvedClass :=
  ResolvedFeynmanGraph.toResolvedClass_eq_of_mapPerm_fields (canonicalLegSaturatedContractStarPerm q R)
    (canonicalLegSaturatedContract_vertices_eq q R)
    (canonicalLegSaturatedContract_internalEdges_eq q R)
    (canonicalLegSaturatedContract_externalLegs_eq q R)

/-! ## Step 7 — `quot_eq` DERIVED (body-110, D-generic; NOT a new socket field). -/

/-- **R-6c-body-545 ∎ — `R.quot_eq` DERIVED.**  The two star-contraction quotients share a resolved class (Step 6), so
their right terms agree — via body-110's `resolved_rightTerm_eq_of_class_eq`. -/
theorem ResolvedCanonicalLegSaturatedAlphaConstructionSupply.quot_eq
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G) :
    (canonicalLegSaturatedCarrierProperSupply.toData.supply G).rightTerm q.1.1
      = (canonicalLegSaturatedCarrierProperSupply.toData.supply
            (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)).rightTerm
          ⟨canonicalCorrectedQuotientRaw R.Measure
              canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
              canonicalLegSaturatedStarFacts q.1,
            R.quotient_mem q⟩ :=
  resolved_rightTerm_eq_of_class_eq q.1.1
    ⟨canonicalCorrectedQuotientRaw R.Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
        canonicalLegSaturatedStarFacts q.1, R.quotient_mem q⟩
    (canonicalLegSaturatedContract_class_eq q R)

end GaugeGeometry.QFT.Combinatorial
