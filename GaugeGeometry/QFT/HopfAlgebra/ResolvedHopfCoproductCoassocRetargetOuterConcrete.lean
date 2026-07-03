import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRetargetOuterCase
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteInvFunValues

/-!
# R-6c-body-29b — the outer (survivingOriginal) retarget route, invFun field DISCHARGED

A follow-up to body-28: its `ResolvedRetargetOuterCaseSupply.corr_invFun_survivor` was stated
UNCONDITIONALLY (`∀ v`, `(invFun ⟨v,hmem⟩).1 = v`), but the correspondence sends two-stage STAR vertices to
one-stage stars, so that field is false for star `v` — unsatisfiable in general.  Body-29's packaged value
lemma `threeRoute_invFun_original_val` lets us discharge the invFun step at exactly the outer vertex (where it
IS a survivingOriginal), so no unconditional field is needed.

For `v ∈ G.vertices`, `v ∉ s.1.1.vertices`:

* `hOrig : isContractSurvivingVertex s.1.1 v = ⟨hv, hnot⟩` (survivor of the input outer — free);
* `v ∈ (resolvedCoassocQuotientGraph (imageOf s)).vertices` (it survives the selected-outer contraction, since
  the selected outer avoids it), so with `freshB` (quotient stars are fresh) `contract_surviving_not_star`
  gives `hnotstarB` (v is not a quotient star);
* then `threeRoute_invFun_original_val` sends the two-stage `v` back to `v`.

So `outer_case` depends only on `selectedOuter_avoids_outer` + `quotient_avoids_outer` + `freshB` — all
satisfiable (body-8/9 + the canonical quotient-star freshness).  This is the concrete outer supply for
body-27's `ResolvedRetargetCorrCaseSupply.outer_case`.

Per the HALT, inner-left / inner-right routes are untouched.

Landed:

* `ResolvedRetargetOuterConcreteSupply D G imageOf Three` — `selectedOuter_avoids_outer` +
  `quotient_avoids_outer` + `freshB`;
* `.outer_case` — body-27's survivingOriginal route, PROVED with the invFun value discharged.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}

/-- **R-6c-body-29b — the concrete survivingOriginal-route supply.**  The selected-outer / quotient-forest
avoid the outer survivors, and the quotient stars are fresh (`freshB`); the invFun value is then discharged. -/
structure ResolvedRetargetOuterConcreteSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (Three : ResolvedThreeRouteProvedSupply D G imageOf) where
  /-- The selected outer avoids the outer survivors (body-8: `selectedOuter.vertices ⊆ A.vertices`). -/
  selectedOuter_avoids_outer : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    v ∉ s.1.1.vertices → v ∉ (imageOf s).selectedOuter.1.vertices
  /-- The quotient forest avoids the outer survivors (body-9). -/
  quotient_avoids_outer : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    v ∉ s.1.1.vertices → v ∉ (imageOf s).quotientForest.vertices
  /-- The quotient forest's stars are fresh (outside the quotient graph). -/
  freshB : ∀ (s : ResolvedCoassocSplitChoice D G),
    ∀ η ∈ (imageOf s).quotientForest.elements,
      D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest η
        ∉ (resolvedCoassocQuotientGraph (imageOf s)).vertices

/-- **R-6c-body-29b — body-27's `outer_case` (survivingOriginal route), PROVED with the invFun value
discharged by `threeRoute_invFun_original_val`. -/
theorem ResolvedRetargetOuterConcreteSupply.outer_case
    {Three : ResolvedThreeRouteProvedSupply D G imageOf}
    (F : ResolvedRetargetOuterConcreteSupply D G imageOf Three)
    (s : ResolvedCoassocSplitChoice D G) {v : VertexId} (hv : v ∈ G.vertices)
    (hnot : v ∉ s.1.1.vertices) :
    RetargetCorrOnVerticesTarget Three s hv := by
  have hrd : rightVertexDomain (imageOf s) v = v :=
    ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ (F.selectedOuter_avoids_outer s hnot)
  have hqf : (imageOf s).quotientForest.retargetVertex
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) v = v :=
    ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ (F.quotient_avoids_outer s hnot)
  have key : (imageOf s).quotientForest.retargetVertex
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
      (rightVertexDomain (imageOf s) v) = v := by rw [hrd]; exact hqf
  have hmem : v ∈ (twoStageContractGraph imageOf s).vertices := key ▸ resolved_retarget_rhs_mem s hv
  have hvQ : v ∈ (resolvedCoassocQuotientGraph (imageOf s)).vertices := by
    have hveq : (resolvedCoassocQuotientGraph (imageOf s)).vertices =
        (G.vertices \ (imageOf s).selectedOuter.1.vertices) ∪
          (imageOf s).selectedOuter.1.starVertices (D.starOf G (imageOf s).selectedOuter.1) := rfl
    rw [hveq]
    exact Finset.mem_union_left _
      (Finset.mem_sdiff.mpr ⟨hv, F.selectedOuter_avoids_outer s hnot⟩)
  have hSurv : isContractSurvivingVertex (imageOf s).quotientForest v :=
    ⟨hvQ, F.quotient_avoids_outer s hnot⟩
  have hnotstarB : ¬ isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) v :=
    fun hst => contract_surviving_not_star (imageOf s).quotientForest _ (F.freshB s) hSurv hst
  have hOrig : isContractSurvivingVertex s.1.1 v := ⟨hv, hnot⟩
  show s.1.1.retargetVertex (D.starOf G s.1.1) v = _
  rw [ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ hnot]
  have hpair : (⟨(imageOf s).quotientForest.retargetVertex
        (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
        (rightVertexDomain (imageOf s) v), resolved_retarget_rhs_mem s hv⟩ :
        {x // x ∈ (twoStageContractGraph imageOf s).vertices}) = ⟨v, hmem⟩ := Subtype.ext key
  rw [hpair]
  exact (threeRoute_invFun_original_val Three s ⟨v, hmem⟩ hnotstarB hOrig).symm

end GaugeGeometry.QFT.Combinatorial
