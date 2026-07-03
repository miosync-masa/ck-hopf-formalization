import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRetargetCorrBody

/-!
# R-6c-body-28 — the survivingOriginal retarget route (outer_case) PROVED

Twenty-eighth genuine-body step, discharging body-27's `outer_case` — the survivingOriginal route of
`retarget_corr_on_vertices` — from three atomic facts.

For `v ∈ G.vertices` with `v ∉ s.1.1.vertices` (outside the input outer forest):

* the one-stage retarget fixes `v` (`retargetVertex_of_not_mem`), so the LHS is `v`;
* `rightVertexDomain (imageOf s) v = (imageOf s).selectedOuter.1.retargetVertex … v = v`, since the selected
  outer avoids the outer survivor (`selectedOuter.vertices ⊆ A.vertices`, body-8);
* the quotient-forest retarget then fixes `v` too, since the quotient forest avoids the outer survivors
  (body-9);
* so the two-stage vertex is `v`, and the correspondence's `invFun` sends the survivingOriginal `v` back to
  `v` (`corr_invFun_survivor`).

The two avoidance facts and the `invFun` survivingOriginal value are the fielded inputs (`selectedOuter` /
`quotientForest` avoid outer survivors — body-8/9; the `invFun` value — the three-route construction's
survivingOriginal branch).  The assembly is proved: LHS `= v` and the RHS collapses to `v` through the two
`retargetVertex_of_not_mem` reductions plus the `invFun` value.

Per the HALT, the inner-left / inner-right routes are untouched; the correspondence `invFun` value is fielded,
not unfolded.

Landed:

* `ResolvedRetargetOuterCaseSupply D G imageOf Three` — the three atomic facts;
* `.outer_case` — body-27's survivingOriginal route, PROVED.

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

/-- **R-6c-body-28 — the survivingOriginal-route supply.**  The selected-outer / quotient-forest avoid the
outer survivors, and the correspondence's `invFun` fixes a survivingOriginal vertex. -/
structure ResolvedRetargetOuterCaseSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (Three : ResolvedThreeRouteProvedSupply D G imageOf) where
  /-- The selected outer avoids the outer survivors (body-8: `selectedOuter.vertices ⊆ A.vertices`). -/
  selectedOuter_avoids_outer : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    v ∉ s.1.1.vertices → v ∉ (imageOf s).selectedOuter.1.vertices
  /-- The quotient forest avoids the outer survivors (body-9). -/
  quotient_avoids_outer : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    v ∉ s.1.1.vertices → v ∉ (imageOf s).quotientForest.vertices
  /-- The correspondence's `invFun` fixes a survivingOriginal two-stage vertex. -/
  corr_invFun_survivor : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId}
    (hmem : v ∈ (twoStageContractGraph imageOf s).vertices),
    ((Three.toVertexCorrespondence s).invFun ⟨v, hmem⟩).1 = v

/-- **R-6c-body-28 — body-27's `outer_case` (survivingOriginal route), PROVED from the three atomic facts. -/
theorem ResolvedRetargetOuterCaseSupply.outer_case
    {Three : ResolvedThreeRouteProvedSupply D G imageOf}
    (F : ResolvedRetargetOuterCaseSupply D G imageOf Three)
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
  show s.1.1.retargetVertex (D.starOf G s.1.1) v = _
  rw [ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ hnot]
  have hpair : (⟨(imageOf s).quotientForest.retargetVertex
        (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
        (rightVertexDomain (imageOf s) v), resolved_retarget_rhs_mem s hv⟩ :
        {x // x ∈ (twoStageContractGraph imageOf s).vertices}) = ⟨v, hmem⟩ := Subtype.ext key
  rw [hpair]
  exact (F.corr_invFun_survivor s hmem).symm

end GaugeGeometry.QFT.Combinatorial
