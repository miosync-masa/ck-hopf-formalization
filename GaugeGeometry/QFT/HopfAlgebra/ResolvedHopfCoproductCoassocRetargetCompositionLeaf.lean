import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRetargetLeaves

/-!
# R-6c-leaf-36 — retarget composition: the membership half proved, the correspondence half scouted

Thirty-first leaf-body step, on the deepest vertex-geometry leaf (leaf-21's `rhs_mem` / `retarget_corr`).

**`rhs_mem` (membership).**  `RHS_inner s v = quotientForest.retargetVertex … (rightVertexDomain (imageOf s) v)`
lands in `(twoStageContractGraph imageOf s).vertices` — PROVED here for `v ∈ G.vertices` by
`retargetVertex_mem_contractWithStars_vertices` applied twice (stage-1 into the quotient graph, stage-2 into
the two-stage graph).  Scout finding: the leaf-21 field is `∀ v`, but for `v ∉ G.vertices`, `retargetVertex`
fixes `v` (`retargetVertex_of_not_mem`) and `v ∉ (twoStageContractGraph …).vertices` in general — so the
unrestricted `∀ v` membership is genuinely FALSE off the vertex set (there, `retargetVertex_eq` instead holds
because both sides equal `v`, needing the perm to fix non-vertices).  The meaningful content is exactly the
`v ∈ G.vertices` version below.

**`retarget_corr` (the correspondence half).**  This is the three-route action of `corr.invFun` on `RHS_inner`,
i.e. the full survivor / left-star / quotient-star case analysis already carried by `threeRouteCorrToFun` /
`threeRouteCorrInvFun` and their round-trip lemmas — deep, left as the leaf-21 field.

Per the HALT, only the membership half is proved; the three-route `retarget_corr` cases are not.

Landed:

* `resolved_retarget_rhs_mem` — `rhs_mem` for `v ∈ G.vertices` (PROVED).

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

/-- **R-6c-leaf-36 — the retarget membership (`rhs_mem`) for `v ∈ G.vertices`.**  The two-stage retarget of
the stage-1 image lands in the two-stage contract graph: stage-1 `rightVertexDomain` maps `v ∈ G.vertices`
into the quotient graph, then the stage-2 quotient-forest retarget maps into the two-stage graph. -/
theorem resolved_retarget_rhs_mem (s : ResolvedCoassocSplitChoice D G) {v : VertexId}
    (hv : v ∈ G.vertices) :
    (imageOf s).quotientForest.retargetVertex
        (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
        (rightVertexDomain (imageOf s) v)
      ∈ (twoStageContractGraph imageOf s).vertices := by
  apply ResolvedAdmissibleSubgraph.retargetVertex_mem_contractWithStars_vertices
  exact (imageOf s).selectedOuter.1.retargetVertex_mem_contractWithStars_vertices _ hv

end GaugeGeometry.QFT.Combinatorial
