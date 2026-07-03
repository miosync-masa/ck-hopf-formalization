import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRetargetStarRecoveryScout

/-!
# R-6c-body-46 — the left recovery `one-stage star = TSV` from retarget agreement + non-membership

Forty-sixth genuine-body step, discharging body-45's `left_oneStageStar_eq_TSV` (the clean left-route vertex
equality) to two atomic facts.

For a left `v`, the two-stage vertex is `TSV = (imageOf s).quotientForest.retargetVertex starB
(rightVertexDomain (imageOf s) v)`.  Since a left star survives the quotient (it is not in the quotient forest,
body-10), the second retarget FIXES `rightVertexDomain (imageOf s) v` (`retargetVertex_of_not_mem`), so `TSV =
rightVertexDomain (imageOf s) v = (imageOf s).selectedOuter.1.retargetVertex (D.starOf G …) v`.  The left
recovery is then

```text
s.1.1.retargetVertex (D.starOf G s.1.1) v = rightVertexDomain (imageOf s) v
```

— the two one-stage retargets (through the input outer `s.1.1` and through the selected outer) AGREE on `v`.
This is the genuine star-allocation compatibility: a left-primitive component's star is carried to the same
`VertexId` whether allocated via `s.1.1` or the selected outer.  It is the fielded core (`retargets_agree`);
the non-membership (`rightDomain_not_mem_quotientForest`) is the body-10 left-star-survives content; the
`retargetVertex_of_not_mem` collapse is proved.

Per the HALT, `retargets_agree` (the star-allocation compatibility) is NOT proved — the `D.starOf G s.1.1` vs
`D.starOf G selectedOuter` allocations are distinct; only the retarget non-membership collapse is proved.

Landed:

* `ResolvedLeftStarRetargetEqSupply D G imageOf App` — `rightDomain_not_mem_quotientForest` + `retargets_agree`;
* `.left_oneStageStar_eq_TSV` — body-45's clean left fact, PROVED.

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

/-- **R-6c-body-46 — the left-star retarget-equality supply.**  The left star's non-membership in the quotient
forest (body-10 survival) and the star-allocation agreement of the two one-stage retargets on `v`. -/
structure ResolvedLeftStarRetargetEqSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (App : ResolvedRetargetInnerApplicabilitySupply D G imageOf) where
  /-- The left star (`rightVertexDomain v`) is not in the quotient forest (it survives — body-10). -/
  rightDomain_not_mem_quotientForest : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    App.innerLeft s v →
    rightVertexDomain (imageOf s) v ∉ (imageOf s).quotientForest.vertices
  /-- The input-outer and selected-outer one-stage retargets agree on `v` (star-allocation compatibility). -/
  retargets_agree : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    App.innerLeft s v →
    s.1.1.retargetVertex (D.starOf G s.1.1) v = rightVertexDomain (imageOf s) v

/-- **R-6c-body-46 — body-45's clean left fact, PROVED.**  `retargets_agree` moves the LHS to
`rightVertexDomain v`, then the left star's non-membership makes the second retarget fix it. -/
theorem ResolvedLeftStarRetargetEqSupply.left_oneStageStar_eq_TSV
    {App : ResolvedRetargetInnerApplicabilitySupply D G imageOf}
    (F : ResolvedLeftStarRetargetEqSupply D G imageOf App)
    (s : ResolvedCoassocSplitChoice D G) {v : VertexId} (hleft : App.innerLeft s v) :
    s.1.1.retargetVertex (D.starOf G s.1.1) v
      = (imageOf s).quotientForest.retargetVertex
          (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
          (rightVertexDomain (imageOf s) v) := by
  rw [F.retargets_agree s hleft]
  exact (ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _
    (F.rightDomain_not_mem_quotientForest s hleft)).symm

end GaugeGeometry.QFT.Combinatorial
