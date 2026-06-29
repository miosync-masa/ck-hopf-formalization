import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocStarIndexRecover

/-!
# R-6c-heart-6a-9a — three-route recoveries from `starOf` injectivity (concrete)

The three-route correspondence's recovery fields and their specs are all instances of the generic
`starVertexEquivIndex` (6a-8b-2): given that each star assignment is injective on its forest's components
(`ResolvedStarIndexRecoverSupply`), the star vertices biject with the component indices.  This file derives,
for both sides:

* `oneStarRecover` / `twoStarRecover` — the star-vertex ≃ index equivalences (the route fields);
* `oneStarRecover_symm_apply` / `twoStarRecover_symm_apply` — the inverse is `toStarVertex` (the key fact);
* `oneStarRecover_vertex` / `twoStarVertex` — the recovered index's star vertex is the original;
* `honeInv` / `htwoInv` — recovery inverts `toStarVertex`.

So the entire "mechanical recovery" group of `ResolvedThreeRouteProvedSupply` collapses to two
`ResolvedStarIndexRecoverSupply` (the `starOf`-injectivity no-collision property).

Per the HALT, `star_injective_on_elements` is NOT proved (the supply field), `quotientStarEquiv` /
`Perm` / `Edge` / `retargetVertex_eq` are NOT touched.

Landed: `ResolvedThreeRouteRecoverSupply D G imageOf` + the six derived recovery facts.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-9a — the three-route recovery supply.**  Per split choice, `starOf` is injective on the
input outer / quotient forest components (no-collision). -/
structure ResolvedThreeRouteRecoverSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- `D.starOf G s.1.1` is injective on the input outer forest's components. -/
  oneRecover : ∀ s : ResolvedCoassocSplitChoice D G,
    ResolvedStarIndexRecoverSupply s.1.1 (D.starOf G s.1.1)
  /-- The quotient graph's star is injective on the quotient forest's components. -/
  twoRecover : ∀ s : ResolvedCoassocSplitChoice D G,
    ResolvedStarIndexRecoverSupply (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)

variable {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}

/-- **R-6c-heart-6a-9a — the one-stage star recovery. -/
noncomputable def ResolvedThreeRouteRecoverSupply.oneStarRecover
    (R : ResolvedThreeRouteRecoverSupply D G imageOf) (s : ResolvedCoassocSplitChoice D G) :
    {v : VertexId // isContractStarVertex s.1.1 (D.starOf G s.1.1) v} ≃ OneStageStarIndex D G s :=
  (starVertexEquivIndex (R.oneRecover s)).trans (oneStageStarIndexEquivSubtype s).symm

/-- **R-6c-heart-6a-9a — the two-stage star recovery. -/
noncomputable def ResolvedThreeRouteRecoverSupply.twoStarRecover
    (R : ResolvedThreeRouteRecoverSupply D G imageOf) (s : ResolvedCoassocSplitChoice D G) :
    {w : VertexId // isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) w}
      ≃ TwoStageStarIndex D G imageOf s :=
  (starVertexEquivIndex (R.twoRecover s)).trans (twoStageStarIndexEquivSubtype imageOf s).symm

/-- **R-6c-heart-6a-9a — the one-stage recovery inverts `toStarVertex`. -/
theorem ResolvedThreeRouteRecoverSupply.oneStarRecover_symm_apply
    (R : ResolvedThreeRouteRecoverSupply D G imageOf) (s : ResolvedCoassocSplitChoice D G)
    (i : OneStageStarIndex D G s) : (R.oneStarRecover s).symm i = i.toStarVertex := rfl

/-- **R-6c-heart-6a-9a — the two-stage recovery inverts `toStarVertex`. -/
theorem ResolvedThreeRouteRecoverSupply.twoStarRecover_symm_apply
    (R : ResolvedThreeRouteRecoverSupply D G imageOf) (s : ResolvedCoassocSplitChoice D G)
    (j : TwoStageStarIndex D G imageOf s) : (R.twoStarRecover s).symm j = j.toStarVertex := rfl

/-- **R-6c-heart-6a-9a — `honeInv`: one-stage recovery inverts `toStarVertex` (forward). -/
theorem ResolvedThreeRouteRecoverSupply.honeInv
    (R : ResolvedThreeRouteRecoverSupply D G imageOf) (s : ResolvedCoassocSplitChoice D G)
    (i : OneStageStarIndex D G s) : R.oneStarRecover s i.toStarVertex = i := by
  rw [← R.oneStarRecover_symm_apply s i, Equiv.apply_symm_apply]

/-- **R-6c-heart-6a-9a — `htwoInv`: two-stage recovery inverts `toStarVertex` (forward). -/
theorem ResolvedThreeRouteRecoverSupply.htwoInv
    (R : ResolvedThreeRouteRecoverSupply D G imageOf) (s : ResolvedCoassocSplitChoice D G)
    (j : TwoStageStarIndex D G imageOf s) : R.twoStarRecover s j.toStarVertex = j := by
  rw [← R.twoStarRecover_symm_apply s j, Equiv.apply_symm_apply]

/-- **R-6c-heart-6a-9a — `oneStarRecover_vertex`: the recovered one-stage index's star vertex is the
original. -/
theorem ResolvedThreeRouteRecoverSupply.oneStarRecover_vertex
    (R : ResolvedThreeRouteRecoverSupply D G imageOf) (s : ResolvedCoassocSplitChoice D G)
    (w : {v : VertexId // isContractStarVertex s.1.1 (D.starOf G s.1.1) v}) :
    (R.oneStarRecover s w).vertex = w.1 := by
  have : (R.oneStarRecover s w).toStarVertex = w := by
    rw [← R.oneStarRecover_symm_apply s (R.oneStarRecover s w), Equiv.symm_apply_apply]
  exact congrArg Subtype.val this

/-- **R-6c-heart-6a-9a — `twoStarVertex`: the recovered two-stage index's star vertex is the original. -/
theorem ResolvedThreeRouteRecoverSupply.twoStarVertex
    (R : ResolvedThreeRouteRecoverSupply D G imageOf) (s : ResolvedCoassocSplitChoice D G)
    (w : {v : VertexId // isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) v}) :
    (R.twoStarRecover s w).vertex = w.1 := by
  have : (R.twoStarRecover s w).toStarVertex = w := by
    rw [← R.twoStarRecover_symm_apply s (R.twoStarRecover s w), Equiv.symm_apply_apply]
  exact congrArg Subtype.val this

end GaugeGeometry.QFT.Combinatorial
