import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocContractTwice

/-!
# R-6c-heart-5c-2b-2a — star permutation + retarget composition scaffold

The contract-twice = contract-once field equalities (5c-2b-1) need the **star permutation** `σ` and the
**retarget composition** matching the one-step retarget of the input outer `A` with the two-step
retarget of `selectedOuter A'` followed by `quotientForest B'`.

The heart is at the **vertex** level:

  `A.retargetVertex starA v = σ (B'.retargetVertex starB' (A'.retargetVertex starA' v))`,

i.e. collapsing `A` to its single star equals: collapse `A'` to its star, then collapse `B'` to its
star, then rename the two-stage star to the one-stage star by `σ`.  This is isolated as a supply
`ResolvedContractTwiceRetargetSupply` (the parametric selectedOuter/quotientForest and the genuine star
matching).

Because resolved edges/legs are **endpoint retargets that preserve the id/sector**
(`ResolvedFeynmanEdge.map π e = e.retarget π`, `(e.retarget f).retarget g = e.retarget (g ∘ f)`,
`e.retarget (σ ∘ h) = (e.retarget h).map σ`, all by `rfl`), the vertex composition **lifts for free** to
edges and legs:

  `A.retargetEdge starA e = (B'.retargetEdge starB' (A'.retargetEdge starA' e)).map σ`
  `A.retargetExternalLeg starA ℓ = (B'.retargetExternalLeg starB' (A'.retargetExternalLeg starA' ℓ)).map σ`

Landed:

* `ResolvedContractTwiceRetargetSupply` — `starPerm` + the vertex retarget composition;
* `retargetEdge_eq` / `retargetExternalLeg_eq` — the edge/leg composition, derived by `rfl`.

No facade, no flat term, no `forgetHopf`.  The three field equalities (the complement-edge / external-leg
multiset correspondences on top of the retarget composition) are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-5c-2b-2a — the retarget composition supply.**  The star permutation `σ` and the vertex
retarget composition: collapsing the input outer `A` once equals collapsing the selected outer `A'`,
then its quotient subforest `B'`, then relabeling the two-stage star to the one-stage star by `σ`.  The
genuine de-contraction star geometry (parametric selectedOuter/quotientForest), isolated as a supply. -/
structure ResolvedContractTwiceRetargetSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- The star permutation relabeling the two-stage star to the one-stage star. -/
  starPerm : ResolvedCoassocSplitChoice D G → Equiv.Perm VertexId
  /-- The vertex retarget composition: one-step `A` retarget = `σ` of (two-step `A'` then `B'` retarget). -/
  retargetVertex_eq : ∀ (s : ResolvedCoassocSplitChoice D G) (v : VertexId),
    s.1.1.retargetVertex (D.starOf G s.1.1) v
      = starPerm s ((imageOf s).quotientForest.retargetVertex
          (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
          ((imageOf s).selectedOuter.1.retargetVertex
            (D.starOf G (imageOf s).selectedOuter.1) v))

/-- **R-6c-heart-5c-2b-2a — the edge retarget composition.**  The vertex composition lifts to edges:
the one-step `A` retarget of an edge is the two-step `A'`-then-`B'` retarget, relabeled by `σ`.  By `rfl`
(edge retarget/map are endpoint maps preserving id/sector). -/
theorem ResolvedContractTwiceRetargetSupply.retargetEdge_eq
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (Ret : ResolvedContractTwiceRetargetSupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) (e : ResolvedFeynmanEdge) :
    s.1.1.retargetEdge (D.starOf G s.1.1) e
      = ((imageOf s).quotientForest.retargetEdge
          (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
          ((imageOf s).selectedOuter.1.retargetEdge
            (D.starOf G (imageOf s).selectedOuter.1) e)).map (Ret.starPerm s) := by
  unfold ResolvedAdmissibleSubgraph.retargetEdge
  rw [funext (Ret.retargetVertex_eq s)]
  rfl

/-- **R-6c-heart-5c-2b-2a — the external-leg retarget composition.**  The vertex composition lifts to
external legs (same shape as edges). -/
theorem ResolvedContractTwiceRetargetSupply.retargetExternalLeg_eq
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (Ret : ResolvedContractTwiceRetargetSupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) (ℓ : ResolvedExternalLeg) :
    s.1.1.retargetExternalLeg (D.starOf G s.1.1) ℓ
      = ((imageOf s).quotientForest.retargetExternalLeg
          (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
          ((imageOf s).selectedOuter.1.retargetExternalLeg
            (D.starOf G (imageOf s).selectedOuter.1) ℓ)).map (Ret.starPerm s) := by
  unfold ResolvedAdmissibleSubgraph.retargetExternalLeg
  rw [funext (Ret.retargetVertex_eq s)]
  rfl

end GaugeGeometry.QFT.Combinatorial
