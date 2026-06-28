import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightStarIndexScout

/-!
# R-6c-heart-6a-8c-fix-1 — three-route vertex correspondence shape (post-mismatch redesign)

The 6a-8c-0 sanity check found the star correspondence is NOT a total star↔star bijection: a **left**
primitive's one-stage star becomes a two-stage **surviving** vertex (it has no quotient-forest component).
This file lays down the corrected shape — a **three-route** vertex correspondence — superseding the
star↔star `ResolvedContractStarMapSupply` framing for the right factor.

The three routes (one-stage vertex → two-stage vertex):

```
surviving original vertex (G \ A)   → two-stage surviving original vertex      (identity)
left primitive star                 → two-stage surviving selectedOuter-star   (identity on δ-star)
right / forest star (hasQuotientStar) → two-stage quotient-forest star          (the genuine index equiv)
```

So `starToStar` is NOT total — it is the **right/forest** part only (`quotientStarEquiv`), and the **left**
stars are absorbed into the **surviving** transport.  The eventual target is the full
`ResolvedContractTwiceVertexCorrespondence (oneStageContractGraph s) (twoStageContractGraph imageOf s)`
(one-stage full vertex subtype ≃ two-stage full vertex subtype) — NOT a star-subtype ≃ star-subtype.

Per the HALT, this only PLACES the shape: no concrete equivalence, no correspondence assembly, no
`retargetVertex_eq`; the existing `ResolvedContractStarMapSupply` / `ResolvedRightStarBijectionSupply` /
`ResolvedRightStarRecoverSupply` are left intact (their replacement / deprecation scope is the next step).

Landed (shape only):

* `ResolvedThreeRouteVertexMapSupply D G imageOf` — the three forward routes (`survivingOriginal_to`,
  `leftStar_toSurvivor`) plus the corrected `quotientStarEquiv : {hasQuotientStar} ≃ TwoStageStarIndex`.

The inverse-side partition (recovering the one-stage route from a two-stage vertex) and the assembly into
`ResolvedContractTwiceVertexCorrespondence` are deferred to fix-2.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-8c-fix-1 — the three-route vertex correspondence supply.**  Replaces the (false)
star↔star bijection: the right/forest stars carry the genuine `quotientStarEquiv`, while the left stars are
routed into the surviving transport. -/
structure ResolvedThreeRouteVertexMapSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- Route 1 (forward): a surviving original vertex (`G \ A`) survives the two-stage contraction. -/
  survivingOriginal_to : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    isContractSurvivingVertex s.1.1 v → isContractSurvivingVertex (imageOf s).quotientForest v
  /-- Route 2 (forward): a left-primitive one-stage star becomes a two-stage surviving vertex (its
  selected-outer `δ`-star, which survives stage 2 because the left component leaves no quotient
  component). -/
  leftStar_toSurvivor : ∀ (s : ResolvedCoassocSplitChoice D G) (i : OneStageStarIndex D G s),
    i.isLeft → isContractSurvivingVertex (imageOf s).quotientForest i.vertex
  /-- Route 3: the right/forest one-stage stars (`hasQuotientStar`) ≃ the quotient-forest stars (the
  genuine `componentPartition` / `Right ⊔ Remnant` correspondence, now correctly typed). -/
  quotientStarEquiv : ∀ s : ResolvedCoassocSplitChoice D G,
    {i : OneStageStarIndex D G s // i.hasQuotientStar} ≃ TwoStageStarIndex D G imageOf s

end GaugeGeometry.QFT.Combinatorial
