import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteVertexMap

/-!
# R-6c-heart-6a-8c-fix-2 — three-route vertex correspondence skeleton

The corrected main line (post-mismatch) targets the **full** vertex correspondence
`ResolvedContractTwiceVertexCorrespondence (oneStageContractGraph s) (twoStageContractGraph imageOf s)`
(one-stage full vertex subtype ≃ two-stage full vertex subtype), assembled from the three routes (fix-1)
plus the inverse-side partition data placed here.

`ResolvedThreeRouteVertexCorrespondenceSupply` extends the fix-1 map supply with the partition facts the
assembly needs:

* `twoStageSurvivor_cases` — a two-stage surviving vertex is either an original survivor or a
  left-primitive `δ`-star;
* `leftStar_unique` — distinct left-primitive stars are distinct vertices (recovery);
* `originalSurvivor_not_leftStar` — original survivors and left `δ`-stars are disjoint.

Per the HALT (skeleton, "field the correspondence if the assembly is heavy"), the correspondence's
`toFun` / `invFun` / `left_inv` / `right_inv` are carried as fields and packaged by `.toVertexCorrespondence`;
the three-route + partition fields document the obligations the eventual *derivation* (fix-3) will discharge
— replacing the fielded `toFun` / `invFun` by the constructive three-route branch.

This is the new main line.  The old star↔star chain (`ResolvedContractStarMapSupply` /
`ResolvedRightStarBijectionSupply` / `ResolvedRightStarRecoverSupply` / `ResolvedRightPermExtensionSupply`)
is left intact, standing alongside; its deprecation / rewiring of `FinalGeometryData` is a later step.

Per the HALT, no `cases` / `unique` / `disjoint` proofs, no old-chain deletion, no `FinalGeometryData`
rewiring.

Landed:

* `ResolvedThreeRouteVertexCorrespondenceSupply D G imageOf` — three-route + partition + raw correspondence
  fields;
* `.toVertexCorrespondence s` — the full `ResolvedContractTwiceVertexCorrespondence`.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-8c-fix-2 — the three-route vertex correspondence supply.**  Extends the fix-1 forward
routes with the inverse-side partition facts, and (skeleton) carries the full correspondence's components. -/
structure ResolvedThreeRouteVertexCorrespondenceSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    extends ResolvedThreeRouteVertexMapSupply D G imageOf where
  /-- A two-stage surviving vertex is an original survivor or a left-primitive `δ`-star. -/
  twoStageSurvivor_cases : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    isContractSurvivingVertex (imageOf s).quotientForest v →
      isContractSurvivingVertex s.1.1 v ∨
        ∃ i : OneStageStarIndex D G s, i.isLeft ∧ i.vertex = v
  /-- Distinct left-primitive stars are distinct vertices (left-star recovery). -/
  leftStar_unique : ∀ (s : ResolvedCoassocSplitChoice D G) (i j : OneStageStarIndex D G s),
    i.isLeft → j.isLeft → i.vertex = j.vertex → i = j
  /-- Original survivors and left-primitive `δ`-stars are disjoint. -/
  originalSurvivor_not_leftStar : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    isContractSurvivingVertex s.1.1 v → ∀ (i : OneStageStarIndex D G s), i.isLeft → v ≠ i.vertex
  /-- The assembled forward map (skeleton field; fix-3 derives it from the three routes). -/
  corrToFun : ∀ s : ResolvedCoassocSplitChoice D G,
    {v : VertexId // v ∈ (oneStageContractGraph s).vertices} →
      {v : VertexId // v ∈ (twoStageContractGraph imageOf s).vertices}
  /-- The assembled inverse map. -/
  corrInvFun : ∀ s : ResolvedCoassocSplitChoice D G,
    {v : VertexId // v ∈ (twoStageContractGraph imageOf s).vertices} →
      {v : VertexId // v ∈ (oneStageContractGraph s).vertices}
  /-- Left-inverse law. -/
  corrLeftInv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.LeftInverse (corrInvFun s) (corrToFun s)
  /-- Right-inverse law. -/
  corrRightInv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.RightInverse (corrInvFun s) (corrToFun s)

/-- **R-6c-heart-6a-8c-fix-2 — the full vertex correspondence (the new main line).** -/
def ResolvedThreeRouteVertexCorrespondenceSupply.toVertexCorrespondence
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (S : ResolvedThreeRouteVertexCorrespondenceSupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) :
    ResolvedContractTwiceVertexCorrespondence (oneStageContractGraph s)
      (twoStageContractGraph imageOf s) where
  toFun := S.corrToFun s
  invFun := S.corrInvFun s
  left_inv := S.corrLeftInv s
  right_inv := S.corrRightInv s

end GaugeGeometry.QFT.Combinatorial
