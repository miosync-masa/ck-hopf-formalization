import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteCorrespondence
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightEdgeConnector

/-!
# R-6c-heart-6a-8c-fix-3a — ThreeRoute-based right geometry combiner (bypasses the star↔star chain)

This confirms the corrected three-route vertex correspondence (fix-2) flows all the way to `right_eq`,
WITHOUT `ResolvedContractStarMapSupply` (the star↔star structure that the 6a-8c-0 mismatch invalidated).

Key fact: the chain `VertexPermExtension corr → FieldEqSupply → ClassData → classEq` is **generic in
`corr`** (`ResolvedContractTwiceFieldEqSupply {corr} (E : VertexPermExtension corr)` takes any
correspondence).  So `ResolvedContractTwiceFinalGeometryData`'s hard-wired `starMap.toVertexCorrespondence`
is sidestepped: we feed `Three.toVertexCorrespondence s` instead, and `ofEdgeLegData` pins the graphs from
the (explicitly-typed) `EdgeLegData` while `E`'s corr matches by defeq.

So the new main line is fully wired:

```
Three.toVertexCorrespondence → VertexPermExtension → EdgeLegVertex (Edge + retargetVertex_eq)
  → FieldEqSupply.ofEdgeLegData → ClassData → contract_class_eq → right_eq
```

Per the HALT, no `corrToFun` / `corrInvFun` implementation, no old-chain deletion, no concrete proofs.

Landed:

* `ResolvedRightThreeRouteFinalGeometrySupply D G imageOf` — `Three` + per-`s` `VertexPermExtension` over
  `Three.toVertexCorrespondence` + `Edge` + `retargetVertex_eq`;
* `.toClassData` / `.toContractTwiceOnceSupply` / `.right_eq` — through to the right-factor class equality.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-8c-fix-3a — the ThreeRoute-based right final-geometry supply.**  The three-route
correspondence, the perm extension over it, the edge-domain connector, and the contract-twice vertex
composition (σ = the perm extension's permutation). -/
structure ResolvedRightThreeRouteFinalGeometrySupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- The three-route vertex correspondence (fix-2). -/
  Three : ResolvedThreeRouteVertexCorrespondenceSupply D G imageOf
  /-- The perm extension over the three-route correspondence (per split choice). -/
  Perm : ∀ s : ResolvedCoassocSplitChoice D G,
    VertexPermExtension (Three.toVertexCorrespondence s)
  /-- The edge-domain connector (6a-6c). -/
  Edge : ResolvedRightEdgeDomainSupply D G imageOf
  /-- The contract-twice vertex composition, with σ = `(Perm s).starPerm`. -/
  retargetVertex_eq : ∀ (s : ResolvedCoassocSplitChoice D G) (v : VertexId),
    s.1.1.retargetVertex (D.starOf G s.1.1) v
      = (Perm s).starPerm ((imageOf s).quotientForest.retargetVertex
          (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
          (rightVertexDomain (imageOf s) v))

/-- **R-6c-heart-6a-8c-fix-3a — the right-factor class datum from the three-route correspondence.** -/
noncomputable def ResolvedRightThreeRouteFinalGeometrySupply.toClassData
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (R : ResolvedRightThreeRouteFinalGeometrySupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) :
    ResolvedContractTwiceClassData (oneStageContractGraph s) (twoStageContractGraph imageOf s) :=
  (ResolvedContractTwiceFieldEqSupply.ofEdgeLegData (R.Perm s)
    (R.Edge.toEdgeLegVertexData s (R.Perm s).starPerm (R.retargetVertex_eq s)).toEdgeLegData).toClassData

/-- **R-6c-heart-6a-8c-fix-3a — the contract-twice = contract-once supply, three-route wired. -/
noncomputable def ResolvedRightThreeRouteFinalGeometrySupply.toContractTwiceOnceSupply
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (R : ResolvedRightThreeRouteFinalGeometrySupply D G imageOf) :
    ResolvedContractTwiceOnceSupply D G imageOf where
  contract_class_eq := fun s => contract_class_eq_of_classData (R.toClassData s)

/-- **R-6c-heart-6a-8c-fix-3a — `right_eq`, fully wired from the three-route correspondence. -/
theorem ResolvedRightThreeRouteFinalGeometrySupply.right_eq
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (R : ResolvedRightThreeRouteFinalGeometrySupply D G imageOf)
    (Inner : ResolvedCoassocInnerRightSupply D G) (s : ResolvedCoassocSplitChoice D G) :
    (D.supply G).rightTerm s.1 = Inner.innerRightTerm (imageOf s) :=
  ResolvedContractTwiceOnceSupply.right_eq Inner R.toContractTwiceOnceSupply s

end GaugeGeometry.QFT.Combinatorial
