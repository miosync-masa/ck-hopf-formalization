import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocEdgeLegFromVertex

/-!
# R-6c-heart-6a-5c-4a — the final contract-twice geometry record

All the minimized star-geometry obligations are now bundled into **one** record
`ResolvedContractTwiceFinalGeometryData` (per contraction context `A`/`starA`, `B`/`starB`):

1. `starMap` — the star bijection + surviving transport + freshness (6a-5c-2b);
2. `permExt` — the `VertexId` perm extension (6a-5c-2c);
3. `edgeLegVertex` — the single vertex retarget equation + the edge/leg domain correspondences
   (6a-5c-3d).

From it, the whole chain `→ FieldEqSupply → ClassData` is derived; for the right factor,
`toRightClassData` lands in the `oneStage`/`twoStage` graph pair feeding `right_eq`.

Per the HALT, none of the record's fields are constructed/proved — this only bundles them.

Landed:

* `ResolvedContractTwiceFinalGeometryData A starA B starB` — the one record;
* `.toFieldEqSupply` / `.toClassData` — the derived field-equality supply and class datum;
* `.toRightClassData` — the right-factor class datum (the `oneStage`/`twoStage` pair).

No facade, no flat term, no `forgetHopf`.  Constructing the record's fields for the actual right/remnant
graphs (the genuine de-contraction geometry) is the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {GA QB : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-5c-4a — the final contract-twice geometry record.**  Bundles the star bijection, the
perm extension, and the vertex retarget + domain data for one contraction pair `(A, starA)` / `(B, starB)`
(graphs `A.contractWithStars starA` and `B.contractWithStars starB`). -/
structure ResolvedContractTwiceFinalGeometryData
    (A : ResolvedAdmissibleSubgraph GA) (starA : ResolvedFeynmanSubgraph GA → VertexId)
    (B : ResolvedAdmissibleSubgraph QB) (starB : ResolvedFeynmanSubgraph QB → VertexId) where
  /-- The star bijection + surviving transport + freshness. -/
  starMap : ResolvedContractStarMapSupply A starA B starB
  /-- The `VertexId` permutation extension. -/
  permExt : VertexPermExtension starMap.toVertexCorrespondence
  /-- The vertex retarget composition + edge/leg domain correspondences. -/
  edgeLegVertex : ResolvedContractTwiceEdgeLegVertexData A starA B starB permExt.starPerm

variable {A : ResolvedAdmissibleSubgraph GA} {starA : ResolvedFeynmanSubgraph GA → VertexId}
  {B : ResolvedAdmissibleSubgraph QB} {starB : ResolvedFeynmanSubgraph QB → VertexId}

/-- **R-6c-heart-6a-5c-4a — the field-equality supply from the final record.** -/
noncomputable def ResolvedContractTwiceFinalGeometryData.toFieldEqSupply
    (F : ResolvedContractTwiceFinalGeometryData A starA B starB) :
    ResolvedContractTwiceFieldEqSupply F.permExt :=
  ResolvedContractTwiceFieldEqSupply.ofEdgeLegData F.permExt F.edgeLegVertex.toEdgeLegData

/-- **R-6c-heart-6a-5c-4a — the class datum from the final record.** -/
noncomputable def ResolvedContractTwiceFinalGeometryData.toClassData
    (F : ResolvedContractTwiceFinalGeometryData A starA B starB) :
    ResolvedContractTwiceClassData (A.contractWithStars starA) (B.contractWithStars starB) :=
  F.toFieldEqSupply.toClassData

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-5c-4a — the right-factor class datum from the final record.**  Instantiated at the
one-stage (`branchRightGraph`) / two-stage (`imageInnerRightGraph`) pair feeding `right_eq`. -/
noncomputable def ResolvedContractTwiceFinalGeometryData.toRightClassData
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    {s : ResolvedCoassocSplitChoice D G}
    (F : ResolvedContractTwiceFinalGeometryData s.1.1 (D.starOf G s.1.1)
      (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)) :
    ResolvedContractTwiceClassData (oneStageContractGraph s) (twoStageContractGraph imageOf s) :=
  F.toClassData

end GaugeGeometry.QFT.Combinatorial
