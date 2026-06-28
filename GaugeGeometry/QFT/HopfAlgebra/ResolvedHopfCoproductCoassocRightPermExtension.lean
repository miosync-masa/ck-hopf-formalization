import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightStarBijection

/-!
# R-6c-heart-6a-6e — RIGHT perm-extension combiner

Behind the BIGGEST star bijection sits the MECHANICAL `Equiv.Perm VertexId` extension: a global
permutation agreeing with the contract-twice vertex correspondence on the two graphs' vertices.  This file
fixes the exit of the star side — it isolates `starPerm` / `on_vertices` / `inv_on_vertices` as a named
supply over the star-bijection / surviving / freshness halves, and provides the adapter into
`VertexPermExtension` at the right `oneStage` / `twoStage` pair.

The correspondence is `(Star.toStarMapSupply Surv Fresh s).toVertexCorrespondence` (6a-6d-2), of type
`ResolvedContractTwiceVertexCorrespondence (oneStageContractGraph s) (twoStageContractGraph imageOf s)`
(defeq via `branchRightGraph` / `imageInnerRightGraph`).  So once the star bijection is concrete, the perm
extension is the only remaining star/perm input.

Per the HALT, `starPerm` is NOT constructed, `on_vertices` / `inv_on_vertices` are NOT proved, no concrete
`starToStar`, no `retargetVertex_eq` / `edge_domain_eq`.

Landed:

* `ResolvedRightPermExtensionSupply … Star Surv Fresh` — `starPerm` / `on_vertices` / `inv_on_vertices`
  per split choice, in `VertexPermExtension` shape;
* `.toPermExtension s` — the adapter producing `VertexPermExtension
  ((Star.toStarMapSupply Surv Fresh s).toVertexCorrespondence)`.

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

/-- **R-6c-heart-6a-6e — the right perm-extension supply.**  The global `Equiv.Perm VertexId` (per split
choice) agreeing with the contract-twice vertex correspondence on the `twoStage` / `oneStage` vertices —
exactly the `VertexPermExtension` fields, over the star-bijection / surviving / freshness halves. -/
structure ResolvedRightPermExtensionSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (Star : ResolvedRightStarBijectionSupply D G imageOf)
    (Surv : ResolvedRightSurvivingSupply D G imageOf)
    (Fresh : ResolvedRightStarFreshSupply D G imageOf) where
  /-- The full-`VertexId` permutation extending the correspondence (per split choice). -/
  starPerm : ∀ s : ResolvedCoassocSplitChoice D G, Equiv.Perm VertexId
  /-- On the two-stage vertices, `starPerm` is the inverse correspondence. -/
  on_vertices : ∀ (s : ResolvedCoassocSplitChoice D G) (w : VertexId)
    (hw : w ∈ (twoStageContractGraph imageOf s).vertices),
    starPerm s w = (((Star.toStarMapSupply Surv Fresh s).toVertexCorrespondence).invFun ⟨w, hw⟩).1
  /-- On the one-stage vertices, `starPerm.symm` is the forward correspondence. -/
  inv_on_vertices : ∀ (s : ResolvedCoassocSplitChoice D G) (v : VertexId)
    (hv : v ∈ (oneStageContractGraph s).vertices),
    (starPerm s).symm v = (((Star.toStarMapSupply Surv Fresh s).toVertexCorrespondence).toFun ⟨v, hv⟩).1

/-- **R-6c-heart-6a-6e — the perm extension at one split choice.**  Assembles `VertexPermExtension` over
the right vertex correspondence from the perm-extension supply. -/
def ResolvedRightPermExtensionSupply.toPermExtension
    {Star : ResolvedRightStarBijectionSupply D G imageOf}
    {Surv : ResolvedRightSurvivingSupply D G imageOf}
    {Fresh : ResolvedRightStarFreshSupply D G imageOf}
    (P : ResolvedRightPermExtensionSupply D G imageOf Star Surv Fresh)
    (s : ResolvedCoassocSplitChoice D G) :
    VertexPermExtension ((Star.toStarMapSupply Surv Fresh s).toVertexCorrespondence) where
  starPerm := P.starPerm s
  on_vertices := P.on_vertices s
  inv_on_vertices := P.inv_on_vertices s

end GaugeGeometry.QFT.Combinatorial
