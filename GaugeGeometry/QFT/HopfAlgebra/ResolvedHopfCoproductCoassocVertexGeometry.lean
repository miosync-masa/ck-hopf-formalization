import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocEdgeLegDomain

/-!
# R-6c-heart-5c-2b-2c — `vertices_eq` field + the assembled geometry supply

The last of the three contract-twice = contract-once graph fields is `vertices_eq`:

  `(branchRightGraph s).vertices = ((imageInnerRightGraph imageOf s).mapPerm σ).vertices`,

i.e. `(G.vertices \ A.vertices) ∪ A.starVertices starA = ((Q.vertices \ B'.vertices) ∪ B'.starVertices
starB').image σ` (with `Q = A'.contractWithStars starA'`).  Unlike the edge/leg fields, this involves
**star vertex sets** and the star renaming `σ` matching `A`'s single star to the two-stage
`A'`/`B'` stars — the genuine final star geometry.  Per the HALT it is kept as a **field**.

With `vertices_eq` supplied (and `internalEdges_eq` from `internalEdges_domain`, `externalLegs_eq` free),
all three fields of `ResolvedContractTwiceOnceGeometrySupply` are available, so `contract_class_eq` and
hence `right_eq` follow.

Landed:

* `ResolvedContractTwiceVertexGeometrySupply` (extends the edge/leg supply with `vertices_eq`);
* `.toGeometrySupply` — the full `ResolvedContractTwiceOnceGeometrySupply` (all 3 field equalities);
* `.toContractTwiceOnceSupply` / `.right_eq` — `right_eq` from the assembled geometry.

So `right_eq` is now reduced to **exactly** `internalEdges_domain` + `vertices_eq` (+ the star
permutation `starPerm` and the vertex retarget composition `retargetVertex_eq`).

No facade, no flat term, no `forgetHopf`.  Discharging `internalEdges_domain` / `vertices_eq` /
`retargetVertex_eq` (the concrete de-contraction star geometry) is the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-5c-2b-2c — the vertex geometry supply.**  Extends the edge/leg supply with the final
star-geometry field: the contract-once vertices are the relabeled contract-twice vertices. -/
structure ResolvedContractTwiceVertexGeometrySupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    extends ResolvedContractTwiceEdgeLegSupply D G imageOf where
  /-- The contract-once vertices are the relabeled contract-twice vertices (the star-vertex
  correspondence). -/
  vertices_eq : ∀ s : ResolvedCoassocSplitChoice D G,
    (branchRightGraph s).vertices
      = ((imageInnerRightGraph imageOf s).mapPerm (starPerm s)).vertices

/-- **R-6c-heart-5c-2b-2c — the assembled geometry supply.**  All three field equalities: `vertices_eq`
(this layer), `internalEdges_eq` (from `internalEdges_domain`), `externalLegs_eq` (free). -/
def ResolvedContractTwiceVertexGeometrySupply.toGeometrySupply
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (V : ResolvedContractTwiceVertexGeometrySupply D G imageOf) :
    ResolvedContractTwiceOnceGeometrySupply D G imageOf where
  starPerm := V.starPerm
  vertices_eq := V.vertices_eq
  internalEdges_eq := V.toResolvedContractTwiceEdgeLegSupply.internalEdges_eq
  externalLegs_eq := V.toResolvedContractTwiceEdgeLegSupply.toResolvedContractTwiceRetargetSupply.externalLegs_eq

/-- **R-6c-heart-5c-2b-2c — the 5c-2a supply from the vertex geometry supply.** -/
def ResolvedContractTwiceVertexGeometrySupply.toContractTwiceOnceSupply
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (V : ResolvedContractTwiceVertexGeometrySupply D G imageOf) :
    ResolvedContractTwiceOnceSupply D G imageOf :=
  V.toGeometrySupply.toContractTwiceOnceSupply

/-- **R-6c-heart-5c-2b-2c — `right_eq` from the vertex geometry supply.**  The whole contract-twice =
contract-once chain: vertex retarget composition + the three field equalities ⇒ class equality ⇒
`right_eq`. -/
theorem ResolvedContractTwiceVertexGeometrySupply.right_eq
    (R : ResolvedCoassocInnerRightSupply D G)
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (V : ResolvedContractTwiceVertexGeometrySupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) :
    (D.supply G).rightTerm s.1 = R.innerRightTerm (imageOf s) :=
  V.toContractTwiceOnceSupply.right_eq R s

end GaugeGeometry.QFT.Combinatorial
