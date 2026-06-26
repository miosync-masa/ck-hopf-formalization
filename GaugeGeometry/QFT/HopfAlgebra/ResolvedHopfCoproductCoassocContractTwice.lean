import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightEq

/-!
# R-6c-heart-5c-2b-1 — contract-twice = contract-once graph anatomy

The `right_eq` obligation (5c-2a) is the single class equality

  `(branchRightGraph s).toResolvedClass = (imageInnerRightGraph imageOf s).toResolvedClass`.

A resolved class equality is exactly an **id-preserving isomorphism** (`mapPerm` by a vertex
permutation), since `(G.mapPerm σ).toResolvedClass = G.toResolvedClass`.  So the class equality reduces
to: the contract-once graph is the contract-twice graph relabeled by a **star permutation** `σ` (the
renaming that matches the single input-outer star to the two-stage selectedOuter+quotient stars), as an
equality of the three graph fields.

Per the HALT (the star map is the genuine de-contraction geometry, and `selectedOuter`/`quotientForest`
are still parametric supplies), the star permutation and the three field equalities are isolated as a
**geometry supply** `ResolvedContractTwiceOnceGeometrySupply`, from which `contract_class_eq` (hence
`right_eq`) follows by `mapPerm` ext + `toResolvedClass_mapPerm`.

Landed:

* `ResolvedFeynmanGraph.ext'` — a resolved graph is determined by its three fields;
* `ResolvedContractTwiceOnceGeometrySupply` — the star permutation + the vertices/internalEdges/external
  Legs equalities (`branchRightGraph s = (imageInnerRightGraph imageOf s).mapPerm σ`);
* `.toContractTwiceOnceSupply` — derives `contract_class_eq` (the 5c-2a supply) from the field equalities.

No facade, no flat term, no `forgetHopf`.  The three field equalities (the genuine de-contraction star
geometry) are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- A resolved Feynman graph is determined by its vertices / internal edges / external legs. -/
theorem ResolvedFeynmanGraph.ext' {G₁ G₂ : ResolvedFeynmanGraph}
    (hv : G₁.vertices = G₂.vertices) (hi : G₁.internalEdges = G₂.internalEdges)
    (he : G₁.externalLegs = G₂.externalLegs) : G₁ = G₂ := by
  cases G₁; cases G₂; cases hv; cases hi; cases he; rfl

/-- **R-6c-heart-5c-2b-1 — the contract-twice = contract-once geometry supply.**  The star permutation
`σ` matching the contract-once graph to the (mapPerm-relabeled) contract-twice graph, together with the
three field equalities `branchRightGraph s = (imageInnerRightGraph imageOf s).mapPerm σ`.  This is the
genuine de-contraction star geometry, isolated as a supply (the parametric selectedOuter/quotientForest
do not pin the stars). -/
structure ResolvedContractTwiceOnceGeometrySupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- The star permutation relabeling the contract-twice graph to the contract-once graph. -/
  starPerm : ResolvedCoassocSplitChoice D G → Equiv.Perm VertexId
  /-- The contract-once vertices are the relabeled contract-twice vertices. -/
  vertices_eq : ∀ s, (branchRightGraph s).vertices
    = ((imageInnerRightGraph imageOf s).mapPerm (starPerm s)).vertices
  /-- The contract-once internal edges are the relabeled contract-twice internal edges. -/
  internalEdges_eq : ∀ s, (branchRightGraph s).internalEdges
    = ((imageInnerRightGraph imageOf s).mapPerm (starPerm s)).internalEdges
  /-- The contract-once external legs are the relabeled contract-twice external legs. -/
  externalLegs_eq : ∀ s, (branchRightGraph s).externalLegs
    = ((imageInnerRightGraph imageOf s).mapPerm (starPerm s)).externalLegs

/-- **R-6c-heart-5c-2b-1 — the contract-twice = contract-once class equality from the geometry.**  The
three field equalities give `branchRightGraph s = (imageInnerRightGraph imageOf s).mapPerm σ`, and
`toResolvedClass` is `mapPerm`-invariant, so the classes agree. -/
theorem ResolvedContractTwiceOnceGeometrySupply.contract_class_eq
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (Geo : ResolvedContractTwiceOnceGeometrySupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) :
    (branchRightGraph s).toResolvedClass = (imageInnerRightGraph imageOf s).toResolvedClass := by
  rw [ResolvedFeynmanGraph.ext' (Geo.vertices_eq s) (Geo.internalEdges_eq s) (Geo.externalLegs_eq s),
    ResolvedFeynmanGraph.toResolvedClass_mapPerm]

/-- **R-6c-heart-5c-2b-1 — the 5c-2a supply from the geometry supply.**  Packages the derived
`contract_class_eq` as a `ResolvedContractTwiceOnceSupply`, ready to feed `right_eq`. -/
def ResolvedContractTwiceOnceGeometrySupply.toContractTwiceOnceSupply
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (Geo : ResolvedContractTwiceOnceGeometrySupply D G imageOf) :
    ResolvedContractTwiceOnceSupply D G imageOf where
  contract_class_eq := Geo.contract_class_eq

end GaugeGeometry.QFT.Combinatorial
