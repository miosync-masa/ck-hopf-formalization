import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocStarVertexMap

/-!
# R-6c-heart-6a-5c-2c — extending the vertex correspondence to a `VertexId` permutation

`ResolvedContractTwiceClassData.starPerm` is a permutation of **all** `VertexId`, while the contract-twice
correspondence (6a-5c-2b) is a bijection on the vertex *Finsets* `G₁.vertices ≃ G₂.vertices`.  Extending a
subtype bijection to a full `Equiv.Perm VertexId` would drag in `Finset`-complement bookkeeping whose
outside-the-graphs behaviour is irrelevant to the geometry.

So — per the HALT — the extension is taken as a **supply** `VertexPermExtension`: a permutation of
`VertexId` that *agrees with the correspondence on the vertices* (`on_vertices` / `inv_on_vertices`),
without pinning its action elsewhere.  `.toClassData` then bundles it with the three field equalities into
`ResolvedContractTwiceClassData`.  The `on_vertices` fields are what later let the field equalities be
proved from the correspondence.

So `ResolvedContractTwiceClassData.starPerm` reduces to: a vertex correspondence + a perm extension
(supply) + the three field equalities.  Per the HALT, the explicit `VertexId` permutation is **not**
constructed and no field equality is proved.

Landed:

* `VertexPermExtension corr` — a `VertexId` permutation agreeing with `corr` on the vertices (supply);
* `.toClassData` — bundle the extension's permutation + the three field equalities into `ClassData`.

No facade, no flat term, no `forgetHopf`.  Constructing the permutation extension (and the field
equalities) is the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {G₁ G₂ : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-5c-2c — the permutation extension supply.**  A permutation of `VertexId` agreeing with
the vertex correspondence on the graphs' vertices (`starPerm` maps `G₂.vertices` to `G₁.vertices` via
`corr.invFun`; its inverse maps `G₁.vertices` via `corr.toFun`).  Its action off the vertex sets is
irrelevant, so it is a supply field. -/
structure VertexPermExtension (corr : ResolvedContractTwiceVertexCorrespondence G₁ G₂) where
  /-- The full-`VertexId` permutation extending the correspondence. -/
  starPerm : Equiv.Perm VertexId
  /-- On `G₂`'s vertices, `starPerm` is the inverse correspondence (`G₂ → G₁`). -/
  on_vertices : ∀ (w : VertexId) (hw : w ∈ G₂.vertices), starPerm w = (corr.invFun ⟨w, hw⟩).1
  /-- On `G₁`'s vertices, `starPerm.symm` is the forward correspondence (`G₁ → G₂`). -/
  inv_on_vertices : ∀ (v : VertexId) (hv : v ∈ G₁.vertices), starPerm.symm v = (corr.toFun ⟨v, hv⟩).1

/-- **R-6c-heart-6a-5c-2c — the class datum from a permutation extension + the field equalities.**  Bundle
the extension's permutation with the three graph-field equalities into `ResolvedContractTwiceClassData`.
-/
def VertexPermExtension.toClassData {corr : ResolvedContractTwiceVertexCorrespondence G₁ G₂}
    (E : VertexPermExtension corr)
    (hv : G₁.vertices = (G₂.mapPerm E.starPerm).vertices)
    (hi : G₁.internalEdges = (G₂.mapPerm E.starPerm).internalEdges)
    (he : G₁.externalLegs = (G₂.mapPerm E.starPerm).externalLegs) :
    ResolvedContractTwiceClassData G₁ G₂ where
  starPerm := E.starPerm
  vertices_eq := hv
  internalEdges_eq := hi
  externalLegs_eq := he

end GaugeGeometry.QFT.Combinatorial
