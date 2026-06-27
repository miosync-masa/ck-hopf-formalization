import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocVertexPermExtend

/-!
# R-6c-heart-6a-5c-3a — `ClassData` from the vertex correspondence + field equalities

The last piece of the contract-twice geometry: bundle the **principled** star permutation (the vertex
correspondence 6a-5c-2b + its `VertexId` extension 6a-5c-2c) with the three graph-field equalities into
`ResolvedContractTwiceClassData` — hence `right_eq` and `remnantGen` (6a-5b).

So the entire contract-twice geometry now flows in one line:

  `VertexCorrespondence` (star bijection + surviving transport + freshness)
    `→ VertexPermExtension` (the `VertexId` permutation, supply)
    `→ ResolvedContractTwiceFieldEqSupply` (the three field equalities)
    `→ ResolvedContractTwiceClassData`
    `→ right_eq / remnantGen`.

Per the HALT, no field equality is proved here.  The three field equalities are the obligations; when
discharged via the retarget route they reduce further (`externalLegs_eq` is **free**, `internalEdges_eq`
follows from the **complement-edge domain** `internalEdges_domain`, both 5c-2b-2b; `vertices_eq` from the
vertex partition + `on_vertices`), but those discharges are not forced into this generic bundling.

Landed:

* `ResolvedContractTwiceFieldEqSupply E` — the three field equalities over a perm extension `E`;
* `.toClassData` — into `ResolvedContractTwiceClassData`.

No facade, no flat term, no `forgetHopf`.  The field equalities, the star bijection, and the perm
extension are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {G₁ G₂ : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-5c-3a — the field-equality supply over a perm extension.**  The three graph-field
equalities `G₁.<field> = (G₂.mapPerm E.starPerm).<field>` — the obligations whose discharge is the last
star geometry (`externalLegs` free, `internalEdges` via the complement domain, `vertices` via the
partition). -/
structure ResolvedContractTwiceFieldEqSupply
    {corr : ResolvedContractTwiceVertexCorrespondence G₁ G₂} (E : VertexPermExtension corr) where
  /-- One-stage vertices = relabeled two-stage vertices. -/
  vertices_eq : G₁.vertices = (G₂.mapPerm E.starPerm).vertices
  /-- One-stage internal edges = relabeled two-stage internal edges. -/
  internalEdges_eq : G₁.internalEdges = (G₂.mapPerm E.starPerm).internalEdges
  /-- One-stage external legs = relabeled two-stage external legs. -/
  externalLegs_eq : G₁.externalLegs = (G₂.mapPerm E.starPerm).externalLegs

/-- **R-6c-heart-6a-5c-3a — into `ClassData`.**  The principled permutation (`E.starPerm`) with the three
field equalities. -/
def ResolvedContractTwiceFieldEqSupply.toClassData
    {corr : ResolvedContractTwiceVertexCorrespondence G₁ G₂} {E : VertexPermExtension corr}
    (F : ResolvedContractTwiceFieldEqSupply E) : ResolvedContractTwiceClassData G₁ G₂ :=
  E.toClassData F.vertices_eq F.internalEdges_eq F.externalLegs_eq

/-- **R-6c-heart-6a-5c-3a — the class equality from the full vertex-correspondence chain.** -/
theorem ResolvedContractTwiceFieldEqSupply.classEq
    {corr : ResolvedContractTwiceVertexCorrespondence G₁ G₂} {E : VertexPermExtension corr}
    (F : ResolvedContractTwiceFieldEqSupply E) : G₁.toResolvedClass = G₂.toResolvedClass :=
  F.toClassData.classEq

end GaugeGeometry.QFT.Combinatorial
