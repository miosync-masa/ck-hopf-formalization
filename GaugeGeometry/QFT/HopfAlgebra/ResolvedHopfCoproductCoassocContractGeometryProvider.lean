import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocVertexGeometry
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteSummandBundle

/-!
# R-6c-body-140 — contract-geometry provider: the contract-twice leaf bundled into one record

Hundred-and-fortieth genuine-body step, a base-side bank before the last geometry (`witnessSplit`).  The
contract-twice geometry `ResolvedContractTwiceOnceGeometrySupply` — the `quot_eq` provider consumed by body-111 /
129 / 130 / 131 — is bundled into one clean per-`D` provider over the summand bundle's forward map, built from the
existing bodies-27–49 vertex/edge/retarget layer.

## The contract-twice geometry (recap)

`ResolvedContractTwiceOnceGeometrySupply D G imageOf` is `starPerm` + the three graph-field equalities
`branchRightGraph s = (imageInnerRightGraph imageOf s).mapPerm (starPerm s)` (vertices / internalEdges /
externalLegs) — the genuine de-contraction star geometry (contract-twice = contract-once up to a star relabel);
`.contract_class_eq` then gives `right_eq` / `quot_eq` by `toResolvedClass`-`mapPerm`-invariance.

## The existing layered builder (bodies 27–49)

The geometry supply is already assembled by the layered record
`ResolvedContractTwiceVertexGeometrySupply` (`VertexGeometry.lean`):

* `starPerm` + `externalLegs_eq` ← the retarget layer (`ResolvedContractTwiceRetargetSupply`);
* `internalEdges_eq` ← the edge/leg layer (`ResolvedContractTwiceEdgeLegSupply`, `internalEdges_domain`);
* `vertices_eq` ← the vertex layer (the star-vertex correspondence, the three-route
  `retarget_corr_on_vertices` content of bodies 27–32);

and `.toGeometrySupply` collects the three equalities into `ResolvedContractTwiceOnceGeometrySupply`.

## The provider (bundle)

`ResolvedContractGeometryProvider D S` fields, per graph `G`, one
`ResolvedContractTwiceVertexGeometrySupply` for the summand bundle's forward image `imageOf q =
⟨selectedOuterOf q, (quotientForest q).1⟩`; `.toContract` streams `.toGeometrySupply` into the exact
`∀ G, ResolvedContractTwiceOnceGeometrySupply …` family that body-130's `ResolvedForestBlockBijectionSideSupply.contract`
(and body-131's provider) consumes.  So the contract-twice leaf is one record whose subleaves are the known
vertex / edge / retarget layers — the three-route star correspondence remains the genuine geometry inside
`vertices_eq`, not re-derived here.

Per the HALT: no retarget / star-allocation body is entered; the provider bundles the existing vertex-geometry
layer per `G` and produces the bijection assembly's `contract` family; the imageOf is kept abstract via the
summand bundle's forward map.

Landed:

* `ResolvedContractGeometryProvider D S` — the per-`G` vertex-geometry bundle over the summand forward map;
* `.toContract` — the `∀ G, ResolvedContractTwiceOnceGeometrySupply …` family for body-130/131.

Toolkit body (like body-137), one base provider.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **R-6c-body-140 — the contract-geometry provider.**  Per graph `G`, one vertex-geometry supply (bodies
27–49) for the summand bundle's forward image `⟨selectedOuterOf q, (quotientForest q).1⟩` — the bundled
contract-twice `quot_eq` provider. -/
structure ResolvedContractGeometryProvider (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) where
  /-- The per-`G` contract-twice vertex geometry (retarget + edge/leg + vertex layers). -/
  vertexGeometry : ∀ (G : ResolvedFeynmanGraph),
    ResolvedContractTwiceVertexGeometrySupply D G
      (fun q => ⟨(S.Forward.imageSupply G).selectedOuterOf q, (S.quotientForest q).1⟩)

/-- **R-6c-body-140 — the contract-twice geometry family for the bijection assembly.**  Streams each per-`G`
vertex geometry's `.toGeometrySupply` into the `∀ G, ResolvedContractTwiceOnceGeometrySupply …` family consumed by
body-130's `contract` field. -/
noncomputable def ResolvedContractGeometryProvider.toContract
    {S : ResolvedConcreteSummandBundleSupply D} (P : ResolvedContractGeometryProvider D S)
    (G : ResolvedFeynmanGraph) :
    ResolvedContractTwiceOnceGeometrySupply D G
      (fun q => ⟨(S.Forward.imageSupply G).selectedOuterOf q, (S.quotientForest q).1⟩) :=
  (P.vertexGeometry G).toGeometrySupply

end GaugeGeometry.QFT.Combinatorial
