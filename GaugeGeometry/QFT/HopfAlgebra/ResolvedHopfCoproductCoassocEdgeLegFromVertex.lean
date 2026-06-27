import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocEdgeLegAuto

/-!
# R-6c-heart-6a-5c-3d — `EdgeLegData` from a single vertex retarget equation

The edge/leg retarget compositions (`retargetEdge_eq` / `retargetLeg_eq`, 6a-5c-3c) follow **for free**
from the **vertex** retarget composition — exactly as in the right-`eq` route (5c-2b-2a), since resolved
edges/legs are endpoint retargets.  So `ResolvedContractTwiceEdgeLegData` compresses to a single
vertex-level equation plus the edge/leg domain correspondences.

So the final star geometry is now its minimal form: per relevant graph pair —
1. the vertex correspondence / star bijection,
2. the perm extension,
3. `retargetVertex_eq` (one vertex-level equation),
4. `edge_domain_eq` (complement edges),
5. `leg_domain_eq` (external legs).

Per the HALT, `retargetVertex_eq` and the domain correspondences are **supply fields** — only the edge/leg
lift is proved.

Landed:

* `ResolvedContractTwiceEdgeLegVertexData A starA B starB σ` — `vertexDomain` + `retargetVertex_eq` + the
  edge/leg domain correspondences (the edge/leg maps are `· .retarget vertexDomain`);
* `.toEdgeLegData` — derive `ResolvedContractTwiceEdgeLegData` (the `retargetEdge`/`Leg_eq` lifts).

No facade, no flat term, no `forgetHopf`.  `retargetVertex_eq`, the domain correspondences, and the star
bijection are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {GA QB : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-5c-3d — the vertex-level edge/leg retarget data.**  The intermediate vertex map
`vertexDomain` (the two-stage inner retarget), the single vertex retarget composition `retargetVertex_eq`,
and the complement-edge / external-leg domain correspondences (stated via `· .retarget vertexDomain`). -/
structure ResolvedContractTwiceEdgeLegVertexData
    (A : ResolvedAdmissibleSubgraph GA) (starA : ResolvedFeynmanSubgraph GA → VertexId)
    (B : ResolvedAdmissibleSubgraph QB) (starB : ResolvedFeynmanSubgraph QB → VertexId)
    (σ : Equiv.Perm VertexId) where
  /-- The intermediate vertex retarget (one-stage ambient → two-stage ambient). -/
  vertexDomain : VertexId → VertexId
  /-- The vertex retarget composition: one-stage retarget = `σ ∘` two-stage retarget `∘ vertexDomain`. -/
  retargetVertex_eq : ∀ v, A.retargetVertex starA v = σ (B.retargetVertex starB (vertexDomain v))
  /-- The complement edges map onto the two-stage complement edges (under `vertexDomain`). -/
  edge_domain_eq : A.complementEdges.map (fun e => e.retarget vertexDomain) = B.complementEdges
  /-- The external legs map onto the two-stage external legs (under `vertexDomain`). -/
  leg_domain_eq : GA.externalLegs.map (fun ℓ => ℓ.retarget vertexDomain) = QB.externalLegs

variable {A : ResolvedAdmissibleSubgraph GA} {starA : ResolvedFeynmanSubgraph GA → VertexId}
  {B : ResolvedAdmissibleSubgraph QB} {starB : ResolvedFeynmanSubgraph QB → VertexId}
  {σ : Equiv.Perm VertexId}

/-- **R-6c-heart-6a-5c-3d — derive the edge/leg data.**  The edge/leg retarget compositions lift for free
from the vertex composition (resolved edges/legs are endpoint retargets). -/
def ResolvedContractTwiceEdgeLegVertexData.toEdgeLegData
    (M : ResolvedContractTwiceEdgeLegVertexData A starA B starB σ) :
    ResolvedContractTwiceEdgeLegData A starA B starB σ where
  edgeDomain := fun e => e.retarget M.vertexDomain
  edge_domain_eq := M.edge_domain_eq
  retargetEdge_eq := fun e => by
    unfold ResolvedAdmissibleSubgraph.retargetEdge
    rw [funext M.retargetVertex_eq]
    rfl
  legDomain := fun ℓ => ℓ.retarget M.vertexDomain
  leg_domain_eq := M.leg_domain_eq
  retargetLeg_eq := fun ℓ => by
    unfold ResolvedAdmissibleSubgraph.retargetExternalLeg
    rw [funext M.retargetVertex_eq]
    rfl

end GaugeGeometry.QFT.Combinatorial
