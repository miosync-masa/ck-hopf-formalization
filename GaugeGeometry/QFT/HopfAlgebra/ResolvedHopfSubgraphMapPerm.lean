import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCarrier
import GaugeGeometry.QFT.Combinatorial.ResolvedSubGraph

/-!
# R-6b-2a — identity-preserving relabeling of resolved subgraphs

The first geometric piece of the `Δᵣ` well-definedness (R-6b-2): transport a resolved subgraph
along a vertex permutation `σ`, **reusing the same `edgeId`/`legId`-preserving edge/leg relabeling**
(`ResolvedFeynmanEdge.map`/`ResolvedExternalLeg.map`) as `ResolvedFeynmanGraph.mapPerm`.  A resolved
subgraph of `G` becomes a resolved subgraph of `G.mapPerm σ`.

Landed here: `ResolvedFeynmanSubgraph.mapPerm` + its field-projection simp lemmas.  The
`contractWithStars` equivariance and the admissible-forest CD/disjoint transport are later steps.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable {G : ResolvedFeynmanGraph}

/-- Transport a resolved subgraph of `G` along a vertex permutation `σ` to a resolved subgraph of
`G.mapPerm σ`, preserving the persistent edge/leg ids (same `ResolvedFeynmanEdge.map`/`.map` used by
`ResolvedFeynmanGraph.mapPerm`). -/
def ResolvedFeynmanSubgraph.mapPerm (σ : Equiv.Perm VertexId)
    (γ : ResolvedFeynmanSubgraph G) : ResolvedFeynmanSubgraph (G.mapPerm σ) where
  vertices := γ.vertices.image σ
  internalEdges := γ.internalEdges.map (ResolvedFeynmanEdge.map σ)
  externalLegs := γ.externalLegs.map (ResolvedExternalLeg.map σ)
  vertices_subset := Finset.image_subset_image γ.vertices_subset
  internalEdges_le := Multiset.map_le_map γ.internalEdges_le
  externalLegs_le := Multiset.map_le_map γ.externalLegs_le
  edges_supported := by
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := Multiset.mem_map.mp he
    obtain ⟨hs, ht⟩ := γ.edges_supported e₀ he₀
    exact ⟨Finset.mem_image_of_mem σ hs, Finset.mem_image_of_mem σ ht⟩
  legs_supported := by
    intro ℓ hℓ
    obtain ⟨ℓ₀, hℓ₀, rfl⟩ := Multiset.mem_map.mp hℓ
    exact Finset.mem_image_of_mem σ (γ.legs_supported ℓ₀ hℓ₀)

@[simp] theorem ResolvedFeynmanSubgraph.mapPerm_vertices (σ : Equiv.Perm VertexId)
    (γ : ResolvedFeynmanSubgraph G) :
    (γ.mapPerm σ).vertices = γ.vertices.image σ := rfl

@[simp] theorem ResolvedFeynmanSubgraph.mapPerm_internalEdges (σ : Equiv.Perm VertexId)
    (γ : ResolvedFeynmanSubgraph G) :
    (γ.mapPerm σ).internalEdges = γ.internalEdges.map (ResolvedFeynmanEdge.map σ) := rfl

@[simp] theorem ResolvedFeynmanSubgraph.mapPerm_externalLegs (σ : Equiv.Perm VertexId)
    (γ : ResolvedFeynmanSubgraph G) :
    (γ.mapPerm σ).externalLegs = γ.externalLegs.map (ResolvedExternalLeg.map σ) := rfl

end GaugeGeometry.QFT.Combinatorial
