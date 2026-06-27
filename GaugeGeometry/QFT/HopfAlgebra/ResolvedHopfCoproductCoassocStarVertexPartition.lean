import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocStarPerm

/-!
# R-6c-heart-6a-5c-2a — the contract-graph vertex partition (surviving ⊔ star)

Before defining the star permutation's `toFun`/`invFun`, name the vertex partition of a star-contracted
graph.  Since `(A.contractWithStars starOf).vertices = (G.vertices \ A.vertices) ∪ A.starVertices starOf`,
each vertex is either a **surviving** original vertex (`v ∈ G.vertices`, `v ∉ A.vertices`) or a **star**
vertex (`v ∈ A.starVertices starOf`).  This holds **generically** for any `A.contractWithStars`, so it
instantiates to both the one-stage graph (`A = s.1.1`) and the two-stage graph (`A = quotientForest`) —
no duplication.

Then the bijection is a clean case split: surviving `↦` itself, star `↦` the corresponding two-stage
star.

Per the HALT, `toFun`/`invFun` are **not** defined, no star-to-star correspondence is proved, and
`vertices_eq` is not touched — this only names the partition.

Landed:

* `isContractSurvivingVertex` / `isContractStarVertex` — the two vertex classes;
* `contractWithStars_vertex_cases` — exhaustiveness (every contract-graph vertex is surviving or star);
* `contract_surviving_not_star` — disjointness (under star freshness, a surviving vertex is not a star).

No facade, no flat term, no `forgetHopf`.  Constructing the bijection (and the star-to-star map) is the
remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-5c-2a — a surviving vertex of a star-contraction.**  An original vertex outside the
contracted forest `A` (it survives the contraction unchanged). -/
def isContractSurvivingVertex (A : ResolvedAdmissibleSubgraph G) (v : VertexId) : Prop :=
  v ∈ G.vertices ∧ v ∉ A.vertices

/-- **R-6c-heart-6a-5c-2a — a star vertex of a star-contraction.**  The star of one of `A`'s components. -/
def isContractStarVertex (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) (v : VertexId) : Prop :=
  v ∈ A.starVertices starOf

/-- **R-6c-heart-6a-5c-2a — exhaustiveness.**  Every vertex of `A.contractWithStars starOf` is surviving
or a star. -/
theorem contractWithStars_vertex_cases (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) {v : VertexId}
    (hv : v ∈ (A.contractWithStars starOf).vertices) :
    isContractSurvivingVertex A v ∨ isContractStarVertex A starOf v := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hv
  rcases hv with h | h
  · exact Or.inl (Finset.mem_sdiff.mp h)
  · exact Or.inr h

/-- **R-6c-heart-6a-5c-2a — disjointness.**  Under star freshness (each star lies outside `G`), a
surviving vertex (in `G`) is not a star vertex. -/
theorem contract_surviving_not_star (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (hfresh : ∀ η ∈ A.elements, starOf η ∉ G.vertices) {v : VertexId}
    (hsurv : isContractSurvivingVertex A v) (hstar : isContractStarVertex A starOf v) : False := by
  obtain ⟨η, hη, rfl⟩ := ResolvedAdmissibleSubgraph.mem_starVertices.mp hstar
  exact hfresh η hη hsurv.1

end GaugeGeometry.QFT.Combinatorial
