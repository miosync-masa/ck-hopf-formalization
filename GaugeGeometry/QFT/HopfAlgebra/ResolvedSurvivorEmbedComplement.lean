import GaugeGeometry.QFT.HopfAlgebra.ResolvedSurvivorEmbedSupport

/-!
# R-6c-heart-6a-3b — survivor `hcompl` from vertex disjointness (the edge complement)

The last survivor support obligation `hcompl : γ.internalEdges ≤ A.complementEdges` turns out to be
**free from `hdisj`**: a `γ` disjoint from `A` (as vertex sets) is automatically edge-disjoint from `A`
(an edge in both would have its source in both vertex sets), so subtracting `A`'s edges removes none of
`γ`'s — `γ.internalEdges - A.internalEdges = γ.internalEdges` — and the existing
`sub_internalEdges_le_complementEdges` finishes.

So `survivorReembedOfDisjoint` is the concrete survivor component depending on **`hdisj` alone**; the only
remaining survivor datum is the vertex disjointness (i.e., for actual right survivors, nonemptiness).

Landed:

* `ResolvedAdmissibleSubgraph.source_mem_vertices_of_mem_internalEdges` — an edge of `A` has its source
  in `A`'s vertices;
* `internalEdges_le_complementEdges_of_disjoint` — `hcompl` from `hdisj` (edge-disjointness + the
  existing complement bound);
* `survivorReembedOfDisjoint` (+ `_gen`) — the concrete survivor, depending on `hdisj` only.

No facade, no flat term, no `forgetHopf`, no rep/perm.  Discharging `hdisj` (nonemptiness) for the actual
right survivors and the remnant embedding are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-3b — an edge of an admissible subgraph has its source in its vertices.** -/
theorem ResolvedAdmissibleSubgraph.source_mem_vertices_of_mem_internalEdges
    (A : ResolvedAdmissibleSubgraph G) {e : ResolvedFeynmanEdge} (he : e ∈ A.internalEdges) :
    e.source ∈ A.vertices := by
  simp only [ResolvedAdmissibleSubgraph.internalEdges, Multiset.mem_sum] at he
  obtain ⟨δ, hδ, heδ⟩ := he
  exact ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨δ, hδ, (δ.edges_supported e heδ).1⟩

/-- **R-6c-heart-6a-3b — the survivor edge complement bound from vertex disjointness.**  A `γ` disjoint
from `A` is edge-disjoint, so its edges survive the complement subtraction. -/
theorem internalEdges_le_complementEdges_of_disjoint (A : ResolvedAdmissibleSubgraph G)
    (γ : ResolvedFeynmanSubgraph G) (hdisj : Disjoint γ.vertices A.vertices) :
    γ.internalEdges ≤ A.complementEdges := by
  have hdisj_edges : ∀ e, e ∈ γ.internalEdges → e ∈ A.internalEdges → False :=
    fun e heγ heA => Finset.disjoint_left.mp hdisj (γ.edges_supported e heγ).1
      (A.source_mem_vertices_of_mem_internalEdges heA)
  have hsub_eq : γ.internalEdges - A.internalEdges = γ.internalEdges := by
    refine Multiset.ext.mpr (fun e => ?_)
    rw [Multiset.count_sub]
    rcases eq_or_ne (Multiset.count e γ.internalEdges) 0 with h0 | h0
    · omega
    · have hA : Multiset.count e A.internalEdges = 0 := by
        by_contra hA
        exact hdisj_edges e (Multiset.count_pos.mp (Nat.pos_of_ne_zero h0))
          (Multiset.count_pos.mp (Nat.pos_of_ne_zero hA))
      omega
  rw [← hsub_eq]
  exact A.sub_internalEdges_le_complementEdges γ

/-- **R-6c-heart-6a-3b — the concrete survivor re-embedding from disjointness alone.**  `survivorReembed`
with the edge complement bound derived from `hdisj`. -/
noncomputable def survivorReembedOfDisjoint (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) (γ : ResolvedFeynmanSubgraph G)
    (hdisj : Disjoint γ.vertices A.vertices) :
    ResolvedFeynmanSubgraph (A.contractWithStars starOf) :=
  survivorReembed A starOf γ hdisj (internalEdges_le_complementEdges_of_disjoint A γ hdisj)

/-- **R-6c-heart-6a-3b — the survivor (from disjointness) has `γ`'s own generator.** -/
theorem resolvedComponentGen_survivorReembedOfDisjoint (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) (γ : ResolvedFeynmanSubgraph G)
    (hdisj : Disjoint γ.vertices A.vertices)
    (hCD : (survivorReembedOfDisjoint A starOf γ hdisj).forget.IsConnectedDivergent)
    (hCD' : γ.forget.IsConnectedDivergent) :
    resolvedComponentGen (survivorReembedOfDisjoint A starOf γ hdisj) hCD
      = resolvedComponentGen γ hCD' := rfl

end GaugeGeometry.QFT.Combinatorial
