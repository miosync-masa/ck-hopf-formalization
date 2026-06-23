import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedCD

/-!
# R-6c-heart-4 P4a — promoted components are contained in their parent

The support lemma for the disjointness (P4): a promoted component's vertices are contained in its parent
input-outer component `γ`.  This is structural — `promote` keeps the vertex set, and the source `δ`
lives in the component graph `γ.toResolvedFeynmanGraph` (whose vertices are `γ.vertices`).  With it, the
*cross-parent* disjointness of promoted components follows from the input outer forest's
pairwise-disjointness (distinct parents are disjoint, and their promoted pieces sit inside them).

The two underlying promote lemmas (`ResolvedFeynmanSubgraph.promote_vertices_subset_parent` and
`ResolvedAdmissibleSubgraph.promote_element_vertices_subset_parent`) live in `ResolvedSubgraphPromote`
(same file as `promote`, so the `mem_image` shares the `Classical` instance and avoids the cross-file
`DecidableEq` diamond).  This file lifts them to the split-choice level.

Landed:

* `ResolvedCoassocSplitChoice.promotedComponentElements_vertices_subset_parent` — a per-component
  promoted piece sits in its parent.

No facade, no flat term, no `forgetHopf`, no rep/perm.  The full `promotedDisjoint`/`cross` (P4) and
carrier membership (P5) are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {G : ResolvedFeynmanGraph} {D : ResolvedCoproductProperForestData}

/-- **R-6c-heart-4 P4a — a per-component promoted piece sits in its parent.**  On a forest choice the
piece is a component of `ResolvedAdmissibleSubgraph.promote γ.1 B.1`, hence `⊆ γ.1.vertices`. -/
theorem ResolvedCoassocSplitChoice.promotedComponentElements_vertices_subset_parent
    (s : ResolvedCoassocSplitChoice D G)
    {γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}} {δ : ResolvedFeynmanSubgraph G}
    (hδ : δ ∈ s.promotedComponentElements γ) : δ.vertices ⊆ γ.1.vertices := by
  rcases hc : s.choiceAt γ with b | B
  · rw [s.promotedComponentElements_inl hc] at hδ
    simp at hδ
  · rw [s.promotedComponentElements_inr hc] at hδ
    exact ResolvedAdmissibleSubgraph.promote_element_vertices_subset_parent γ.1 B.1 hδ

end GaugeGeometry.QFT.Combinatorial
