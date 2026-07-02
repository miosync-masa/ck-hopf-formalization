import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientDisjointConcrete
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedDisjoint

/-!
# R-6c-leaf-13 — Product `hPD` from promoted-component subset-to-parent + nonemptiness

Ninth leaf-body discharge, closing the Product disjointness group.  `ResolvedProductDisjointSupply.hPD` is
`Set.PairwiseDisjoint (s.1.1.elements.attach) s.promotedComponentElements` — the per-parent promoted sets are
`Finset`-disjoint for distinct parents.  This is the different-parent case of `promotedElements_pairwiseDisjoint`
(heart-4 P4b): each promoted piece sits inside its parent (`promotedComponentElements_vertices_subset_parent`),
distinct parents are vertex-disjoint (`pairwiseDisjoint`), so the two parents' promoted sets have an
unconditional vertex-cross — and the leaf-12 engine turns that into `Finset`-disjointness given nonemptiness.

Per the HALT, the promoted-component nonemptiness is a hypothesis (same family as leaf-10/11/12); nothing is
re-proved from scratch.

Landed:

* `product_hPD_of_promoted_nonempty` — the Product `hPD` leaf from promoted-component nonemptiness.

With this, the whole Product disjointness group (`hPD` / `hLP` / `hCross` / `hDisj`) is discharged modulo the
shared nonemptiness / vertex-cross geometry.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-leaf-13 — the Product `hPD` leaf from promoted-component nonemptiness.**  Distinct parents' promoted
sets are vertex-disjoint (each piece ⊆ its parent, parents disjoint), so the leaf-12 `Finset`-disjointness
engine applies given the promoted pieces are nonempty. -/
theorem product_hPD_of_promoted_nonempty
    (hne : ∀ (s : ResolvedCoassocSplitChoice D G)
      (γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}),
      ∀ δ ∈ s.promotedComponentElements γ, δ.vertices.Nonempty)
    (s : ResolvedCoassocSplitChoice D G) :
    (↑(s.1.1.elements.attach) : Set {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}).PairwiseDisjoint
      s.promotedComponentElements := by
  intro γ₁ _ γ₂ _ hγne
  refine finset_disjoint_of_vertex_cross_nonempty ?_ (fun δ hδ => hne s γ₂ δ hδ)
  intro δ₁ hδ₁ δ₂ hδ₂
  have hγ' : γ₁.1 ≠ γ₂.1 := fun h => hγne (Subtype.ext h)
  exact Finset.disjoint_of_subset_left (s.promotedComponentElements_vertices_subset_parent hδ₁)
    (Finset.disjoint_of_subset_right (s.promotedComponentElements_vertices_subset_parent hδ₂)
      (s.1.1.pairwiseDisjoint γ₁.2 γ₂.2 hγ'))

end GaugeGeometry.QFT.Combinatorial
