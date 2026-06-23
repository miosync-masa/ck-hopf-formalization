import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedVertices

/-!
# R-6c-heart-4 P4b — `promotedDisjoint` (the promoted components are pairwise disjoint)

The disjointness half of the promoted-forest admissibility.  Two distinct promoted components `δ₁ ≠ δ₂`:

* **same parent** `γ`: both lie in one `ResolvedAdmissibleSubgraph.promote γ.1 B.1`, whose own
  `pairwiseDisjoint` field gives `δ₁.Disjoint δ₂` (no `mem_image` — just the field);
* **different parents** `γ₁ ≠ γ₂`: `δᵢ.vertices ⊆ γᵢ.1.vertices` (P4a), and the input outer forest's
  components are pairwise disjoint (`s.1.1.pairwiseDisjoint`), so the pieces are vertex-disjoint by
  subset monotonicity.

With CD (P3) and this, the promoted-forest supply is **fully concrete** (`resolvedPromotedOfSupply`),
leaving only the cross-disjointness with `leftOf` (P4c) and the carrier membership (P5).

Landed:

* `ResolvedCoassocSplitChoice.promotedComponentElements_pairwiseDisjoint` — same-parent pieces are
  pairwise disjoint;
* `ResolvedCoassocSplitChoice.promotedElements_pairwiseDisjoint` — all promoted components are pairwise
  disjoint (same/different parent case split);
* `resolvedPromotedOfSupply` — the promoted-forest supply with BOTH fields proved (CD + disjoint).

No facade, no flat term, no `forgetHopf`, no rep/perm.  The cross-disjointness (P4c) and carrier
membership (P5) are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-4 P4b — same-parent pieces are pairwise disjoint.**  On a forest choice both pieces lie
in `ResolvedAdmissibleSubgraph.promote γ.1 B.1`, so its own `pairwiseDisjoint` applies. -/
theorem ResolvedCoassocSplitChoice.promotedComponentElements_pairwiseDisjoint
    (s : ResolvedCoassocSplitChoice D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}) :
    ∀ ⦃δ₁⦄, δ₁ ∈ s.promotedComponentElements γ → ∀ ⦃δ₂⦄, δ₂ ∈ s.promotedComponentElements γ →
      δ₁ ≠ δ₂ → δ₁.Disjoint δ₂ := by
  rcases hc : s.choiceAt γ with b | B
  · intro δ₁ hδ₁
    rw [s.promotedComponentElements_inl hc] at hδ₁
    simp at hδ₁
  · intro δ₁ hδ₁ δ₂ hδ₂ hne
    rw [s.promotedComponentElements_inr hc] at hδ₁ hδ₂
    exact (ResolvedAdmissibleSubgraph.promote γ.1 B.1).pairwiseDisjoint hδ₁ hδ₂ hne

/-- **R-6c-heart-4 P4b — the promoted components are pairwise disjoint.**  Same-parent pieces by the
per-component lemma; different-parent pieces by the vertices-subset support (P4a) and the input outer
forest's pairwise-disjointness. -/
theorem ResolvedCoassocSplitChoice.promotedElements_pairwiseDisjoint
    (s : ResolvedCoassocSplitChoice D G) :
    ∀ ⦃δ₁⦄, δ₁ ∈ s.promotedElements → ∀ ⦃δ₂⦄, δ₂ ∈ s.promotedElements → δ₁ ≠ δ₂ → δ₁.Disjoint δ₂ := by
  intro δ₁ hδ₁ δ₂ hδ₂ hne
  obtain ⟨γ₁, hδ₁'⟩ := s.mem_promotedElements hδ₁
  obtain ⟨γ₂, hδ₂'⟩ := s.mem_promotedElements hδ₂
  by_cases hγ : γ₁ = γ₂
  · subst hγ
    exact s.promotedComponentElements_pairwiseDisjoint γ₁ hδ₁' hδ₂' hne
  · have hsub₁ := s.promotedComponentElements_vertices_subset_parent hδ₁'
    have hsub₂ := s.promotedComponentElements_vertices_subset_parent hδ₂'
    have hγne : γ₁.1 ≠ γ₂.1 := fun h => hγ (Subtype.ext h)
    have hdisj : _root_.Disjoint γ₁.1.vertices γ₂.1.vertices :=
      s.1.1.pairwiseDisjoint γ₁.2 γ₂.2 hγne
    exact Finset.disjoint_of_subset_left hsub₁ (Finset.disjoint_of_subset_right hsub₂ hdisj)

/-- **R-6c-heart-4 P4b — the fully-concrete promoted-forest supply.**  Both admissibility fields are now
proved (CD by P3, disjointness by P4b), so the promoted forest of every split choice is built with no
remaining supply obligation. -/
def resolvedPromotedOfSupply (D : ResolvedCoproductProperForestData) (G : ResolvedFeynmanGraph) :
    ResolvedPromotedOfSupply D G where
  promotedCD := fun s => s.promotedElements_CD
  promotedDisjoint := fun s => s.promotedElements_pairwiseDisjoint

end GaugeGeometry.QFT.Combinatorial
