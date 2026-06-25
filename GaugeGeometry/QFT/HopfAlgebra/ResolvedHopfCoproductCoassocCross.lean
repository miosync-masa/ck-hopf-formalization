import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedDisjoint
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftSelectConcrete

/-!
# R-6c-heart-4 P4c — cross-disjointness of `leftOf` and `promotedOf`

The last admissibility obligation for `selectedOuterRaw = leftOf ∪ promotedOf`: the left-selected
components and the promoted components are disjoint.  With the concrete `leftSelected` (P4c-pre) and the
vertices-subset support (P4a), this mirrors the P4b cross-parent case plus a same-parent contradiction:

* a left-selected component `δL` lies in the input outer forest and has `choiceAt = Sum.inl true`;
* a promoted component `δP` has a parent `γP` with `choiceAt = Sum.inr B`, and `δP.vertices ⊆ γP.vertices`;
* if `δL = γP.1` the two choices clash (`not_leftSelectedConcrete_of_inr`); otherwise `δL ≠ γP.1` are
  distinct outer components, disjoint by `s.1.1.pairwiseDisjoint`, and `δP ⊆ γP` gives `δL ⊥ δP`.

So `selectedOuterRaw` is a fully concrete admissible forest (`resolvedConcreteForestPromoteSupply`),
leaving only the carrier membership `selectedOuter_mem` (P5).

Landed:

* `cross_disjoint_leftOf_promotedOf` — the cross-disjointness;
* `resolvedConcreteForestPromoteSupply` — the concrete `ResolvedForestPromoteSupply` (concrete `leftOf`
  + concrete `promotedOf` + cross), whose `selectedOuterRawOf` is the concrete selected outer forest.

No facade, no flat term, no `forgetHopf`, no rep/perm.  The carrier membership (P5) is the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-4 P4c — cross-disjointness of `leftOf` and `promotedOf`.**  A left-selected component is
disjoint from every promoted component: same parent ⇒ the `inl true`/`inr B` choices clash; different
parents ⇒ disjoint outer components + the promoted piece sits in its parent. -/
theorem cross_disjoint_leftOf_promotedOf :
    ∀ s : ResolvedCoassocSplitChoice D G,
      ∀ δL ∈ ((resolvedConcreteLeftSelectionSupply D G).leftOf s).elements,
      ∀ δP ∈ ((resolvedPromotedOfSupply D G).promotedOf s).elements,
      δL ≠ δP → δL.Disjoint δP := by
  intro s δL hδL δP hδP _
  classical
  obtain ⟨hδL_parent, hleft⟩ :=
    Finset.mem_filter.mp (by rwa [ResolvedSplitChoiceLeftSelectionSupply.leftOf_elements] at hδL)
  rw [ResolvedPromotedOfSupply.promotedOf_elements] at hδP
  obtain ⟨γP, hδP'⟩ := s.mem_promotedElements hδP
  obtain ⟨B, hchoice⟩ := s.promotedComponentElements_choiceAt_inr hδP'
  have hsubset := s.promotedComponentElements_vertices_subset_parent hδP'
  by_cases hγ : δL = γP.1
  · subst hγ
    exact absurd hleft (s.not_leftSelectedConcrete_of_inr γP.2 hchoice)
  · have hdisj : _root_.Disjoint δL.vertices γP.1.vertices :=
      s.1.1.pairwiseDisjoint hδL_parent γP.2 hγ
    exact Finset.disjoint_of_subset_right hsubset hdisj

/-- **R-6c-heart-4 P4c — the concrete selected-outer forest-promote supply.**  Concrete `leftOf`
(P4c-pre) + concrete `promotedOf` (P1–P4b) + the cross-disjointness, so `selectedOuterRawOf` is a fully
concrete admissible forest. -/
noncomputable def resolvedConcreteForestPromoteSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) : ResolvedForestPromoteSupply D G :=
  (resolvedPromotedOfSupply D G).toForestPromoteSupply (resolvedConcreteLeftSelectionSupply D G)
    cross_disjoint_leftOf_promotedOf

end GaugeGeometry.QFT.Combinatorial
