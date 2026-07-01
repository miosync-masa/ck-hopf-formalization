import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocProductDisjointLeaves
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCross

/-!
# R-6c-leaf-10 — Product `hLP` PROVED from `leftOf`/`promotedOf` classification + element nonemptiness

Seventh leaf-body discharge.  `ResolvedProductDisjointSupply.hLP` — the `Finset`-disjointness of the
left-selected components and the promoted sub-forests — is proved from the same classification behind
`cross_disjoint_leftOf_promotedOf` (heart-4), plus one genuine nonemptiness fact.

A shared element `δ ∈ leftOf.elements ∩ promotedOf.elements` is BOTH a left-selected component (`choiceAt δ =
inl true`) and a promoted sub-forest of some parent `γP` (`choiceAt γP = inr B`, `δ.vertices ⊆ γP.vertices`):

* if `δ = γP` — the `inl true` / `inr B` choices clash (`not_leftSelectedConcrete_of_inr`);
* if `δ ≠ γP` — `δ` and `γP` are distinct components, so `pairwiseDisjoint` gives `δ.vertices` disjoint from
  `γP.vertices`; but `δ.vertices ⊆ γP.vertices`, so `δ.vertices = ∅` — contradicting `δ.vertices.Nonempty`.

The nonemptiness of components (`hne`) is a genuine supplied fact (mirroring the survivor's
`rightComponentNonempty`; there is no `IsConnectedDivergent → vertices.Nonempty` lemma in this development).

Per the HALT, `hne` is a hypothesis (not proved); `hPD` / `hDisj` are untouched.

Landed:

* `product_hLP_of_elements_nonempty` — the Product `hLP` leaf from component nonemptiness.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-leaf-10 — the Product `hLP` leaf from element nonemptiness.**  Left-selected components and
promoted sub-forests share no element: a shared `δ` is either its own parent (choice clash) or a strict
sub-forest of a disjoint parent (empty, contradicting nonemptiness). -/
theorem product_hLP_of_elements_nonempty
    (hne : ∀ (s : ResolvedCoassocSplitChoice D G), ∀ δ ∈ s.1.1.elements, δ.vertices.Nonempty)
    (s : ResolvedCoassocSplitChoice D G) :
    Disjoint ((resolvedConcreteLeftSelectionSupply D G).leftOf s).elements
      ((resolvedPromotedOfSupply D G).promotedOf s).elements := by
  classical
  rw [Finset.disjoint_left]
  intro δ hδL hδP
  obtain ⟨hδL_parent, hleft⟩ :=
    Finset.mem_filter.mp (by rwa [ResolvedSplitChoiceLeftSelectionSupply.leftOf_elements] at hδL)
  rw [ResolvedPromotedOfSupply.promotedOf_elements] at hδP
  obtain ⟨γP, hδP'⟩ := s.mem_promotedElements hδP
  obtain ⟨B, hchoice⟩ := s.promotedComponentElements_choiceAt_inr hδP'
  have hsubset := s.promotedComponentElements_vertices_subset_parent hδP'
  by_cases hγ : δ = γP.1
  · subst hγ
    exact absurd hleft (s.not_leftSelectedConcrete_of_inr γP.2 hchoice)
  · have hdisj : _root_.Disjoint δ.vertices γP.1.vertices :=
      s.1.1.pairwiseDisjoint hδL_parent γP.2 hγ
    obtain ⟨v, hv⟩ := hne s δ hδL_parent
    exact (Finset.disjoint_left.mp hdisj hv) (hsubset hv)

end GaugeGeometry.QFT.Combinatorial
