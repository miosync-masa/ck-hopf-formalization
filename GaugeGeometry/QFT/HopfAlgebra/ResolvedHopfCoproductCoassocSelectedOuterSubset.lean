import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedVertices
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCross
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientGraphAlign

/-!
# R-6c-body-8 — the selected-outer vertices lie in the input outer (PROVED)

Eighth genuine-body step, on the first Transport containment.  `selectedOuterRawOf s = leftOf ∪ promotedOf`,
and both halves live in the input outer `s.1.1`:

* a `leftOf` element is a filtered input-outer component (`leftOf_elements` is a `filter` of `s.1.1.elements`),
  so its vertices are input-outer vertices;
* a `promotedOf` element is a promoted piece of some parent `γ ∈ s.1.1.elements`
  (`promotedComponentElements_vertices_subset_parent`), so its vertices sit in `γ ⊆ s.1.1`.

Hence `selectedOuterRawOf_vertices_subset`, and — through the selected-outer alignment (leaf-20/25) —
`selectedOuter_vertices_subset` (the Transport `survivingOriginal_to` containment, leaf-17).

Per the HALT, only this one containment; the quotient-forest side and the other Transport facts are untouched.

Landed:

* `selectedOuterRawOf_vertices_subset` — `(selectedOuterRawOf s).vertices ⊆ s.1.1.vertices` (PROVED);
* `ResolvedSelectedOuterAlignment.selectedOuter_vertices_subset` — the aligned image version.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-body-8 — the selected-outer forest's vertices lie in the input outer forest.** -/
theorem selectedOuterRawOf_vertices_subset (s : ResolvedCoassocSplitChoice D G) :
    ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).vertices ⊆ s.1.1.vertices := by
  classical
  intro v hv
  rw [ResolvedAdmissibleSubgraph.mem_vertices] at hv
  obtain ⟨δ, hδ, hvδ⟩ := hv
  rw [ResolvedAdmissibleSubgraph.mem_vertices]
  simp only [ResolvedForestPromoteSupply.selectedOuterRawOf,
    ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union] at hδ
  rcases hδ with hδL | hδP
  · have hδL' : δ ∈ ((resolvedConcreteLeftSelectionSupply D G).leftOf s).elements := hδL
    rw [ResolvedSplitChoiceLeftSelectionSupply.leftOf_elements, Finset.mem_filter] at hδL'
    exact ⟨δ, hδL'.1, hvδ⟩
  · have hδP' : δ ∈ ((resolvedPromotedOfSupply D G).promotedOf s).elements := hδP
    rw [ResolvedPromotedOfSupply.promotedOf_elements] at hδP'
    obtain ⟨γ, hδγ⟩ := s.mem_promotedElements hδP'
    exact ⟨γ.1, γ.2, s.promotedComponentElements_vertices_subset_parent hδγ hvδ⟩

variable {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}

/-- **R-6c-body-8 — the aligned selected-outer vertices containment (Transport `survivingOriginal_to`). -/
theorem ResolvedSelectedOuterAlignment.selectedOuter_vertices_subset
    (Al : ResolvedSelectedOuterAlignment D G imageOf) (s : ResolvedCoassocSplitChoice D G) :
    (imageOf s).selectedOuter.1.vertices ⊆ s.1.1.vertices := by
  rw [Al.selectedOuter_eq s]
  exact selectedOuterRawOf_vertices_subset s

end GaugeGeometry.QFT.Combinatorial
