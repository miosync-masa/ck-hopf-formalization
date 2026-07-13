import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocComplementEdgesMono
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredOuterNonempty
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftPrimitiveFactor

/-!
# R-6c-body-263 — complement-edge positivity for the two constructed forests (PROVED)

Two-hundred-and-sixty-third genuine-body step — the final `IsProperForest` conjunct `0 < A.complementEdges.card`
discharged for both constructed forests via body-262's global monotonicity, with **no deep leaf** (body-261 verdict).
Both reduce to the domain outer's carrier properness: a constructed forest with `internalEdges ≤` the carrier forest
has a `≥` complement, which stays positive.

## X — `selectedOuterRawOf`

`selectedOuterRaw_component_internalEdges_le`: every component of `selectedOuterRawOf s` has `internalEdges ≤
s.1.1.internalEdges` — left components are `∈ s.1.1.elements` (`internalEdges_le_of_mem`); promoted pieces
`γ.promote δ` have `internalEdges = δ.internalEdges ≤ γ.internalEdges ≤ s.1.1.internalEdges`.  Aggregated by
`internalEdges_le_of_components_le`, then `complementEdges_card_pos_of_internalEdges_le` with the carrier forest's
properness.  Works for **any** `s : ResolvedCoassocSplitChoice D G` (only `carrier_isProperForest` on `s.1.1` is used —
no filtered domain, no `p_L`).

## Y — the recovered outer on the forward image

`(unionOuter (fwdMap S q)).1.elements = q.1.1.elements` (body-241 route: `union_eq` ∘ `recovered_region_partition`) →
`internalEdges` equal → complement positivity transfers from `q.1.1`'s properness.  Membership-independent.

Per the HALT: only complement positivity for X (any `s`) and Y (forward image) is proved — no `promote_collapse`, no
per-tag missing-edge witness, no certificate assembly (next).  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]
  [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-263 — every selected-outer component's edges are ≤ the domain outer's.**  Left components lie in
`s.1.1.elements`; promoted pieces `γ.promote δ` have edges `= δ.internalEdges ≤ γ.internalEdges ≤ s.1.1.internalEdges`. -/
theorem selectedOuterRaw_component_internalEdges_le (s : ResolvedCoassocSplitChoice D G)
    {η : ResolvedFeynmanSubgraph G}
    (hη : η ∈ ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).elements) :
    η.internalEdges ≤ s.1.1.internalEdges := by
  simp only [ResolvedForestPromoteSupply.selectedOuterRawOf, ResolvedAdmissibleSubgraph.union_elements,
    Finset.mem_union] at hη
  rcases hη with hL | hP
  · have hsub : ((resolvedConcreteForestPromoteSupply D G).leftOf s).elements ⊆ s.1.1.elements := by
      show ((resolvedConcreteLeftSelectionSupply D G).leftOf s).elements ⊆ s.1.1.elements
      rw [resolved_leftOf_elements_eq]; exact Finset.filter_subset _ _
    exact ResolvedAdmissibleSubgraph.internalEdges_le_of_mem s.1.1 (hsub hL)
  · have hPe : η ∈ s.promotedElements := hP
    obtain ⟨γ, hγP⟩ := ResolvedCoassocSplitChoice.mem_promotedElements hPe
    rcases hc : ResolvedCoassocSplitChoice.choiceAt s γ with b | B
    · rw [ResolvedCoassocSplitChoice.promotedComponentElements, hc] at hγP
      simp at hγP
    · rw [ResolvedCoassocSplitChoice.promotedComponentElements_inr s hc,
        ResolvedAdmissibleSubgraph.promote_elements] at hγP
      simp only [Finset.mem_image] at hγP
      obtain ⟨δ₀, _, rfl⟩ := hγP
      have h1 : (γ.1.promote δ₀).internalEdges = δ₀.internalEdges := rfl
      have h2 : δ₀.internalEdges ≤ γ.1.internalEdges := δ₀.internalEdges_le
      rw [h1]
      exact h2.trans (ResolvedAdmissibleSubgraph.internalEdges_le_of_mem s.1.1 γ.2)

/-- **R-6c-body-263 — the selected outer has positive complement.**  Its internal edges are `≤ s.1.1.internalEdges`
(component-wise), and `s.1.1` is a proper carrier forest, so its complement is positive. -/
theorem selectedOuterRaw_complementEdges_card_pos (P : ResolvedCarrierProperProvider D)
    (s : ResolvedCoassocSplitChoice D G) :
    0 < ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).complementEdges.card :=
  ResolvedAdmissibleSubgraph.complementEdges_card_pos_of_internalEdges_le
    (ResolvedAdmissibleSubgraph.internalEdges_le_of_components_le _
      (fun η hη => selectedOuterRaw_component_internalEdges_le s hη))
    (ResolvedAdmissibleSubgraph.complementEdges_card_pos_of_isProperForest
      (P.carrier_isProperForest G s.1.1 s.1.2))

/-- **R-6c-body-263 — the recovered outer has positive complement on the forward image.**  Its elements equal
`q.1.1.elements` (body-241 partition transfer), so its internal edges and complement equal `q.1.1`'s, which is proper.
Membership-independent. -/
theorem recoveredOuter_complementEdges_card_pos (P : ResolvedCarrierProperProvider D)
    {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}
    (A : ResolvedRecoveredRegionMembershipAssemblySupply D S Region) (q : ForestBlockDomType D G) :
    0 < (Region.Union.unionOuter (fwdMap S q)).1.complementEdges.card := by
  have hunion : (Region.Union.unionOuter (fwdMap S q)).1.elements = q.1.1.elements := by
    rw [Region.Union.union_eq (fwdMap S q),
      A.toRecoveredOuterRegionPartitionSupply.recovered_region_partition q]
  have hIE : (Region.Union.unionOuter (fwdMap S q)).1.internalEdges = q.1.1.internalEdges := by
    simp only [ResolvedAdmissibleSubgraph.internalEdges, hunion]
  exact ResolvedAdmissibleSubgraph.complementEdges_card_pos_of_internalEdges_le hIE.le
    (ResolvedAdmissibleSubgraph.complementEdges_card_pos_of_isProperForest
      (P.carrier_isProperForest G q.1.1 q.1.2))

end GaugeGeometry.QFT.Combinatorial
