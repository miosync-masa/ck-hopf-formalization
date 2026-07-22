import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSaturationAlgebra
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSaturatedCarrier
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaFmemReduction

/-!
# R-6c-body-534 (Step 2) — `W″` selected-outer saturation closure + `W″` Fmem (PROVED)

Five-hundred-and-thirty-fourth genuine-body step (Step 2) — the first major construction (selectedOuter) passes the
fourth axis.  Using body-534 Step 1's saturation algebra, the selected outer of a `W″` split choice is forest-saturated
(RAW `s`, no filtered membership), so the `W″` selected-outer carrier membership — hence `Fmem` — is CANONICAL DERIVED.

* `selectedOuterRawOf_forestExternalLegSaturated` — `selectedOuterRawOf s = leftOf s ∪ promotedOf s`; `leftOf` reuses the
  input outer's `W″`-membership saturation directly, `promotedOf` feeds parent + chosen-inner saturation through the
  nested-promote closure, and `union` closes it.  RAW `s`.
* `canonicalLegSaturatedSelectedOuterFilteredMemSupply` (+ `_of_measure`) — the body-496 mirror on `W″`: the four ambient
  conditions from the input-outer `W″` membership, properness from `selectedOuterRaw_isProperForest`, and the SIXTH
  condition (saturation) from the theorem above.  `W″` `Fmem` is GONE (a theorem of membership).

Per the HALT/guards: the saturation theorem reads NEITHER a target selectedOuter membership NOR `hp`; the `W″` `LegModel`
is NOT applied to the target; recovered union / corrected quotient are NOT entered; `Parent`-CD is NOT touched; multiset
multiplicity is preserved throughout; strict `StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc claim.  No
facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! ## Step 2a — selectedOuter saturation (RAW `s`) -/

/-- **R-6c-body-534 ∎ — the `W″` selected outer is forest-saturated.**  RAW `s`; no filtered membership. -/
theorem selectedOuterRawOf_forestExternalLegSaturated {G : ResolvedFeynmanGraph}
    (s : ResolvedCoassocSplitChoice canonicalLegSaturatedCarrierProperSupply.toData G) :
    ResolvedForestExternalLegSaturated
      ((resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf s) := by
  have hOuter : ResolvedForestExternalLegSaturated s.1.1 := canonicalLegSaturatedCarrier_saturated s.1.2
  rw [ResolvedForestPromoteSupply.selectedOuterRawOf]
  apply resolvedForestExternalLegSaturated_union
  · intro δ hδ
    have hδ2 : δ ∈ ((resolvedConcreteLeftSelectionSupply canonicalLegSaturatedCarrierProperSupply.toData G).leftOf
        s).elements := hδ
    rw [resolved_leftOf_elements_eq] at hδ2
    exact hOuter δ (Finset.mem_of_mem_filter δ hδ2)
  · intro δ hδ
    have hδ' : δ ∈ ResolvedCoassocSplitChoice.promotedElements s := hδ
    obtain ⟨γ, hγP⟩ := ResolvedCoassocSplitChoice.mem_promotedElements hδ'
    rcases hc : ResolvedCoassocSplitChoice.choiceAt s γ with b | B
    · rw [ResolvedCoassocSplitChoice.promotedComponentElements_inl s hc] at hγP
      exact absurd hγP (by simp)
    · rw [ResolvedCoassocSplitChoice.promotedComponentElements_inr s hc] at hγP
      simp only [ResolvedAdmissibleSubgraph.promote_elements, Finset.mem_image] at hγP
      obtain ⟨b, hb, rfl⟩ := hγP
      exact resolvedExternalLegSaturated_promote_of_nested γ.1 (hOuter γ.1 γ.2)
        ((canonicalLegSaturatedCarrier_saturated B.2) b hb)

/-! ## Step 2b — the `W″` Fmem inhabitant (CANONICAL DERIVED) -/

/-- **R-6c-body-534 ∎ — the `W″` selected-outer filtered-membership supply** (body-496 mirror).  The four ambient
conditions from the input-outer `W″` membership, properness from `selectedOuterRaw_isProperForest`, saturation from
Step 2a.  `W″` `Fmem` is a theorem of membership. -/
noncomputable def canonicalLegSaturatedSelectedOuterFilteredMemSupply
    (N : ∀ G : ResolvedFeynmanGraph, ResolvedConnectedDivergentNonemptySupply G)
    (E : ∀ G : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply G) :
    ResolvedSelectedOuterFilteredMemSupply canonicalLegSaturatedCarrierProperSupply.toData where
  selectedOuter_mem := fun {G} A p hp => by
    obtain ⟨hAS, hCD, hEdge, hLeg, -, -⟩ := (mem_canonicalLegSaturatedCarrier_full_iff A.1).mp A.2
    refine (mem_canonicalLegSaturatedCarrier_full_iff _).mpr ⟨hAS, hCD, hEdge, hLeg, ?_, ?_⟩
    · have hq : (⟨A, p⟩ : ForestBlockDomType canonicalLegSaturatedCarrierProperSupply.toData G)
          ∈ forestBlockDomFinset G := by
        simp only [forestBlockDomFinset, Finset.mem_sigma]
        exact ⟨Finset.mem_attach _ _, hp⟩
      exact selectedOuterRaw_isProperForest (N G) (E G)
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider ⟨⟨A, p⟩, hq⟩
    · exact selectedOuterRawOf_forestExternalLegSaturated ⟨A, p⟩

/-- **R-6c-body-534 ∎ — the same, from a measure leaf supply.** -/
noncomputable def canonicalLegSaturatedSelectedOuterFilteredMemSupply_of_measure
    (Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData)
    (E : ∀ G : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply G) :
    ResolvedSelectedOuterFilteredMemSupply canonicalLegSaturatedCarrierProperSupply.toData :=
  canonicalLegSaturatedSelectedOuterFilteredMemSupply
    (fun G => Measure.toConnectedDivergentNonemptySupply G) E

end GaugeGeometry.QFT.Combinatorial
