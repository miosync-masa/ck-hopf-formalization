import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCross
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestCoreIndex
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCarrierProperProvider
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocIsNonemptyTransfer
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftPrimitiveFactor

/-!
# R-6c-body-244 — selected-outer nonemptiness on the filtered domain (PROVED)

Two-hundred-and-forty-fourth genuine-body step — the filtered-domain `X.IsNonempty` local theorem that body-242's
audit isolated.  On the consumer's actual index domain `forestChoiceCarrier A` (which excludes the all-right split
`p_R`), the selected outer `selectedOuterRawOf ⟨A, p⟩` is nonempty — proved using **only** the `p ≠ p_R` fact from the
`forestChoiceCarrier` filter, never `EmptyPivot`, body-151, `promote_collapse`, or the total `selectedOuter_mem`.

## The route

`p ≠ p_R` (from `Finset.mem_filter` on `forestChoiceCarrier`) yields a component `γ` with tag `≠ Sum.inl false`, i.e.
`Sum.inl true` (→ `γ` is left-selected, so `leftOf` is nonempty) or `Sum.inr B` (→ the promoted piece of the carrier
member `B` is nonempty).  Either way `selectedOuterRawOf = (leftOf).union (promotedOf)` is nonempty by body-240's
`union_isNonempty_left` / `union_isNonempty_right`.

* the `inr B` branch needs `B.1.elements.Nonempty`: `B` is a carrier member for free
  (`(D.supply H).ForestIdx = {A // A ∈ D.carrier H}`), so `P.carrier_isProperForest` + `isNonempty_of_isProperForest`
  supply it; `promote_elements` (an image) then gives the promoted piece nonempty — **no `promote_collapse` needed**.

Per the HALT: only `X.IsNonempty` on the filtered domain is proved (via `ResolvedCarrierProperProvider`, needed for the
`inr` branch); no other conjunct, no certificate, no re-typing of `selectedOuterOf` (that is body-245).  No facade, no
flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-244 — a non-all-right choice has a non-`inl false` component.**  If `p ≠ p_R` (`fun _ _ => Sum.inl
false`), some component's tag is not `Sum.inl false`. -/
theorem exists_nonright_of_ne_pR
    {A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}}
    {p : ∀ γ ∈ A.1.elements.attach, Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx}
    (hR : p ≠ (fun _ _ => Sum.inl false)) :
    ∃ (γ : {x : ResolvedFeynmanSubgraph G // x ∈ A.1.elements}) (hγ : γ ∈ A.1.elements.attach),
      p γ hγ ≠ Sum.inl false := by
  by_contra h
  push_neg at h
  exact hR (funext fun γ => funext fun hγ => h γ hγ)

/-- **R-6c-body-244 — an `inr`-tagged component makes the promoted set nonempty.**  The tagged `B` is a carrier
member, so `carrier_isProperForest` gives `B.1.elements.Nonempty`, whose promoted image lands in `promotedElements`. -/
theorem promotedElements_nonempty_of_inr (P : ResolvedCarrierProperProvider D)
    (s : ResolvedCoassocSplitChoice D G)
    {γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}}
    {B : (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx}
    (hB : ResolvedCoassocSplitChoice.choiceAt s γ = Sum.inr B) :
    s.promotedElements.Nonempty := by
  obtain ⟨x, hx⟩ := (P.carrier_isProperForest _ B.1 B.2).1
  refine ⟨γ.1.promote x, ?_⟩
  show γ.1.promote x ∈ s.1.1.elements.attach.biUnion s.promotedComponentElements
  refine Finset.mem_biUnion.mpr ⟨γ, Finset.mem_attach _ _, ?_⟩
  rw [ResolvedCoassocSplitChoice.promotedComponentElements_inr s hB,
    ResolvedAdmissibleSubgraph.promote_elements]
  simp only [Finset.mem_image]
  exact ⟨x, hx, rfl⟩

/-- **R-6c-body-244 — the selected outer is nonempty on the filtered domain.**  For `p ∈ forestChoiceCarrier A`
(hence `p ≠ p_R`), `selectedOuterRawOf ⟨A, p⟩` is nonempty.  Uses only the `p ≠ p_R` filter fact. -/
theorem selectedOuterRaw_isNonempty_of_mem_forestChoiceCarrier (P : ResolvedCarrierProperProvider D)
    {A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}}
    {p : ∀ γ ∈ A.1.elements.attach, Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx}
    (hp : p ∈ forestChoiceCarrier A) :
    ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf ⟨A, p⟩).IsNonempty := by
  rw [forestChoiceCarrier, Finset.mem_filter] at hp
  obtain ⟨γ, hγ, hne⟩ := exists_nonright_of_ne_pR hp.2.1
  simp only [ResolvedForestPromoteSupply.selectedOuterRawOf]
  rcases hpt : p γ hγ with b | B
  · cases b
    · exact absurd hpt hne
    · refine ResolvedAdmissibleSubgraph.union_isNonempty_left _ ⟨γ.1, ?_⟩
      show γ.1 ∈ ((resolvedConcreteLeftSelectionSupply D G).leftOf ⟨A, p⟩).elements
      rw [resolved_leftOf_elements_eq]
      exact Finset.mem_filter.mpr ⟨γ.2, γ.2, hpt⟩
  · refine ResolvedAdmissibleSubgraph.union_isNonempty_right _ ?_
    have hBc : ResolvedCoassocSplitChoice.choiceAt (⟨A, p⟩ : ResolvedCoassocSplitChoice D G) γ
        = Sum.inr B := hpt
    show (ResolvedCoassocSplitChoice.promotedElements (⟨A, p⟩ : ResolvedCoassocSplitChoice D G)).Nonempty
    exact promotedElements_nonempty_of_inr P ⟨A, p⟩ hBc

end GaugeGeometry.QFT.Combinatorial
