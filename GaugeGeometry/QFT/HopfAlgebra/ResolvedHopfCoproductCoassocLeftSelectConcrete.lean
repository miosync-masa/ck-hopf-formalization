import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedCD

/-!
# R-6c-heart-4 P4c-pre — the concrete left-selection predicate

`leftSelected` was a supply field (R-6c-support-3); to prove the cross-disjointness of `leftOf` with the
promoted forest (P4c), it must be concrete and tied to the split choice.  A component `γ` is left-selected
exactly when its local choice is the **left-primitive** `Sum.inl true` (matching the LocalChoice term
`X γ ⊗ 1`).

The cross-disjointness then closes by a clean contradiction: a left-selected component has
`choiceAt = Sum.inl true`, while a promoted component's parent has `choiceAt = Sum.inr B`; these conflict,
so a left-selected component is never a promoted parent — and distinct outer components are disjoint.

Landed:

* `ResolvedCoassocSplitChoice.leftSelectedConcrete` — `∃ hγ, choiceAt ⟨γ, hγ⟩ = Sum.inl true`;
* `ResolvedCoassocSplitChoice.choiceAt_eq_of_mem_proof_irrel` — `choiceAt` is independent of the
  membership proof (proof irrelevance, `rfl`);
* `ResolvedCoassocSplitChoice.not_leftSelectedConcrete_of_inr` — a forest-choice component is not
  left-selected;
* `ResolvedCoassocSplitChoice.promotedComponentElements_choiceAt_inr` — a promoted parent has a forest
  choice;
* `resolvedConcreteLeftSelectionSupply` — the concrete `ResolvedSplitChoiceLeftSelectionSupply`.

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

/-- **R-6c-heart-4 P4c-pre — the concrete left-selection predicate.**  A component `γ` of the input outer
forest is left-selected when its local choice is the left primitive `Sum.inl true` (the `X γ ⊗ 1` term). -/
def ResolvedCoassocSplitChoice.leftSelectedConcrete (s : ResolvedCoassocSplitChoice D G)
    (γ : ResolvedFeynmanSubgraph G) : Prop :=
  ∃ hγ : γ ∈ s.1.1.elements, s.choiceAt ⟨γ, hγ⟩ = Sum.inl true

/-- `choiceAt` does not depend on the membership proof (proof irrelevance). -/
theorem ResolvedCoassocSplitChoice.choiceAt_eq_of_mem_proof_irrel
    (s : ResolvedCoassocSplitChoice D G) {γ : ResolvedFeynmanSubgraph G}
    (h₁ h₂ : γ ∈ s.1.1.elements) : s.choiceAt ⟨γ, h₁⟩ = s.choiceAt ⟨γ, h₂⟩ := rfl

/-- **R-6c-heart-4 P4c-pre — a forest-choice component is not left-selected.**  If `choiceAt ⟨γ, h⟩ =
Sum.inr B`, then `γ` cannot be left-selected (whose choice would be `Sum.inl true`). -/
theorem ResolvedCoassocSplitChoice.not_leftSelectedConcrete_of_inr
    (s : ResolvedCoassocSplitChoice D G) {γ : ResolvedFeynmanSubgraph G} (h : γ ∈ s.1.1.elements)
    {B : (D.supply (γ.toResolvedFeynmanGraph)).ForestIdx} (hB : s.choiceAt ⟨γ, h⟩ = Sum.inr B) :
    ¬ s.leftSelectedConcrete γ := by
  rintro ⟨hγ, hinl⟩
  rw [s.choiceAt_eq_of_mem_proof_irrel hγ h, hB] at hinl
  simp at hinl

/-- **R-6c-heart-4 P4c-pre — a promoted parent has a forest choice.**  If a component `γ` contributes to
`promotedElements` (its per-component promoted set is nonempty), its local choice is `Sum.inr B`. -/
theorem ResolvedCoassocSplitChoice.promotedComponentElements_choiceAt_inr
    (s : ResolvedCoassocSplitChoice D G)
    {γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}} {δ : ResolvedFeynmanSubgraph G}
    (hδ : δ ∈ s.promotedComponentElements γ) : ∃ B, s.choiceAt γ = Sum.inr B := by
  rcases hc : s.choiceAt γ with b | B
  · rw [s.promotedComponentElements_inl hc] at hδ
    simp at hδ
  · exact ⟨B, rfl⟩

/-- **R-6c-heart-4 P4c-pre — the concrete left-selection supply.**  `leftSelected := leftSelectedConcrete`
— so `leftOf s = s.1.1.filterElements (leftSelectedConcrete s)` is the genuine left-selected sub-forest. -/
def resolvedConcreteLeftSelectionSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) : ResolvedSplitChoiceLeftSelectionSupply D G where
  leftSelected := fun s => s.leftSelectedConcrete

end GaugeGeometry.QFT.Combinatorial
