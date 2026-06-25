import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocComponentPartition
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCross

/-!
# R-6c-heart-5b-2 — the quotient-side right-survivor forest

The full quotient forest is `Right ⊔ Remnant`.  This file builds the **Right** part: the components
`γ` with `choiceAt γ = Sum.inl false` (the right-primitive `1 ⊗ X γ` legs).  Such a `γ` was **not**
selected into the selected-outer forest, so after contracting `selectedOuter` it survives untouched as a
quotient component.

The genuine combinatorial content (5b-2a, proved here) is the **disjointness** of a right-primitive
component from the selected-outer forest: every right-primitive `γ` is

* not left-selected (`not_leftSelectedConcrete_of_isRightPrimitive`) hence `∉ leftOf`
  (`isRightPrimitive_not_mem_leftOf`);
* not a forest choice (`not_isForestChoice_of_isRightPrimitive`, from 5b-1), hence its promoted siblings
  sit in *other* parents and are disjoint from `γ` (`isRightPrimitive_disjoint_promotedOf`);

so `γ` is disjoint from every distinct component of `selectedOuterRaw`
(`isRightPrimitive_disjoint_selectedOuterRaw`).  This is exactly the fact that lets `γ` survive into the
quotient graph `selectedOuter.contractWithStars`.

The actual embedding of `γ` into the contract graph (5b-2b) needs the `contractWithStars` remnant
machinery, so — per the HALT — the survivor **component map** and its CD/disjoint are isolated as a
supply `ResolvedRightSurvivorSupply`, and the **forest** (5b-2c) is assembled via `ofElements` over the
supplied component images.

No facade, no flat term, no `forgetHopf`, no rep/perm.  The concrete survivor embedding and the remnant
components (5b-3) / `fullQuotientOf` (5b-4) are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-! ## 5b-2a — right-primitive components are disjoint from the selected outer -/

/-- **R-6c-heart-5b-2a — a right-primitive component is not left-selected.**  Its choice is `Sum.inl
false`, while a left-selected component's choice is `Sum.inl true`. -/
theorem ResolvedCoassocSplitChoice.not_leftSelectedConcrete_of_isRightPrimitive
    {s : ResolvedCoassocSplitChoice D G} {γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}}
    (hγ : s.isRightPrimitive γ) : ¬ s.leftSelectedConcrete γ.1 := by
  rintro ⟨hmem, hinl⟩
  have e : s.choiceAt γ = Sum.inl true := hinl
  rw [show s.choiceAt γ = Sum.inl false from hγ] at e
  simp at e

/-- **R-6c-heart-5b-2a — a right-primitive component is not in `leftOf`.** -/
theorem ResolvedCoassocSplitChoice.isRightPrimitive_not_mem_leftOf
    {s : ResolvedCoassocSplitChoice D G} {γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}}
    (hγ : s.isRightPrimitive γ) :
    γ.1 ∉ ((resolvedConcreteLeftSelectionSupply D G).leftOf s).elements := by
  rw [ResolvedSplitChoiceLeftSelectionSupply.leftOf_elements]
  intro h
  obtain ⟨_, hsel⟩ := Finset.mem_filter.mp h
  exact s.not_leftSelectedConcrete_of_isRightPrimitive hγ hsel

/-- **R-6c-heart-5b-2a — a right-primitive component is disjoint from every distinct `leftOf`
component.**  (Distinct input outer components are always disjoint.) -/
theorem ResolvedCoassocSplitChoice.isRightPrimitive_disjoint_leftOf
    {s : ResolvedCoassocSplitChoice D G} {γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}}
    {δ : ResolvedFeynmanSubgraph G}
    (hδ : δ ∈ ((resolvedConcreteLeftSelectionSupply D G).leftOf s).elements) (hne : γ.1 ≠ δ) :
    γ.1.Disjoint δ := by
  rw [ResolvedSplitChoiceLeftSelectionSupply.leftOf_elements] at hδ
  obtain ⟨hδ_mem, _⟩ := Finset.mem_filter.mp hδ
  exact s.1.1.pairwiseDisjoint γ.2 hδ_mem hne

/-- **R-6c-heart-5b-2a — a right-primitive component is disjoint from every promoted component.**  A
promoted component sits in a forest-choice parent `γP`; since `γ` is right-primitive (not a forest
choice), `γ ≠ γP`, so `γ` is disjoint from `γP` and hence from the promoted piece inside it. -/
theorem ResolvedCoassocSplitChoice.isRightPrimitive_disjoint_promotedOf
    {s : ResolvedCoassocSplitChoice D G} {γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}}
    (hγ : s.isRightPrimitive γ) {δ : ResolvedFeynmanSubgraph G}
    (hδ : δ ∈ ((resolvedPromotedOfSupply D G).promotedOf s).elements) : γ.1.Disjoint δ := by
  rw [ResolvedPromotedOfSupply.promotedOf_elements] at hδ
  obtain ⟨γP, hδ'⟩ := s.mem_promotedElements hδ
  obtain ⟨B, hchoice⟩ := s.promotedComponentElements_choiceAt_inr hδ'
  have hsubset := s.promotedComponentElements_vertices_subset_parent hδ'
  have hγ' : s.choiceAt γ = Sum.inl false := hγ
  have hγγP : γ.1 ≠ γP.1 := by
    intro h
    have hγeq : γ = γP := Subtype.ext h
    subst hγeq
    rw [hγ'] at hchoice
    simp at hchoice
  have hdisj : _root_.Disjoint γ.1.vertices γP.1.vertices :=
    s.1.1.pairwiseDisjoint γ.2 γP.2 hγγP
  exact Finset.disjoint_of_subset_right hsubset hdisj

/-- **R-6c-heart-5b-2a — a right-primitive component is disjoint from the selected outer forest.**  The
key survivor fact: `γ` is disjoint from every distinct component of `selectedOuterRaw = leftOf ∪
promotedOf`, so it survives the contraction of `selectedOuter`. -/
theorem ResolvedCoassocSplitChoice.isRightPrimitive_disjoint_selectedOuterRaw
    {s : ResolvedCoassocSplitChoice D G} {γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}}
    (hγ : s.isRightPrimitive γ) {δ : ResolvedFeynmanSubgraph G}
    (hδ : δ ∈ ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).elements)
    (hne : γ.1 ≠ δ) : γ.1.Disjoint δ := by
  simp only [ResolvedForestPromoteSupply.selectedOuterRawOf,
    ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union] at hδ
  rcases hδ with hL | hP
  · exact s.isRightPrimitive_disjoint_leftOf hL hne
  · exact s.isRightPrimitive_disjoint_promotedOf hγ hP

/-! ## 5b-2b/2c — the right-survivor forest (scaffold)

The quotient graph of a split choice is `selectedOuter.contractWithStars (D.starOf …)`.  Embedding each
right-primitive component into that quotient graph (5b-2b) needs the `contractWithStars` remnant
machinery; per the HALT it is isolated as a supply `ResolvedRightSurvivorSupply` — a survivor component
map keyed by the right components together with its CD/disjoint obligations.  The right-survivor forest
(5b-2c) is then assembled via `ofElements` over the supplied component images. -/

/-- **R-6c-heart-5b-2 — the quotient (contract) graph of a split choice.**  The selected outer forest
contracted to its stars; the right-survivors and the remnants live here as the `Right ⊔ Remnant`
quotient forest. -/
noncomputable def ResolvedCoassocSplitChoice.selectedOuterContractGraph
    (s : ResolvedCoassocSplitChoice D G) : ResolvedFeynmanGraph :=
  ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).contractWithStars
    (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s))

/-- **R-6c-heart-5b-2b — the right-survivor supply.**  Per the HALT, the embedding of each
right-primitive component into the quotient graph (`survivorComponent`) plus its connected-divergence and
the pairwise disjointness of the embedded family are isolated as supply fields — the genuine
`contractWithStars` remnant content, fed by the 5b-2a disjointness. -/
structure ResolvedRightSurvivorSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) where
  /-- The embedding of a right-primitive component into the quotient graph. -/
  survivorComponent : (s : ResolvedCoassocSplitChoice D G) →
    {γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements} // γ ∈ s.rightComponents} →
    ResolvedFeynmanSubgraph s.selectedOuterContractGraph
  /-- Each survivor component is connected-divergent. -/
  survivorCD : ∀ (s : ResolvedCoassocSplitChoice D G)
    (γ : {γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements} // γ ∈ s.rightComponents}),
    (survivorComponent s γ).forget.IsConnectedDivergent
  /-- The survivor components are pairwise disjoint in the quotient graph. -/
  survivorDisjoint : ∀ (s : ResolvedCoassocSplitChoice D G),
    ∀ ⦃δ⦄, δ ∈ s.rightComponents.attach.image (survivorComponent s) →
    ∀ ⦃δ'⦄, δ' ∈ s.rightComponents.attach.image (survivorComponent s) →
    δ ≠ δ' → δ.Disjoint δ'

/-- **R-6c-heart-5b-2c — the right-survivor forest.**  The `ofElements` admissible forest over the
survivor component images in the quotient graph — the `Right` half of the full quotient. -/
noncomputable def ResolvedRightSurvivorSupply.rightSurvivorForest
    (R : ResolvedRightSurvivorSupply D G) (s : ResolvedCoassocSplitChoice D G) :
    ResolvedAdmissibleSubgraph s.selectedOuterContractGraph :=
  ResolvedAdmissibleSubgraph.ofElements
    (s.rightComponents.attach.image (R.survivorComponent s))
    (by
      intro δ hδ
      obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp hδ
      exact R.survivorCD s γ)
    (R.survivorDisjoint s)

@[simp] theorem ResolvedRightSurvivorSupply.rightSurvivorForest_elements
    (R : ResolvedRightSurvivorSupply D G) (s : ResolvedCoassocSplitChoice D G) :
    (R.rightSurvivorForest s).elements =
      s.rightComponents.attach.image (R.survivorComponent s) := rfl

end GaugeGeometry.QFT.Combinatorial
