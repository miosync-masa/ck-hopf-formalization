import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftFactor
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocComponentPartition
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterMem

/-!
# R-6c-heart-5c-1c — `leftFactorProduct` partition split

`leftFactorProduct s = ∏ γ, localChoiceLeftFactor γ (choiceAt γ)` (over the input outer components).
Splitting it over the component partition (`leftComponents ∪ rightComponents ∪ forestComponents`, 5b-1)
and simplifying each region is the route to `leftFactorProduct s = resolvedForestLeftTerm (leftOf s) *
resolvedForestLeftTerm (promotedOf s)` (= `resolvedSelectedOuterTerm`).

This file delivers the split and the easy regions:

* `leftFactorOf` — the per-component left factor (over the single `attach`, via `choiceAt`);
* `leftFactorProduct_eq` — `leftFactorProduct s = ∏ γ ∈ s.1.1.elements.attach, leftFactorOf s γ`;
* `leftFactorProduct_split` — splits the product over the three partition regions;
* `leftFactorProduct_right_eq_one` — the right-primitive region contributes `1`;
* `leftFactorProduct_left_eq` — the left-primitive region is `resolvedForestLeftTerm (leftOf s)`;
* `leftFactorProduct_eq_leftOf_mul_forestPart` — the minimal win
  `leftFactorProduct s = resolvedForestLeftTerm (leftOf s) * (∏ γ ∈ forestComponents, leftFactorOf s γ)`.

No facade, no flat term, no `forgetHopf`, no rep/perm.  The forest region (`= resolvedForestLeftTerm
promotedOf` via the promote-gen equality) and the right factor equality are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-5c-1c — the per-component left factor.**  The local-choice left factor at a component
`γ` of the input outer forest, indexed over the single `attach` via `choiceAt`. -/
noncomputable def ResolvedCoproductProperForestData.leftFactorOf (D : ResolvedCoproductProperForestData)
    {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}) : ResolvedHopfH :=
  D.localChoiceLeftFactor (γ.1.toResolvedFeynmanGraph) (componentCD s.1.1 γ) (s.choiceAt γ)

/-- **R-6c-heart-5c-1c — `leftFactorProduct` over the single `attach`.**  The double-`attach` product
collapses to the product of `leftFactorOf` over `s.1.1.elements.attach` (proof-irrelevant membership). -/
theorem ResolvedCoproductProperForestData.leftFactorProduct_eq (D : ResolvedCoproductProperForestData)
    {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G) :
    D.leftFactorProduct s = ∏ γ ∈ s.1.1.elements.attach, D.leftFactorOf s γ := by
  unfold ResolvedCoproductProperForestData.leftFactorProduct
  rw [← Finset.prod_attach (s.1.1.elements.attach) (D.leftFactorOf s)]
  rfl

/-- **R-6c-heart-5c-1c — the partition split of `leftFactorProduct`.**  Over the three partition regions
`leftComponents` / `rightComponents` / `forestComponents`. -/
theorem ResolvedCoproductProperForestData.leftFactorProduct_split
    (D : ResolvedCoproductProperForestData) {G : ResolvedFeynmanGraph}
    (s : ResolvedCoassocSplitChoice D G) :
    D.leftFactorProduct s
      = (∏ γ ∈ s.leftComponents, D.leftFactorOf s γ)
        * (∏ γ ∈ s.rightComponents, D.leftFactorOf s γ)
        * (∏ γ ∈ s.forestComponents, D.leftFactorOf s γ) := by
  rw [D.leftFactorProduct_eq, ← s.components_union,
    Finset.prod_union (Finset.disjoint_union_left.mpr
      ⟨s.leftComponents_disjoint_forestComponents, s.rightComponents_disjoint_forestComponents⟩),
    Finset.prod_union s.leftComponents_disjoint_rightComponents]

/-- **R-6c-heart-5c-1c — the right-primitive region contributes `1`.**  A right-primitive component has
`choiceAt = Sum.inl false`, whose left factor is `1`. -/
theorem ResolvedCoproductProperForestData.leftFactorProduct_right_eq_one
    (D : ResolvedCoproductProperForestData) {G : ResolvedFeynmanGraph}
    (s : ResolvedCoassocSplitChoice D G) :
    (∏ γ ∈ s.rightComponents, D.leftFactorOf s γ) = 1 := by
  classical
  apply Finset.prod_eq_one
  intro γ hγ
  have hr : s.choiceAt γ = Sum.inl false := (Finset.mem_filter.mp hγ).2
  unfold ResolvedCoproductProperForestData.leftFactorOf
  rw [hr]
  rfl

/-- **R-6c-heart-5c-1c — left-primitive ↔ left-selected.**  A component is left-primitive (its choice is
`Sum.inl true`) iff it is left-selected (the concrete `leftOf` predicate). -/
theorem ResolvedCoassocSplitChoice.isLeftPrimitive_iff_leftSelectedConcrete
    (s : ResolvedCoassocSplitChoice D G) (γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}) :
    s.isLeftPrimitive γ ↔ s.leftSelectedConcrete γ.1 := by
  constructor
  · intro h; exact ⟨γ.2, h⟩
  · rintro ⟨h, hh⟩
    show s.choiceAt γ = Sum.inl true
    exact (s.choiceAt_eq_of_mem_proof_irrel γ.2 h).trans hh

/-- **R-6c-heart-5c-1c — the left factor of a left-primitive component is its generator term.** -/
theorem leftFactorOf_eq_genTerm_of_isLeftPrimitive
    {s : ResolvedCoassocSplitChoice D G} {γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}}
    (h : s.isLeftPrimitive γ) : D.leftFactorOf s γ = resolvedComponentGenTerm γ.1 := by
  have hc : s.choiceAt γ = Sum.inl true := h
  have hcd : γ.1.forget.IsConnectedDivergent := s.1.1.isConnectedDivergent γ.1 γ.2
  unfold ResolvedCoproductProperForestData.leftFactorOf
    ResolvedCoproductProperForestData.localChoiceLeftFactor resolvedComponentGenTerm
  rw [hc, dif_pos hcd]
  rfl

/-- **R-6c-heart-5c-1c — the left-primitive region is the left-selected forest term.**  `∏ over
leftComponents leftFactor = resolvedForestLeftTerm (leftOf s)` — via the bijection `γ ↦ γ.1` between
`leftComponents` and `leftOf.elements`. -/
theorem ResolvedCoproductProperForestData.leftFactorProduct_left_eq
    (D : ResolvedCoproductProperForestData) {G : ResolvedFeynmanGraph}
    (s : ResolvedCoassocSplitChoice D G) :
    (∏ γ ∈ s.leftComponents, D.leftFactorOf s γ)
      = resolvedForestLeftTerm ((resolvedConcreteLeftSelectionSupply D G).leftOf s) := by
  classical
  rw [resolvedForestLeftTerm_eq_prod]
  refine Finset.prod_bij (fun γ _ => γ.1) ?_ ?_ ?_ ?_
  · intro γ hγ
    rw [ResolvedSplitChoiceLeftSelectionSupply.leftOf_elements, Finset.mem_filter]
    have hlp : s.isLeftPrimitive γ := (Finset.mem_filter.mp hγ).2
    exact ⟨γ.2, (s.isLeftPrimitive_iff_leftSelectedConcrete γ).mp hlp⟩
  · intro γ₁ _ γ₂ _ h
    exact Subtype.ext h
  · intro δ hδ
    rw [ResolvedSplitChoiceLeftSelectionSupply.leftOf_elements, Finset.mem_filter] at hδ
    obtain ⟨hδmem, hδsel⟩ := hδ
    refine ⟨⟨δ, hδmem⟩, ?_, rfl⟩
    rw [ResolvedCoassocSplitChoice.leftComponents, Finset.mem_filter]
    exact ⟨Finset.mem_attach _ _, (s.isLeftPrimitive_iff_leftSelectedConcrete ⟨δ, hδmem⟩).mpr hδsel⟩
  · intro γ hγ
    have hlp : s.isLeftPrimitive γ := (Finset.mem_filter.mp hγ).2
    exact leftFactorOf_eq_genTerm_of_isLeftPrimitive hlp

/-- **R-6c-heart-5c-1c — the minimal win.**  `leftFactorProduct s = resolvedForestLeftTerm (leftOf s) *
(forest region)` — the right region drops out (`= 1`), the left region is the left-selected forest term,
and only the forest region (`= resolvedForestLeftTerm (promotedOf s)`, the promote-gen step) remains. -/
theorem ResolvedCoproductProperForestData.leftFactorProduct_eq_leftOf_mul_forestPart
    (D : ResolvedCoproductProperForestData) {G : ResolvedFeynmanGraph}
    (s : ResolvedCoassocSplitChoice D G) :
    D.leftFactorProduct s
      = resolvedForestLeftTerm ((resolvedConcreteLeftSelectionSupply D G).leftOf s)
        * (∏ γ ∈ s.forestComponents, D.leftFactorOf s γ) := by
  rw [D.leftFactorProduct_split, D.leftFactorProduct_right_eq_one, mul_one,
    D.leftFactorProduct_left_eq]

end GaugeGeometry.QFT.Combinatorial
