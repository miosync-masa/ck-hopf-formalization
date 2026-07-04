import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocDoubleAttachReindex
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedOf
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftSelectConcrete

/-!
# R-6c-body-119 — left-primitive factor COMPLETE: the first of four factor products, fully proved

Hundred-and-nineteenth genuine-body step, the FIRST full proof of a factor product: the assembly's
`left_primitive_factor` for the concrete left-selection construction,

```text
∏_{γ : ¬(p γ).isRight} localLeftFactor(p γ) = leftTerm(leftOf q)
```

is PROVED from the body-103/117/118 toolkit.  This establishes the template for the remaining three factor
products (`promoted_factor` / `right_primitive_factor` / `remnant_factor`).

## The proof (PROVED)

`left_primitive_factor_concrete`, in five moves:

1. `leftSelected_iff_choice`: on a component, `leftSelectedConcrete q γ.1.1 ↔ q.2 γ.1 γ.2 = Sum.inl true` (the
   choice at the component is `inl true`; via `choiceAt`, `Iff`);
2. RIGHT-PRIMITIVE DROP-OUT (`Finset.prod_subset`): the `leftSelectedConcrete`-filter is contained in the
   `¬isRight`-filter, and on the difference (the `inl false` right primitives) `localLeftFactor = 1`; so the
   product over `¬isRight` equals the product over `leftSelectedConcrete`;
3. `localLeftFactor(inl true) = X(component gen)` (`Finset.prod_congr`, the `inl true` evaluation);
4. `prod_double_attach_filter_reindex` (body-118): reindex the `leftSelected`-filtered double-`attach` product to
   the single `attach` of `A'.elements.filter leftSelectedConcrete`;
5. that IS `leftTerm(leftOf q) = ∏ X(component gen)` over `(leftOf).elements = A'.elements.filter
   leftSelectedConcrete` (`resolved_leftOf_elements_eq`, `resolvedForestLeftTerm`) — `exact` (all definitional,
   the CD witnesses are proof-irrelevant).

## The template for the other three

The same five moves prove all four factor products; only the selection predicate and the summand change:

* `left_primitive_factor` — `leftSelectedConcrete` (`inl true`), summand `X` — THIS body;
* `promoted_factor` — the forest-choice (`inr`) components, summand `leftTerm Bᵧ` (the sub-forest's left term);
* `right_primitive_factor` — the right-primitive (`inl false`) components, `localRightFactor`, summand `X`;
* `remnant_factor` — the forest-choice (`inr`) components, `localRightFactor`, summand `rightTerm Bᵧ`.

The right-hand ones use `localRightFactor` (the mirror evals) and the quotient-side forests; `promoted` /
`remnant` carry the sub-forest identification (heavier), but the drop-out + reindex skeleton is identical.

Per the HALT: `left_primitive_factor` is PROVED in full; the promoted / right / remnant products are NOT entered;
the small `leftSelected_iff_choice` lemma is landed; no sector forward map is constructed.

Landed:

* `leftSelected_iff_choice` — the per-component selection↔choice equivalence (PROVED);
* `left_primitive_factor_concrete` — the assembly's `left_primitive_factor` for the concrete construction
  (PROVED, full).

Toolkit body (like body-103/108/117/118), no new supply.  No facade, no flat term, no `forgetHopf`.
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
set_option linter.unusedVariables false

/-- **R-6c-body-119 — the per-component selection↔choice equivalence.**  On a component, the concrete
left-selection predicate holds iff the component's choice is `inl true`. -/
theorem leftSelected_iff_choice (q : ResolvedCoassocSplitChoice D G)
    (γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ q.1.1.elements} // x ∈ q.1.1.elements.attach}) :
    ResolvedCoassocSplitChoice.leftSelectedConcrete q γ.1.1 ↔ q.2 γ.1 γ.2 = Sum.inl true := by
  simp only [ResolvedCoassocSplitChoice.leftSelectedConcrete, ResolvedCoassocSplitChoice.choiceAt]
  exact ⟨fun ⟨_, he⟩ => he, fun he => ⟨γ.1.2, he⟩⟩

/-- **R-6c-body-119 — `left_primitive_factor` for the concrete construction** (PROVED, full).  `∏_{¬isRight}
localLeftFactor = leftTerm(leftOf)` — the first of the four factor products, the template for the rest. -/
theorem left_primitive_factor_concrete (q : ResolvedCoassocSplitChoice D G) :
    (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => ¬ (q.2 γ.1 γ.2).isRight),
        localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = resolvedForestLeftTerm ((resolvedConcreteLeftSelectionSupply D G).leftOf q) := by
  have hsub : (q.1.1.elements.attach).attach.filter
        (fun γ => ResolvedCoassocSplitChoice.leftSelectedConcrete q γ.1.1)
      ⊆ (q.1.1.elements.attach).attach.filter (fun γ => ¬ (q.2 γ.1 γ.2).isRight) := by
    intro γ hγ
    rw [Finset.mem_filter] at hγ ⊢
    refine ⟨hγ.1, ?_⟩
    rw [(leftSelected_iff_choice q γ).mp hγ.2]; simp [Sum.isRight]
  rw [← Finset.prod_subset hsub (fun γ hγ hγ' => by
    rw [Finset.mem_filter] at hγ hγ'
    have hnr : ¬ (q.2 γ.1 γ.2).isRight := hγ.2
    have hnt : q.2 γ.1 γ.2 ≠ Sum.inl true := fun he =>
      hγ' ⟨Finset.mem_attach _ _, (leftSelected_iff_choice q γ).mpr he⟩
    obtain ⟨b, hb⟩ : ∃ b, q.2 γ.1 γ.2 = Sum.inl b := by
      cases hc : q.2 γ.1 γ.2 with
      | inl b => exact ⟨b, rfl⟩
      | inr B => simp [hc, Sum.isRight] at hnr
    rw [hb] at hnt ⊢; cases b with
    | true => exact absurd rfl hnt
    | false => rfl)]
  rw [Finset.prod_congr rfl (fun γ hγ =>
    show localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2)
        = MvPolynomial.X ((γ.1.1.toResolvedFeynmanGraph).toResolvedHopfGen (componentCD q.1.1 γ.1))
      from by rw [(leftSelected_iff_choice q γ).mp (Finset.mem_filter.mp hγ).2]; rfl)]
  exact prod_double_attach_filter_reindex q.1.1.elements
    (fun γ => ResolvedCoassocSplitChoice.leftSelectedConcrete q γ)
    (fun β => MvPolynomial.X ((β.1.toResolvedFeynmanGraph).toResolvedHopfGen (componentCD q.1.1 β)))

end GaugeGeometry.QFT.Combinatorial
