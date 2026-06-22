import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocChoiceSum

/-!
# R-6c-3a-3b (part 2) — filling the component-choice expansion vessel

Using the single global-choice sum (part 1) and splitting the global-choice carrier by the
**all-primitive** predicate, we construct the `ResolvedComponentChoiceExpansion D A` vessel
(R-6c-2d-2b) concretely.

CRITICAL granularity: `primitiveLeak` is the sum over **all** primitive-only global choices
(`2^(#components)` terms), *not* a single term — it is kept as a sum.  `choiceSum` is the sum over the
global choices with at least one nontrivial (forest) component choice.

Landed:

* `ResolvedCoproductProperForestData.componentChoiceExpansion` — a concrete
  `ResolvedComponentChoiceExpansion D A` for every carrier-forest `A`, with `primitiveLeak`/`choiceSum`
  the all-primitive / has-a-forest global-choice sums and `expansion` from part 1 +
  `Finset.sum_filter_add_sum_filter_not`.

This fully fills the branch-side vessel: `branchSummand_eq_of_componentChoiceExpansion` (R-6c-2d-3b)
now has a concrete instance.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable (D : ResolvedCoproductProperForestData)

/-- **R-6c-3a-3b (part 2) — the concrete component-choice expansion.**  Splitting the global-choice
sum (part 1) by the all-primitive predicate fills the vessel: `primitiveLeak` is the all-primitive
global-choice sum (kept as a sum, `2^(#components)` terms), `choiceSum` the has-a-forest one. -/
noncomputable def ResolvedCoproductProperForestData.componentChoiceExpansion
    {G : ResolvedFeynmanGraph} (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}) :
    ResolvedComponentChoiceExpansion D A where
  primitiveLeak :=
    ∑ p ∈ ((A.1.elements.attach).pi
            (fun γ => D.localChoiceCarrier (γ.1.toResolvedFeynmanGraph))).filter
          (fun p => ∀ γ (hγ : γ ∈ A.1.elements.attach), (p γ hγ).isLeft = true),
      (Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
        ((∏ γ ∈ (A.1.elements.attach).attach,
            D.localChoiceTerm (γ.1.1.toResolvedFeynmanGraph) (componentCD A.1 γ.1) (p γ.1 γ.2))
          ⊗ₜ[ℚ] (D.supply G).rightTerm A)
  choiceSum :=
    ∑ p ∈ ((A.1.elements.attach).pi
            (fun γ => D.localChoiceCarrier (γ.1.toResolvedFeynmanGraph))).filter
          (fun p => ¬ ∀ γ (hγ : γ ∈ A.1.elements.attach), (p γ hγ).isLeft = true),
      (Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
        ((∏ γ ∈ (A.1.elements.attach).attach,
            D.localChoiceTerm (γ.1.1.toResolvedFeynmanGraph) (componentCD A.1 γ.1) (p γ.1 γ.2))
          ⊗ₜ[ℚ] (D.supply G).rightTerm A)
  expansion := by
    rw [show (D.supply G).leftTerm A = resolvedForestLeftTerm A.1 from rfl,
      D.coassocLeftTail_resolvedForestLeftTerm_choiceSum A.1 ((D.supply G).rightTerm A)]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

end GaugeGeometry.QFT.Combinatorial
