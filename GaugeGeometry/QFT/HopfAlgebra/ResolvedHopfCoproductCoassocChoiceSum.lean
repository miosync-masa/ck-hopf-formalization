import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocGlobalChoice

/-!
# R-6c-3a-3b (part 1) — the inner left tail as a single global-choice sum

Combining `coassocLeftTail_tmul` (3a-3a) with `coproduct_resolvedForestLeftTerm_localChoiceSum`
(3a-3a) and pushing the associator through the sum: the inner left tail of a forest summand is a
**single sum over global component choices**, each contributing the associator applied to
`(∏ component choice terms) ⊗ rightTerm`.

Landed:

* `ResolvedCoproductProperForestData.coassocLeftTail_resolvedForestLeftTerm_choiceSum` —
  `coassocLeftTail D (resolvedForestLeftTerm A ⊗ r) = ∑ p ∈ choices, assoc((∏ γ, localChoiceTerm (p γ))
  ⊗ r)`.

This is the keystone for the all-primitive/nontrivial filter split filling the
`ResolvedComponentChoiceExpansion` vessel (next part).  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable (D : ResolvedCoproductProperForestData)

/-- **R-6c-3a-3b (part 1) — the inner left tail as a single global-choice sum.**  The associator is
pushed through the product-of-sums: `coassocLeftTail D (resolvedForestLeftTerm A ⊗ r)` is the sum over
global component choices `p` of `assoc((∏ γ, localChoiceTerm (p γ)) ⊗ r)`. -/
theorem ResolvedCoproductProperForestData.coassocLeftTail_resolvedForestLeftTerm_choiceSum
    {G : ResolvedFeynmanGraph} (A : ResolvedAdmissibleSubgraph G) (r : ResolvedHopfH) :
    D.coassocLeftTail (resolvedForestLeftTerm A ⊗ₜ[ℚ] r)
      = ∑ p ∈ (A.elements.attach).pi
            (fun γ => D.localChoiceCarrier (γ.1.toResolvedFeynmanGraph)),
          (Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
            ((∏ γ ∈ (A.elements.attach).attach,
                D.localChoiceTerm (γ.1.1.toResolvedFeynmanGraph) (componentCD A γ.1) (p γ.1 γ.2))
              ⊗ₜ[ℚ] r) := by
  rw [D.coassocLeftTail_tmul, D.coproduct_resolvedForestLeftTerm_localChoiceSum A,
    TensorProduct.sum_tmul, map_sum]

end GaugeGeometry.QFT.Combinatorial
