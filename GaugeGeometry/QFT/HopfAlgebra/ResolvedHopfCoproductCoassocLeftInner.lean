import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightInner

/-!
# R-6c-2d-2a — `Δᵣ` over the forest-product left factor (algebra-hom product lemma)

The left inner expansion starts here.  Unlike the right factor (a single quotient generator, R-6c-2d-3),
the **left** factor of a forest summand is a *product* of component generators
`leftTerm A = ∏ γ ∈ A.elements, X (componentGen γ)`.  Since `Δᵣ` is an algebra hom, it carries this
product to the product of the component coproducts (`map_prod`):

  `Δᵣ (leftTerm A) = ∏ γ ∈ A.elements, Δᵣ (X (componentGen γ)) = ∏ γ, gen (componentGen γ)`.

This pure algebra-hom step is isolated here.  Each factor `gen (componentGen γ) = primitive γ +
forestSum γ` is a *sum*, so the full product-of-sums expansion (the component-choice sum — primitive
vs nontrivial subforest per component) is the next, heavier step (2d-2b), kept separate.

Landed:

* `ResolvedCoproductProperForestData.coproduct_resolvedForestLeftTerm` —
  `Δᵣ (leftTerm A) = ∏ γ ∈ A.elements.attach, gen (componentGen γ)`.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable (D : ResolvedCoproductProperForestData)

/-- **R-6c-2d-2a — `Δᵣ` over the forest-product left factor.**  Since `Δᵣ` is an algebra hom and
`leftTerm A` is the product of the component generators, `Δᵣ (leftTerm A)` is the product of the
component coproducts (`map_prod` + `coproduct_X`).  Each factor `gen (componentGen γ)` is itself
`primitive + forestSum`; expanding that product-of-sums is the next step (2d-2b). -/
theorem ResolvedCoproductProperForestData.coproduct_resolvedForestLeftTerm
    {G : ResolvedFeynmanGraph} (A : ResolvedAdmissibleSubgraph G) :
    D.coproduct (resolvedForestLeftTerm A)
      = ∏ γ ∈ A.elements.attach,
          D.toGenSupply.gen (resolvedComponentGen γ.1 (A.isConnectedDivergent γ.1 γ.2)) := by
  simp only [resolvedForestLeftTerm]
  rw [map_prod]
  simp only [ResolvedCoproductProperForestData.coproduct, ResolvedCoproductGenSupply.coproduct_X]

end GaugeGeometry.QFT.Combinatorial
