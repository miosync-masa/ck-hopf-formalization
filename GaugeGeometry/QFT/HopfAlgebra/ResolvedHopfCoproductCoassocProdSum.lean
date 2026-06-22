import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocBranchInner

/-!
# R-6c-3a-1 — the resolved product-of-sums core (`Finset.prod_sum`)

The branch inner expansion needs `Δᵣ(leftTerm A) = ∏ γ gen(componentGen γ)` (R-6c-2d-2a) expanded as a
sum over **component choices**.  Mathlib's `Finset.prod_sum` is exactly the dependent product-of-sums:

  `∏ a ∈ s, ∑ b ∈ t a, f a b = ∑ p ∈ s.pi t, ∏ x ∈ s.attach, f x.1 (p x.1 x.2)`.

This file applies it to the resolved forest-product, given a **per-component sum decomposition** of each
`gen(componentGen γ)` (the genuine remaining input — primitive ⊔ the component's own proper forests).
The combinatorial core (the product-of-sums itself) is thereby isolated from that decomposition and
from the σ-cover.

Landed:

* `ResolvedCoproductProperForestData.coproduct_resolvedForestLeftTerm_prodSum` — given per-component
  sum decompositions `gen(componentGen γ) = ∑ b ∈ t γ, f γ b`, the forest-product coproduct is the sum
  over global component choices `∑ p ∈ (A.elements.attach).pi t, ∏ γ, f γ (p γ)` (by R-6c-2d-2a +
  `Finset.prod_sum`).

No facade, no flat term, no `forgetHopf`; the per-component decomposition and σ-cover are deferred.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable (D : ResolvedCoproductProperForestData)

/-- **R-6c-3a-1 — the resolved product-of-sums core.**  If each component coproduct
`gen(componentGen γ)` is given as a finite sum `∑ b ∈ t γ, f γ b` (the per-component decomposition into
primitive/forest choices), then `Δᵣ(leftTerm A)` is the sum over **global component choices**
(functions `p` assigning a choice to each component) of the product of the chosen terms — Mathlib's
`Finset.prod_sum` applied to the forest-product coproduct (R-6c-2d-2a). -/
theorem ResolvedCoproductProperForestData.coproduct_resolvedForestLeftTerm_prodSum
    {G : ResolvedFeynmanGraph} (A : ResolvedAdmissibleSubgraph G)
    {κ : {x : ResolvedFeynmanSubgraph G // x ∈ A.elements} → Type}
    (t : (γ : {x : ResolvedFeynmanSubgraph G // x ∈ A.elements}) → Finset (κ γ))
    (f : (γ : {x : ResolvedFeynmanSubgraph G // x ∈ A.elements}) → κ γ →
      ResolvedHopfH ⊗[ℚ] ResolvedHopfH)
    (hdecomp : ∀ γ ∈ A.elements.attach,
      D.toGenSupply.gen (resolvedComponentGen γ.1 (A.isConnectedDivergent γ.1 γ.2))
        = ∑ b ∈ t γ, f γ b) :
    D.coproduct (resolvedForestLeftTerm A)
      = ∑ p ∈ (A.elements.attach).pi t,
          ∏ γ ∈ (A.elements.attach).attach, f γ.1 (p γ.1 γ.2) := by
  rw [D.coproduct_resolvedForestLeftTerm, Finset.prod_congr rfl hdecomp, Finset.prod_sum]

end GaugeGeometry.QFT.Combinatorial
