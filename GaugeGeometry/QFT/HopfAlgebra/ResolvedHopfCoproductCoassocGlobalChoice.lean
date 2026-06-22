import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLocalChoice

/-!
# R-6c-3a-3a — the global component-choice sum (keystones)

Assembling the branch inner expansion: feed the per-component decomposition (R-6c-3a-2) into the
product-of-sums core (R-6c-3a-1) to expand `Δᵣ(leftTerm A)` as a sum over **global component choices**
(functions assigning a local primitive/forest choice to each component), then push it through the left
tail.

This file lands the keystones:

* `componentCD` — the connected-divergence of a component-as-graph (the proof carried inside
  `resolvedComponentGen`, named so the local choice data can be stated);
* `coassocLeftTail_tmul` — the left tail on a pure tensor `coassocLeftTail D (a ⊗ b) = assoc(Δᵣ a ⊗ b)`
  (mirror of `coassocRightTail_tmul`);
* `coproduct_resolvedForestLeftTerm_localChoiceSum` — `Δᵣ(leftTerm A)` as the global component-choice
  sum, by `coproduct_resolvedForestLeftTerm_prodSum` fed the local decomposition (`gen_eq_localChoiceSum`).

The associator-combination into `coassocLeftTail` and the all-primitive/nontrivial filter split (which
fills the `ResolvedComponentChoiceExpansion` vessel) are the next step.  No facade, no flat term, no
`forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable (D : ResolvedCoproductProperForestData)

/-- The connected-divergence of a component-as-graph (mirrors the proof inside
`resolvedComponentGen`), named so the local choice carrier/term can be stated for a component. -/
theorem componentCD {G : ResolvedFeynmanGraph} (A : ResolvedAdmissibleSubgraph G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ A.elements}) :
    (γ.1.toResolvedFeynmanGraph).forget.toClass.IsConnectedDivergent := by
  rw [← ResolvedFeynmanSubgraph.forget_toFeynmanGraph γ.1]
  exact (FeynmanGraphClass.isConnectedDivergent_toClass _).mpr
    (γ.1.forget.toFeynmanGraph_isConnectedDivergent (A.isConnectedDivergent γ.1 γ.2))

/-- The left tail on a pure tensor: `coassocLeftTail D (a ⊗ b) = assoc(Δᵣ a ⊗ b)`. -/
theorem ResolvedCoproductProperForestData.coassocLeftTail_tmul (a b : ResolvedHopfH) :
    D.coassocLeftTail (a ⊗ₜ[ℚ] b)
      = (Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
          (D.coproduct a ⊗ₜ[ℚ] b) := by
  simp only [ResolvedCoproductProperForestData.coassocLeftTail, AlgHom.comp_apply,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

/-- **R-6c-3a-3a — `Δᵣ(leftTerm A)` as the global component-choice sum.**  The product-of-sums core
(R-6c-3a-1) fed the per-component decomposition (R-6c-3a-2): the forest-product coproduct is the sum
over global choices `p` (a local primitive/forest choice per component) of the product of the chosen
local terms. -/
theorem ResolvedCoproductProperForestData.coproduct_resolvedForestLeftTerm_localChoiceSum
    {G : ResolvedFeynmanGraph} (A : ResolvedAdmissibleSubgraph G) :
    D.coproduct (resolvedForestLeftTerm A)
      = ∑ p ∈ (A.elements.attach).pi
            (fun γ => D.localChoiceCarrier (γ.1.toResolvedFeynmanGraph)),
          ∏ γ ∈ (A.elements.attach).attach,
            D.localChoiceTerm (γ.1.1.toResolvedFeynmanGraph) (componentCD A γ.1) (p γ.1 γ.2) := by
  refine D.coproduct_resolvedForestLeftTerm_prodSum A
    (fun γ => D.localChoiceCarrier (γ.1.toResolvedFeynmanGraph))
    (fun γ => D.localChoiceTerm (γ.1.toResolvedFeynmanGraph) (componentCD A γ)) ?_
  intro γ _
  exact D.gen_eq_localChoiceSum (γ.1.toResolvedFeynmanGraph) (componentCD A γ)

end GaugeGeometry.QFT.Combinatorial
