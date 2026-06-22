import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageSide

/-!
# R-6c-2d-4b-3a — the branch side, fixed as an explicit outer sum

The mirror of `ImageSide.lean` for the **branch side** `regroupBranchSum`.  At a representative `G`, it
is an explicit sum over the outer proper forests `A`, each contributing the left leak
`assoc((leftTerm A ⊗ rightTerm A) ⊗ 1)` plus `coassocLeftTail D (leftTerm A ⊗ rightTerm A)`.

This is pure linearity/bookkeeping (`sum_tmul`, `map_sum`, `sum_add_distrib`) — *no* product-of-sums
yet.  The inner expansion of `coassocLeftTail D (leftTerm A ⊗ rightTerm A) = assoc(Δᵣ(leftTerm A) ⊗
rightTerm A)` into the component-choice sum (via R-6c-2d-2a + the R-6c-2d-2b vessel) is the next, heavy
step (3b), kept separate.

Landed:

* `ResolvedCoproductProperForestData.regroupBranchSum_eq_outerSum` — `regroupBranchSum` at a
  representative as `∑ A, (assoc((leftTerm A ⊗ rightTerm A) ⊗ 1) + coassocLeftTail D (leftTerm A ⊗
  rightTerm A))`.

No facade, no flat term, no `forgetHopf`, no product-of-sums.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable (D : ResolvedCoproductProperForestData)

/-- **R-6c-2d-4b-3a — the branch side as an explicit outer sum.**  At a representative `G`,
`regroupBranchSum` is the sum over outer proper forests of the left leak `assoc((forest summand) ⊗ 1)`
plus `coassocLeftTail D (forest summand)`.  Pure linearity: the forest sum descends on the
representative (`forestSum_mk`), then `sum_tmul` / `map_sum` distribute over the outer carrier. -/
theorem ResolvedCoproductProperForestData.regroupBranchSum_eq_outerSum
    (G : ResolvedFeynmanGraph) (hCD : G.forget.toClass.IsConnectedDivergent) :
    D.regroupBranchSum (G.toResolvedHopfGen hCD)
      = ∑ A ∈ (D.supply G).forestCarrier,
          ((Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
              (((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A) ⊗ₜ[ℚ] (1 : ResolvedHopfH))
            + D.coassocLeftTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)) := by
  unfold ResolvedCoproductProperForestData.regroupBranchSum
  simp only [ResolvedFeynmanGraph.toResolvedHopfGen_val, ResolvedCoproductGenSupply.forestSum_mk,
    ResolvedCoproductProperForestData.toGenSupply]
  simp only [ResolvedCoproductForestSummandSupply.sum]
  rw [TensorProduct.sum_tmul]
  simp only [map_sum]
  rw [← Finset.sum_add_distrib]

end GaugeGeometry.QFT.Combinatorial
