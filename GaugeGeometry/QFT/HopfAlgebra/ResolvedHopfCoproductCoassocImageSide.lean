import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerCover

/-!
# R-6c-2d-4b-2 — the image side, fixed as an explicit outer sum

Towards the `image_agreement` field of `ResolvedInnerCoassocSigmaCoverData`, this file fixes the
**image side** `regroupImageSum` completely: at a representative `G`, it is an explicit sum over the
outer proper forests `A`, each contributing `1 ⊗ (leftTerm A ⊗ rightTerm A) + coassocRightTail D
(leftTerm A ⊗ rightTerm A)`, and (via the R-6c-2d-3 right inner expansion) the latter is
`leftTerm A ⊗ (primitive (quotient gen) + the quotient's sub-forest sum)`.

This is pure linearity/bookkeeping (`tmul_sum`, `map_sum`, `sum_add_distrib`) plus the right inner
expansion — no product-of-sums, no branch side, no cover construction yet.  It pins the exact terms
the cover's image weight must realise (R-6c-2d-4b-1 `image_agreement`).

Landed:

* `ResolvedCoproductProperForestData.regroupImageSum_eq_outerSum` — `regroupImageSum` at a
  representative as `∑ A, (1 ⊗ (leftTerm A ⊗ rightTerm A) + coassocRightTail D (leftTerm A ⊗
  rightTerm A))`;
* `ResolvedCoproductProperForestData.regroupImageSum_eq_outerSum_expanded` — the same with each outer
  summand's `coassocRightTail` replaced by the R-6c-2d-3 explicit form.

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

/-- **R-6c-2d-4b-2 — the image side as an explicit outer sum.**  At a representative `G`,
`regroupImageSum` is the sum over outer proper forests of `1 ⊗ (forest summand) + coassocRightTail D
(forest summand)`.  Pure linearity: the forest sum descends on the representative
(`forestSum_mk`), then `tmul_sum` / `map_sum` distribute over the outer carrier. -/
theorem ResolvedCoproductProperForestData.regroupImageSum_eq_outerSum
    (G : ResolvedFeynmanGraph) (hCD : G.forget.toClass.IsConnectedDivergent) :
    D.regroupImageSum (G.toResolvedHopfGen hCD)
      = ∑ A ∈ (D.supply G).forestCarrier,
          ((1 : ResolvedHopfH) ⊗ₜ[ℚ] ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)
            + D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)) := by
  unfold ResolvedCoproductProperForestData.regroupImageSum
  simp only [ResolvedFeynmanGraph.toResolvedHopfGen_val, ResolvedCoproductGenSupply.forestSum_mk,
    ResolvedCoproductProperForestData.toGenSupply]
  simp only [ResolvedCoproductForestSummandSupply.sum]
  rw [TensorProduct.tmul_sum, map_sum, ← Finset.sum_add_distrib]

/-- **R-6c-2d-4b-2 — the image side, fully expanded.**  Each outer summand's `coassocRightTail` is the
R-6c-2d-3 image-side inner term `leftTerm A ⊗ (primitive (quotient gen) + the quotient's sub-forest
sum)`.  This is the exact term the cover's image weight must realise. -/
theorem ResolvedCoproductProperForestData.regroupImageSum_eq_outerSum_expanded
    (G : ResolvedFeynmanGraph) (hCD : G.forget.toClass.IsConnectedDivergent) :
    D.regroupImageSum (G.toResolvedHopfGen hCD)
      = ∑ A ∈ (D.supply G).forestCarrier,
          ((1 : ResolvedHopfH) ⊗ₜ[ℚ] ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)
            + (D.supply G).leftTerm A ⊗ₜ[ℚ]
                (resolvedCoproductGenPrimitive
                    ((A.1.contractWithStars (D.starOf G A.1)).toResolvedHopfGen (D.hCD G A.1 A.2))
                  + (D.supply (A.1.contractWithStars (D.starOf G A.1))).sum)) := by
  rw [D.regroupImageSum_eq_outerSum G hCD]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  rw [D.coassocRightTail_forestSummand]

end GaugeGeometry.QFT.Combinatorial
