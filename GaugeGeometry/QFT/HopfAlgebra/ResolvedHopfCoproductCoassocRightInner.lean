import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightExpand

/-!
# R-6c-2d-3 — the right inner expansion (image side, per outer forest)

Refines each outer-forest summand of the right iterated coproduct.  The right tail is `id ⊗ Δᵣ`, so
on a forest summand `leftTerm A ⊗ rightTerm A` it leaves the (forest-product) left factor untouched
and applies `Δᵣ` to the right factor — and the right factor is a **single quotient generator**
`rightTerm A = X (quotient gen)`, so `Δᵣ` hits the generator coproduct formula directly:
`Δᵣ(X q) = (X q ⊗ 1 + 1 ⊗ X q) + (sub-forest sum of the quotient)`.  This is the **image-side inner
sum**: the quotient further decomposed into its own forests.  It is simpler than the left inner
expansion (which must distribute `Δᵣ` over the forest *product*), which is why we do it first.

Landed:

* `ResolvedCoproductProperForestData.coassocRightTail_tmul` — the right tail on a pure tensor:
  `coassocRightTail D (a ⊗ b) = a ⊗ Δᵣ b`;
* `ResolvedCoproductProperForestData.coproduct_rightTerm` — `Δᵣ` on the quotient right factor:
  `Δᵣ (rightTerm A) = primitive (quotient gen) + (sub-forest sum of the contraction)`;
* `ResolvedCoproductProperForestData.coassocRightTail_forestSummand` — the per-outer right inner
  expansion: `coassocRightTail D (leftTerm A ⊗ rightTerm A) = leftTerm A ⊗ (primitive q + sub-forest
  sum)`.

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

/-- The right tail `id ⊗ Δᵣ` on a pure tensor: the left factor is untouched, `Δᵣ` hits the right. -/
theorem ResolvedCoproductProperForestData.coassocRightTail_tmul (a b : ResolvedHopfH) :
    D.coassocRightTail (a ⊗ₜ[ℚ] b) = a ⊗ₜ[ℚ] D.coproduct b := by
  simp only [ResolvedCoproductProperForestData.coassocRightTail, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply]

/-- `Δᵣ` applied to the quotient right factor of a forest summand.  Since `rightTerm A` is a single
quotient generator `X q`, this is just the generator coproduct: the primitive part plus the
quotient's own sub-forest sum. -/
theorem ResolvedCoproductProperForestData.coproduct_rightTerm (G : ResolvedFeynmanGraph)
    (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}) :
    D.coproduct ((D.supply G).rightTerm A)
      = resolvedCoproductGenPrimitive
            ((A.1.contractWithStars (D.starOf G A.1)).toResolvedHopfGen (D.hCD G A.1 A.2))
          + (D.supply (A.1.contractWithStars (D.starOf G A.1))).sum := by
  show D.coproduct (resolvedForestRightTerm A.1 (D.starOf G A.1) (D.hCD G A.1 A.2))
      = resolvedCoproductGenPrimitive
            ((A.1.contractWithStars (D.starOf G A.1)).toResolvedHopfGen (D.hCD G A.1 A.2))
          + (D.supply (A.1.contractWithStars (D.starOf G A.1))).sum
  simp only [resolvedForestRightTerm, ResolvedCoproductProperForestData.coproduct]
  rw [ResolvedCoproductGenSupply.coproduct_X]
  simp only [ResolvedCoproductGenSupply.gen, ResolvedFeynmanGraph.toResolvedHopfGen_val,
    ResolvedCoproductGenSupply.forestSum_mk]
  rfl

/-- **R-6c-2d-3 — the per-outer right inner expansion (image side).**  On a forest summand, the right
tail leaves the forest-product left factor untouched and expands the quotient right factor into its
own coproduct (primitive + sub-forest sum).  This is the image-side inner sum for outer forest `A`. -/
theorem ResolvedCoproductProperForestData.coassocRightTail_forestSummand (G : ResolvedFeynmanGraph)
    (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}) :
    D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)
      = (D.supply G).leftTerm A ⊗ₜ[ℚ]
          (resolvedCoproductGenPrimitive
              ((A.1.contractWithStars (D.starOf G A.1)).toResolvedHopfGen (D.hCD G A.1 A.2))
            + (D.supply (A.1.contractWithStars (D.starOf G A.1))).sum) := by
  rw [D.coassocRightTail_tmul, D.coproduct_rightTerm]

end GaugeGeometry.QFT.Combinatorial
