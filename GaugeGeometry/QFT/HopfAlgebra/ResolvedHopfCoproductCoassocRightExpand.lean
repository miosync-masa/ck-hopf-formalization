import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftExpand

/-!
# R-6c-2c — the right iterated-coproduct expansion (`rhsExpansion`, first level)

The mirror of R-6c-2b for the right iterated coproduct `coassocRight D = (id ⊗ Δᵣ) ∘ Δᵣ`.  Since the
right coproduct already lands in the canonical right-associated triple tensor, **no associator is
needed**: the tail is simply `coassocRightTail = id ⊗ Δᵣ`.  The first-level linear expansion is then
symmetric to the left one — split `Δᵣ(X x) = primitive + ∑ forest summands` and push the tail
(an algebra hom) through `map_add`/`map_sum`.

The two expansions only start to differ at the **inner** level (how `Δᵣ` on the forest factor
distributes, and where the image-vs-branch reindex sits); at the first level both are the same shape.
Here we pin the outer right shape.

Landed:

* `ResolvedCoproductProperForestData.coassocRightTail` — `id ⊗ Δᵣ : ResolvedHopfH ⊗ ResolvedHopfH →ₐ
  ResolvedHopfH3`, with `coassocRight D y = coassocRightTail D (Δᵣ y)` (`coassocRight_apply`,
  definitional);
* `ResolvedCoproductProperForestData.coassocRight_expand` — **the first-level right expansion**:
  `coassocRight D (X (G.toResolvedHopfGen hCD))` equals `coassocRightTail D (primitive g)` plus
  `∑ A ∈ (D.supply G).forestCarrier, coassocRightTail D (leftTerm A ⊗ rightTerm A)`.

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

/-- The post-`Δᵣ` tail of `coassocRight`: apply `Δᵣ` to the right tensor factor (no associator).
By definition `coassocRight D = coassocRightTail D ∘ Δᵣ`. -/
noncomputable def ResolvedCoproductProperForestData.coassocRightTail :
    ResolvedHopfH ⊗[ℚ] ResolvedHopfH →ₐ[ℚ] ResolvedHopfH3 :=
  Algebra.TensorProduct.map (AlgHom.id ℚ ResolvedHopfH) D.coproduct

/-- `coassocRight` factors through `coassocRightTail` after `Δᵣ` (definitional). -/
theorem ResolvedCoproductProperForestData.coassocRight_apply (y : ResolvedHopfH) :
    D.coassocRight y = D.coassocRightTail (D.coproduct y) := rfl

/-- **R-6c-2c — the first-level right expansion of the iterated coproduct.**  On a generator
`X (G.toResolvedHopfGen hCD)`, `coassocRight D` splits into the primitive part (the tail applied to
`X g ⊗ 1 + 1 ⊗ X g`) plus the outer branch sum (the tail applied to each forest summand
`leftTerm A ⊗ rightTerm A`).  Same proof as the left expansion: `coassocRight = coassocRightTail ∘
Δᵣ`, `Δᵣ(X g) = gen g = primitive + forest sum`, and `coassocRightTail` is an algebra hom. -/
theorem ResolvedCoproductProperForestData.coassocRight_expand
    (G : ResolvedFeynmanGraph) (hCD : G.forget.toClass.IsConnectedDivergent) :
    D.coassocRight (MvPolynomial.X (G.toResolvedHopfGen hCD))
      = D.coassocRightTail (resolvedCoproductGenPrimitive (G.toResolvedHopfGen hCD))
        + ∑ A ∈ (D.supply G).forestCarrier,
            D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A) := by
  rw [D.coassocRight_apply]
  simp only [ResolvedCoproductProperForestData.coproduct]
  rw [ResolvedCoproductGenSupply.coproduct_X]
  simp only [ResolvedCoproductGenSupply.gen, ResolvedFeynmanGraph.toResolvedHopfGen_val,
    ResolvedCoproductGenSupply.forestSum_mk]
  rw [map_add]
  simp only [ResolvedCoproductForestSummandSupply.sum]
  rw [map_sum]
  rfl

end GaugeGeometry.QFT.Combinatorial
