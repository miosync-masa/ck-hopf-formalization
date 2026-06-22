import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCoverShape

/-!
# R-6c-4c — the per-outer-forest cover shape (two-layer, mirroring flat `outer_sum_reindex`)

The R-6c-4b scout found a **granularity decision**: a single global `FL` vs a per-outer-forest family.
This file takes the **per-outer-A family** path, mirroring the flat
`ResolvedH58FullGrainOuterSumSupply.outer_sum_reindex` (a per-`Aout` inner cover summed over outer
forests).

Validation (single component `l_A = X c`):

  `imageOuterTerm A = c⊗(r⊗1) + c⊗(1⊗r) + 1⊗(c⊗r) + c⊗(quotient sub-forest sum)`
  `branchSummand A  = c⊗(r⊗1) + c⊗(1⊗r) + 1⊗(c⊗r) + assoc(component sub-forest sum ⊗ r)`

— the first three (near-primitive) terms **agree exactly per `A`**, and the fourth is the genuine
per-`A` de-contraction bijection (component sub-forests ↔ quotient sub-forests, the resolved replay of
the flat per-`Aout` `concrete_sum_reindex`).  So per-`A` is the correct grain (the 2d-fix `B_A ≠ I_A`
mismatch was at a coarser grain).

Landed:

* `ResolvedCoproductProperForestData.imageOuterTerm` — the per-outer-`A` image summand (matching
  `regroupImageSum_eq_outerSum`);
* `regroupImageSum_eq_imageOuterTermSum` — `regroupImageSum` at a representative as `∑ A,
  imageOuterTerm A` (branch side is already `∑ A, branchSummand A` via
  `regroupBranchSum_eq_branchSummandSum`);
* `ResolvedInnerCoassocOuterCoverShape D A` — the **per-outer-forest** cover shape vessel
  (`imageOuterTerm A = ∑ image weight`, `∑ forest+mixed weight = branchSummand A`);
* `ResolvedInnerCoassocOuterCoverShape.outer_reindex` — the per-`A` reindex `imageOuterTerm A =
  branchSummand A`;
* `reindex_of_outerCoverShapes` — a per-`A` family yields the representative-level reindex
  `regroupImageSum = regroupBranchSum`, by `Finset.sum_congr`.

So the final geometry reduces to building one `ResolvedInnerCoassocOuterCoverShape D A` per outer
forest — exactly the flat per-`Aout` σ-cover, replayed in resolved terms.  No facade, no flat term, no
`forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable (D : ResolvedCoproductProperForestData)

/-- The per-outer-forest image summand (matching the `regroupImageSum_eq_outerSum` summand): the
`1 ⊗ (forest summand)` leak plus the right tail of the forest summand. -/
noncomputable def ResolvedCoproductProperForestData.imageOuterTerm {G : ResolvedFeynmanGraph}
    (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}) : ResolvedHopfH3 :=
  (1 : ResolvedHopfH) ⊗ₜ[ℚ] ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)
    + D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)

/-- `regroupImageSum` at a representative as the outer sum of `imageOuterTerm`. -/
theorem ResolvedCoproductProperForestData.regroupImageSum_eq_imageOuterTermSum
    (G : ResolvedFeynmanGraph) (hCD : G.forget.toClass.IsConnectedDivergent) :
    D.regroupImageSum (G.toResolvedHopfGen hCD)
      = ∑ A ∈ (D.supply G).forestCarrier, D.imageOuterTerm A := by
  rw [D.regroupImageSum_eq_outerSum G hCD]
  rfl

/-- **R-6c-4c — the per-outer-forest cover shape vessel.**  For one outer forest `A`, a finite cover
layer + resolved-`ResolvedHopfH3` weights with the per-`A` image/branch agreements (the image side
`imageOuterTerm A`, the branch side `branchSummand A`). -/
structure ResolvedInnerCoassocOuterCoverShape (D : ResolvedCoproductProperForestData)
    {G : ResolvedFeynmanGraph} (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}) where
  /-- The finite cover layer for this outer forest. -/
  FL : ResolvedCarrierFiniteBranchMapLayer
  /-- The resolved-term weights. -/
  W : ResolvedH58WeightData FL ResolvedHopfH3
  /-- The per-`A` image side equals the cover's image-weight sum. -/
  image_agreement : D.imageOuterTerm A = ∑ z ∈ FL.imageCarrier, W.imageWeight z
  /-- The cover's (forest + mixed) branch-weight sum equals the per-`A` branch side. -/
  branch_agreement :
    (∑ q ∈ FL.forestCarrier, W.forestWeight q) + (∑ q ∈ FL.mixedCarrier, W.mixedWeight q)
      = D.branchSummand A

/-- **R-6c-4c — the per-`A` reindex.**  The per-outer image term equals the per-outer branch term, by
the cover sum_bij (`ResolvedH58WeightData.sum_reindex`) chained through the two agreements. -/
theorem ResolvedInnerCoassocOuterCoverShape.outer_reindex {D : ResolvedCoproductProperForestData}
    {G : ResolvedFeynmanGraph} {A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}}
    (S : ResolvedInnerCoassocOuterCoverShape D A) :
    D.imageOuterTerm A = D.branchSummand A := by
  rw [S.image_agreement, S.W.sum_reindex, S.branch_agreement]

/-- **R-6c-4c — the per-outer-family reindex.**  A per-outer-forest family of cover shapes yields the
representative-level reindex `regroupImageSum = regroupBranchSum`, by summing the per-`A` reindexes
over the outer carrier (the resolved replay of the flat `outer_sum_reindex`). -/
theorem reindex_of_outerCoverShapes (G : ResolvedFeynmanGraph)
    (hCD : G.forget.toClass.IsConnectedDivergent)
    (S : ∀ A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G},
      ResolvedInnerCoassocOuterCoverShape D A) :
    D.regroupImageSum (G.toResolvedHopfGen hCD)
      = D.regroupBranchSum (G.toResolvedHopfGen hCD) := by
  rw [D.regroupImageSum_eq_imageOuterTermSum G hCD, D.regroupBranchSum_eq_branchSummandSum G hCD]
  exact Finset.sum_congr rfl (fun A _ => (S A).outer_reindex)

end GaugeGeometry.QFT.Combinatorial
