import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageCoverFiberingBody

/-!
# R-6c-body-74 — the IMAGE per-`A` fiber equation: the single clean OUTPUT-IMAGE leaf

Seventy-fourth genuine-body step, re-scoping the IMAGE OUTPUT side to ONE per-`A` equation.  Body-73 proved the
`selectedOuter` partition is free, so no `cover_fibering` field and no separate boundary field are needed: the
whole IMAGE cover is captured by the single local claim "each `selectedOuter = A` fiber sums to
`leftTerm A ⊗ Δᵣ(rightTerm A)`".

## The single leaf

```text
fiber_eq :  ∀ A,  ∑_{selectedOuter (imageOf q) = A} splitTerm q  =  leftTerm A ⊗ Δᵣ(rightTerm A)
```

This is the beautiful local statement: fiber the split-choice cover by the image's selected outer forest, and
each fiber is exactly `leftTerm A` tensored with the quotient generator's coproduct — the localized `(1 ⊗ Δᵣ)`.
It matches body-68's tunnel (`term_eq` → `imageWeight = leftTerm(selectedOuter) ⊗ strictSummandTerm`, so the
fiber factors as `leftTerm A ⊗ (∑ strictSummandTerm)`) with the genuine content being `∑ strictSummandTerm =
Δᵣ(rightTerm A)` (the `right_eq` quotient de-contraction).

## The cover from the single leaf

Via body-73's proved `resolved_image_cover_fibered` (cover = `∑_A` fiber `A`) and `fiber_eq`:

* `image_tail_sum` : `∑ cover = ∑_A leftTerm A ⊗ Δᵣ(rightTerm A)`;
* `image_tail_sum_coassoc` : `∑ cover = ∑_A coassocRightTail A` (via `coassocRightTail_tmul`, connecting to the
  tail sum) — the image cover IS the right-tail sum, boundary and all, with NO additive-separate boundary term.

So the IMAGE OUTPUT primitive is exactly `fiber_eq` — one clean `selectedOuter`-fiber equation.  The boundary
`1 ⊗ forestSum G` is not separate: it is the `A` with `leftTerm A = 1` (the empty `selectedOuter`), whose
`fiber_eq` reads `fiber ∅ = 1 ⊗ Δᵣ(rightTerm ∅)` — handled by the SAME leaf, no special case at the cover level
(the `∅` vs nonempty split, if the construction needs it, lives inside proving `fiber_eq`, not in the wiring).

Per the HALT, `fiber_eq` is NOT proved (it is the quotient de-contraction, `right_eq`-adjacent); the cover
assembly is proved from it via body-73; no boundary-separated formulation is resurrected.

Landed:

* `ResolvedImageFiberEquationSupply F` — the single per-`A` `selectedOuter`-fiber equation;
* `.image_tail_sum` / `.image_tail_sum_coassoc` — the full IMAGE cover from the single leaf.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-74 — the IMAGE per-`A` fiber equation** (the single OUTPUT-IMAGE leaf).  Each `selectedOuter = A`
split-choice fiber sums to `leftTerm A ⊗ Δᵣ(rightTerm A)` — the localized second coproduct.  No boundary field,
no `cover_fibering` field: body-73's proved fibering assembles the whole cover from this one local claim. -/
structure ResolvedImageFiberEquationSupply (F : ResolvedCoassocGrandFullSupply D G) where
  /-- The `selectedOuter = A` fiber sum = `leftTerm A ⊗ Δᵣ(rightTerm A)`. -/
  fiber_eq : ∀ A ∈ (D.supply G).forestCarrier,
    (∑ q ∈ F.forestCarrier with resolvedImageForestFiber F q = A, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier with resolvedImageMixedFiber F q = A, D.resolvedSplitChoiceTerm q.1)
      = (D.supply G).leftTerm A ⊗ₜ[ℚ] D.coproduct ((D.supply G).rightTerm A)

/-- **R-6c-body-74 — the IMAGE cover from the fiber equation** (second-coproduct form).  Body-73's free fibering
plus `fiber_eq`. -/
theorem ResolvedImageFiberEquationSupply.image_tail_sum
    {F : ResolvedCoassocGrandFullSupply D G} (S : ResolvedImageFiberEquationSupply F) :
    (∑ q ∈ F.forestCarrier, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier, D.resolvedSplitChoiceTerm q.1)
      = ∑ A ∈ (D.supply G).forestCarrier,
          (D.supply G).leftTerm A ⊗ₜ[ℚ] D.coproduct ((D.supply G).rightTerm A) := by
  rw [← resolved_image_cover_fibered F]
  exact Finset.sum_congr rfl (fun A hA => S.fiber_eq A hA)

/-- **R-6c-body-74 — the IMAGE cover as the right-tail sum.**  `∑ cover = ∑_A coassocRightTail A` — the image
cover IS the sum of the per-`A` right tails (`coassocRightTail_tmul`), with no additive-separate boundary. -/
theorem ResolvedImageFiberEquationSupply.image_tail_sum_coassoc
    {F : ResolvedCoassocGrandFullSupply D G} (S : ResolvedImageFiberEquationSupply F) :
    (∑ q ∈ F.forestCarrier, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier, D.resolvedSplitChoiceTerm q.1)
      = ∑ A ∈ (D.supply G).forestCarrier,
          D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A) := by
  rw [S.image_tail_sum]
  exact Finset.sum_congr rfl
    (fun A _ => (D.coassocRightTail_tmul ((D.supply G).leftTerm A) ((D.supply G).rightTerm A)).symm)

end GaugeGeometry.QFT.Combinatorial
