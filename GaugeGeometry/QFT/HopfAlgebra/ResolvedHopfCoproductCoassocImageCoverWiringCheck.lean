import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageFiberEquationBody
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocResolvedOuterCoverSigma

/-!
# R-6c-body-75 — corrected IMAGE wiring check: body-54 needs the boundary-IN summand form

Seventy-fifth genuine-body step, checking body-74's clean IMAGE result against the EXISTING exit — body-54's
`ResolvedOuterCoverSigmaSupply.outer_image_cover` (which feeds body-38 → `coassoc_gen`).  The check finds a
genuine orientation mismatch and fixes the IMAGE leaf to the wiring-compatible form.

## The mismatch

* body-54's `outer_image_cover` requires `∑_A (1 ⊗ (leftTerm A ⊗ rightTerm A) + coassocRightTail A) = ∑ cover`
  — i.e. `∑ cover = regroupImageSum`, the BOUNDARY (`1 ⊗ forestSum`) INCLUDED in the cover.
* body-74's `image_tail_sum_coassoc` gives `∑ cover = ∑_A coassocRightTail A` — the boundary DROPPED.

These differ by `1 ⊗ forestSum G = ∑_A 1 ⊗ (leftTerm A ⊗ rightTerm A)`.  So body-74's `fiber_eq` (fiber `A` =
`leftTerm A ⊗ Δᵣ(rightTerm A)` = `coassocRightTail A`, tails-only) is NOT wiring-compatible with the existing
exit: summed via body-73's free fibering it yields `∑ cover = ∑_A coassocRightTail A`, missing the boundary.
The existing chain wants `∑ cover = regroupImageSum`.

## The fix: the boundary-IN summand form

The wiring-compatible per-`A` leaf keeps the boundary INSIDE each fiber:

```text
fiber_eq_summand :  ∀ A,  (selectedOuter = A fiber sum)  =  1 ⊗ (leftTerm A ⊗ rightTerm A) + coassocRightTail A
```

Summed via body-73's PROVED `resolved_image_cover_fibered` (`∑ cover = ∑_A fiber A`), this yields body-54's
`outer_image_cover` VERBATIM (`ResolvedImageFiberSummandSupply.outer_image_cover`, type-matching the field).  So
this IS the IMAGE leaf that plugs into the existing `coassoc_gen` chain — no new adapter, no reindex surgery.

## Reconciliation with the boundary asymmetry

This does not contradict body-70/73/74: the boundary `1 ⊗ forestSum` is still not an ADDITIVE-separate term at
the cover level (body-73's fibering is free, no separate boundary sum).  It is DISTRIBUTED per-`A` inside the
fibers: for the empty-`selectedOuter` `A` (`leftTerm A = 1`) the `1 ⊗ (leftTerm A ⊗ rightTerm A) = 1 ⊗ (1 ⊗
rightTerm A)` part is in-slot; for nonempty `A` the fiber genuinely carries `1 ⊗ (leftTerm A ⊗ rightTerm A)` as
part of the image summand.  body-68's slot observation (fiber `A` sits in `leftTerm A ⊗ (·)`) is the SATISFIABILITY
question for `fiber_eq_summand` at nonempty `A` — the deep content — not a wiring obstruction.  The WIRING is
settled: body-54 needs the summand form, and body-73 delivers it.  body-74's tails-only `fiber_eq` is superseded
for wiring purposes (it stays valid as the `∑_A coassocRightTail A` identity, but that is `regroupImageSum` MINUS
the boundary, not the cover).

Per the HALT, the branch side is untouched; `fiber_eq_summand` is NOT proved; only the wiring orientation is
fixed.

Landed:

* `ResolvedImageFiberSummandSupply F` — the wiring-compatible per-`A` IMAGE leaf (boundary-IN summand form);
* `ResolvedImageFiberSummandSupply.outer_image_cover` — body-54's `outer_image_cover` VERBATIM, from the leaf
  via body-73.

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

/-- **R-6c-body-75 — the wiring-compatible per-`A` IMAGE leaf** (boundary-IN summand form).  Each
`selectedOuter = A` fiber sums to the full image summand `1 ⊗ (leftTerm A ⊗ rightTerm A) + coassocRightTail A`
(NOT the tails-only `coassocRightTail A` of body-74).  This is the form body-54's `outer_image_cover` needs. -/
structure ResolvedImageFiberSummandSupply (F : ResolvedCoassocGrandFullSupply D G) where
  /-- The `selectedOuter = A` fiber sum = the full image summand for `A`. -/
  fiber_eq_summand : ∀ A ∈ (D.supply G).forestCarrier,
    (∑ q ∈ F.forestCarrier with resolvedImageForestFiber F q = A, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier with resolvedImageMixedFiber F q = A, D.resolvedSplitChoiceTerm q.1)
      = (1 : ResolvedHopfH) ⊗ₜ[ℚ] ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)
        + D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)

/-- **R-6c-body-75 — body-54's `outer_image_cover` from the summand-form leaf.**  Body-73's free fibering
(`∑ cover = ∑_A fiber A`) plus `fiber_eq_summand` gives body-54's field verbatim — so the IMAGE leaf plugs
straight into the existing `coassoc_gen` chain. -/
theorem ResolvedImageFiberSummandSupply.outer_image_cover
    {F : ResolvedCoassocGrandFullSupply D G} (S : ResolvedImageFiberSummandSupply F) :
    (∑ A ∈ (D.supply G).forestCarrier,
        ((1 : ResolvedHopfH) ⊗ₜ[ℚ] ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)
          + D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)))
      = (∑ q ∈ F.forestCarrier, D.resolvedSplitChoiceTerm q.1)
          + (∑ q ∈ F.mixedCarrier, D.resolvedSplitChoiceTerm q.1) := by
  rw [← resolved_image_cover_fibered F]
  exact Finset.sum_congr rfl (fun A hA => (S.fiber_eq_summand A hA).symm)

end GaugeGeometry.QFT.Combinatorial
