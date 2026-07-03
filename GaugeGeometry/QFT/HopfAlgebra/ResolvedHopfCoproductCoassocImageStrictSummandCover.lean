import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageFiberSummandBody

/-!
# R-6c-body-80 — image strict-summand tail cover: the slot-correct per-`A` IMAGE primitive

Eightieth genuine-body step, replacing the unsatisfiable `fiber_eq_summand` (body-79) with the slot-correct
per-`A` content.  Body-79 proved the `selectedOuter = A` fiber lives in `leftTerm A ⊗ (·)` (the concrete
`imageWeight = leftTerm(selectedOuter) ⊗ strictSummandTerm`), so the fiber CANNOT equal the summand's
`1 ⊗ (·)` boundary for nonempty `A`.  The correct per-`A` statement puts the fiber where it actually lives.

## The slot-correct per-`A` cover

For each NON-boundary outer forest `A` (the guard `isBoundaryOuter` isolates the empty-`selectedOuter` `A`, where
`leftTerm A = 1`), the fiber sum equals the RIGHT TAIL — in the `leftTerm A ⊗ (·)` subspace, exactly where
body-79 showed it lives:

```text
∑_{selectedOuter (imageOf q) = A} splitTerm q  =  coassocRightTail A  =  leftTerm A ⊗ Δᵣ(rightTerm A).
```

Via `coassocRightTail_tmul` this is `leftTerm A ⊗ (∑ strictSummandTerm)` with `∑ strictSummandTerm =
Δᵣ(rightTerm A)` — the genuine quotient de-contraction (the `right_eq` geometry): the image quotient forests
over `selectedOuter = A` reassemble the quotient generator's coproduct.  This is SATISFIABLE (both sides in
`leftTerm A ⊗ (·)`), unlike `fiber_eq_summand`.

## The boundary guard

`isBoundaryOuter` marks the `A` with `leftTerm A = 1` (the empty `selectedOuter`), whose fiber lies in `1 ⊗ (·)`
and carries the image boundary `1 ⊗ forestSum` (body-70).  Those fibers are excluded from `strict_summand_cover`
and handled at the SUM level (body-78's `outer_image_cover`, the floor) — NOT forced into the tail form.  So the
IMAGE per-`A` obligation is `strict_summand_cover` on the non-boundary outers; the boundary is a sum-level fact.

## Result

`strict_summand_cover` is the slot-correct IMAGE per-`A` primitive, superseding the unsatisfiable
`fiber_eq_summand` (body-75/78).  `nonboundary_tail_sum` sums it over the non-boundary outers.  The full
`outer_image_cover` reconstruction (adding the boundary fibers' `1 ⊗ forestSum`) is the sum-level reconciliation
(body-78), deferred here.

Per the HALT, the quotient-choice bijection (`∑ strictSummandTerm = Δᵣ(rightTerm A)`, `right_eq`) is NOT proved;
`isBoundaryOuter` is an abstract guard; the correct per-`A` statement is fixed.

Landed:

* `ResolvedImageStrictSummandCoverSupply F` — the slot-correct per-`A` tail cover (non-boundary outers) + the
  boundary guard;
* `.nonboundary_tail_sum` — the non-boundary fibers sum to the right tails.

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

/-- **R-6c-body-80 — the slot-correct per-`A` IMAGE tail cover.**  For each non-boundary outer `A`, the
`selectedOuter = A` fiber sums to the right tail `coassocRightTail A = leftTerm A ⊗ Δᵣ(rightTerm A)` — in the
`leftTerm A ⊗ (·)` subspace where body-79 showed it lives (satisfiable, unlike `fiber_eq_summand`).  The
boundary outers (`isBoundaryOuter`, `leftTerm A = 1`) are excluded and handled at the sum level. -/
structure ResolvedImageStrictSummandCoverSupply (F : ResolvedCoassocGrandFullSupply D G) where
  /-- The boundary outers (`leftTerm A = 1`, empty `selectedOuter`), whose fibers carry `1 ⊗ forestSum`. -/
  isBoundaryOuter : (D.supply G).ForestIdx → Prop
  /-- Each non-boundary `selectedOuter = A` fiber = the right tail `coassocRightTail A`. -/
  strict_summand_cover : ∀ A ∈ (D.supply G).forestCarrier, ¬ isBoundaryOuter A →
    (∑ q ∈ F.forestCarrier with resolvedImageForestFiber F q = A, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier with resolvedImageMixedFiber F q = A, D.resolvedSplitChoiceTerm q.1)
      = D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)

/-- **R-6c-body-80 — the non-boundary fibers sum to the right tails.**  `strict_summand_cover` summed over the
non-boundary outers. -/
theorem ResolvedImageStrictSummandCoverSupply.nonboundary_tail_sum
    {F : ResolvedCoassocGrandFullSupply D G} (S : ResolvedImageStrictSummandCoverSupply F) :
    (∑ A ∈ (D.supply G).forestCarrier with ¬ S.isBoundaryOuter A,
        ((∑ q ∈ F.forestCarrier with resolvedImageForestFiber F q = A, D.resolvedSplitChoiceTerm q.1)
          + (∑ q ∈ F.mixedCarrier with resolvedImageMixedFiber F q = A, D.resolvedSplitChoiceTerm q.1)))
      = ∑ A ∈ (D.supply G).forestCarrier with ¬ S.isBoundaryOuter A,
          D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A) := by
  refine Finset.sum_congr rfl (fun A hA => ?_)
  rw [Finset.mem_filter] at hA
  exact S.strict_summand_cover A hA.1 hA.2

end GaugeGeometry.QFT.Combinatorial
