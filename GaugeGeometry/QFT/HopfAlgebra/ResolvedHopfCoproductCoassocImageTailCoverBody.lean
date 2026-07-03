import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageOutputCoverComplete

/-!
# R-6c-body-72 — IMAGE tail per-`A` fibration: the boundary-free per-outer quotient cover

Seventy-second genuine-body step, reducing body-71's global `image_tail_cover` to a boundary-FREE per-`A`
quotient fiber cover.  Now that the `∅`-fiber boundary is split off (body-70/71), the per-`A` fibration finally
lands in the RIGHT place — the nonempty `selectedOuter = A` fibers, where the image summand genuinely factors as
`leftTerm A ⊗ (…)` with no boundary to misplace.

## The per-`A` tail (boundary-free)

For each outer forest `A ∈ forestCarrier` (nonempty — proper forests), the right tail equals its
`selectedOuter = A` fiber sum:

```text
coassocRightTail (leftTerm A ⊗ rightTerm A)
  = (∑ q ∈ F.forestCarrier with selectedOuter (imageOf q.1) = A, splitTerm q.1)
      + (∑ q ∈ F.mixedCarrier with selectedOuter (imageOf q.1) = A, splitTerm q.1).
```

This is satisfiable (unlike the discarded body-66 `image_quotient_fiber`): the `selectedOuter = A` fiber sum
factors as `leftTerm A ⊗ (∑ strictSummandTerm)` (body-68's `resolved_image_fiber_termEq_sum` + `imageWeight =
leftTerm(selectedOuter) ⊗ strictSummandTerm`), and `coassocRightTail (leftTerm A ⊗ rightTerm A) = leftTerm A ⊗
Δᵣ(rightTerm A)` (body-62/66) — BOTH in the `leftTerm A ⊗ (·)` slot, no `1 ⊗ (·)` boundary.  The genuine
remaining content of `tail_cover A` is the quotient de-contraction `∑ strictSummandTerm = Δᵣ(rightTerm A)` (the
`right_eq` geometry) — fielded here, not entered.

## The cover fibering

`cover_fibering` partitions `F`'s split-choice cover by `selectedOuter`: the `∅`-fiber (the boundary, one
all-right-primitive term per base `A`) plus the nonempty `selectedOuter = A` fibers.  This is the structural
combinatorial fact that `F`'s carriers split as `{∅-fiber} ⊔ {nonempty A-fibers}` — fielded.

## Result

`ResolvedImageTailCoverSupply` (body-71's single IMAGE obligation) reduces to `∀ A, tail_cover A` plus the
`cover_fibering` partition: `image_tail_cover` follows by `rw [cover_fibering]` then `Finset.sum_congr` with the
per-`A` tails.  So the IMAGE OUTPUT side is now `global boundary (PROVED, body-70) + per-A local quotient tails
(tail_cover) + cover fibering` — the natural "global boundary + local quotient tails" shape, with the per-`A`
fibration finally correct.

Per the HALT, the quotient-choice ↔ `selectedOuter = A` bijection is NOT proved (it is `tail_cover`); the cover
partition is fielded (`cover_fibering`); the combination is proved.

Landed:

* `ResolvedImageTailPerOuterSupply F` — the per-`A` tail cover + the `selectedOuter` cover fibering;
* `ResolvedImageTailPerOuterSupply.toImageTailCoverSupply` — recovers body-71's global tail cover.

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

/-- **R-6c-body-72 — the boundary-free per-`A` IMAGE tail cover** + the `selectedOuter` cover fibering.  For each
nonempty outer `A`, the right tail equals its `selectedOuter = A` fiber sum (the quotient de-contraction, now
boundary-free); and `F`'s cover partitions by `selectedOuter` into the `∅`-boundary plus the nonempty fibers. -/
structure ResolvedImageTailPerOuterSupply (F : ResolvedCoassocGrandFullSupply D G) where
  /-- The per-`A` right tail = its `selectedOuter = A` fiber sum (boundary-free). -/
  tail_cover : ∀ A ∈ (D.supply G).forestCarrier,
    D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)
      = (∑ q ∈ F.forestCarrier with resolvedImageForestFiber F q = A, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier with resolvedImageMixedFiber F q = A, D.resolvedSplitChoiceTerm q.1)
  /-- `F`'s cover partitions by `selectedOuter`: the `∅`-boundary (all-right-primitive per base `A`) plus the
  nonempty `selectedOuter = A` fibers. -/
  cover_fibering :
    (∑ q ∈ F.forestCarrier, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier, D.resolvedSplitChoiceTerm q.1)
      = (∑ A ∈ (D.supply G).forestCarrier,
          D.resolvedSplitChoiceTerm (⟨A, fun _ _ => Sum.inl false⟩ : ResolvedCoassocSplitChoice D G))
        + ∑ A ∈ (D.supply G).forestCarrier,
            ((∑ q ∈ F.forestCarrier with resolvedImageForestFiber F q = A, D.resolvedSplitChoiceTerm q.1)
              + (∑ q ∈ F.mixedCarrier with resolvedImageMixedFiber F q = A, D.resolvedSplitChoiceTerm q.1))

/-- **R-6c-body-72 — body-71's global tail cover from the per-`A` tails.**  Fiber the cover by `selectedOuter`
(`cover_fibering`), then replace each nonempty fiber sum by its right tail (`tail_cover`). -/
def ResolvedImageTailPerOuterSupply.toImageTailCoverSupply
    {F : ResolvedCoassocGrandFullSupply D G} (S : ResolvedImageTailPerOuterSupply F) :
    ResolvedImageTailCoverSupply F where
  image_tail_cover := by
    rw [S.cover_fibering]
    congr 1
    exact Finset.sum_congr rfl (fun A hA => (S.tail_cover A hA).symm)

end GaugeGeometry.QFT.Combinatorial
