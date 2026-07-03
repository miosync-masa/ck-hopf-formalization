import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageTailCoverBody

/-!
# R-6c-body-73 — IMAGE cover fibering: the selectedOuter partition is FREE (proved), boundary is the ∅-fiber

Seventy-third genuine-body step, scouting body-72's `cover_fibering`.  The structural `selectedOuter` partition
of `F`'s cover turns out to be UNCONDITIONALLY PROVABLE — and it reveals the boundary is NOT an additive-separate
term, but the empty-`selectedOuter` fiber.

## The fibering is free

`resolvedImageForestFiber F q = (imageOf q.1).selectedOuter` is ALWAYS a carrier element (its type is
`(D.supply G).ForestIdx = {A // A ∈ D.carrier G}`, and `forestCarrier = (D.carrier G).attach` is the FULL
subtype).  So `Finset.sum_fiberwise_of_maps_to`'s `maps_to` is free (`Finset.mem_attach`), and

```text
∑_A ((∑ q ∈ F.forestCarrier with selectedOuter = A, splitTerm q.1)
       + (∑ q ∈ F.mixedCarrier with selectedOuter = A, splitTerm q.1))
  = ∑ forest splitTerm + ∑ mixed splitTerm
```

holds unconditionally (`resolved_image_cover_fibered`).  The whole cover is exactly the sum of ALL its
`selectedOuter = A` fibers — every split choice lies in precisely one fiber.

## What this reveals: no additive boundary

Consequently the cover has NO additive-separate boundary term.  Body-72's `cover_fibering` wrote the cover as
`∑_A boundary⟨A, p₀⟩ + ∑_A fiber A`; comparing with the proved fibering forces `∑_A boundary⟨A, p₀⟩ = 0`, so
that form is over-specified (it double-counts unless the all-right-primitive boundary choices are excluded from
`F`).  The boundary `1 ⊗ forestSum G` is instead the **empty-`selectedOuter` fiber**: the all-right-primitive
choices have `selectedOuter = ∅` (nothing left-selected), `leftTerm ∅ = 1`, and their fiber sum is
`1 ⊗ (quotient's forest sum) = 1 ⊗ forestSum G`.  So the boundary is one of the `selectedOuter = A` fibers (the
`A` with `leftTerm A = 1`), not a term outside them.

## Corrected IMAGE picture

The IMAGE cover fibers FREELY (proved): `∑ cover = ∑_A fiber A`.  Per `A` the fiber is `leftTerm A ⊗ (∑
strictSummandTerm)` (body-68 `term_eq` tunnel + `imageWeight = leftTerm(selectedOuter) ⊗ strictSummandTerm`):
for the `∅`-fiber (`leftTerm = 1`) this is the boundary `1 ⊗ forestSum`; for nonempty `A` it is the tail
`coassocRightTail A = leftTerm A ⊗ Δᵣ(rightTerm A)`.  So the single genuine IMAGE obligation is the per-`A` fiber
= its image weight sum, i.e. the quotient de-contraction (`∑ strictSummandTerm = Δᵣ(rightTerm A)`, the `right_eq`
geometry) — the structural partition (`cover_fibering`) is now discharged by `resolved_image_cover_fibered`, no
longer fielded.

Per the HALT, the fibering is proved (`sum_fiberwise` + `mem_attach`); no `tail_cover` / `right_eq` proof is
entered; the boundary classification is documented.

Landed:

* `resolved_image_cover_fibered` — the split-choice cover = the sum of its `selectedOuter = A` fibers (PROVED,
  unconditional), discharging body-72's structural `cover_fibering`.

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

/-- **R-6c-body-73 — the IMAGE cover fibers freely by `selectedOuter`.**  The split-choice cover equals the sum
over outer forests `A` of its `selectedOuter = A` fibers — unconditionally, since `selectedOuter` always lands in
the carrier (`Finset.mem_attach`).  So the structural cover partition is proved, not fielded; the boundary
`1 ⊗ forestSum G` is the empty-`selectedOuter` fiber, not an additive-separate term. -/
theorem resolved_image_cover_fibered (F : ResolvedCoassocGrandFullSupply D G) :
    (∑ A ∈ (D.supply G).forestCarrier,
        ((∑ q ∈ F.forestCarrier with resolvedImageForestFiber F q = A, D.resolvedSplitChoiceTerm q.1)
          + (∑ q ∈ F.mixedCarrier with resolvedImageMixedFiber F q = A, D.resolvedSplitChoiceTerm q.1)))
      = (∑ q ∈ F.forestCarrier, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier, D.resolvedSplitChoiceTerm q.1) := by
  have hf : ∀ q ∈ F.forestCarrier, resolvedImageForestFiber F q ∈ (D.supply G).forestCarrier :=
    fun q _ => Finset.mem_attach _ _
  have hm : ∀ q ∈ F.mixedCarrier, resolvedImageMixedFiber F q ∈ (D.supply G).forestCarrier :=
    fun q _ => Finset.mem_attach _ _
  rw [Finset.sum_add_distrib,
    Finset.sum_fiberwise_of_maps_to hf (fun q => D.resolvedSplitChoiceTerm q.1),
    Finset.sum_fiberwise_of_maps_to hm (fun q => D.resolvedSplitChoiceTerm q.1)]

end GaugeGeometry.QFT.Combinatorial
