import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOutputBoundaryCovers
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOutputFullSumBoundary

/-!
# R-6c-body-71 — IMAGE output cover completion: boundary discharged, only the tail cover remains

Seventy-first genuine-body step, completing the IMAGE side of the corrected full-sum OUTPUT reindex (body-69).
The IMAGE side is the tractable one: its boundary sits INSIDE the cover (body-70's `∅`-fiber), so with the
boundary discharged the whole IMAGE obligation collapses to a single tail cover field.

## The IMAGE side, minimized

Body-69's `image_cover_partition` is `cover = 1 ⊗ forestSum G + ∑_A coassocRightTail A`.  Body-70 PROVED the
boundary `1 ⊗ forestSum G = ∑_A resolvedSplitChoiceTerm ⟨A, allRightPrimitive⟩` (the `selectedOuter = ∅`
split-choice fiber).  Substituting it, the IMAGE cover reads entirely in split-choice / tail vocabulary:

```text
∑ forest splitTerm + ∑ mixed splitTerm
  = ∑_A resolvedSplitChoiceTerm ⟨A, allRightPrimitive⟩    (boundary, PROVED = 1 ⊗ forestSum)
  + ∑_A coassocRightTail A                                (tail)
```

So the IMAGE OUTPUT obligation is the SINGLE tail field `image_tail_cover` (the boundary is no longer an opaque
tensor — it is proved-equal to concrete split terms).  `ResolvedImageTailCoverSupply.image_cover_partition`
recovers body-69's `image_cover_partition` by rewriting the boundary back via body-70 — feeding body-69's
`ResolvedOutputFullSumCoverSupply` (image half) → body-54 → body-38 → `coassoc_gen`.

## The remaining tail

`image_tail_cover`'s genuine content is the tail `∑_A coassocRightTail A` against the NON-boundary cover.  Its
per-`A` refinement is now boundary-FREE (the `∅`-fiber is split off), so — unlike the discarded body-66 form — a
per-`A` fibration `coassocRightTail A = ∑_{selectedOuter = A, nonempty} splitTerm` IS satisfiable, via body-68's
`resolved_image_fiber_termEq_sum` tunnel (`term_eq` → image weights) plus body-62's `coassocRightTail_forestSummand`
/ body-66's `coproduct_rightTerm` tail expansion.  That per-`A` tail fibration is the next step; here the tail is
carried as one aggregate field.

## Status

IMAGE side: boundary DISCHARGED (body-70, proved), obligation = `image_tail_cover` (one field).  BRANCH side:
still awaits re-derivation (body-70: its boundary is cover-EXTERNAL primitive-outer, to be routed to the image
tail's primitive part — not this body).

Per the HALT, the tail fiber bijection is NOT entered (it is `image_tail_cover`); the boundary is folded in via
the proved body-70 theorem.

Landed:

* `ResolvedImageTailCoverSupply F` — the IMAGE obligation reduced to the single tail cover (boundary in
  concrete split-term form);
* `ResolvedImageTailCoverSupply.image_cover_partition` — recovers body-69's IMAGE partition equation.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-71 — the IMAGE tail cover** (the single remaining IMAGE obligation).  The splitPhi cover equals
the all-right-primitive boundary split terms (proved `= 1 ⊗ forestSum G`, body-70) plus the tail
`∑_A coassocRightTail A`.  Everything is in split-choice / tail vocabulary — the boundary is discharged. -/
structure ResolvedImageTailCoverSupply (F : ResolvedCoassocGrandFullSupply D G) where
  /-- Cover = all-right-primitive boundary terms + the per-`A` right tail. -/
  image_tail_cover :
    (∑ q ∈ F.forestCarrier, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier, D.resolvedSplitChoiceTerm q.1)
      = (∑ A ∈ (D.supply G).forestCarrier,
          D.resolvedSplitChoiceTerm (⟨A, fun _ _ => Sum.inl false⟩ : ResolvedCoassocSplitChoice D G))
        + ∑ A ∈ (D.supply G).forestCarrier,
            D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)

/-- **R-6c-body-71 — body-69's IMAGE partition from the tail cover.**  Fold the all-right-primitive boundary
terms back to `1 ⊗ forestSum G` via body-70's proved boundary theorem. -/
theorem ResolvedImageTailCoverSupply.image_cover_partition
    {F : ResolvedCoassocGrandFullSupply D G} (S : ResolvedImageTailCoverSupply F) :
    (∑ q ∈ F.forestCarrier, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier, D.resolvedSplitChoiceTerm q.1)
      = (1 : ResolvedHopfH) ⊗ₜ[ℚ] (D.supply G).sum
        + ∑ A ∈ (D.supply G).forestCarrier,
            D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A) := by
  rw [resolved_image_boundary_eq_allRightPrimitive_sum]
  exact S.image_tail_cover

end GaugeGeometry.QFT.Combinatorial
