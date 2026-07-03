import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageStrictSummandCover
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageCoverFiberingBody
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOutputFullSumBoundary

/-!
# R-6c-body-81 — image sum reconstruction: slot-correct tails + boundary ⇒ `outer_image_cover`

Eighty-first genuine-body step, wiring body-80's slot-correct `strict_summand_cover` back to the sum-level
`outer_image_cover` (body-54/78).  So the coordinate correction (body-79/80) is guaranteed to plug into the
`coassoc_gen` exit.

## The reconstruction

Body-80 fixed the per-`A` IMAGE content in the correct slot: for NON-boundary outers, `fiber A =
coassocRightTail A` (`strict_summand_cover`).  The boundary outers (`isBoundaryOuter`, `leftTerm A = 1`) carry
the image boundary; their combined fibers give `1 ⊗ forestSum` plus their own tails (`boundary_cover`).  These
two assemble to body-54's `outer_image_cover`:

```text
∑ cover
  = ∑_A fiber A                                                (body-73, free fibering)
  = ∑_{boundary} fiber A + ∑_{¬boundary} fiber A               (filter partition)
  = (1 ⊗ forestSum + ∑_{boundary} coassocRightTail A) + ∑_{¬boundary} coassocRightTail A
                                                               (boundary_cover, strict_summand_cover)
  = 1 ⊗ forestSum + ∑_A coassocRightTail A                    (recombine)
  = ∑_A (1 ⊗ (leftTerm A ⊗ rightTerm A) + coassocRightTail A) (body-69 split, reversed)
```

— exactly `outer_image_cover` (`ResolvedImageStrictToOuterCoverSupply.outer_image_cover`, PROVED via
`resolved_image_cover_fibered` + `outer_branch/image_boundary_tail_split` + `Finset.sum_filter_add_sum_filter_not`
+ `abel`).

## What this settles

The unsatisfiable per-`A` `fiber_eq_summand` (body-75/78) is fully replaced: the IMAGE OUTPUT obligation is now
the slot-correct `strict_summand_cover` (non-boundary tails, the `right_eq` quotient de-contraction) plus the
`boundary_cover` (the `∅`-fiber `1 ⊗ forestSum` bookkeeping), and they PROVABLY reconstruct body-54's
`outer_image_cover` — which flows through body-54's `image_cover_reindex` → body-38 → `coassoc_gen`.  So body-80's
coordinate fix is exit-compatible.

Per the HALT, `strict_summand_cover` is not entered (it is body-80's field); `boundary_cover` is fielded (the
`∅`-fiber bookkeeping); the reconstruction is proved.

Landed:

* `ResolvedImageStrictToOuterCoverSupply F` — the slot-correct tails (body-80) + the boundary-fiber cover;
* `.outer_image_cover` — body-54's `outer_image_cover`, reconstructed.

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

/-- **R-6c-body-81 — the slot-correct IMAGE cover** (tails + boundary).  Body-80's non-boundary tail cover plus
the boundary-fiber cover (the `∅`-fiber carries `1 ⊗ forestSum` plus its own tails). -/
structure ResolvedImageStrictToOuterCoverSupply (F : ResolvedCoassocGrandFullSupply D G) where
  /-- The slot-correct non-boundary tail cover (body-80). -/
  Strict : ResolvedImageStrictSummandCoverSupply F
  /-- The boundary fibers carry the image boundary `1 ⊗ forestSum` plus their own tails. -/
  boundary_cover :
    (∑ A ∈ (D.supply G).forestCarrier with Strict.isBoundaryOuter A,
        ((∑ q ∈ F.forestCarrier with resolvedImageForestFiber F q = A, D.resolvedSplitChoiceTerm q.1)
          + (∑ q ∈ F.mixedCarrier with resolvedImageMixedFiber F q = A, D.resolvedSplitChoiceTerm q.1)))
      = (1 : ResolvedHopfH) ⊗ₜ[ℚ] (D.supply G).sum
        + ∑ A ∈ (D.supply G).forestCarrier with Strict.isBoundaryOuter A,
            D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)

/-- **R-6c-body-81 — body-54's `outer_image_cover`, reconstructed from the slot-correct tails + boundary.** -/
theorem ResolvedImageStrictToOuterCoverSupply.outer_image_cover
    {F : ResolvedCoassocGrandFullSupply D G} (S : ResolvedImageStrictToOuterCoverSupply F) :
    (∑ A ∈ (D.supply G).forestCarrier,
        ((1 : ResolvedHopfH) ⊗ₜ[ℚ] ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)
          + D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)))
      = (∑ q ∈ F.forestCarrier, D.resolvedSplitChoiceTerm q.1)
          + (∑ q ∈ F.mixedCarrier, D.resolvedSplitChoiceTerm q.1) := by
  rw [← resolved_image_cover_fibered F, outer_image_boundary_tail_split,
    ← Finset.sum_filter_add_sum_filter_not (D.supply G).forestCarrier S.Strict.isBoundaryOuter
        (fun A => (∑ q ∈ F.forestCarrier with resolvedImageForestFiber F q = A, D.resolvedSplitChoiceTerm q.1)
          + (∑ q ∈ F.mixedCarrier with resolvedImageMixedFiber F q = A, D.resolvedSplitChoiceTerm q.1)),
    S.boundary_cover, S.Strict.nonboundary_tail_sum,
    ← Finset.sum_filter_add_sum_filter_not (D.supply G).forestCarrier S.Strict.isBoundaryOuter
        (fun A => D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A))]
  abel

end GaugeGeometry.QFT.Combinatorial
