import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageCoverWiringCheck

/-!
# R-6c-body-78 — OUTPUT cover sum reconciliation: both sides boundary-IN at the sum level (Option 1)

Seventy-eighth genuine-body step, settling the value of `∑ cover splitTerm` after body-75/76/77 exposed a
tension.  The reconciliation: the OUTPUT cover sum is `regroupImageSum = regroupBranchSum` (boundary INCLUDED on
BOTH sides), matching body-54's `ResolvedOuterCoverSigmaSupply`.  The per-`A` boundary asymmetry (body-70) is
NOT a sum-level asymmetry.

## The reconciliation (Option 1)

`∑ cover = ∑ imageWeight` (`term_eq`) is intrinsically the IMAGE-side quantity, so its value is `regroupImageSum`
(body-75, via the boundary-IN `fiber_eq_summand`).  Coassociativity is exactly `regroupImageSum =
regroupBranchSum`, so `∑ cover = regroupBranchSum` TOO — i.e. body-54's `outer_branch_cover` (boundary IN), NOT
body-76/77's tails-only form.  The two sum-level OUTPUT primitives are therefore:

* IMAGE: `∑_A (1 ⊗ (leftTerm A ⊗ rightTerm A) + coassocRightTail A) = ∑ cover` — body-54's `outer_image_cover`,
  delivered by body-75's `ResolvedImageFiberSummandSupply.outer_image_cover` (via body-73's free fibering);
* BRANCH: `∑ cover = ∑_A (assoc((leftTerm A ⊗ rightTerm A) ⊗ 1) + coassocLeftTail A)` — body-54's
  `outer_branch_cover`, the genuine full-sum identity (boundary IN), fielded.

Both are boundary-IN and both equal `∑ cover`; together they give `regroupImageSum = ∑ cover = regroupBranchSum`,
the coassociativity content.

## Where the asymmetry actually lives

Body-70's asymmetry is PER-`A`, not sum-level: the image boundary `1 ⊗ forestSum` IS a split-choice fiber (the
`∅`-`selectedOuter` all-right-primitive, PROVED), so it distributes into the image summand fibers; the branch
boundary `assoc(forestSum ⊗ 1)` is NOT any base-outer fiber (PROVED), so the per-`A` base-outer decomposition
does not term-match the branch summand.  But the SUMS agree — both `= ∑ cover` — so at the reindex (sum) level
the two sides are symmetric (both body-54 forms).  Body-76's `fiber_eq_tail` / body-77's tails-only branch
reindex are SUPERSEDED for wiring: they assert `∑ cover = branch_tail`, which combined with `∑ cover =
regroupImageSum` would force the branch boundary to vanish.  They remain valid only as the identity `∑_A
coassocLeftTail A = regroupBranchSum − boundary` (a decomposition of `regroupBranchSum`, not of `∑ cover`).

## The reconciled OUTPUT primitive

`ResolvedOutputCoverSumSupply` bundles body-75's image leaf (`fiber_eq_summand`) with the fielded branch
sum-level `outer_branch_cover`, and rebuilds body-54's `ResolvedOuterCoverSigmaSupply` (whence
`image_cover_reindex` / `branch_cover_reindex` → body-38 → `coassoc_gen`).  So the OUTPUT reindex's genuine
obligations are exactly TWO sum-level agreements — `fiber_eq_summand` (image, per-`A` but summing to the image
cover) and `outer_branch_cover` (branch, fielded) — both boundary-IN.

Per the HALT, no per-`A` branch tail path is used; the branch sum-level identity is fielded (it IS the coassoc
content on the branch side); no circular use of coassociativity.

Landed:

* `ResolvedOutputCoverSumSupply F` — the reconciled OUTPUT primitive (image `fiber_eq_summand` + branch
  sum-level `outer_branch_cover`);
* `ResolvedOutputCoverSumSupply.toOuterCoverSigmaSupply` — rebuilds body-54's σ-cover skeleton.

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

/-- **R-6c-body-78 — the reconciled OUTPUT cover primitive** (both sides boundary-IN, sum-level).  The image leaf
is body-75's per-`A` `fiber_eq_summand` (summing to body-54's `outer_image_cover`); the branch is the fielded
sum-level `outer_branch_cover` (boundary IN — the genuine coassoc content on the branch side, NOT the tails-only
body-76 form). -/
structure ResolvedOutputCoverSumSupply (F : ResolvedCoassocGrandFullSupply D G) where
  /-- The IMAGE per-`A` boundary-IN summand leaf (body-75). -/
  imageFiber : ResolvedImageFiberSummandSupply F
  /-- The BRANCH sum-level cover (body-54's `outer_branch_cover`, boundary IN). -/
  outer_branch_cover :
    (∑ q ∈ F.forestCarrier, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier, D.resolvedSplitChoiceTerm q.1)
      = ∑ A ∈ (D.supply G).forestCarrier,
          ((Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
              (((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A) ⊗ₜ[ℚ] (1 : ResolvedHopfH))
            + D.coassocLeftTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A))

/-- **R-6c-body-78 — body-54's σ-cover skeleton from the reconciled primitive.**  Image via body-75's
`fiber_eq_summand` (summing through body-73), branch fielded — both boundary-IN, both `= ∑ cover`. -/
def ResolvedOutputCoverSumSupply.toOuterCoverSigmaSupply
    {F : ResolvedCoassocGrandFullSupply D G} (S : ResolvedOutputCoverSumSupply F) :
    ResolvedOuterCoverSigmaSupply F where
  outer_image_cover := S.imageFiber.outer_image_cover
  outer_branch_cover := S.outer_branch_cover

end GaugeGeometry.QFT.Combinatorial
