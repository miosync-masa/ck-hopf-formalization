import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageFiberBody
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightInner

/-!
# R-6c-body-62 — Image fiber agreement body: RIGHT expansion reduced via the RIGHT-tail theorem

Sixty-second genuine-body step, the RIGHT-side mirror of body-61.  Scouts body-58's `image_fiber_agree` — the
RIGHT (image) per-`A` expansion, the second remaining OUTPUT-reindex leaf (body-60) — and reduces it to an
ALREADY-PROVED RIGHT-tail expansion plus a fielded cover, exactly as body-61 did on the left.

## The RIGHT-tail expansion is already discharged (but NOT to a split-term sum)

The codebase proves `coassocRightTail_forestSummand` (in `…CoassocRightInner`):

```text
D.coassocRightTail (leftTerm A ⊗ rightTerm A)
  = leftTerm A ⊗ (primitive (quotient gen of A) + (D.supply (A contracted at its stars)).sum)
```

via `coassocRightTail_tmul` (`id ⊗ Δᵣ`) + `coproduct_rightTerm` (`Δᵣ` of the single quotient generator
`rightTerm A`).  So the entire `coassocRightTail` is expanded — no residual tail.

## The asymmetry with the LEFT side (honest note)

Body-61's LEFT tail collapsed all the way to a split-term SUM (`coassocLeftTail_eq_splitChoiceTermSum`),
leaving a PURE sum-vs-sum cover.  The RIGHT tail does NOT: `Δᵣ` hits the QUOTIENT factor `rightTerm A`, so it
lands on `leftTerm A ⊗ (primitive + the quotient graph's OWN forest sum)` — the de-contraction structure, not a
split choice sum.  Hence the RIGHT cover keeps the fully-expanded tensor on its LHS; the genuine content is the
quotient de-contraction (`(D.supply (quotient graph)).sum` reassembling into `F`'s `selectedOuter`-fibered
split terms).

## The reduction

`image_fiber_agree` LHS is `1 ⊗ (leftTerm A ⊗ rightTerm A) + coassocRightTail (leftTerm A ⊗ rightTerm A)`.
Rewriting the tail by `coassocRightTail_forestSummand` gives the fully-expanded image summand, which the
fielded `ResolvedImageFiberCoverSupply.image_cover` equates with body-58's `selectedOuter`-fibered RHS:

```text
1 ⊗ (leftTerm A ⊗ rightTerm A) + leftTerm A ⊗ (primitive (quot gen) + (quot graph).sum)
  = (∑ q ∈ F.forestCarrier with selectedOuter (imageOf q.1) = A, splitTerm q.1)
      + (∑ q ∈ F.mixedCarrier with selectedOuter (imageOf q.1) = A, splitTerm q.1).
```

So the RIGHT OUTPUT leaf is the single field `image_cover`, with all `coassocRightTail` tail content
discharged by the pre-existing theorem — the parallel of body-61's `branch_cover`.

Per the HALT, the quotient / right-factor de-contraction cover is NOT proved (it IS `image_cover`); the branch
side is untouched; no return to the retarget / `right_eq` chain — only the pre-existing
`coassocRightTail_forestSummand` is used.

Landed:

* `ResolvedImageFiberCoverSupply F` — the RIGHT de-contraction cover (fully-expanded summand ↔
  `selectedOuter`-fibered split terms);
* `ResolvedImageFiberCoverSupply.toImageFiberAgreementSupply` — body-58's agreement, tail rewritten.

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

/-- **R-6c-body-62 — the RIGHT de-contraction cover.**  With the RIGHT tail expanded by
`coassocRightTail_forestSummand`, the fully-expanded image outer summand equals `F`'s `selectedOuter`-fibered
split-term sum.  The genuine RIGHT inner cover (the quotient de-contraction), with no residual tail. -/
structure ResolvedImageFiberCoverSupply (F : ResolvedCoassocGrandFullSupply D G) where
  /-- The fully-expanded image summand reindexes onto `F`'s `selectedOuter = A` fibers. -/
  image_cover : ∀ A ∈ (D.supply G).forestCarrier,
    ((1 : ResolvedHopfH) ⊗ₜ[ℚ] ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)
        + (D.supply G).leftTerm A ⊗ₜ[ℚ]
            (resolvedCoproductGenPrimitive
                ((A.1.contractWithStars (D.starOf G A.1)).toResolvedHopfGen (D.hCD G A.1 A.2))
              + (D.supply (A.1.contractWithStars (D.starOf G A.1))).sum))
      = (∑ q ∈ F.forestCarrier with resolvedImageForestFiber F q = A, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier with resolvedImageMixedFiber F q = A, D.resolvedSplitChoiceTerm q.1)

/-- **R-6c-body-62 — body-58's image agreement from the de-contraction cover.**  Rewrite the RIGHT tail by the
proved `coassocRightTail_forestSummand`, then apply the fielded cover. -/
def ResolvedImageFiberCoverSupply.toImageFiberAgreementSupply
    {F : ResolvedCoassocGrandFullSupply D G} (S : ResolvedImageFiberCoverSupply F) :
    ResolvedImageFiberAgreementSupply F where
  image_fiber_agree := fun A hA => by
    rw [D.coassocRightTail_forestSummand G A]
    exact S.image_cover A hA

end GaugeGeometry.QFT.Combinatorial
