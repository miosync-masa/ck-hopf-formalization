import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageFiberEquationBody

/-!
# R-6c-body-79 — image `fiber_eq_summand` scout: the concrete imageWeight forces the empty/nonempty split

Seventy-ninth genuine-body step, scouting `fiber_eq_summand` (body-75/78's IMAGE primitive) against the CONCRETE
image weight.  The finding: `fiber_eq_summand` is UNSATISFIABLE for nonempty `A` — the `selectedOuter = A` fiber
lands in the `leftTerm A ⊗ (·)` subspace, which cannot contain the summand's `1 ⊗ (leftTerm A ⊗ rightTerm A)`
boundary.  So the correct per-`A` IMAGE form is empty-boundary + nonempty-tail (body-74's tails-only), with the
sum-level (body-78) carrying the reconciliation.

## The term_eq tunnel + concrete factorization

`term_eq` rewrites each fiber's split-term sum to an image-weight sum (`resolved_image_fiber_imageWeight_sum`).
The image weight is CONCRETE: `imageWeightOf = resolvedCoassocQuotientTerm = resolvedSelectedOuterTerm z ⊗
strictSummandTerm z = leftTerm(z.selectedOuter) ⊗ strictSummandTerm z` (`…QuotientTerm`,
`…TermEqToFullSupply`).  On the `selectedOuter = A` fiber, `z.selectedOuter = A`, so every term is `leftTerm A ⊗
strictSummandTerm z`, and the fiber sum factors:

```text
∑_{selectedOuter = A} splitTerm  =  leftTerm A ⊗ (∑_{selectedOuter = A} strictSummandTerm (imageOf q)).
```

So the `selectedOuter = A` fiber ALWAYS lies in `leftTerm A ⊗ (ResolvedHopfH ⊗ ResolvedHopfH)`.

## The slot obstruction (fiber_eq_summand unsatisfiable for nonempty A)

`fiber_eq_summand` asserts this fiber equals `1 ⊗ (leftTerm A ⊗ rightTerm A) + coassocRightTail A`.  The tail
`coassocRightTail A = leftTerm A ⊗ Δᵣ(rightTerm A)` is in `leftTerm A ⊗ (·)`, but the boundary `1 ⊗ (leftTerm A ⊗
rightTerm A)` is in `1 ⊗ (·)` — a DIFFERENT outer-slot subspace (the monomials `1` and `leftTerm A` are
independent for `A ≠ ∅`).  So for nonempty `A` the fiber (in `leftTerm A ⊗ (·)`) cannot equal the summand
(which has a `1 ⊗ (·)` component): **`fiber_eq_summand` is UNSATISFIABLE for nonempty `A`**, confirming body-68's
slot observation at the concrete image weight.

## The re-scope: empty boundary + nonempty tail

The satisfiable per-`A` form is therefore:

* `A ≠ ∅` (`leftTerm A ≠ 1`): `fiber A = coassocRightTail A` (tails only — body-74's `fiber_eq`), i.e.
  `∑ strictSummandTerm = Δᵣ(rightTerm A)`, the genuine quotient de-contraction (the `right_eq` geometry);
* `A = ∅` (`leftTerm ∅ = 1`): `fiber ∅` lies in `1 ⊗ (·)` and carries the boundary — `∑ strictSummandTerm`
  reassembles into `1 ⊗ forestSum`-shaped contributions.

So `fiber_eq_summand` (the body-78 IMAGE primitive) does NOT hold per-`A`; only its SUM `∑_A fiber A = ∑_A
summand A = ∑ cover` holds (body-73's free fibering + body-78's reconciliation).  The genuine per-`A` IMAGE
content is `strict_summand_cover` (`∑_{selectedOuter = A} strictSummandTerm = Δᵣ(rightTerm A)`, tails), and the
`∅` boundary is a sum-level fact (body-78).  So the canonical IMAGE obligation is either the SUM-level
`outer_image_cover` (body-78, the floor) or, per-`A`, the tails-only `strict_summand_cover` + the `∅` boundary.

Per the HALT: `strict_summand_cover` / `right_eq` is not entered; only the tunnel is proved and the slot
obstruction documented; the empty/nonempty re-scope is fixed.

Landed:

* `resolved_image_fiber_imageWeight_sum` — the `term_eq` tunnel (fiber split-term sum = fiber image-weight sum),
  the connection to the concrete image weight `leftTerm(selectedOuter) ⊗ strictSummandTerm`.

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

/-- **R-6c-body-79 — the image fiber sum is an image-weight sum** (the `term_eq` tunnel, summand context).  Each
`selectedOuter = A` fiber's split-term sum equals its image-weight sum.  Since the concrete image weight is
`leftTerm(selectedOuter) ⊗ strictSummandTerm`, the fiber sum factors as `leftTerm A ⊗ (∑ strictSummandTerm)` —
in the `leftTerm A ⊗ (·)` subspace, which for nonempty `A` cannot contain the summand's `1 ⊗ (·)` boundary. -/
theorem resolved_image_fiber_imageWeight_sum (F : ResolvedCoassocGrandFullSupply D G)
    (A : (D.supply G).ForestIdx) :
    (∑ q ∈ F.forestCarrier with resolvedImageForestFiber F q = A, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier with resolvedImageMixedFiber F q = A, D.resolvedSplitChoiceTerm q.1)
      = (∑ q ∈ F.forestCarrier with resolvedImageForestFiber F q = A,
          F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageWeight
            (F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf q.1))
        + (∑ q ∈ F.mixedCarrier with resolvedImageMixedFiber F q = A,
          F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageWeight
            (F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf q.1)) :=
  congrArg₂ (· + ·)
    (Finset.sum_congr rfl (fun q _ => F.ImageTerm.toImageSideTermSupply.toSplitPhiData.term_eq q.1))
    (Finset.sum_congr rfl (fun q _ => F.ImageTerm.toImageSideTermSupply.toSplitPhiData.term_eq q.1))

end GaugeGeometry.QFT.Combinatorial
