import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageQuotientCoverBody

/-!
# R-6c-body-68 — image_quotient_fiber scout: the term_eq/right_eq tunnel merge, and a boundary-slot concern

Sixty-eighth genuine-body step, a SCOUT connecting `image_quotient_fiber` to the existing `term_eq` / `right_eq`
quotient infrastructure.  The tunnel merges — but the scout also surfaces a structural concern about the
per-`A` boundary placement that corrects body-65's "RIGHT closes per-`A`" reading.

## The tunnel merges: `image_quotient_fiber` IS term_eq/right_eq geometry

The RIGHT fiber sum is exactly a sum of image weights.  `term_eq : resolvedSplitChoiceTerm s =
imageWeight (imageOf s)` (the splitPhiData heart field) rewrites each `selectedOuter = A` fiber's split terms
to image weights (`resolved_image_fiber_termEq_sum` below).  And the concrete image weight factors as

```text
imageWeight z = leftTerm(z.selectedOuter) ⊗ (leftTerm(z.quotientForest) ⊗ innerRightTerm z)
```

(`resolvedCoassocQuotientTerm` = `resolvedSelectedOuterTerm ⊗ strictSummandTerm`), with `right_eq :
(D.supply G).rightTerm s.1 = innerRightTerm (imageOf s)` supplying the inner gen.  So on the `selectedOuter = A`
fiber the sum factors as `leftTerm A ⊗ (∑ strictSummandTerm)` — the quotient graph's own forest de-contraction.
This is a genuine junction: the OUTPUT RIGHT cover and the `term_eq`/`right_eq` tunnels meet here.

## The boundary-slot concern (corrects body-65)

Body-65 proved `splitTerm ⟨A, p₀⟩ = 1 ⊗ (leftTerm A ⊗ rightTerm A)` (the all-right-primitive boundary) and read
this as "the image boundary is a split term, so RIGHT closes per-`A`".  But WHICH fiber is `⟨A, p₀⟩` in?  Its
outer factor is `1 = leftTerm ∅`; under `term_eq` + the image-weight factoring, its `selectedOuter` has
`leftTerm = 1`, i.e. `selectedOuter ⟨A, p₀⟩ = ∅` (consistent with `selectedOuterRaw` = "left-selected ∪
promoted", which is EMPTY when every component is right-primitive).  So `⟨A, p₀⟩` lies in the `selectedOuter = ∅`
fiber, NOT the `selectedOuter = A` fiber (for `A ≠ ∅`).

Consequently the `selectedOuter = A` fiber sum lives in the `leftTerm A ⊗ (ResolvedHopfH ⊗ ResolvedHopfH)`
subspace, while the boundary `1 ⊗ (leftTerm A ⊗ rightTerm A)` lives in the `1 ⊗ (·)` subspace — distinct outer
tensor slots (the monomials `1` and `leftTerm A` are independent for `A ≠ ∅`).  So `image_quotient_fiber`, which
ADDS the boundary split term to the `A`-fiber sum, places it in the wrong outer slot: the per-`A` RIGHT cover
carries a boundary that does not belong to its fiber — MIRRORING body-64's LEFT finding.  Both OUTPUT boundaries
escape the per-`A` fibration; the image boundary IS a split term, but one in the `∅` fiber.

## Decision

The per-`A` OUTPUT fibration (bodies 55/56) attributes the outer boundary `1 ⊗ forestSum` / `forestSum ⊗ 1`
per-`A`, but under `term_eq` that boundary belongs to the `selectedOuter = ∅` contributions, not the nonempty
`A` fibers.  The SATISFIABLE form is body-54's FULL-SUM `outer_image_cover` / `outer_branch_cover`, where the
boundary is one aggregate term.  So the OUTPUT reindex is best completed at the full-sum level (body-54) — the
boundary handled once, the tails fibered — rather than by the per-`A` covers (`image_quotient_fiber` /
`branch_cover_direct`), which misplace the boundary.  The `term_eq`/`right_eq` tunnel (this scout) is the right
machinery for the TAILS; the boundary needs the `∅`-fiber, not a per-`A` slot.

Per the HALT, no retarget / `right_eq` internal proof is entered; the tunnel connection (`term_eq`) is the one
proved lemma; the concern is documented, not forced.

Landed:

* `resolved_image_fiber_termEq_sum` — the RIGHT fiber's split-term sum = its image-weight sum (via `term_eq`),
  the concrete junction to the quotient/`right_eq` world.

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

/-- **R-6c-body-68 — the RIGHT fiber sum is an image-weight sum** (the `term_eq` tunnel connection).  Each
`selectedOuter = A` fiber's split-term sum equals its image-weight sum, by the splitPhiData `term_eq`.  Combined
with `imageWeight z = leftTerm(z.selectedOuter) ⊗ strictSummandTerm z`, this factors the RIGHT fiber sum through
the quotient de-contraction (`right_eq`) world — the junction of the OUTPUT cover and the `term_eq`/`right_eq`
tunnels. -/
theorem resolved_image_fiber_termEq_sum (F : ResolvedCoassocGrandFullSupply D G)
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
