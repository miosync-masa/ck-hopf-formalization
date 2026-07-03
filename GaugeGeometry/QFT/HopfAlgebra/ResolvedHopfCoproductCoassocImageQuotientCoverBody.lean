import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageCoverBody

/-!
# R-6c-body-66 — image quotient cover scout: the RIGHT cover is `leftTerm A ⊗ Δᵣ(rightTerm A)`

Sixty-sixth genuine-body step.  Body-65 discharged the image boundary (it IS the all-right-primitive split
term), leaving `image_cover_quotient` as the genuine RIGHT de-contraction.  Here that residue is put in its
natural form — the localized second coproduct — exposing exactly the `right_eq` quotient geometry.

## The quotient part is `leftTerm A ⊗ Δᵣ(rightTerm A)`

`coproduct_rightTerm` gives `D.coproduct (rightTerm A) = primitive (quot gen A) + (quot graph A).sum`.  So
body-65's `image_cover_quotient` residue `leftTerm A ⊗ (primitive (quot gen A) + (quot graph A).sum)` is exactly
`leftTerm A ⊗ D.coproduct (rightTerm A)` — the outer forest `A` held on the left while its quotient generator
`rightTerm A` undergoes a SECOND resolved coproduct.  This is the `(1 ⊗ Δᵣ) ∘ Δᵣ` structure localized to the
single outer forest `A`, and its `Δᵣ(rightTerm A)` de-contracts into the quotient graph's own forests
(`(quot graph A).sum`) plus the quotient primitive — precisely the `right_eq` / retarget quotient world.

## The reduced obligation

With the boundary written as its split term (body-65) and the quotient part as the second coproduct, the RIGHT
cover reads:

```text
resolvedSplitChoiceTerm ⟨A, p₀⟩  +  leftTerm A ⊗ Δᵣ(rightTerm A)
  = (∑ q ∈ F.forestCarrier with selectedOuter (imageOf q.1) = A, splitTerm q.1)
      + (∑ q ∈ F.mixedCarrier with selectedOuter (imageOf q.1) = A, splitTerm q.1).
```

Conceptually the `selectedOuter = A` fibers split into the all-right-primitive boundary `⟨A, p₀⟩` (the trivial
"quotient stays whole" choice) and the nontrivial quotient choices, whose split terms realise
`leftTerm A ⊗ Δᵣ(rightTerm A)` — the quotient graph's forest de-contraction reindexed onto the image fibers.
This aggregate identity is the genuine RIGHT inner content, fielded as
`ResolvedImageQuotientFiberSupply.image_quotient_fiber`.  Its proof is the quotient de-contraction bijection
(the `right_eq` geometry), NOT entered here.

## Result

`image_cover_quotient` reduces to `image_quotient_fiber` — the same identity with the quotient part folded to the
readable `leftTerm A ⊗ Δᵣ(rightTerm A)`.  So the RIGHT OUTPUT leaf is now explicitly the second-coproduct
de-contraction cover, connecting the OUTPUT reindex to the `right_eq` quotient geometry.

Per the HALT, the quotient de-contraction bijection is NOT proved (it is `image_quotient_fiber`); only the
coproduct restatement (`coproduct_rightTerm`) is used; no retarget / star-allocation body is entered.

Landed:

* `ResolvedImageQuotientFiberSupply F` — the RIGHT cover as `boundary split term + leftTerm A ⊗ Δᵣ(rightTerm A) =
  selectedOuter-`A` fibers`;
* `ResolvedImageQuotientFiberSupply.toImageQuotientCoverSupply` — recovers body-65's `image_cover_quotient`.

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

/-- **R-6c-body-66 — the RIGHT quotient de-contraction cover** in second-coproduct form.  The all-right-primitive
boundary split term plus `leftTerm A ⊗ Δᵣ(rightTerm A)` (the localized `(1 ⊗ Δᵣ)` on the quotient) equals the
`selectedOuter = A` image fiber sum.  The genuine RIGHT inner content — the quotient graph's forest
de-contraction — is this fielded identity (the `right_eq` geometry). -/
structure ResolvedImageQuotientFiberSupply (F : ResolvedCoassocGrandFullSupply D G) where
  /-- Boundary split term + `leftTerm A ⊗ Δᵣ(rightTerm A)` = the `selectedOuter = A` fiber sum. -/
  image_quotient_fiber : ∀ A ∈ (D.supply G).forestCarrier,
    (D.resolvedSplitChoiceTerm (⟨A, fun _ _ => Sum.inl false⟩ : ResolvedCoassocSplitChoice D G)
        + (D.supply G).leftTerm A ⊗ₜ[ℚ] D.coproduct ((D.supply G).rightTerm A))
      = (∑ q ∈ F.forestCarrier with resolvedImageForestFiber F q = A, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier with resolvedImageMixedFiber F q = A, D.resolvedSplitChoiceTerm q.1)

/-- **R-6c-body-66 — body-65's quotient cover from the second-coproduct form.**  Unfold `Δᵣ(rightTerm A)` to
`primitive + (quot graph).sum` via `coproduct_rightTerm`. -/
def ResolvedImageQuotientFiberSupply.toImageQuotientCoverSupply
    {F : ResolvedCoassocGrandFullSupply D G} (S : ResolvedImageQuotientFiberSupply F) :
    ResolvedImageQuotientCoverSupply F where
  image_cover_quotient := fun A hA => by
    rw [← D.coproduct_rightTerm G A]
    exact S.image_quotient_fiber A hA

end GaugeGeometry.QFT.Combinatorial
