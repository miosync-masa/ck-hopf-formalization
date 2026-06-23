import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageSideSupply

/-!
# R-6c-heart-1 — the concrete resolved quotient term (`imageWeight`)

The heart-scout (2026-06-23) found the decisive gap: there was **no concrete resolved quotient term** —
`imageWeight` was always a supply field, blocking both `term_eq` and `image_agreement`.  This file
defines it, the resolved analogue of flat `forestQuotientForestSigmaTerm` (`Coassoc.lean:14427`):

  `forestQuotientForestSigmaTerm = selectedOuter.toHopfH ⊗ admissibleForestStrictSummandWithCanonicalStars(quotient)`,

where the strict summand is itself `quotientForest.toHopfH ⊗ (inner quotient-of-quotient gen)`.  So the
quotient term is a triple tensor `ResolvedHopfH ⊗ (ResolvedHopfH ⊗ ResolvedHopfH)` = `ResolvedHopfH3`:

  `resolvedCoassocQuotientTerm z = leftTerm(selectedOuter) ⊗ (leftTerm(quotientForest) ⊗ innerRightTerm z)`.

**Two of the three tensor factors are CONCRETE** (both component-generator products, via the existing
`resolvedForestLeftTerm`, which matches the `leftTerm A'` terms appearing in `regroupImageSum`).  Only the
deepest factor — the inner quotient-of-quotient generator (`innerRightTerm`, the gen of the quotient
subforest contracted in the quotient graph) — needs the quotient graph's star + CD (genuine
de-contraction data), so it is **isolated as a supply field** with exact target `ResolvedHopfH` (per the
HALT).  Once supplied, `imageWeightOf := resolvedCoassocQuotientTerm` pins the image weight concretely.

Landed:

* `ResolvedQuotientStrictSummandSupply D G` — the inner-right quotient-of-quotient gen as a supply field;
* `.strictSummandTerm` — `leftTerm(quotientForest) ⊗ innerRightTerm` (the resolved strict summand,
  `ResolvedHopfH ⊗ ResolvedHopfH`);
* `.resolvedCoassocQuotientTerm` — `leftTerm(selectedOuter) ⊗ strictSummandTerm` (the concrete quotient
  term, `ResolvedHopfH3`);
* `.toImageSideSupply` — build a `ResolvedCoassocImageSideSupply` with `imageWeightOf :=
  resolvedCoassocQuotientTerm` (the rest still supply), confirming the image weight is now concrete.

No facade, no flat term, no `forgetHopf`; `term_eq` / `image_agreement` and the de-contraction bodies
(including the inner-right gen) are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-1 — the selected-outer tensor factor (concrete).**  The outer factor of the quotient
term: the product of the selected outer forest's component generators.  This is exactly the `leftTerm A'`
that appears in `regroupImageSum` (`(D.supply G).leftTerm z.selectedOuter = resolvedForestLeftTerm
z.selectedOuter.1` by `rfl`). -/
noncomputable def resolvedSelectedOuterTerm
    (z : ResolvedCoassocQuotientImage D G) : ResolvedHopfH :=
  resolvedForestLeftTerm z.selectedOuter.1

/-- **R-6c-heart-1 — the inner quotient-of-quotient generator, isolated as supply.**  The deepest
(inner-right) tensor factor of the quotient term: the generator of the quotient subforest contracted in
the quotient graph (the resolved analogue of the inner gen of `admissibleForestStrictSummandWithCanonical
Stars`).  It needs the quotient graph's star + CD (genuine de-contraction data), so it is a supply field
with exact target `ResolvedHopfH`. -/
structure ResolvedQuotientStrictSummandSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) where
  /-- The inner quotient-of-quotient generator term (the strict summand's right factor). -/
  innerRightTerm : ResolvedCoassocQuotientImage D G → ResolvedHopfH

/-- **R-6c-heart-1 — the resolved strict summand term.**  `leftTerm(quotientForest) ⊗ innerRightTerm` —
the resolved analogue of `admissibleForestStrictSummandWithCanonicalStars`: the quotient subforest's
component-generator product tensored with the inner quotient-of-quotient generator.  The inner-left factor
is concrete (`resolvedForestLeftTerm` over the quotient graph); only the inner-right is supplied. -/
noncomputable def ResolvedQuotientStrictSummandSupply.strictSummandTerm
    (T : ResolvedQuotientStrictSummandSupply D G) (z : ResolvedCoassocQuotientImage D G) :
    ResolvedHopfH ⊗[ℚ] ResolvedHopfH :=
  resolvedForestLeftTerm z.quotientForest ⊗ₜ[ℚ] T.innerRightTerm z

/-- **R-6c-heart-1 — the concrete resolved quotient term.**  `leftTerm(selectedOuter) ⊗ strictSummand` —
the resolved analogue of flat `forestQuotientForestSigmaTerm`, in `ResolvedHopfH3`.  Two of the three
tensor factors are concrete (selectedOuter + quotientForest component products); the inner-right gen is
supplied.  This is the value to use for `imageWeightOf`. -/
noncomputable def ResolvedQuotientStrictSummandSupply.resolvedCoassocQuotientTerm
    (T : ResolvedQuotientStrictSummandSupply D G) (z : ResolvedCoassocQuotientImage D G) :
    ResolvedHopfH3 :=
  resolvedSelectedOuterTerm z ⊗ₜ[ℚ] T.strictSummandTerm z

/-- **R-6c-heart-1 — image side with the concrete quotient term.**  Build a
`ResolvedCoassocImageSideSupply` whose `imageWeightOf` is the concrete `resolvedCoassocQuotientTerm`
(the selected-outer + quotient supplies and the discriminator still supplied).  Confirms the image
weight is now a concrete definition, not an abstract field. -/
noncomputable def ResolvedQuotientStrictSummandSupply.toImageSideSupply
    (T : ResolvedQuotientStrictSummandSupply D G)
    (selected : ResolvedCoassocSelectedOuterImageSupply D G)
    (quotient : ResolvedCoassocQuotientForestSupply D G selected)
    (discriminatorOf : ResolvedCoassocQuotientImage D G → Prop) :
    ResolvedCoassocImageSideSupply D G where
  selected := selected
  quotient := quotient
  imageWeightOf := T.resolvedCoassocQuotientTerm
  discriminatorOf := discriminatorOf

end GaugeGeometry.QFT.Combinatorial
