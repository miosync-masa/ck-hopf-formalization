import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSplitChoice

/-!
# R-6c-4f part 2a — the image index + the resolved splitPhi skeleton

With the branch side concrete (R-6c-4f part 1: `ResolvedCoassocSplitChoice` / `resolvedSplitChoiceTerm`),
this fixes the **image coordinate** and the **`resolvedSplitPhi` signature**, isolating the hard
`selectedOuter` de-contraction as supplied fields.

The image index is concrete, mirroring flat `forestQuotientForestSigma = Σ A', AdmissibleSubgraph
(quotient of A')`: a *selected* outer forest `A'` (which the split choice's left-selected / promoted
components determine) together with a subforest of its star-contraction quotient.

The `resolvedSplitPhi` map (`imageOf`), the image weight (the quotient term), the star discriminator,
and — crucially — the **term agreement** `term_eq` (`resolvedSplitChoiceTerm s = imageWeight (imageOf
s)`, the resolved facade-free replay of the gated flat `forestComponentSplitPhi_term_eq_of_split`) are
isolated as fields of `ResolvedCoassocSplitPhiData`, so the concrete de-contraction construction is the
remaining input.

Landed:

* `ResolvedCoassocQuotientImage D G` — the concrete image index `(selected outer A', quotient subforest
  B')`;
* `ResolvedCoassocSplitPhiData D G` — the splitPhi skeleton: `imageOf` (the resolved splitPhi),
  `imageWeight`, `discriminator`, and the term agreement `term_eq`.

No facade, no flat splitPhi theorem, no `forgetHopf`; the concrete `imageOf`/weights are deferred.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

/-- **R-6c-4f part 2a — the image index.**  A resolved quotient image is a *selected* outer forest
`A'` (a carrier forest, determined by the split choice's left-selected/promoted components) together
with a subforest of its star-contraction quotient.  The resolved analogue of flat
`forestQuotientForestSigma`. -/
structure ResolvedCoassocQuotientImage (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) where
  /-- The selected outer forest `A'` (a carrier forest). -/
  selectedOuter : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}
  /-- A subforest of the star-contraction quotient of `A'`. -/
  quotientForest :
    ResolvedAdmissibleSubgraph (selectedOuter.1.contractWithStars (D.starOf G selectedOuter.1))

/-- **R-6c-4f part 2a — the resolved splitPhi skeleton.**  The resolved `forestComponentSplitPhi`
(`imageOf`), the image weight (the quotient term in `ResolvedHopfH3`), the star discriminator, and the
**term agreement** `term_eq` — the resolved, facade-free replay of the gated flat
`forestComponentSplitPhi_term_eq_of_split`.  Supplying this datum (the concrete de-contraction) is the
remaining geometry. -/
structure ResolvedCoassocSplitPhiData (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) where
  /-- The resolved `forestComponentSplitPhi`: each split choice's image quotient. -/
  imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G
  /-- The image (quotient) weight in `ResolvedHopfH3`. -/
  imageWeight : ResolvedCoassocQuotientImage D G → ResolvedHopfH3
  /-- The star discriminator (forest-branch iff the image touches the stars). -/
  discriminator : ResolvedCoassocQuotientImage D G → Prop
  /-- **The term agreement**: the branch weight of a split choice equals the image weight of its
  splitPhi image.  The resolved, facade-free replay of the gated flat
  `forestComponentSplitPhi_term_eq_of_split`. -/
  term_eq : ∀ s, D.resolvedSplitChoiceTerm s = imageWeight (imageOf s)

end GaugeGeometry.QFT.Combinatorial
