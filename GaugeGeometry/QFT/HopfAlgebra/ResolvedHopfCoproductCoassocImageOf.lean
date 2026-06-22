import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientImage

/-!
# R-6c-4f part 3a — separating the splitPhi map from the term agreement

Design confirmation (R-6c-4f part 3a scout): the image type `ResolvedCoassocQuotientImage`'s
`selectedOuter : {A // A ∈ D.carrier G}` is **correct** — the image-side `regroupImageSum` is a sum
over the carrier forests, so each image element's outer is a carrier forest.  (Concretely the
*selected* outer `A'` of a split choice `(A, p)` is a sub-forest of `A`; its carrier membership holds
when the proper-forest supply is sub-forest-closed — a supply obligation, as in the canonical complete
supply.)  The existing resolved σ-cover uses `Aout : ResolvedAdmissibleSubgraph G` (general) with
`ResolvedActualQuotientImage D := ResolvedAdmissibleSubgraph (D.Aout.contractWithStars D.starOf)` — the
same shape per selected outer, to be assembled globally.

So the concrete `imageOf` (the resolved `forestComponentSplitPhi`) is the remaining de-contraction
build.  This file cleanly **separates the combinatorial map + weights (part 3a) from the term agreement
(part 3b)**: `ResolvedCoassocSplitPhiImageOfData` carries `imageOf`/`imageWeight`/`discriminator`, and
`toSplitPhiData` adds the term agreement `term_eq` to recover the full `ResolvedCoassocSplitPhiData`.

Landed:

* `ResolvedCoassocSplitPhiImageOfData D G` — the splitPhi map + image weight + discriminator (no term
  agreement);
* `ResolvedCoassocSplitPhiImageOfData.toSplitPhiData` — add `term_eq` to recover the full skeleton.

No facade, no flat splitPhi theorem, no `forgetHopf`; the concrete `imageOf` and `term_eq` are the
remaining de-contraction geometry.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-4f part 3a — the splitPhi map data (no term agreement).**  The resolved
`forestComponentSplitPhi` (`imageOf`), the image weight (the quotient term), and the star
discriminator — everything in `ResolvedCoassocSplitPhiData` *except* the term agreement.  This is the
purely combinatorial / weight-level data; supplying it (the concrete de-contraction) is part 3a, and
the term agreement `term_eq` is part 3b. -/
structure ResolvedCoassocSplitPhiImageOfData (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) where
  /-- The resolved `forestComponentSplitPhi`. -/
  imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G
  /-- The image (quotient) weight in `ResolvedHopfH3`. -/
  imageWeight : ResolvedCoassocQuotientImage D G → ResolvedHopfH3
  /-- The star discriminator. -/
  discriminator : ResolvedCoassocQuotientImage D G → Prop

/-- Recover the full splitPhi skeleton by adding the term agreement (part 3b). -/
def ResolvedCoassocSplitPhiImageOfData.toSplitPhiData (I : ResolvedCoassocSplitPhiImageOfData D G)
    (term_eq : ∀ s, D.resolvedSplitChoiceTerm s = I.imageWeight (I.imageOf s)) :
    ResolvedCoassocSplitPhiData D G where
  imageOf := I.imageOf
  imageWeight := I.imageWeight
  discriminator := I.discriminator
  term_eq := term_eq

end GaugeGeometry.QFT.Combinatorial
