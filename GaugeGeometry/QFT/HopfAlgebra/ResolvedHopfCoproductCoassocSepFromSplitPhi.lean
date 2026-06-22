import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientImage

/-!
# R-6c-4f part 2b — the separation data + weights from the splitPhi skeleton

From a `ResolvedCoassocSplitPhiData` (part 2a), the **separation data** and the **weights** of the
cover are fully determined — only the finite carriers + cover/injectivity remain (the genuine
combinatorics, part 2c).

* The branch split-choice type splits into forest/mixed by the star discriminator applied to the
  splitPhi image: `ForestIdx := {s // discriminator (imageOf s)}`, `MixedIdx := {s // ¬ …}`; the
  branch maps are `imageOf`, and `forest_sat`/`mixed_unsat` are the subtype memberships.
* The forest/mixed **weights** are `resolvedSplitChoiceTerm` on the underlying split choice, and the
  branch agreements `forestWeight_eq`/`mixedWeight_eq` are *exactly* the term agreement `term_eq`.

So once the finite carriers + cover/inj are supplied (a `ResolvedCarrierFiniteBranchMapLayer` over
`toSeparationData`), the `ResolvedH58WeightData` (and hence the whole cover) follows from the splitPhi
skeleton with no extra term work.

Landed:

* `ResolvedCoassocSplitPhiData.toSeparationData` — the resolved branch separation data;
* `ResolvedCoassocSplitPhiData.toWeightData` — the `ResolvedHopfH3` weight data for any layer over
  `toSeparationData`, with the branch agreements discharged by `term_eq`.

No facade, no flat splitPhi theorem, no `forgetHopf`; the finite carriers + cover/inj are deferred.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-4f part 2b — the resolved branch separation data from the splitPhi skeleton.**  The split
choices split into forest/mixed by the star discriminator on their splitPhi image; the branch maps are
`imageOf`, and the saturation facts are the subtype memberships. -/
def ResolvedCoassocSplitPhiData.toSeparationData (P : ResolvedCoassocSplitPhiData D G) :
    ResolvedBranchSeparationData where
  ForestIdx := {s : ResolvedCoassocSplitChoice D G // P.discriminator (P.imageOf s)}
  MixedIdx := {s : ResolvedCoassocSplitChoice D G // ¬ P.discriminator (P.imageOf s)}
  Image := ResolvedCoassocQuotientImage D G
  discriminator := P.discriminator
  forestImage := fun q => P.imageOf q.1
  mixedImage := fun q => P.imageOf q.1
  forest_sat := fun q => q.2
  mixed_unsat := fun q => q.2

/-- **R-6c-4f part 2b — the resolved weight data from the splitPhi skeleton** (for the canonical layer
whose `sep` *is* `toSeparationData`).  The `ResolvedHopfH3` weights are the image weight and the branch
`resolvedSplitChoiceTerm`s; the branch agreements are exactly the term agreement `term_eq` (no cast,
since the carrier indices are definitionally the split-choice subtypes). -/
noncomputable def ResolvedCoassocSplitPhiData.toWeightDataOfLayer
    (P : ResolvedCoassocSplitPhiData D G)
    (forestCarrier : Finset {s : ResolvedCoassocSplitChoice D G // P.discriminator (P.imageOf s)})
    (mixedCarrier : Finset {s : ResolvedCoassocSplitChoice D G // ¬ P.discriminator (P.imageOf s)})
    (imageCarrier : Finset (ResolvedCoassocQuotientImage D G))
    (forestImage_mem : ∀ q ∈ forestCarrier, P.imageOf q.1 ∈ imageCarrier)
    (mixedImage_mem : ∀ q ∈ mixedCarrier, P.imageOf q.1 ∈ imageCarrier)
    (cover_on : ∀ z ∈ imageCarrier,
      (∃ q ∈ forestCarrier, P.imageOf q.1 = z) ∨ (∃ q ∈ mixedCarrier, P.imageOf q.1 = z))
    (forest_inj_on : ∀ q₁ ∈ forestCarrier, ∀ q₂ ∈ forestCarrier,
      P.imageOf q₁.1 = P.imageOf q₂.1 → q₁ = q₂)
    (mixed_inj_on : ∀ q₁ ∈ mixedCarrier, ∀ q₂ ∈ mixedCarrier,
      P.imageOf q₁.1 = P.imageOf q₂.1 → q₁ = q₂) :
    ResolvedH58WeightData
      { sep := P.toSeparationData, forestCarrier := forestCarrier, mixedCarrier := mixedCarrier,
        imageCarrier := imageCarrier, forestImage_mem := forestImage_mem,
        mixedImage_mem := mixedImage_mem, cover_on := cover_on, forest_inj_on := forest_inj_on,
        mixed_inj_on := mixed_inj_on }
      ResolvedHopfH3 where
  imageWeight := P.imageWeight
  forestWeight := fun q => D.resolvedSplitChoiceTerm q.1
  mixedWeight := fun q => D.resolvedSplitChoiceTerm q.1
  forestWeight_eq := fun q => P.term_eq q.1
  mixedWeight_eq := fun q => P.term_eq q.1

end GaugeGeometry.QFT.Combinatorial
