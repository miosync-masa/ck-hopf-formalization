import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSepFromSplitPhi

/-!
# R-6c-4f part 2c — the finite cover layer from the splitPhi skeleton

Extending the splitPhi skeleton (`ResolvedCoassocSplitPhiData`) with the **finite carriers + cover +
injectivity** yields the cover layer `FL` and (via part 2b) the weight data `W` — with the injectivity
kept as *fields* (the id-bearing de-contraction injectivity, isolated, not proved inline).

So a `ResolvedCoassocSplitPhiFiniteData` is the last *combinatorial* input: split-choice carriers
classified forest/mixed by the star discriminator, an image carrier, the cover (every image is a
branch image), and the branch injectivities.  Its `toLayer`/`toWeightData` produce the `FL`/`W` that
`ResolvedCoassocGlobalCoverData` needs — leaving only the concrete `imageOf` + `term_eq` (the
de-contraction geometry) and the two regroup agreements.

Landed:

* `ResolvedCoassocSplitPhiFiniteData D G` — the splitPhi skeleton + finite carriers + cover + inj;
* `ResolvedCoassocSplitPhiFiniteData.toLayer` — the `ResolvedCarrierFiniteBranchMapLayer`;
* `ResolvedCoassocSplitPhiFiniteData.toWeightData` — the `ResolvedH58WeightData` over `toLayer`
  (branch agreements discharged by `term_eq`).

No facade, no flat splitPhi theorem, no `forgetHopf`; the concrete `imageOf`/`term_eq` and the carrier
finiteness witnesses are the remaining input.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-4f part 2c — the splitPhi skeleton with finite cover/injectivity.**  Split-choice carriers
classified forest/mixed by the star discriminator on the splitPhi image, an image carrier, the cover
(every image is a branch image), and the branch injectivities (kept as fields — the id-bearing
de-contraction injectivity). -/
structure ResolvedCoassocSplitPhiFiniteData (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) extends ResolvedCoassocSplitPhiData D G where
  /-- The finite forest-classified split-choice carrier. -/
  forestCarrier : Finset {s : ResolvedCoassocSplitChoice D G // discriminator (imageOf s)}
  /-- The finite mixed-classified split-choice carrier. -/
  mixedCarrier : Finset {s : ResolvedCoassocSplitChoice D G // ¬ discriminator (imageOf s)}
  /-- The finite image carrier. -/
  imageCarrier : Finset (ResolvedCoassocQuotientImage D G)
  /-- Forest images land in the image carrier. -/
  forestImage_mem : ∀ q ∈ forestCarrier, imageOf q.1 ∈ imageCarrier
  /-- Mixed images land in the image carrier. -/
  mixedImage_mem : ∀ q ∈ mixedCarrier, imageOf q.1 ∈ imageCarrier
  /-- Cover: every image carrier element is a forest or mixed branch image. -/
  cover_on : ∀ z ∈ imageCarrier,
    (∃ q ∈ forestCarrier, imageOf q.1 = z) ∨ (∃ q ∈ mixedCarrier, imageOf q.1 = z)
  /-- Forest-branch injectivity on the carrier (id-bearing de-contraction injectivity). -/
  forest_inj_on : ∀ q₁ ∈ forestCarrier, ∀ q₂ ∈ forestCarrier,
    imageOf q₁.1 = imageOf q₂.1 → q₁ = q₂
  /-- Mixed-branch injectivity on the carrier. -/
  mixed_inj_on : ∀ q₁ ∈ mixedCarrier, ∀ q₂ ∈ mixedCarrier,
    imageOf q₁.1 = imageOf q₂.1 → q₁ = q₂

/-- **R-6c-4f part 2c — the cover layer.**  The `ResolvedCarrierFiniteBranchMapLayer` over the splitPhi
separation, with the finite carriers + cover + injectivity from the finite data. -/
def ResolvedCoassocSplitPhiFiniteData.toLayer (F : ResolvedCoassocSplitPhiFiniteData D G) :
    ResolvedCarrierFiniteBranchMapLayer where
  sep := F.toResolvedCoassocSplitPhiData.toSeparationData
  forestCarrier := F.forestCarrier
  mixedCarrier := F.mixedCarrier
  imageCarrier := F.imageCarrier
  forestImage_mem := F.forestImage_mem
  mixedImage_mem := F.mixedImage_mem
  cover_on := F.cover_on
  forest_inj_on := F.forest_inj_on
  mixed_inj_on := F.mixed_inj_on

/-- **R-6c-4f part 2c — the weight data over the cover layer.**  The `ResolvedHopfH3` weights with the
branch agreements discharged by the splitPhi `term_eq`. -/
noncomputable def ResolvedCoassocSplitPhiFiniteData.toWeightData
    (F : ResolvedCoassocSplitPhiFiniteData D G) :
    ResolvedH58WeightData F.toLayer ResolvedHopfH3 :=
  F.toResolvedCoassocSplitPhiData.toWeightDataOfLayer
    F.forestCarrier F.mixedCarrier F.imageCarrier
    F.forestImage_mem F.mixedImage_mem F.cover_on F.forest_inj_on F.mixed_inj_on

/-- **R-6c-4f part 2c — the global cover bundle from the finite splitPhi data.**  Given the two
regroup agreements (image side = the cover's image sum; (forest+mixed) split-term sum = branch side),
the finite splitPhi data yields a `ResolvedCoassocGlobalCoverData D x` — and hence (via
`ofGlobalCoverData`) the compatibility and `coassoc_gen`.  All weights/term-agreements come from the
splitPhi skeleton; only the two regroup agreements are supplied here. -/
noncomputable def ResolvedCoassocSplitPhiFiniteData.toGlobalCoverData
    (F : ResolvedCoassocSplitPhiFiniteData D G) (x : ResolvedHopfGen)
    (image_agreement : D.regroupImageSum x = ∑ z ∈ F.imageCarrier, F.imageWeight z)
    (branch_agreement :
      (∑ q ∈ F.forestCarrier, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier, D.resolvedSplitChoiceTerm q.1)
        = D.regroupBranchSum x) :
    ResolvedCoassocGlobalCoverData D x where
  FL := F.toLayer
  imageWeight := F.imageWeight
  forestWeight := fun q => D.resolvedSplitChoiceTerm q.1
  mixedWeight := fun q => D.resolvedSplitChoiceTerm q.1
  resolvedSplitPhi_forest_term_eq := fun q => F.term_eq q.1
  resolvedSplitPhi_mixed_term_eq := fun q => F.term_eq q.1
  image_agreement := image_agreement
  branch_agreement := branch_agreement

end GaugeGeometry.QFT.Combinatorial
