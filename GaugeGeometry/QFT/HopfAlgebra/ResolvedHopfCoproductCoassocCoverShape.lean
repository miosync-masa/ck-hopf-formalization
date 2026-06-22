import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocChoiceVessel

/-!
# R-6c-4a — the inner σ-cover shape (the last vessel)

The final geometry is the inner σ-cover.  Rather than wrestle the cover carriers/weights directly into
`ResolvedH58TermReindex` and `ResolvedInnerCoassocSigmaCoverData`, this file places the **cover shape
vessel**: a finite cover layer `FL` and resolved-`ResolvedHopfH3` weights `W`, together with the two
agreements stated against the *explicit* regrouped sums

  `image_agreement  : regroupImageSum x  = ∑ z ∈ FL.imageCarrier, W.imageWeight z`
  `branch_agreement : (∑ forest W.forestWeight) + (∑ mixed W.mixedWeight) = regroupBranchSum x`.

Since `ResolvedH58TermReindex.imageSum`/`.branchSum` are *definitionally* those sums, the shape
collapses straight onto `ResolvedInnerCoassocSigmaCoverData` (and thence, via
`ofInnerCoassocSigmaCover`, onto the full compatibility and `coassoc_gen`).  So all of resolved
coassociativity now reduces to constructing one `ResolvedInnerCoassocCoverShape D x` per generator —
build `FL`, `W`, and prove the two agreements (image side fed by `ImageSide`, branch side by
`BranchSide`/`ChoiceVessel`).

Landed:

* `ResolvedInnerCoassocCoverShape D x` — the cover-shape vessel;
* `ResolvedInnerCoassocCoverShape.toTermReindex` / `toSigmaCoverData` — the collapse onto the bridge
  datum;
* `ResolvedCoproductH58Compatibility.ofCoverShape` — a per-generator family of cover shapes yields the
  full compatibility, hence `coassoc_gen`.

No facade, no flat term, no `forgetHopf`; the cover carriers/weights themselves are the remaining
de-contraction geometry.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

/-- **R-6c-4a — the inner σ-cover shape vessel.**  A finite cover layer with resolved-`ResolvedHopfH3`
weights, plus the two agreements identifying the cover's image-side sum with `regroupImageSum` and its
(forest + mixed) branch-side sum with `regroupBranchSum`. -/
structure ResolvedInnerCoassocCoverShape (D : ResolvedCoproductProperForestData)
    (x : ResolvedHopfGen) where
  /-- The finite cover layer (forest/mixed/image carriers, cover, injectivity). -/
  FL : ResolvedCarrierFiniteBranchMapLayer
  /-- The resolved-term weights (image + forest/mixed branch, with branch agreements). -/
  W : ResolvedH58WeightData FL ResolvedHopfH3
  /-- The image side equals the cover's image-weight sum. -/
  image_agreement : D.regroupImageSum x = ∑ z ∈ FL.imageCarrier, W.imageWeight z
  /-- The cover's (forest + mixed) branch-weight sum equals the branch side. -/
  branch_agreement :
    (∑ q ∈ FL.forestCarrier, W.forestWeight q) + (∑ q ∈ FL.mixedCarrier, W.mixedWeight q)
      = D.regroupBranchSum x

namespace ResolvedInnerCoassocCoverShape

variable {D : ResolvedCoproductProperForestData} {x : ResolvedHopfGen}
  (S : ResolvedInnerCoassocCoverShape D x)

/-- The cover-shape vessel as a resolved-term cover reindex. -/
noncomputable def toTermReindex : ResolvedH58TermReindex where
  FL := S.FL
  W := S.W

/-- The cover shape collapses onto the inner-σ-cover bridge datum (the agreements match the
`ResolvedH58TermReindex.imageSum`/`.branchSum` definitions). -/
noncomputable def toSigmaCoverData : ResolvedInnerCoassocSigmaCoverData D x where
  termReindex := S.toTermReindex
  image_agreement := S.image_agreement
  branch_agreement := S.branch_agreement

end ResolvedInnerCoassocCoverShape

/-- **R-6c-4a — the cover-shape constructor.**  A per-generator family of inner σ-cover shapes yields
the full `ResolvedCoproductH58Compatibility` (via `ofInnerCoassocSigmaCover`), hence `coassoc_gen`.
All of resolved coassociativity now reduces to constructing one `ResolvedInnerCoassocCoverShape D x`
per generator. -/
noncomputable def ResolvedCoproductH58Compatibility.ofCoverShape
    {D : ResolvedCoproductProperForestData}
    (S : ∀ x : ResolvedHopfGen, ResolvedInnerCoassocCoverShape D x) :
    ResolvedCoproductH58Compatibility D :=
  ResolvedCoproductH58Compatibility.ofInnerCoassocSigmaCover (fun x => (S x).toSigmaCoverData)

end GaugeGeometry.QFT.Combinatorial
