import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCoverShape

/-!
# R-6c-4e — the global splitPhi cover skeleton (correct granularity)

The R-6c-4d' sub-scout fixed the **true global granularity** (the per-`A` family of 4c is
unsatisfiable for multi-component forests, because `Δᵣ(∏ component gens)` deconcatenates into
partial products that cross outer forests).  The correct coordinates mirror the flat
`forestComponentSplitPhi` cover, *globally*:

* **branch carrier** = resolved split choices `(input outer forest A, per-component choice p)`
  (`forestComponentSplitChoiceSigma`-analogue), classified forest / mixed by star-touch;
* **image carrier** = resolved quotient sigmas `(selected outer forest A', quotient subforest B')`
  (`forestQuotientForestSigma`-analogue) — `A'` is the **selected** forest (left-selected + promoted
  components), *not* the input `A`;
* **map** = the resolved `forestComponentSplitPhi` (`forestImage`/`mixedImage`).

This file places the **global cover skeleton** as one bundle, exposing the splitPhi coordinates and —
crucially — naming the **single genuine new theorem** of R-6c: the resolved term agreement
`resolvedSplitPhi_*_term_eq` (the facade-free replay of the *gated* flat
`forestComponentSplitPhi_term_eq_of_split`, now provable because resolved generators are id-bearing —
the R-5 wall dissolves).  Everything else is the existing facade-free reindex spine.

Landed:

* `ResolvedCoassocGlobalCoverData D x` — the global cover bundle: the cover layer `FL` (carrying the
  splitPhi separation via `FL.sep`), the `ResolvedHopfH3` weights, the **term agreements**
  `resolvedSplitPhi_forest_term_eq` / `resolvedSplitPhi_mixed_term_eq`, and the two regroup
  agreements;
* `ResolvedCoassocGlobalCoverData.toCoverShape` — collapse onto the 4a single-FL vessel;
* `ResolvedCoproductH58Compatibility.ofGlobalCoverData` — a per-generator family yields the full
  compatibility, hence `coassoc_gen`.

So R-6c reduces to: build the resolved splitPhi cover (`FL` + weights, reusing the existing resolved
σ-cover machinery globally) and prove `resolvedSplitPhi_*_term_eq` (the one genuine lemma).  No facade,
no flat gated theorem, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

/-- **R-6c-4e — the global splitPhi cover bundle.**  A cover layer `FL` (whose separation `FL.sep`
carries the resolved splitPhi coordinates: forest/mixed split indices, the quotient image type, the
branch maps `forestImage`/`mixedImage`, the star discriminator) together with `ResolvedHopfH3` weights
and the two **term agreements** — the resolved, facade-free replay of the gated flat
`forestComponentSplitPhi_term_eq_of_split`.  The two regroup agreements connect the cover sums to
`regroupImageSum`/`regroupBranchSum`. -/
structure ResolvedCoassocGlobalCoverData (D : ResolvedCoproductProperForestData)
    (x : ResolvedHopfGen) where
  /-- The cover layer (its `sep` carries the resolved splitPhi separation). -/
  FL : ResolvedCarrierFiniteBranchMapLayer
  /-- The image (quotient sigma) weight in `ResolvedHopfH3`. -/
  imageWeight : FL.sep.Image → ResolvedHopfH3
  /-- The forest-branch (split choice) weight. -/
  forestWeight : FL.sep.ForestIdx → ResolvedHopfH3
  /-- The mixed-branch (split choice) weight. -/
  mixedWeight : FL.sep.MixedIdx → ResolvedHopfH3
  /-- **The genuine new theorem (forest branch): the resolved splitPhi term agreement** — the
  facade-free replay of the gated flat `forestComponentSplitPhi_term_eq_of_split`. -/
  resolvedSplitPhi_forest_term_eq : ∀ q, forestWeight q = imageWeight (FL.sep.forestImage q)
  /-- **The genuine new theorem (mixed branch): the resolved splitPhi term agreement.** -/
  resolvedSplitPhi_mixed_term_eq : ∀ q, mixedWeight q = imageWeight (FL.sep.mixedImage q)
  /-- The image side equals the cover's image-weight sum. -/
  image_agreement : D.regroupImageSum x = ∑ z ∈ FL.imageCarrier, imageWeight z
  /-- The cover's (forest + mixed) branch-weight sum equals the branch side. -/
  branch_agreement :
    (∑ q ∈ FL.forestCarrier, forestWeight q) + (∑ q ∈ FL.mixedCarrier, mixedWeight q)
      = D.regroupBranchSum x

namespace ResolvedCoassocGlobalCoverData

variable {D : ResolvedCoproductProperForestData} {x : ResolvedHopfGen}
  (C : ResolvedCoassocGlobalCoverData D x)

/-- The weight data assembled from the global cover bundle (weights + the term agreements). -/
def toWeightData : ResolvedH58WeightData C.FL ResolvedHopfH3 where
  imageWeight := C.imageWeight
  forestWeight := C.forestWeight
  mixedWeight := C.mixedWeight
  forestWeight_eq := C.resolvedSplitPhi_forest_term_eq
  mixedWeight_eq := C.resolvedSplitPhi_mixed_term_eq

/-- The global cover bundle collapses onto the 4a single-FL cover shape. -/
def toCoverShape : ResolvedInnerCoassocCoverShape D x where
  FL := C.FL
  W := C.toWeightData
  image_agreement := C.image_agreement
  branch_agreement := C.branch_agreement

end ResolvedCoassocGlobalCoverData

/-- **R-6c-4e — the global-cover constructor.**  A per-generator family of resolved splitPhi cover
bundles yields the full `ResolvedCoproductH58Compatibility` (via the 4a `ofCoverShape`), hence
`coassoc_gen`.  So resolved coassociativity reduces to building one `ResolvedCoassocGlobalCoverData D
x` per generator — the resolved splitPhi cover plus the term agreement. -/
noncomputable def ResolvedCoproductH58Compatibility.ofGlobalCoverData
    {D : ResolvedCoproductProperForestData}
    (C : ∀ x : ResolvedHopfGen, ResolvedCoassocGlobalCoverData D x) :
    ResolvedCoproductH58Compatibility D :=
  ResolvedCoproductH58Compatibility.ofCoverShape (fun x => (C x).toCoverShape)

end GaugeGeometry.QFT.Combinatorial
