import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegroupReindexBody

/-!
# R-6c-body-39 — finite cover carriers scout: alignment to the R-4-full H5.8 reindex

Thirty-ninth genuine-body step, a SCOUT fixing the shape of `ResolvedCoassocGrandFullSupply`'s finite cover
fields and their alignment to the *proved* R-4-full H5.8 reindex machinery — the connection point body-38's two
`*_cover_reindex` leaves must flow through.

## Complete finite-cover field inventory (GrandFull / support-9)

`ResolvedCoassocGrandFullSupply` carries **eight** finite-cover fields (there is no separate `imageImage_mem`
or `image_inj_on` — the image side is pinned by `cover_on` + the two `inj_on`):

| Field | Shape |
|---|---|
| `forestCarrier` | `Finset {s // discriminator (imageOf s)}` — forest-branch split choices |
| `mixedCarrier`  | `Finset {s // ¬ discriminator (imageOf s)}` — mixed-branch split choices |
| `imageCarrier`  | `Finset (ResolvedCoassocQuotientImage D G)` — the image indices |
| `forestImage_mem` | `∀ q ∈ forestCarrier, imageOf q.1 ∈ imageCarrier` |
| `mixedImage_mem`  | `∀ q ∈ mixedCarrier,  imageOf q.1 ∈ imageCarrier` |
| `cover_on`      | `∀ z ∈ imageCarrier, (∃ q ∈ forestCarrier, imageOf q.1 = z) ∨ (∃ q ∈ mixedCarrier, imageOf q.1 = z)` |
| `forest_inj_on` | `imageOf` injective on `forestCarrier` |
| `mixed_inj_on`  | `imageOf` injective on `mixedCarrier` |

## Alignment to `ResolvedFiniteBranchMapLayer.sum_reindex` (the proved partition reindex)

`ResolvedH58Reindex.ResolvedFiniteBranchMapLayer.sum_reindex (w) : ∑ z ∈ imageCarrier, w z = ∑ q ∈
forestCarrier, w (forestImage q) + ∑ q ∈ mixedCarrier, w (mixedImage q)` is the abstract H5.8 partition
reindex, PROVED (via `imageCarrier_eq` = `forestImages ∪ mixedImages` + `disjoint_images` + `Finset.sum_image`).
It needs a layer with `forestImage`/`mixedImage`/`cover`/`forest_inj`/`mixed_inj`/**`cross`** (forest images
disjoint from mixed images).  The GrandFull cover supplies all of these directly — `imageOf` is both
`forestImage` and `mixedImage`, `cover_on` is `cover`, `forest_inj_on`/`mixed_inj_on` are the injectivities —
EXCEPT `cross`, which is not a field but **follows from the discriminator partition** (a forest image satisfies
`discriminator`, a mixed image does not), proved below.

So the GrandFull finite cover feeds the proved `sum_reindex` for the **image ↔ forest+mixed** partition (over
split choices).  The `toGlobalCoverData` / `ofGlobalCoverData` machinery already consumes that internally.

## Where body-38's `*_cover_reindex` leaves land

The two body-38 leaves connect the **outer forest carrier** `(D.supply (repGraph x)).forestCarrier` (proper
forests `A` of the representative) to these split-choice cover sums — the *outer × inner* double sum, i.e. the
R-4-full `outer_sum_reindex` / `concrete_sum_reindex` shape (`ResolvedActualSigmaCover`), NOT the single
partition `sum_reindex`.  That double sum is the genuine remaining H5.8 content; per the HALT it is left named.

Landed:

* `grandFull_forest_image_ne_mixed_image` — the `cross` disjointness (from the discriminator partition), the one
  ingredient the GrandFull cover does not field explicitly; with it the cover feeds `sum_reindex`.

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

/-- **R-6c-body-39 — the `cross` disjointness of the GrandFull cover.**  A forest-branch image satisfies the
star discriminator and a mixed-branch image does not, so their images are never equal — the `cross` ingredient
`ResolvedFiniteBranchMapLayer` needs, not fielded by `ResolvedCoassocGrandFullSupply` but forced by the
discriminator partition of `forestCarrier` / `mixedCarrier`. -/
theorem grandFull_forest_image_ne_mixed_image (F : ResolvedCoassocGrandFullSupply D G)
    (q₁ : {s : ResolvedCoassocSplitChoice D G //
      F.ImageTerm.toImageSideTermSupply.toSplitPhiData.discriminator
        (F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf s)})
    (q₂ : {s : ResolvedCoassocSplitChoice D G //
      ¬ F.ImageTerm.toImageSideTermSupply.toSplitPhiData.discriminator
        (F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf s)}) :
    F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf q₁.1
      ≠ F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf q₂.1 :=
  fun heq => q₂.2 (heq ▸ q₁.2)

end GaugeGeometry.QFT.Combinatorial
