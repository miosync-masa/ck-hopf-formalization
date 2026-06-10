import GaugeGeometry.QFT.HopfAlgebra.ResolvedBranchMap

/-!
# Instantiating `ResolvedBranchMapLayer` — forest side (Track R-4-superfull, Step 7D ph.1)

First concrete win toward instantiating the branch-map layer from actual resolved
σ-index data: fix the forest index and forest image map, and prove `forest_inj`
directly from `ResolvedSigmaCoverData.parentRemnant_injOn`.

**Image strategy (7D-1).**  For the forest side the natural image is the *remnant*
itself — a `ResolvedFeynmanSubgraph (D.Aout.contractWithStars D.starOf)` — because that
is exactly what `parentRemnant_injOn` separates.  We take
`forestImage γ := resolvedParentRemnant D.Aout D.starOf γ`.  Whether this remnant-only
image suffices for the full `ResolvedBranchMapLayer.Image` (which must also host the
mixed images and carry the `isForestByStar` discriminator) is the open question for the
next phase — see the report note.
-/

set_option linter.unusedSectionVars false

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ H : FeynmanGraph, DivergenceMeasure H]
         [∀ H : FeynmanGraph, IsPermInvariantDivergence H]
         [∀ H : FeynmanGraph, IsIsoInvariantDivergence H]
         [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)]
         [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
         [IsDivergencePreservedByAdmissibleForestContract]

variable {G : ResolvedFeynmanGraph}

/-- The forest branch index: the parents of the σ-cover datum. -/
abbrev ResolvedForestIdx (D : ResolvedSigmaCoverData G) :=
  {γ : ResolvedFeynmanSubgraph G // γ ∈ D.parents}

/-- The forest branch image: a parent's remnant under the outer forest. -/
noncomputable def resolvedForestImage (D : ResolvedSigmaCoverData G)
    (γ : ResolvedForestIdx D) :
    ResolvedFeynmanSubgraph (D.Aout.contractWithStars D.starOf) :=
  resolvedParentRemnant D.Aout D.starOf γ.1

/-- **Forest-branch injectivity** — straight from `parentRemnant_injOn`.  This is the
`forest_inj` field of `ResolvedBranchMapLayer`, now constructive on the actual σ-index
parent set. -/
theorem resolvedForestImage_injective (D : ResolvedSigmaCoverData G)
    (hEdgeId : G.EdgeIdsUnique) (hLegId : G.LegIdsUnique) :
    Function.Injective (resolvedForestImage D) := by
  intro x y h
  exact Subtype.ext (D.parentRemnant_injOn hEdgeId hLegId x.2 y.2 h)

/-! **Report (7D ph.1).**
* `ForestIdx := ResolvedForestIdx D = {γ // γ ∈ D.parents}` — landed.
* `forestImage := resolvedForestImage D` (= parent remnant) — landed.
* `forest_inj := resolvedForestImage_injective` (from `parentRemnant_injOn`) — landed.

Remaining for the layer (next phases):
* **Image**: the remnant type `ResolvedFeynmanSubgraph (Aout.contractWithStars starOf)`
  carries the forest image, but the `isForestByStar` discriminator inspects the
  *actual-quotient subgraph's components vs. star vertices*; the remnant is one
  subgraph, not a forest of components, so the discriminator likely needs the image to
  also carry the outer-forest/actual-quotient data.  **Open: does the remnant-only image
  determine `isForestByStar`, or must `Image` be a richer Σ-type (outer + remnant)?**
* **mixedImage / MixedIdx**: the mixed-boundary branch — needs the resolved
  mixed-boundary choice index and its image map (not yet defined).
* **isForestByStar / forest_sat / mixed_unsat**: the resolved discriminator + its two
  branch lemmas (the resolved actual-quotient component-vs-star statement).
* **cover**: branch-map surjectivity onto the image index.

The forest side (`ForestIdx`, `forestImage`, `forest_inj`) is the half tied to the
already-discharged insertion repair; it is closed.  The mixed/discriminator/cover half
is the resolved actual-quotient construction, the next building block. -/

end GaugeGeometry.QFT.Combinatorial
