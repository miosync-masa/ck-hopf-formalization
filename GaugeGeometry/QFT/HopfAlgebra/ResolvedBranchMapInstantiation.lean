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

/-! ## Step 7D phase 2 — actual-quotient image strategy (scout + discriminator)

**Flat finding.**  `forestQuotientForestSigma g := Σ A : forestOuterProperIndex g,
AdmissibleSubgraph (forestOuterQuotientGraph g A)` — a *dependent Σ*: an outer proper
forest `A` plus an admissible subgraph (a *forest*, with `.elements`) of the
outer-contracted graph.  The discriminator is
`isForestByStar g r := ∃ δ ∈ (ActualQuotientSubgraph g r).elements,
  ¬ Disjoint δ.vertices (r.1.1.starVertices (canonicalStarOf …))`,
i.e. **a component of the actual-quotient forest meets the outer forest's star
vertices** (option (d): a relation between outer-forest stars and the
quotient-forest components).

**Decision.**  Remnant-only `Image` is *ruled out*: the discriminator needs the
quotient *forest* (components) and the outer star vertices, not a single remnant
subgraph.  Within one `ResolvedSigmaCoverData` (fixed `Aout`/`starOf`), the resolved
`Image` is the quotient forest of the contracted graph, and the discriminator is
resolved-native (`D.Aout.starVertices D.starOf` exists). -/

/-- The resolved actual-quotient image (fixed outer forest): an admissible subgraph
(forest) of the contracted graph.  Replaces the remnant-only image. -/
abbrev ResolvedActualQuotientImage (D : ResolvedSigmaCoverData G) :=
  ResolvedAdmissibleSubgraph (D.Aout.contractWithStars D.starOf)

/-- **Resolved `isForestByStar` discriminator.**  Some component of the quotient forest
meets the outer forest's star vertices — the resolved-native mirror of the flat
discriminator. -/
def resolvedIsForestByStar (D : ResolvedSigmaCoverData G)
    (img : ResolvedActualQuotientImage D) : Prop :=
  ∃ δ ∈ img.elements, ¬ Disjoint δ.vertices (D.Aout.starVertices D.starOf)

/-! **Report (7D ph.2).**
1. **Flat `isForestByStar`**: `∃ δ ∈ (ActualQuotientSubgraph r).elements,
   ¬ Disjoint δ.vertices (outer.starVertices …)` — inspects the quotient *forest's*
   components against the outer star vertices.
2. **Chosen `Image`**: `ResolvedActualQuotientImage D =
   ResolvedAdmissibleSubgraph (D.Aout.contractWithStars D.starOf)` (a forest), with
   `resolvedIsForestByStar` the discriminator — both landed here.
3. **Consequence for `forestImage`**: the layer's `forestImage` must be **forest-valued**
   (an actual-quotient forest), *not* the single remnant of phase 1.  So
   `resolvedForestImage` (single remnant) is a per-component building block; the real
   `forestImage` assembles a forest, and `forest_inj` must be proved at the forest level
   (built from the per-component remnant injectivity).  **This is the exact extra data
   the HALT warned about: the image carries a forest, not just a remnant.**
4. **Mixed branch**: can target the *same* `Image` (a quotient forest of the same
   contracted graph) — the mixed-boundary image is another admissible subgraph there.
   `mixed_unsat` is `resolvedIsForestByStar img` failing, i.e. *no* component meets the
   star vertices (the resolved mirror of `…ActualRightQuotientSubgraph_no_starVertices`).
5. **`forest_sat`**: the forest-branch image must contain a component meeting a star —
   the resolved mirror of `…ActualQuotientSubgraph_exists_starVertex`; provable once the
   forest-valued `forestImage` is defined. -/

end GaugeGeometry.QFT.Combinatorial
