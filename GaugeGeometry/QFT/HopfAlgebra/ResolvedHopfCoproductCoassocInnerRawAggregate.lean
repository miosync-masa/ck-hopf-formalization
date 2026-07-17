import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerSourceSelector

/-!
# R-6c-body-351 — inner-forest aggregate = touched outer forest + the total explicit star (PROVED)

Three-hundred-and-fifty-first genuine-body step — the "section vocabulary" bridge for the explicit-star
re-contract data section (body-349's layer 1).  `innerRaw` is `toInner`-image of the touched outer components
(body-328), and `toInner` keeps the three carrier data (body-327), so `innerRaw`'s AGGREGATE vertices/internal
edges coincide with the touched outer FOREST's — bringing the custom parent's inner forest back into the
`touchedOuterForest` vocabulary.  Plus the `dite`-extended total star map for `contractWithStars`.

Landed axiom-clean:

* `touchedInnerStarTotal` / `touchedInnerStarTotal_of_mem` — the total explicit star (member-limited spec);
* `innerRaw_vertices_eq_touchedOuterForest` — `innerRaw.vertices = touchedOuterForest.vertices`;
* `innerRaw_internalEdges_eq_touchedOuterForest` — `innerRaw.internalEdges = touchedOuterForest.internalEdges`.

## The remaining three graph-data equalities (audit, next body)

`contractedSourceGraph = innerRaw.contractWithStars starMap` unfolds (Combinatorial contract) to

```text
vertices     = (parentGraph.vertices \ innerRaw.vertices) ∪ innerRaw.starVertices starMap
internalEdges = innerRaw.complementEdges.map (retargetEdge starMap)
externalLegs  = parentGraph.externalLegs.map (retargetExternalLeg starMap)
```

with `parentGraph = (localizedParentWithTouchedLegs …).tRFG` (`internalEdges = touchedOuterForest.internalEdges
+ quotientEdgePreimage …`, `externalLegs = datum.legs`, TouchedLegLiftDatum.lean:105-107).  So, using
`innerRaw.vertices = touchedOuterForest.vertices` and `innerRaw.internalEdges = touchedOuterForest.internalEdges`
(this body) hence `innerRaw.complementEdges = quotientEdgePreimage …`:

```text
internalEdges = quotientEdgePreimage(…).map (retargetEdge touchedInnerStarTotal)   →  δ.1.internalEdges   (quotientEdgePreimage_map)
externalLegs  = datum.legs.map (retargetExternalLeg touchedInnerStarTotal)         →  δ.1.externalLegs    (legLift.map_eq)
vertices      = (parentGraph.vertices \ touchedOuterForest.vertices) ∪ (innerRaw stars)  →  δ.1.vertices    (parent vertex section)
```

CAUTION (star-map alignment): the RHS section lemmas (`quotientEdgePreimage_map`, `legLift.map_eq`) are keyed
to `touchedOuterForest`'s retarget under `D.starOf G z.1.1`, whereas the LHS retargets under
`touchedInnerStarTotal` (on `innerRaw`).  Since `touchedInnerStar B = D.starOf G z.1.1 (innerSource B).1` and
`innerSource (toInner A) = A` (body-350), the two star VALUES agree on the touched components BY CONSTRUCTION
(NOT `innerStar_agrees`), but the two `retargetVertex`s use different `componentAt` structures
(`innerRaw` vs `touchedOuterForest`); the mechanical body must bridge them by member-congruence
(`∀ B ∈ innerRaw.elements, touchedInnerStarTotal B = touchedInnerStar …`) — no whole-function equality.

Per the HALT: only the aggregate bridge + the total star are proved; the three graph-data equalities are the
next body; `innerStar_agrees`, occurrence, and the remnant provider are NOT used; no forward quotient / global
forward round-trip.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` /
singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  (z : ForestBlockCodType D G)
  (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
  (datum : ResolvedTouchedLegLiftDatum z δ)
  (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
  (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)

set_option linter.unusedSectionVars false

/-- **R-6c-body-351 — the `dite`-extended total explicit star.**  On the inner forest's components it is
`touchedInnerStar`; off them, the harmless hardcoded fallback (never read by `contractWithStars`). -/
noncomputable def touchedInnerStarTotal
    (B : ResolvedFeynmanSubgraph (localizedParentWithTouchedLegs z δ datum hE hL).toResolvedFeynmanGraph) :
    VertexId :=
  if hB : B ∈ (innerRaw z δ datum hE hL).elements then touchedInnerStar z δ datum hE hL ⟨B, hB⟩
  else D.starOf (localizedParentWithTouchedLegs z δ datum hE hL).toResolvedFeynmanGraph
    (innerRaw z δ datum hE hL) B

/-- **R-6c-body-351 — the total star on a member is `touchedInnerStar`.** -/
theorem touchedInnerStarTotal_of_mem
    (B : ResolvedFeynmanSubgraph (localizedParentWithTouchedLegs z δ datum hE hL).toResolvedFeynmanGraph)
    (hB : B ∈ (innerRaw z δ datum hE hL).elements) :
    touchedInnerStarTotal z δ datum hE hL B = touchedInnerStar z δ datum hE hL ⟨B, hB⟩ :=
  dif_pos hB

/-- **R-6c-body-351 — inner forest aggregate vertices = touched outer forest vertices.** -/
theorem innerRaw_vertices_eq_touchedOuterForest :
    (innerRaw z δ datum hE hL).vertices = (touchedOuterForest z δ).vertices := by
  ext v
  rw [ResolvedAdmissibleSubgraph.mem_vertices, ResolvedAdmissibleSubgraph.mem_vertices]
  constructor
  · rintro ⟨B, hB, hvB⟩
    rw [innerRaw_elements] at hB
    obtain ⟨A, -, rfl⟩ := Finset.mem_image.mp hB
    exact ⟨A.1, by rw [touchedOuterForest_elements]; exact A.2, hvB⟩
  · rintro ⟨A, hA, hvA⟩
    rw [touchedOuterForest_elements] at hA
    refine ⟨toInner z δ datum hE hL ⟨A, hA⟩, ?_, hvA⟩
    rw [innerRaw_elements]
    exact Finset.mem_image.mpr ⟨⟨A, hA⟩, Finset.mem_attach _ _, rfl⟩

/-- **R-6c-body-351 — inner forest aggregate internal edges = touched outer forest internal edges.** -/
theorem innerRaw_internalEdges_eq_touchedOuterForest :
    (innerRaw z δ datum hE hL).internalEdges = (touchedOuterForest z δ).internalEdges := by
  rw [ResolvedAdmissibleSubgraph.internalEdges, innerRaw_elements,
    Finset.sum_image (fun a _ b _ h => toInner_injective z δ datum hE hL h),
    ResolvedAdmissibleSubgraph.internalEdges, touchedOuterForest_elements]
  exact Finset.sum_attach (touchedOuterComponents z δ) (fun γ => γ.internalEdges)

end GaugeGeometry.QFT.Combinatorial
