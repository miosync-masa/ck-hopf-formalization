import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerStarImage

/-!
# R-6c-body-355 — re-contract vertices, `⊆ δ` half + the coverage is structural (no new datum) (PROVED)

Three-hundred-and-fifty-fifth genuine-body step — the re-contract vertex section, the easy inclusion plus the
scout verdict that the hard inclusion needs NO new datum.

## The `⊆ δ` half (PROVED)

After `contractWithStars_vertices` + body-351 (`innerRaw.vertices = touchedOuterForest.vertices`) + body-354
(star image), `((innerRaw).contractWithStars touchedInnerStarTotal).vertices` is
`(parentGraph.vertices \ touchedOuterForest.vertices) ∪ touchedOuterForest.starVertices (D.starOf G z.1.1)`;
each piece lands in `δ.vertices`:

* the difference — `localizedParentVertex_retargets` (body-329) sends every parent vertex into `δ.vertices`, and
  off `touchedOuterForest` the retarget is the identity, so `v ∈ δ.vertices`;
* the star image — `mem_touchedOuterComponents` (body-316) is BY DEFINITION `D.starOf G z.1.1 A ∈ δ.vertices`.

## Verdict on the `δ ⊆` half — structural, no per-image datum

The base version documented the reverse as a "structural obstruction" for the WHOLE-`Aout` parent (all outer
stars end up in the remnant, ActualSigmaCover:1000-1045).  Our custom parent is built over
`touchedOuterForest` (exactly `δ`'s touched stars), so the obstruction is AVOIDED.  The base's `δ ⊆`
saturation `QuotientVertexCovered` is DERIVED — not a datum — from connectivity + edge-positivity
(`quotientVertexCovered_of_connected_pos`, ActualSigmaCover:1184), both inside `δ`'s CD datum
(`z.2.1.isConnectedDivergent`).  Banked here as `recontract_vertexCovered`.  So the `δ ⊆` inclusion (body-356)
closes by: `δ.vertices_subset` splits star / non-star; star ⟹ `touchedOuterComponents` (right of `∪`);
non-star ⟹ `recontract_vertexCovered`'s edge/leg endpoint sits in the parent's filter (edge/leg disjunct via
`quotientEdgePreimage_map` / `legLift`), and is off `touchedOuterForest` — the difference side.  NO new datum.

Landed axiom-clean: `recontract_vertices_subset_delta`, `recontract_vertexCovered`.

Per the HALT: only the `⊆ δ` inclusion and the structural coverage are proved; the `δ ⊆` inclusion (hence the
vertex equality) and the remnant round-trip are next; `innerStar_agrees` and the hardcoded `D.starOf parent
innerRaw` are NOT used; no forward quotient / global forward round-trip.  No facade, no flat term, no
`forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-355 — the `⊆ δ` half of the re-contract vertex section.** -/
theorem recontract_vertices_subset_delta :
    ((innerRaw z δ datum hE hL).contractWithStars (touchedInnerStarTotal z δ datum hE hL)).vertices
      ⊆ δ.vertices := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, innerRaw_vertices_eq_touchedOuterForest,
    innerRaw_starVertices_eq_touched]
  intro v hv
  rw [Finset.mem_union] at hv
  rcases hv with hvdiff | hvstar
  · rw [Finset.mem_sdiff] at hvdiff
    obtain ⟨hvparent, hvnottouch⟩ := hvdiff
    have hret := localizedParentVertex_retargets z δ datum hE hL hvparent
    rwa [ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ hvnottouch] at hret
  · rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hvstar
    obtain ⟨A, hA, rfl⟩ := hvstar
    rw [touchedOuterForest_elements] at hA
    exact (mem_touchedOuterComponents.mp hA).2

/-- **R-6c-body-355 — the quotient vertex coverage is structural** (derived from `touchedLocalComponent`'s
connectivity + edge-positivity — `touchedLocalComponent` carries `δ`'s data over `touchedOuterForest`'s
contraction — no per-image datum). -/
theorem recontract_vertexCovered (hConn : (touchedLocalComponent z δ).forget.IsConnected)
    (hPos : 0 < (touchedLocalComponent z δ).internalEdges.card) :
    QuotientVertexCovered (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ) :=
  quotientVertexCovered_of_connected_pos (touchedOuterForest z δ) (D.starOf G z.1.1) hConn hPos

end GaugeGeometry.QFT.Combinatorial
