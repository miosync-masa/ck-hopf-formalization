import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerRawAggregate

/-!
# R-6c-body-352 — inner-forest retarget = touched-outer-forest retarget (PROVED)

Three-hundred-and-fifty-second genuine-body step — the main trunk of the config board: the `retargetVertex`
of `innerRaw` under the explicit star `touchedInnerStarTotal` COINCIDES with the `retargetVertex` of
`touchedOuterForest` under the original star `D.starOf G z.1.1`, POINTWISE.  Proved once at the vertex level,
then propagated to edges and legs by `congrArg` on the endpoints — no `innerStar_agrees`, no hardcoded star.

## The vertex crux

For `v`, body-351's aggregate vertex equality synchronizes "inside `innerRaw`" with "inside `touchedOuterForest`":

* outside both — each retarget is the identity (`retargetVertex_of_not_mem`);
* inside — `innerRaw.componentAt v` is `toInner`-of a touched component, whose `innerSource` (body-350) is the
  SAME touched component as `touchedOuterForest.componentAt v` (both contain `v`, both in
  `touchedOuterForest.elements`, pairwise-disjoint uniqueness); then `touchedInnerStarTotal_of_mem` +
  `innerSource_spec` make the two stars equal.

`componentAt`'s membership-proof difference is absorbed by proof irrelevance.

Landed axiom-clean:

* `innerRaw_retargetVertex_eq_touched` — the pointwise vertex retarget equality (the crux);
* `innerRaw_retargetEdge_eq_touched` / `innerRaw_retargetExternalLeg_eq_touched` — the edge / leg corollaries.

Per the HALT: only the three retarget equalities are proved; the three graph-data equalities (which are now a
rewrite job over these) and the remnant round-trip are next; `innerStar_agrees`, occurrence, and the remnant
provider are NOT used; the hardcoded `D.starOf parent innerRaw` is NOT touched; no forward quotient / global
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

/-- **R-6c-body-352 — the vertex retarget crux.**  `innerRaw`/`touchedInnerStarTotal` retargets `v` exactly as
`touchedOuterForest`/`D.starOf G z.1.1` does. -/
theorem innerRaw_retargetVertex_eq_touched (v : VertexId) :
    (innerRaw z δ datum hE hL).retargetVertex (touchedInnerStarTotal z δ datum hE hL) v
      = (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) v := by
  by_cases hv : v ∈ (innerRaw z δ datum hE hL).vertices
  · have hv' : v ∈ (touchedOuterForest z δ).vertices := by
      rw [← innerRaw_vertices_eq_touchedOuterForest]; exact hv
    rw [ResolvedAdmissibleSubgraph.retargetVertex,
      ResolvedAdmissibleSubgraph.componentAt?_of_mem _ hv,
      ResolvedAdmissibleSubgraph.retargetVertex,
      ResolvedAdmissibleSubgraph.componentAt?_of_mem _ hv']
    show touchedInnerStarTotal z δ datum hE hL ((innerRaw z δ datum hE hL).componentAt hv)
      = D.starOf G z.1.1 ((touchedOuterForest z δ).componentAt hv')
    rw [touchedInnerStarTotal_of_mem z δ datum hE hL _
      ((innerRaw z δ datum hE hL).componentAt_mem hv)]
    unfold touchedInnerStar
    congr 1
    have hvin : v ∈ (innerSource z δ datum hE hL
        ⟨(innerRaw z δ datum hE hL).componentAt hv,
          (innerRaw z δ datum hE hL).componentAt_mem hv⟩).1.vertices := by
      show v ∈ (toInner z δ datum hE hL (innerSource z δ datum hE hL
        ⟨(innerRaw z δ datum hE hL).componentAt hv,
          (innerRaw z δ datum hE hL).componentAt_mem hv⟩)).vertices
      rw [innerSource_spec z δ datum hE hL
        ⟨(innerRaw z δ datum hE hL).componentAt hv, (innerRaw z δ datum hE hL).componentAt_mem hv⟩]
      exact (innerRaw z δ datum hE hL).componentAt_vertex_mem hv
    have hAmem : (innerSource z δ datum hE hL
        ⟨(innerRaw z δ datum hE hL).componentAt hv,
          (innerRaw z δ datum hE hL).componentAt_mem hv⟩).1 ∈ (touchedOuterForest z δ).elements := by
      rw [touchedOuterForest_elements]
      exact (innerSource z δ datum hE hL
        ⟨(innerRaw z δ datum hE hL).componentAt hv,
          (innerRaw z δ datum hE hL).componentAt_mem hv⟩).2
    by_contra hne
    exact Finset.disjoint_left.mp
      ((touchedOuterForest z δ).pairwiseDisjoint hAmem
        ((touchedOuterForest z δ).componentAt_mem hv') hne)
      hvin ((touchedOuterForest z δ).componentAt_vertex_mem hv')
  · have hv' : v ∉ (touchedOuterForest z δ).vertices := by
      rw [← innerRaw_vertices_eq_touchedOuterForest]; exact hv
    rw [ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ hv,
      ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ hv']

/-- **R-6c-body-352 — the edge retarget corollary.** -/
theorem innerRaw_retargetEdge_eq_touched (e : ResolvedFeynmanEdge) :
    (innerRaw z δ datum hE hL).retargetEdge (touchedInnerStarTotal z δ datum hE hL) e
      = (touchedOuterForest z δ).retargetEdge (D.starOf G z.1.1) e := by
  unfold ResolvedAdmissibleSubgraph.retargetEdge ResolvedFeynmanEdge.retarget
  rw [innerRaw_retargetVertex_eq_touched, innerRaw_retargetVertex_eq_touched]

/-- **R-6c-body-352 — the leg retarget corollary.** -/
theorem innerRaw_retargetExternalLeg_eq_touched (ℓ : ResolvedExternalLeg) :
    (innerRaw z δ datum hE hL).retargetExternalLeg (touchedInnerStarTotal z δ datum hE hL) ℓ
      = (touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1) ℓ := by
  unfold ResolvedAdmissibleSubgraph.retargetExternalLeg ResolvedExternalLeg.retarget
  rw [innerRaw_retargetVertex_eq_touched]

end GaugeGeometry.QFT.Combinatorial
