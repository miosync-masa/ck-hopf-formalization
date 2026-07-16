import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTouchedLocalizationVertex
import GaugeGeometry.QFT.HopfAlgebra.ResolvedActualSigmaCover

/-!
# R-6c-body-319 — M1 internal-edge localization: whole↔touched retarget-eq + `internalEdges_le` (PROVED)

Three-hundred-and-nineteenth genuine-body step — M1 (Front 1): the INTERNAL-EDGE obligation of localizing a quotient
component `δ` into `(touchedOuterForest z δ).contractWithStars f`.  It banks the multi-component whole↔touched
retarget-vertex/edge equalities + endpoint classification (the shared core, reused by legs in body-320) and the
internal-edge inclusion.  These are the multi-component analogues of ActualSigmaCover.lean:1321-1480, but LIGHTER: the
touched endpoint classification is DERIVED from `mem_touchedOuterComponents` (a δ-star is a touched star), so NO
`UsesOnlyStar` / `hStarInj` is needed.

## Banked here

* `whole_touched_retargetVertex_eq` — `z.1.1.retargetVertex f v = (touchedOuterForest z δ).retargetVertex f v` when
  `v ∈ touched.vertices ∨ v ∉ z.1.1.vertices` (touched star → same star; outside → identity).
* `touched_vertex_ok` — a `δ`-preimage vertex is in a touched component or outside (derived; no `UsesOnlyStar`).
* `whole_touched_retargetEdge_eq` — the edge version (both endpoints).
* `touched_edge_source_ok` / `touched_edge_target_ok` — endpoints of a `quotientEdgePreimage` edge are touched-or-outside.
* `touchedOuterForest_internalEdges_le` — `touched.internalEdges ≤ z.1.1.internalEdges` (sum over the filtered subset).
* `touchedContractedInternalEdges_le` — `δ.internalEdges ≤ ((touchedOuterForest z δ).contractWithStars f).internalEdges`
  — the M1 internal-edge field.

## Remaining M1 (body-320)

`whole_touched_retargetLeg_eq` + `touched_leg_att_ok` (reuse the shared vertex core) and
`touchedContractedExternalLegs_le : δ.externalLegs ≤ ((touchedOuterForest z δ).contractWithStars f).externalLegs`
(external legs map over `G.externalLegs`, so the complement-inclusion step differs — `quotientLegPreimage_le` lands in
`G.externalLegs` directly, no `complementEdges` subtraction).  Then `TouchedLocalizationData.localComponent` assembles
(value-only); `whole_local_compat` / D2 / CD later.

Per the HALT: only the vertex core + internal-edge inclusion are proved; legs, the `localComponent` assembly, CD, carrier,
and D2 are NOT entered; no singleton `η`; no reliance on the touched enumeration order; endpoint classification is a named
lemma, not a `simp` blast; no facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-319 — whole↔touched retarget-vertex agreement.** -/
theorem whole_touched_retargetVertex_eq {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))) {v : VertexId}
    (hv : v ∈ (touchedOuterForest z δ).vertices ∨ v ∉ z.1.1.vertices) :
    z.1.1.retargetVertex (D.starOf G z.1.1) v
      = (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) v := by
  rcases hv with hvT | hvA
  · rw [ResolvedAdmissibleSubgraph.mem_vertices] at hvT
    obtain ⟨γ, hγT, hvγ⟩ := hvT
    have hγW : γ ∈ z.1.1.elements := by
      rw [touchedOuterForest_elements] at hγT; exact (mem_touchedOuterComponents.mp hγT).1
    rw [retargetVertex_eq_star_of_mem_element z.1.1 (D.starOf G z.1.1) hγW hvγ,
      retargetVertex_eq_star_of_mem_element (touchedOuterForest z δ) (D.starOf G z.1.1) hγT hvγ]
  · have hvT : v ∉ (touchedOuterForest z δ).vertices := fun h =>
      hvA (touchedOuterForest_vertices_subset z h)
    rw [ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem z.1.1 (D.starOf G z.1.1) hvA,
      ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem (touchedOuterForest z δ)
        (D.starOf G z.1.1) hvT]

/-- **R-6c-body-319 — a `δ`-preimage vertex is touched-or-outside** (derived; no `UsesOnlyStar`). -/
theorem touched_vertex_ok {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))) {v : VertexId}
    (hv : z.1.1.retargetVertex (D.starOf G z.1.1) v ∈ δ.vertices) :
    v ∈ (touchedOuterForest z δ).vertices ∨ v ∉ z.1.1.vertices := by
  by_cases hvA : v ∈ z.1.1.vertices
  · left
    have hγ : z.1.1.componentAt hvA ∈ z.1.1.elements := z.1.1.componentAt_mem hvA
    have hvγ : v ∈ (z.1.1.componentAt hvA).vertices := z.1.1.componentAt_vertex_mem hvA
    have hretarget : z.1.1.retargetVertex (D.starOf G z.1.1) v
        = D.starOf G z.1.1 (z.1.1.componentAt hvA) :=
      retargetVertex_eq_star_of_mem_element z.1.1 (D.starOf G z.1.1) hγ hvγ
    have hInδ : D.starOf G z.1.1 (z.1.1.componentAt hvA) ∈ δ.vertices := hretarget ▸ hv
    rw [ResolvedAdmissibleSubgraph.mem_vertices]
    refine ⟨z.1.1.componentAt hvA, ?_, hvγ⟩
    rw [touchedOuterForest_elements]
    exact mem_touchedOuterComponents.mpr ⟨hγ, hInδ⟩
  · right; exact hvA

/-- **R-6c-body-319 — whole↔touched retarget-edge agreement.** -/
theorem whole_touched_retargetEdge_eq {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (e : ResolvedFeynmanEdge)
    (hsrc : e.source ∈ (touchedOuterForest z δ).vertices ∨ e.source ∉ z.1.1.vertices)
    (htgt : e.target ∈ (touchedOuterForest z δ).vertices ∨ e.target ∉ z.1.1.vertices) :
    z.1.1.retargetEdge (D.starOf G z.1.1) e
      = (touchedOuterForest z δ).retargetEdge (D.starOf G z.1.1) e := by
  have h1 := whole_touched_retargetVertex_eq z δ hsrc
  have h2 := whole_touched_retargetVertex_eq z δ htgt
  unfold ResolvedAdmissibleSubgraph.retargetEdge ResolvedFeynmanEdge.retarget
  rw [h1, h2]

/-- **R-6c-body-319 — source endpoint of a `δ`-preimage edge is touched-or-outside.** -/
theorem touched_edge_source_ok {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    {e : ResolvedFeynmanEdge} (he : e ∈ quotientEdgePreimage z.1.1 (D.starOf G z.1.1) δ) :
    e.source ∈ (touchedOuterForest z δ).vertices ∨ e.source ∉ z.1.1.vertices := by
  apply touched_vertex_ok z δ
  have hmem : z.1.1.retargetEdge (D.starOf G z.1.1) e ∈ δ.internalEdges := by
    rw [← quotientEdgePreimage_map z.1.1 (D.starOf G z.1.1) δ]; exact Multiset.mem_map_of_mem _ he
  simpa [ResolvedAdmissibleSubgraph.retargetEdge] using (δ.edges_supported _ hmem).1

/-- **R-6c-body-319 — target endpoint of a `δ`-preimage edge is touched-or-outside.** -/
theorem touched_edge_target_ok {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    {e : ResolvedFeynmanEdge} (he : e ∈ quotientEdgePreimage z.1.1 (D.starOf G z.1.1) δ) :
    e.target ∈ (touchedOuterForest z δ).vertices ∨ e.target ∉ z.1.1.vertices := by
  apply touched_vertex_ok z δ
  have hmem : z.1.1.retargetEdge (D.starOf G z.1.1) e ∈ δ.internalEdges := by
    rw [← quotientEdgePreimage_map z.1.1 (D.starOf G z.1.1) δ]; exact Multiset.mem_map_of_mem _ he
  simpa [ResolvedAdmissibleSubgraph.retargetEdge] using (δ.edges_supported _ hmem).2

/-- **R-6c-body-319 — the touched forest has fewer internal edges** (sum over the filtered subset). -/
theorem touchedOuterForest_internalEdges_le {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))) :
    (touchedOuterForest z δ).internalEdges ≤ z.1.1.internalEdges := by
  apply Finset.sum_le_sum_of_subset
  intro A hA
  rw [touchedOuterForest_elements] at hA
  exact (mem_touchedOuterComponents.mp hA).1

/-- **R-6c-body-319 — the M1 internal-edge field.** -/
theorem touchedContractedInternalEdges_le {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))) :
    δ.internalEdges
      ≤ ((touchedOuterForest z δ).contractWithStars (D.starOf G z.1.1)).internalEdges := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_internalEdges,
    ← quotientEdgePreimage_map z.1.1 (D.starOf G z.1.1) δ,
    Multiset.map_congr rfl (fun e he =>
      whole_touched_retargetEdge_eq z δ e (touched_edge_source_ok z δ he)
        (touched_edge_target_ok z δ he))]
  apply Multiset.map_le_map
  refine le_trans (quotientEdgePreimage_le z.1.1 (D.starOf G z.1.1) δ) ?_
  unfold ResolvedAdmissibleSubgraph.complementEdges
  exact tsub_le_tsub_left (touchedOuterForest_internalEdges_le z δ) _

end GaugeGeometry.QFT.Combinatorial
