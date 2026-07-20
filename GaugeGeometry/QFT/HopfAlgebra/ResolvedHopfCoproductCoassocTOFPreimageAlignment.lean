import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAmbientRetargetTransport
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTouchedLocalComponent
import GaugeGeometry.QFT.HopfAlgebra.ResolvedActualSigmaCover

/-!
# R-6c-body-437 — the TOF-preimage endpoint alignment; the whole-retarget quotient map (PROVED)

Four-hundred-and-thirty-seventh genuine-body step — closing the forest alignment entirely inside the touched/M1 geometry,
with NO occurrence / `StarProm` / `Wiring` and NO reconciliation of the two `Classical.choose` preimages.  The forest
parent's quotient-edge preimage `Q := quotientEdgePreimage (touchedOuterForest z δ) (D.starOf …) (touchedLocalComponent z
δ)` is keyed to the touched outer forest; its edges' endpoints are shown touched-or-outside *directly*, then the
whole↔touched retarget agreement is applied on `Q`'s support only.

* `touched_vertex_ok_of_local` — the `touchedOuterForest`-retarget analogue of body-319's `touched_vertex_ok`: from
  `TOF.retargetVertex v ∈ δ.vertices`, `v ∈ TOF.vertices ∨ v ∉ z.1.1.vertices`.  The untouched sub-case is impossible by
  star freshness: an untouched outer vertex would have to be a star vertex of the contracted graph, but
  `Fstar.starOf_fresh` puts every star outside `z.1.1`.
* `TOF_qEP_retargetEdge_eq_whole` — for `e ∈ Q`, `TOF.retargetEdge e = z.1.1.retargetEdge e`, from
  `whole_touched_retargetEdge_eq` on the two endpoints (each `TOF.retargetVertex`-in-`δ` via `quotientEdgePreimage_map` +
  `δ.edges_supported`).
* `quotientEdgePreimage_map_whole` — `Q.map (z.1.1.retargetEdge …) = δ.internalEdges`: `Multiset.map_congr` swaps the
  `TOF` retarget for the whole one on `Q`, then `quotientEdgePreimage_map` + `touchedLocalComponent_internalEdges`.

This is exactly the single `map_congr` isolation: the body-438 count transport then reads
`count e Q = count (z.1.1.retargetEdge e) δ.internalEdges` through the body-436 domain-widened `InjOn` tool.

Per the HALT/guards: no `StarProm`/`Wiring`/occurrence/parent-reconstruction; no equality of the two `Classical.choose`
preimages is required; the alignment lives only on `Q`'s support (never on the selected witness `e`); freshness comes from
`Fstar : ResolvedCanonicalStarFacts D` (which `W` supplies), not from occurrence geometry.  No facade, no flat term, no
`forgetHopf`, no rep/perm, and NO strict `star_mapPerm` / `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-body-437 — touched-or-outside from the `touchedOuterForest` retarget.**  If the touched-forest retarget of `v`
lands in `δ`, then `v` is a touched vertex or lies outside the outer forest.  The untouched case is excluded by star
freshness. -/
theorem touched_vertex_ok_of_local (Fstar : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))) {v : VertexId}
    (hv : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) v ∈ δ.vertices) :
    v ∈ (touchedOuterForest z δ).vertices ∨ v ∉ z.1.1.vertices := by
  by_cases hvA : v ∈ z.1.1.vertices
  · left
    by_contra hvT
    rw [ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem (touchedOuterForest z δ)
      (D.starOf G z.1.1) hvT] at hv
    have hvsub := δ.vertices_subset hv
    rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hvsub
    rcases hvsub with hsdiff | hstar
    · exact (Finset.mem_sdiff.mp hsdiff).2 hvA
    · rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hstar
      obtain ⟨η, hη, hstareq⟩ := hstar
      have hvG : v ∈ G.vertices := by
        obtain ⟨γ, hγ, hvγ⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hvA
        exact γ.vertices_subset hvγ
      exact Fstar.starOf_fresh G z.1.1 η hη (hstareq ▸ hvG)
  · right; exact hvA

/-- **R-6c-body-437 — whole↔touched retarget agreement on a `Q`-edge.** -/
theorem TOF_qEP_retargetEdge_eq_whole (Fstar : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    {e : ResolvedFeynmanEdge}
    (he : e ∈ quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1)
        (touchedLocalComponent z δ)) :
    (touchedOuterForest z δ).retargetEdge (D.starOf G z.1.1) e
      = z.1.1.retargetEdge (D.starOf G z.1.1) e := by
  have hmem : (touchedOuterForest z δ).retargetEdge (D.starOf G z.1.1) e ∈ δ.internalEdges := by
    rw [← touchedLocalComponent_internalEdges z δ,
      ← quotientEdgePreimage_map (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ)]
    exact Multiset.mem_map_of_mem _ he
  obtain ⟨hs, ht⟩ := δ.edges_supported _ hmem
  have hs' : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) e.source ∈ δ.vertices := by
    simpa only [ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget_source] using hs
  have ht' : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) e.target ∈ δ.vertices := by
    simpa only [ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget_target] using ht
  exact (whole_touched_retargetEdge_eq z δ e (touched_vertex_ok_of_local Fstar z δ hs')
    (touched_vertex_ok_of_local Fstar z δ ht')).symm

/-- **R-6c-body-437 ∎ — the quotient-edge preimage maps to `δ` under the WHOLE outer retarget.**  Swapping the touched
retarget for the whole one on `Q`'s support (`Multiset.map_congr`), then `quotientEdgePreimage_map` +
`touchedLocalComponent_internalEdges`. -/
theorem quotientEdgePreimage_map_whole (Fstar : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))) :
    (quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1)
        (touchedLocalComponent z δ)).map (z.1.1.retargetEdge (D.starOf G z.1.1))
      = δ.internalEdges := by
  rw [show (quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1)
        (touchedLocalComponent z δ)).map (z.1.1.retargetEdge (D.starOf G z.1.1))
      = (quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1)
        (touchedLocalComponent z δ)).map ((touchedOuterForest z δ).retargetEdge (D.starOf G z.1.1))
      from Multiset.map_congr rfl (fun e he => (TOF_qEP_retargetEdge_eq_whole Fstar z δ he).symm),
    quotientEdgePreimage_map, touchedLocalComponent_internalEdges]

end GaugeGeometry.QFT.Combinatorial
