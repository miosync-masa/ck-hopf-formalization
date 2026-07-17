import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecontractVertexSubset

/-!
# R-6c-body-356 — re-contract vertices: `δ ⊆` half + the full vertex equality (PROVED)

Three-hundred-and-fifty-sixth genuine-body step — the last pipe of the re-contract data section.  The reverse
inclusion `δ.vertices ⊆ (innerRaw.contractWithStars touchedInnerStarTotal).vertices`, closed with NO new datum:
`δ.vertices_subset` splits star / non-star; a star `δ`-vertex is a touched star (body-316); a non-star
`δ`-vertex is covered (body-355 `recontract_vertexCovered`, structural) by a quotient edge / leg preimage
endpoint, which — being non-star, so the retarget is the identity (`starOf_fresh`) — sits in the custom
parent's filter (edge/leg disjunct via `quotientEdgePreimage_map` / `legLift.map_eq`) and off `touchedOuterForest`.

Landed axiom-clean: `delta_vertices_subset_recontract`, `recontract_innerRaw_vertices`.  With bodies 353
(edges/legs) the explicit-star re-contract section's THREE data equalities are now complete.

Per the HALT: only the vertex equality is proved; the remnant round-trip (compose bodies 343/349/353/356 +
`houter`) is next; the hardcoded `D.starOf parent innerRaw` is swapped only via `innerStar_agrees` in the
round-trip body; no forward quotient / global forward round-trip.  No facade, no flat term, no `forgetHopf`, no
rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-356 — the `δ ⊆` half of the re-contract vertex section.** -/
theorem delta_vertices_subset_recontract (Fstar : ResolvedCanonicalStarFacts D)
    (hConn : (touchedLocalComponent z δ).forget.IsConnected)
    (hPos : 0 < (touchedLocalComponent z δ).internalEdges.card) :
    δ.vertices
      ⊆ ((innerRaw z δ datum hE hL).contractWithStars (touchedInnerStarTotal z δ datum hE hL)).vertices := by
  intro v hv
  rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, innerRaw_vertices_eq_touchedOuterForest,
    innerRaw_starVertices_eq_touched, Finset.mem_union]
  have hvsub := δ.vertices_subset hv
  rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hvsub
  rcases hvsub with hvGout | hvstar
  · -- non-star: v ∈ G \ z.1.1
    have hvG : v ∈ G.vertices := (Finset.mem_sdiff.mp hvGout).1
    have hvz : v ∉ z.1.1.vertices := (Finset.mem_sdiff.mp hvGout).2
    have hns : ∀ w, (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) w = v → w = v := by
      intro w hw
      by_cases hwt : w ∈ (touchedOuterForest z δ).vertices
      · exfalso
        rw [ResolvedAdmissibleSubgraph.mem_vertices] at hwt
        obtain ⟨η, hη, hwη⟩ := hwt
        rw [retargetVertex_eq_star_of_mem_element (touchedOuterForest z δ) (D.starOf G z.1.1) hη hwη] at hw
        rw [touchedOuterForest_elements] at hη
        exact Fstar.starOf_fresh G z.1.1 η (mem_touchedOuterComponents.mp hη).1 (hw ▸ hvG)
      · rwa [ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ hwt] at hw
    have hvnottouch : v ∉ (touchedOuterForest z δ).vertices := fun hvt =>
      hvz (touchedOuterForest_vertices_subset z hvt)
    refine Or.inl (Finset.mem_sdiff.mpr ⟨?_, hvnottouch⟩)
    -- v ∈ parentGraph.vertices (the custom parent filter)
    rcases recontract_vertexCovered z δ hConn hPos v hv with hstar | ⟨e, heδ, hend⟩ | ⟨ℓ, hℓδ, hatt⟩
    · exfalso
      rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hstar
      obtain ⟨η, hη, rfl⟩ := hstar
      rw [touchedOuterForest_elements] at hη
      exact Fstar.starOf_fresh G z.1.1 η (mem_touchedOuterComponents.mp hη).1 hvG
    · rw [← quotientEdgePreimage_map] at heδ
      obtain ⟨e0, he0, rfl⟩ := Multiset.mem_map.mp heδ
      show v ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices
      rcases hend with hs | ht
      · refine Finset.mem_filter.mpr ⟨hvG, Or.inr (Or.inl ⟨e0, he0, Or.inl ?_⟩)⟩
        exact hns e0.source hs
      · refine Finset.mem_filter.mpr ⟨hvG, Or.inr (Or.inl ⟨e0, he0, Or.inr ?_⟩)⟩
        exact hns e0.target ht
    · rw [← datum.map_eq] at hℓδ
      obtain ⟨ℓ0, hℓ0, rfl⟩ := Multiset.mem_map.mp hℓδ
      show v ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices
      refine Finset.mem_filter.mpr ⟨hvG, Or.inr (Or.inr ⟨ℓ0, hℓ0, ?_⟩)⟩
      exact hns ℓ0.attachedTo hatt
  · -- star: v ∈ z.1.1.starVertices
    refine Or.inr ?_
    rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hvstar ⊢
    obtain ⟨A, hA, rfl⟩ := hvstar
    refine ⟨A, ?_, rfl⟩
    rw [touchedOuterForest_elements, mem_touchedOuterComponents]
    exact ⟨hA, hv⟩

/-- **R-6c-body-356 — the re-contract's vertices are `δ`'s** (the full vertex equality). -/
theorem recontract_innerRaw_vertices (Fstar : ResolvedCanonicalStarFacts D)
    (hConn : (touchedLocalComponent z δ).forget.IsConnected)
    (hPos : 0 < (touchedLocalComponent z δ).internalEdges.card) :
    ((innerRaw z δ datum hE hL).contractWithStars (touchedInnerStarTotal z δ datum hE hL)).vertices
      = δ.vertices :=
  Finset.Subset.antisymm (recontract_vertices_subset_delta z δ datum hE hL)
    (delta_vertices_subset_recontract z δ datum hE hL Fstar hConn hPos)

end GaugeGeometry.QFT.Combinatorial
