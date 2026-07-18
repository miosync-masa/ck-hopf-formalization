import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocParentExternalLegsConcrete
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCarrierProperProvider
import GaugeGeometry.QFT.HopfAlgebra.ResolvedSigmaSaturation

/-!
# R-6c-body-389 — bank-3b: the parent-section vertices projection, recovered as a THEOREM (PROVED)

Three-hundred-and-eighty-ninth genuine-body step — the THIRD and last parent/remnant projection.  Audit finding: the
vertex equality does NOT consume `externalLegs`; it closes on `internalEdges` equality (body-387) + no-isolated-vertex
alone — the minimal dependency.  Under `hEdgeId` (via body-387) it is a THEOREM:
`(Core.parent (fwd q) δ).vertices = o.γ.1.vertices`.

Both inclusions are symmetric, each a single application of the resolved no-isolated-vertex coverage lemma
`resolvedSubgraph_vertex_incident_edge_of_connected_pos` (a connected, positively-edged subgraph has every vertex on one
of its own internal edges), then transporting that edge across the `internalEdges` equality and reading its endpoints:

* **parent ⊆ o.γ.1** — `Core.parent` is connected (`parentCD`) and positively edged (`hEdges` + `hγPos`); an incident
  edge lands in `o.γ.1.internalEdges` (`hEdges`), whose endpoints are `o.γ.1`-vertices (`edges_supported`).
* **o.γ.1 ⊆ parent** — `o.γ.1` is connected (`isConnectedDivergent`) and positively edged (`carrier_isProperForest`); an
  incident edge lands in `Core.parent.internalEdges` (`← hEdges`), whose endpoints are `Core.parent`-vertices.

Per the HALT: NO `QuotientVertexCovered` reconstruction; body-388's `externalLegs` equality is NOT needed here; `hLegId`
is NOT needed (only `hEdgeId`, via body-387); NO new vertex datum; positivity is supplied honestly from
`P.carrier_isProperForest`; `OccInv` / the parent equality / the forest bridge / the forward round-trip are NOT used.
This lands the last of the three projections as a THEOREM.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
`promote_collapse` / singleton / floor-297.
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

variable {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
  {Concrete : ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G),
    ResolvedConcreteRemnantReembedSupply D G s}

/-- **R-6c-body-389 — the vertices projection (THEOREM, last of the three).**  The de-contracted parent's vertices are
the occurrence source outer's — from the internal-edge equality (body-387) + no-isolated-vertex, both directions. -/
theorem parent_remnantComponent_vertices
    (Core : ResolvedMultiStarDecontractionValueCoreSupply D)
    (P : ResolvedCarrierProperProvider D)
    (Fstar : ResolvedCanonicalStarFacts D)
    (StarProm : ResolvedPromotedStarCoherenceValueSupply Fmem V)
    (Wiring : ResolvedRemnantComponentValueWiringSupply V Concrete)
    {G : ResolvedFeynmanGraph} (hEdgeId : G.EdgeIdsUnique) (q : FilteredForestBlockDom D G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredValue Fmem V q)})
    (hδ : HEq (V.Remnant.remnant.remnantComponent q.1 o) δ.1) :
    (Core.parent (fwdMapFilteredValue Fmem V q) δ).vertices = o.γ.1.vertices := by
  have hEdges := parent_remnantComponent_internalEdges Core Fstar StarProm Wiring hEdgeId q o δ hδ
  have hγConn := (q.1.1.1.isConnectedDivergent o.γ.1 o.γ.2).1
  have hγPos := (P.carrier_isProperForest G q.1.1.1 q.1.1.2).2.2.2.1 o.γ.1 o.γ.2
  have hParentConn : (Core.parent (fwdMapFilteredValue Fmem V q) δ).forget.IsConnected :=
    (Core.parentCD (fwdMapFilteredValue Fmem V q) δ).1
  have hParentPos : 0 < (Core.parent (fwdMapFilteredValue Fmem V q) δ).internalEdges.card := by
    rw [hEdges]; exact hγPos
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨e, he, hend⟩ :=
      resolvedSubgraph_vertex_incident_edge_of_connected_pos hParentConn hParentPos hv
    rw [hEdges] at he
    obtain ⟨hs, ht⟩ := o.γ.1.edges_supported e he
    rcases hend with h | h
    · rw [← h]; exact hs
    · rw [← h]; exact ht
  · intro v hv
    obtain ⟨e, he, hend⟩ :=
      resolvedSubgraph_vertex_incident_edge_of_connected_pos hγConn hγPos hv
    rw [← hEdges] at he
    obtain ⟨hs, ht⟩ := (Core.parent (fwdMapFilteredValue Fmem V q) δ).edges_supported e he
    rcases hend with h | h
    · rw [← h]; exact hs
    · rw [← h]; exact ht

end GaugeGeometry.QFT.Combinatorial
