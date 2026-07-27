import GaugeGeometry.QFT.Combinatorial.Phi4PermutationInvariance

/-!
# QFT-R1-body-567 — boundary-completed intrinsic graph

The left factor, realized in the Combinatorial layer only (no `HopfGen` wiring yet).

Body-562 showed the intrinsic lift `γ.toFeynmanGraph` *drops* the induced boundary, so its φ⁴ degree
overshoots by `|∂γ|`.  The honest repair is to carry the cut boundary edges *forward* as genuine external
legs before intrinsifying — not to fabricate `IsAmbientInvariantDivergence`.  Each boundary edge
(exactly-one-endpoint-inside) induces one external leg attached to its inside endpoint, with the edge's own
sector.  Adding these to `γ.externalLegs` yields the **boundary-completed** intrinsic graph, whose φ⁴ degree
equals `ω(γ)` exactly.

## Contents

* Step 1 `boundaryInsideVertex` — the inside endpoint of a boundary edge (membership read off
  `IsBoundaryEdge`, not stored as data); with rename equivariance.
* Step 2 `boundaryExternalLeg` — the induced leg (sector = edge sector, `rfl`); support + rename.
* Step 3 `inducedBoundaryExternalLegs` — the multiplicity-safe induced legs (`.map`, **no** edge→leg
  injectivity assumed); exact rename transport via body-564's `mapPerm_boundaryEdges`.
* Step 4 `boundaryCompletedExternalLegs` — original + induced; card = `physicalExternalLegCount`.
* Step 5 `boundaryCompletedGraph` — the intrinsic graph (same vertices / internal edges, completed legs);
  well-formed; rename-coherent.
* Step 6 `phi4SuperficialDegree_self_boundaryCompletedGraph` — the gap repaired: `ω(self …) = ω(γ)`.

## Verdict

```text
inside endpoint          DERIVED from IsBoundaryEdge
sector                   FREE / rfl
multiplicity             EXACT via Multiset.map
well-formedness          DERIVED
rename coherence         DERIVED from body-564
φ⁴ degree recovery       DERIVED
edge-origin traceability NOT PROVIDED by flat ExternalLeg
```

The last line matters: this **flat** completion suffices for φ⁴ valence / divergence / generator class, but
recovering a general QFT's gluing orbits / symmetry factors needs a *resolved boundary-ID* version, built
separately.  No such traceability is fabricated here.

Per the HALT: no HopfAlgebra import; `toFeynmanGraph` is not edited; no new `class`/`structure`/`instance`;
`IsAmbientInvariantDivergence` is not inhabited; no left `HopfGen` / coproduct / coassociativity; no
`Finset`-ification / dedup of the induced legs; no edge→leg injectivity or inverse recovery is claimed; no
resolved traceability is faked into this flat construction.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable {G : FeynmanGraph}

/-! ## Step 1 — inside endpoint of a boundary edge -/

/-- The endpoint of `e` that lies inside `γ` (as a plain choice; the membership certificate is read off
`IsBoundaryEdge`, never stored). -/
def FeynmanSubgraph.boundaryInsideVertex (γ : FeynmanSubgraph G) (e : FeynmanEdge) : VertexId :=
  if e.source ∈ γ.vertices then e.source else e.target

/-- **R-6c-QFT-R1-body-567 — the inside endpoint is inside.**  For a boundary edge, the chosen endpoint
lies in `γ.vertices`. -/
theorem FeynmanSubgraph.boundaryInsideVertex_mem (γ : FeynmanSubgraph G) (e : FeynmanEdge)
    (h : γ.IsBoundaryEdge e) : γ.boundaryInsideVertex e ∈ γ.vertices := by
  unfold FeynmanSubgraph.boundaryInsideVertex
  by_cases hs : e.source ∈ γ.vertices
  · rw [if_pos hs]; exact hs
  · rw [if_neg hs]
    rcases h with ⟨hs', _⟩ | ⟨_, ht⟩
    · exact absurd hs' hs
    · exact ht

/-- **R-6c-QFT-R1-body-567 — inside endpoint is rename-equivariant.** -/
theorem FeynmanSubgraph.boundaryInsideVertex_mapPerm (γ : FeynmanSubgraph G)
    (π : Equiv.Perm VertexId) (e : FeynmanEdge) :
    (γ.mapPerm π).boundaryInsideVertex (e.map π) = π (γ.boundaryInsideVertex e) := by
  unfold FeynmanSubgraph.boundaryInsideVertex
  simp only [FeynmanSubgraph.mapPerm_vertices, FeynmanEdge.map_source, FeynmanEdge.map_target,
    π.injective.mem_finset_image]
  by_cases hs : e.source ∈ γ.vertices
  · rw [if_pos hs, if_pos hs]
  · rw [if_neg hs, if_neg hs]

/-! ## Step 2 — induced external leg -/

/-- The external leg induced by a boundary edge: attached to the inside endpoint, carrying the edge's own
sector (sector preservation is `rfl`, entirely free). -/
def FeynmanSubgraph.boundaryExternalLeg (γ : FeynmanSubgraph G) (e : FeynmanEdge) : ExternalLeg where
  attachedTo := γ.boundaryInsideVertex e
  sector := e.sector

@[simp] theorem FeynmanSubgraph.boundaryExternalLeg_attachedTo (γ : FeynmanSubgraph G)
    (e : FeynmanEdge) : (γ.boundaryExternalLeg e).attachedTo = γ.boundaryInsideVertex e := rfl

@[simp] theorem FeynmanSubgraph.boundaryExternalLeg_sector (γ : FeynmanSubgraph G) (e : FeynmanEdge) :
    (γ.boundaryExternalLeg e).sector = e.sector := rfl

/-- **R-6c-QFT-R1-body-567 — the induced leg is supported on `γ`.** -/
theorem FeynmanSubgraph.boundaryExternalLeg_supported (γ : FeynmanSubgraph G) (e : FeynmanEdge)
    (h : γ.IsBoundaryEdge e) : (γ.boundaryExternalLeg e).SupportedOn γ.vertices :=
  γ.boundaryInsideVertex_mem e h

/-- **R-6c-QFT-R1-body-567 — the induced leg is rename-equivariant.** -/
theorem FeynmanSubgraph.boundaryExternalLeg_mapPerm (γ : FeynmanSubgraph G)
    (π : Equiv.Perm VertexId) (e : FeynmanEdge) :
    (γ.mapPerm π).boundaryExternalLeg (e.map π) = (γ.boundaryExternalLeg e).map π := by
  simp only [FeynmanSubgraph.boundaryExternalLeg, ExternalLeg.map, ExternalLeg.mk.injEq]
  exact ⟨γ.boundaryInsideVertex_mapPerm π e, FeynmanEdge.map_sector π e⟩

/-! ## Step 3 — multiplicity-safe induced boundary legs -/

/-- The induced boundary legs of `γ` — one per boundary edge, kept with multiplicity (**no** edge→leg
injectivity: distinct cut edges may induce equal `(attachedTo, sector)` legs; `Multiset.map` preserves the
count). -/
def FeynmanSubgraph.inducedBoundaryExternalLegs (γ : FeynmanSubgraph G) : Multiset ExternalLeg :=
  γ.boundaryEdges.map γ.boundaryExternalLeg

@[simp] theorem FeynmanSubgraph.inducedBoundaryExternalLegs_card (γ : FeynmanSubgraph G) :
    γ.inducedBoundaryExternalLegs.card = γ.boundaryEdgeCount := by
  unfold FeynmanSubgraph.inducedBoundaryExternalLegs FeynmanSubgraph.boundaryEdgeCount
  rw [Multiset.card_map]

theorem FeynmanSubgraph.inducedBoundaryExternalLegs_supported (γ : FeynmanSubgraph G) :
    ∀ ℓ ∈ γ.inducedBoundaryExternalLegs, ℓ.SupportedOn γ.vertices := by
  intro ℓ hℓ
  unfold FeynmanSubgraph.inducedBoundaryExternalLegs at hℓ
  rcases Multiset.mem_map.mp hℓ with ⟨e, he, rfl⟩
  have hbe : γ.IsBoundaryEdge e := by
    unfold FeynmanSubgraph.boundaryEdges at he
    exact (Multiset.mem_filter.mp he).2
  exact γ.boundaryExternalLeg_supported e hbe

/-- **R-6c-QFT-R1-body-567 — induced legs transport exactly under `mapPerm`.**  The load-bearing coherence:
body-564's `mapPerm_boundaryEdges` + Step 2's pointwise equivariance, closed by `Multiset.map_map`. -/
theorem FeynmanSubgraph.mapPerm_inducedBoundaryExternalLegs (γ : FeynmanSubgraph G)
    (π : Equiv.Perm VertexId) :
    (γ.mapPerm π).inducedBoundaryExternalLegs
      = γ.inducedBoundaryExternalLegs.map (ExternalLeg.map π) := by
  unfold FeynmanSubgraph.inducedBoundaryExternalLegs
  rw [FeynmanSubgraph.mapPerm_boundaryEdges, Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro e _
  exact γ.boundaryExternalLeg_mapPerm π e

/-! ## Step 4 — completed boundary legs -/

/-- The boundary-completed external legs: original ambient legs plus induced boundary legs. -/
def FeynmanSubgraph.boundaryCompletedExternalLegs (γ : FeynmanSubgraph G) : Multiset ExternalLeg :=
  γ.externalLegs + γ.inducedBoundaryExternalLegs

@[simp] theorem FeynmanSubgraph.boundaryCompletedExternalLegs_card (γ : FeynmanSubgraph G) :
    γ.boundaryCompletedExternalLegs.card = γ.physicalExternalLegCount := by
  unfold FeynmanSubgraph.boundaryCompletedExternalLegs
  rw [Multiset.card_add, FeynmanSubgraph.inducedBoundaryExternalLegs_card]
  rfl

theorem FeynmanSubgraph.boundaryCompletedExternalLegs_supported (γ : FeynmanSubgraph G) :
    ∀ ℓ ∈ γ.boundaryCompletedExternalLegs, ℓ.SupportedOn γ.vertices := by
  intro ℓ hℓ
  unfold FeynmanSubgraph.boundaryCompletedExternalLegs at hℓ
  rcases Multiset.mem_add.mp hℓ with h | h
  · exact γ.legs_supported ℓ h
  · exact γ.inducedBoundaryExternalLegs_supported ℓ h

/-- **R-6c-QFT-R1-body-567 — completed legs transport exactly under `mapPerm`.** -/
theorem FeynmanSubgraph.mapPerm_boundaryCompletedExternalLegs (γ : FeynmanSubgraph G)
    (π : Equiv.Perm VertexId) :
    (γ.mapPerm π).boundaryCompletedExternalLegs
      = γ.boundaryCompletedExternalLegs.map (ExternalLeg.map π) := by
  unfold FeynmanSubgraph.boundaryCompletedExternalLegs
  rw [Multiset.map_add, FeynmanSubgraph.mapPerm_externalLegs,
    FeynmanSubgraph.mapPerm_inducedBoundaryExternalLegs]

/-! ## Step 5 — the boundary-completed intrinsic graph -/

/-- **R-6c-QFT-R1-body-567 — the boundary-completed intrinsic graph.**  Same vertices and internal edges as
`γ`, but with the boundary-completed external legs — so no boundary is forgotten. -/
def FeynmanSubgraph.boundaryCompletedGraph (γ : FeynmanSubgraph G) : FeynmanGraph where
  vertices := γ.vertices
  internalEdges := γ.internalEdges
  externalLegs := γ.boundaryCompletedExternalLegs

@[simp] theorem FeynmanSubgraph.boundaryCompletedGraph_vertices (γ : FeynmanSubgraph G) :
    γ.boundaryCompletedGraph.vertices = γ.vertices := rfl

@[simp] theorem FeynmanSubgraph.boundaryCompletedGraph_internalEdges (γ : FeynmanSubgraph G) :
    γ.boundaryCompletedGraph.internalEdges = γ.internalEdges := rfl

@[simp] theorem FeynmanSubgraph.boundaryCompletedGraph_externalLegs (γ : FeynmanSubgraph G) :
    γ.boundaryCompletedGraph.externalLegs = γ.boundaryCompletedExternalLegs := rfl

/-- **R-6c-QFT-R1-body-567 — the boundary-completed graph is well-formed.** -/
theorem FeynmanSubgraph.boundaryCompletedGraph_wellFormed (γ : FeynmanSubgraph G) :
    γ.boundaryCompletedGraph.WellFormed :=
  ⟨γ.edges_supported, γ.boundaryCompletedExternalLegs_supported⟩

@[simp] theorem FeynmanSubgraph.boundaryCompletedGraph_externalLegCount (γ : FeynmanSubgraph G) :
    γ.boundaryCompletedGraph.externalLegCount = γ.physicalExternalLegCount := by
  unfold FeynmanGraph.externalLegCount
  rw [FeynmanSubgraph.boundaryCompletedGraph_externalLegs,
    FeynmanSubgraph.boundaryCompletedExternalLegs_card]

/-- **R-6c-QFT-R1-body-567 — boundary completion commutes with rename.** -/
theorem FeynmanSubgraph.boundaryCompletedGraph_mapPerm (γ : FeynmanSubgraph G)
    (π : Equiv.Perm VertexId) :
    (γ.mapPerm π).boundaryCompletedGraph = γ.boundaryCompletedGraph.mapPerm π := by
  simp only [FeynmanSubgraph.boundaryCompletedGraph, FeynmanGraph.mapPerm,
    FeynmanSubgraph.mapPerm_vertices, FeynmanSubgraph.mapPerm_internalEdges, FeynmanGraph.mk.injEq]
  exact ⟨trivial, trivial, γ.mapPerm_boundaryCompletedExternalLegs π⟩

/-! ## Step 6 — the boundary gap, repaired -/

/-- **R-6c-QFT-R1-body-567 — φ⁴ degree recovery.**  The intrinsic self-graph of the *boundary-completed*
graph has φ⁴ degree exactly `ω(γ)` — the boundary gap of body-562 (`ω(self γ.toFeynmanGraph) = ω(γ) + |∂γ|`)
is repaired, with no `IsAmbientInvariantDivergence` fabricated: the forgotten boundary was carried into the
external legs before intrinsifying. -/
theorem FeynmanSubgraph.phi4SuperficialDegree_self_boundaryCompletedGraph (γ : FeynmanSubgraph G) :
    (FeynmanSubgraph.self γ.boundaryCompletedGraph
        γ.boundaryCompletedGraph_wellFormed).phi4SuperficialDegree
      = γ.phi4SuperficialDegree := by
  rw [FeynmanSubgraph.phi4SuperficialDegree_self]
  unfold FeynmanSubgraph.phi4SuperficialDegree
  rw [FeynmanSubgraph.boundaryCompletedGraph_externalLegs,
    FeynmanSubgraph.boundaryCompletedExternalLegs_card]

end GaugeGeometry.QFT.Combinatorial
