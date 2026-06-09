import GaugeGeometry.QFT.HopfAlgebra.ResolvedCoproduct

/-!
# Canonical resolved payload model (Track R-4-full, Phase 6c)

The non-vacuity capstone: a *canonical* construction of resolved witnesses by the
constant-id lift `ofFlat…` (decorate every flat edge/leg with `edgeId/legId = ⟨0⟩`).
Because the coproduct/coassoc transfer (Phases 2–5) never uses `EdgeIdsUnique`, the
constant-id lift suffices and is fully canonical (no choice): a flat subgraph lifts
by a plain `Multiset.map`, and `forget` round-trips definitionally up to
`Multiset.map id = id`.

Phase 6c builds, per generator, a `ResolvedHopfPayload`, hence a
`ResolvedHopfPayloadFamily` — so the resolved coproduct of Phase 4c is **inhabited**
for every generator.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable {Gf : FeynmanGraph}

/-- Constant-id lift of a flat edge. -/
def ofFlatEdge (e : FeynmanEdge) : ResolvedFeynmanEdge :=
  { edgeId := ⟨0⟩, source := e.source, target := e.target, sector := e.sector }

/-- Constant-id lift of a flat external leg. -/
def ofFlatLeg (ℓ : ExternalLeg) : ResolvedExternalLeg :=
  { legId := ⟨0⟩, attachedTo := ℓ.attachedTo, sector := ℓ.sector }

@[simp] theorem forget_ofFlatEdge (e : FeynmanEdge) : (ofFlatEdge e).forget = e := rfl
@[simp] theorem forget_ofFlatLeg (ℓ : ExternalLeg) : (ofFlatLeg ℓ).forget = ℓ := rfl

theorem forget_comp_ofFlatEdge : ResolvedFeynmanEdge.forget ∘ ofFlatEdge = id := rfl
theorem forget_comp_ofFlatLeg : ResolvedExternalLeg.forget ∘ ofFlatLeg = id := rfl

/-- Constant-id lift of a flat graph. -/
def ofFlatGraph (Gf : FeynmanGraph) : ResolvedFeynmanGraph :=
  { vertices := Gf.vertices
    internalEdges := Gf.internalEdges.map ofFlatEdge
    externalLegs := Gf.externalLegs.map ofFlatLeg }

@[simp] theorem ofFlatGraph_vertices (Gf : FeynmanGraph) :
    (ofFlatGraph Gf).vertices = Gf.vertices := rfl
@[simp] theorem ofFlatGraph_internalEdges (Gf : FeynmanGraph) :
    (ofFlatGraph Gf).internalEdges = Gf.internalEdges.map ofFlatEdge := rfl
@[simp] theorem ofFlatGraph_externalLegs (Gf : FeynmanGraph) :
    (ofFlatGraph Gf).externalLegs = Gf.externalLegs.map ofFlatLeg := rfl

/-- `forget` round-trips on the canonical graph lift. -/
theorem forget_ofFlatGraph (Gf : FeynmanGraph) : (ofFlatGraph Gf).forget = Gf := by
  show ResolvedFeynmanGraph.forget _ = _
  unfold ResolvedFeynmanGraph.forget ofFlatGraph
  have hi : (Gf.internalEdges.map ofFlatEdge).map ResolvedFeynmanEdge.forget = Gf.internalEdges := by
    rw [Multiset.map_map, forget_comp_ofFlatEdge, Multiset.map_id]
  have hl : (Gf.externalLegs.map ofFlatLeg).map ResolvedExternalLeg.forget = Gf.externalLegs := by
    rw [Multiset.map_map, forget_comp_ofFlatLeg, Multiset.map_id]
  rw [hi, hl]

/-- Constant-id lift of a flat subgraph. -/
def ofFlatSubgraph (γ : FeynmanSubgraph Gf) : ResolvedFeynmanSubgraph (ofFlatGraph Gf) where
  vertices := γ.vertices
  internalEdges := γ.internalEdges.map ofFlatEdge
  externalLegs := γ.externalLegs.map ofFlatLeg
  vertices_subset := γ.vertices_subset
  internalEdges_le := Multiset.map_le_map γ.internalEdges_le
  externalLegs_le := Multiset.map_le_map γ.externalLegs_le
  edges_supported := by
    intro e' he'
    obtain ⟨e, he, rfl⟩ := Multiset.mem_map.mp he'
    simpa [ofFlatEdge, FeynmanEdge.SupportedOn] using γ.edges_supported e he
  legs_supported := by
    intro ℓ' hℓ'
    obtain ⟨ℓ, hℓ, rfl⟩ := Multiset.mem_map.mp hℓ'
    simpa [ofFlatLeg, ExternalLeg.SupportedOn] using γ.legs_supported ℓ hℓ

/-- Carrier-level `forget` round-trip for the subgraph lift (the carrier fields are
graph-independent types, so these typecheck without graph transport). -/
@[simp] theorem forget_ofFlatSubgraph_vertices (γ : FeynmanSubgraph Gf) :
    (ofFlatSubgraph γ).forget.vertices = γ.vertices := rfl

@[simp] theorem forget_ofFlatSubgraph_internalEdges (γ : FeynmanSubgraph Gf) :
    (ofFlatSubgraph γ).forget.internalEdges = γ.internalEdges := by
  show (γ.internalEdges.map ofFlatEdge).map ResolvedFeynmanEdge.forget = γ.internalEdges
  rw [Multiset.map_map, forget_comp_ofFlatEdge, Multiset.map_id]

@[simp] theorem forget_ofFlatSubgraph_externalLegs (γ : FeynmanSubgraph Gf) :
    (ofFlatSubgraph γ).forget.externalLegs = γ.externalLegs := by
  show (γ.externalLegs.map ofFlatLeg).map ResolvedExternalLeg.forget = γ.externalLegs
  rw [Multiset.map_map, forget_comp_ofFlatLeg, Multiset.map_id]

end GaugeGeometry.QFT.Combinatorial
