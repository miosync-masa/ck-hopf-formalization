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

set_option linter.unusedSectionVars false

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

/-! ### Phase 6c-2 — connected-divergence transfer for the subgraph lift

`IsConnected`/`IsOnePI` depend only on `toFeynmanGraph` (carrier), so transfer by
rewriting the carrier-graph equality.  `IsDivergent` depends on the ambient
`DivergenceMeasure`; it transfers via `IsAmbientInvariantDivergence` (degree of a
subgraph equals the degree of the self-subgraph of its own intrinsic graph). -/

variable [∀ H : FeynmanGraph, DivergenceMeasure H] [IsAmbientInvariantDivergence]

/-- The forgotten subgraph lift has the same intrinsic graph as the original
(carrier-level, no graph transport). -/
theorem forget_ofFlatSubgraph_toFeynmanGraph (δ : FeynmanSubgraph Gf) :
    (ofFlatSubgraph δ).forget.toFeynmanGraph = δ.toFeynmanGraph := by
  simp only [FeynmanSubgraph.toFeynmanGraph, forget_ofFlatSubgraph_vertices,
    forget_ofFlatSubgraph_internalEdges, forget_ofFlatSubgraph_externalLegs]

theorem forget_ofFlatSubgraph_isConnected (δ : FeynmanSubgraph Gf) :
    (ofFlatSubgraph δ).forget.IsConnected ↔ δ.IsConnected := by
  unfold FeynmanSubgraph.IsConnected
  rw [forget_ofFlatSubgraph_toFeynmanGraph]

theorem forget_ofFlatSubgraph_isOnePI (δ : FeynmanSubgraph Gf) :
    (ofFlatSubgraph δ).forget.IsOnePI ↔ δ.IsOnePI := by
  unfold FeynmanSubgraph.IsOnePI
  rw [forget_ofFlatSubgraph_toFeynmanGraph]

/-- Degree of a self-subgraph depends only on the (equal) ambient graph. -/
private theorem degree_self_eq_of_graph_eq {g₁ g₂ : FeynmanGraph} (h : g₁ = g₂)
    (wf₁ : g₁.WellFormed) (wf₂ : g₂.WellFormed) :
    DivergenceMeasure.degree (FeynmanSubgraph.self g₁ wf₁) =
      DivergenceMeasure.degree (FeynmanSubgraph.self g₂ wf₂) := by
  subst h; rfl

/-- The divergence degree is preserved by the subgraph lift, via
`IsAmbientInvariantDivergence` (both equal the degree of the self-subgraph of the
common intrinsic graph). -/
theorem forget_ofFlatSubgraph_degree (δ : FeynmanSubgraph Gf) :
    DivergenceMeasure.degree ((ofFlatSubgraph δ).forget) = DivergenceMeasure.degree δ := by
  rw [← IsAmbientInvariantDivergence.degree_self_eq ((ofFlatSubgraph δ).forget),
      ← IsAmbientInvariantDivergence.degree_self_eq δ]
  exact degree_self_eq_of_graph_eq (forget_ofFlatSubgraph_toFeynmanGraph δ) _ _

/-- **CD transfer (Phase 6c-2 headline).**  A connected-divergent flat subgraph
lifts to a connected-divergent resolved subgraph (after forgetting).  This is the
field needed for `ofFlatForest.isConnectedDivergent`. -/
theorem forget_ofFlatSubgraph_isConnectedDivergent {δ : FeynmanSubgraph Gf}
    (hδ : δ.IsConnectedDivergent) :
    (ofFlatSubgraph δ).forget.IsConnectedDivergent := by
  obtain ⟨hc, ho, hd⟩ := hδ
  refine ⟨(forget_ofFlatSubgraph_isConnected δ).mpr hc,
          (forget_ofFlatSubgraph_isOnePI δ).mpr ho, ?_⟩
  have hd' : (0 : Int) ≤ DivergenceMeasure.degree δ := hd
  show (0 : Int) ≤ DivergenceMeasure.degree ((ofFlatSubgraph δ).forget)
  rw [forget_ofFlatSubgraph_degree]; exact hd'

end GaugeGeometry.QFT.Combinatorial
