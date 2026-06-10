import GaugeGeometry.QFT.HopfAlgebra.ResolvedSigmaIndex

/-!
# Component vertex-saturation, first cut (Track R-4-superfull, Step 6C-3)

Toward the reverse source-vertex recovery
`resolvedRemainderSourceVertices … (remnant γ) ⊆ γ.vertices`, whose obstruction
(Step 6C-2) is that a star pulls back a *whole* `Aout`-component, so recovery is
exact only if `γ` is **component-saturated**.

This file establishes the solid, structural part of saturation — **edge-endpoint
saturation**: if a parent `γ` contains all of `Aout`'s internal edges, then every
endpoint of every component-edge lies in `γ.vertices` (from `hA` + `edges_supported`).

The remaining gap (a component vertex that is *not* an edge endpoint — the
no-isolated-vertex fact needed to lift edge-endpoint saturation to full vertex
saturation) is a connectivity/reachability argument; see the report note at the end.
-/

set_option linter.unusedSectionVars false

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ H : FeynmanGraph, DivergenceMeasure H]
         [∀ H : FeynmanGraph, IsPermInvariantDivergence H]
         [∀ H : FeynmanGraph, IsIsoInvariantDivergence H]
         [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)]
         [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
         [IsDivergencePreservedByAdmissibleForestContract]

variable {G : ResolvedFeynmanGraph}

/-! ### Step 1 — edge endpoints lie in the subgraph (from `edges_supported`) -/

/-- Both endpoints of an internal edge of a subgraph lie in its vertices. -/
theorem vertices_of_edge_mem_subgraph {γ : ResolvedFeynmanSubgraph G}
    {e : ResolvedFeynmanEdge} (he : e ∈ γ.internalEdges) :
    e.source ∈ γ.vertices ∧ e.target ∈ γ.vertices :=
  γ.edges_supported e he

/-! ### Step 2 — a component's edges are contained in any parent of `Aout` -/

/-- A forest component's internal edges are below the aggregate (single ≤ sum). -/
theorem element_internalEdges_le_aout
    (Aout : ResolvedAdmissibleSubgraph G) {η : ResolvedFeynmanSubgraph G}
    (hη : η ∈ Aout.elements) : η.internalEdges ≤ Aout.internalEdges :=
  Finset.single_le_sum (fun _ _ => Multiset.zero_le _) hη

/-- Every internal edge of a component lands in any parent containing `Aout`'s edges. -/
theorem component_edge_mem_parent
    (Aout : ResolvedAdmissibleSubgraph G) {η γ : ResolvedFeynmanSubgraph G}
    (hη : η ∈ Aout.elements) (hA : Aout.internalEdges ≤ γ.internalEdges)
    {e : ResolvedFeynmanEdge} (he : e ∈ η.internalEdges) :
    e ∈ γ.internalEdges :=
  Multiset.mem_of_le hA (Multiset.mem_of_le (element_internalEdges_le_aout Aout hη) he)

/-! ### Step 3 — edge-endpoint saturation -/

/-- **Edge-endpoint saturation.**  If `γ` contains all of `Aout`'s internal edges,
then both endpoints of every component-edge lie in `γ.vertices`.  Structural — `hA`
+ `edges_supported`, no connectivity. -/
theorem component_edge_endpoints_in_parent
    (Aout : ResolvedAdmissibleSubgraph G) {η γ : ResolvedFeynmanSubgraph G}
    (hη : η ∈ Aout.elements) (hA : Aout.internalEdges ≤ γ.internalEdges)
    {e : ResolvedFeynmanEdge} (he : e ∈ η.internalEdges) :
    e.source ∈ γ.vertices ∧ e.target ∈ γ.vertices :=
  γ.edges_supported e (component_edge_mem_parent Aout hη hA he)

/-! ### Report (HALT — the no-isolated-vertex gap)

Edge-endpoint saturation (Step 3) lifts to **full** vertex saturation
`η.vertices ⊆ γ.vertices` precisely when every vertex of `η` is an endpoint of some
internal edge of `η` (so that Step 3 covers it).  That "no isolated vertex" fact is a
connectivity statement:

* `η`'s connectivity is `η.forget.IsConnected = η.forget.toFeynmanGraph.IsSupportConnected`,
  i.e. mutual `SupportReachable` (reflexive-transitive closure of `SupportAdj`), and
  `SupportAdj u v := u ≠ v ∧ ∃ e ∈ internalEdges, {e endpoints} = {u, v}`.
* For a component with ≥ 2 vertices, connectivity forces each vertex to have an
  incident edge (an isolated vertex is unreachable) — but extracting this needs a
  genuine `SimpleGraph.Reachable`/`Walk` argument, plus a separate treatment of the
  one-vertex case (where positivity of `internalEdges.card` would force a self-loop,
  which `SupportAdj` drops).

Per the HALT this reachability campaign is **not** entered here.  Step 6C-3 delivers
edge-endpoint saturation (the structural half); the no-isolated-vertex half — hence
full `component_vertices_subset_parent_of_edges`, hence the reverse source-vertex
recovery and a constructive `remnant_vertex_recovery` — remains the precise next
target. -/

end GaugeGeometry.QFT.Combinatorial
