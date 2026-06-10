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

Step 6C-3 delivered edge-endpoint saturation (the structural half).  Step 6C-4 below
discharges the no-isolated-vertex half via a `ReflTransGen.cases_head` first-step
argument, completing component vertex-saturation. -/

/-! ### Step 6C-4 — no isolated vertex (connected + positive edges) -/

/-- **First-step lemma.**  If `v` reaches a *different* vertex `u`, the first hop is an
internal edge incident to `v` (head of the reflexive-transitive `SupportAdj` chain). -/
theorem incident_edge_of_reachable_ne {H : FeynmanGraph} {v u : VertexId}
    (hReach : H.SupportReachable v u) (hne : v ≠ u) :
    ∃ e ∈ H.internalEdges, e.source = v ∨ e.target = v := by
  rw [FeynmanGraph.SupportReachable, SimpleGraph.reachable_iff_reflTransGen] at hReach
  rcases hReach.cases_head with h | ⟨w, hadj, _⟩
  · exact absurd h hne
  · have hadj' : H.SupportAdj v w := hadj
    obtain ⟨_, e, heH, hend⟩ := hadj'
    rcases hend with ⟨hs, _⟩ | ⟨_, ht⟩
    · exact ⟨e, heH, Or.inl hs⟩
    · exact ⟨e, heH, Or.inr ht⟩

/-- **No isolated vertex (flat).**  Every vertex of a connected subgraph with a
positive internal-edge count is incident to some internal edge. -/
theorem feynmanSubgraph_vertex_incident_edge_of_connected_pos
    {Gf : FeynmanGraph} {γ : FeynmanSubgraph Gf}
    (hConn : γ.IsConnected) (hPos : 0 < γ.internalEdges.card)
    {v : VertexId} (hv : v ∈ γ.vertices) :
    ∃ e ∈ γ.internalEdges, e.source = v ∨ e.target = v := by
  obtain ⟨e₀, he₀⟩ := Multiset.card_pos_iff_exists_mem.mp hPos
  have hu : e₀.source ∈ γ.vertices := (γ.edges_supported e₀ he₀).1
  by_cases hvu : v = e₀.source
  · exact ⟨e₀, he₀, Or.inl hvu.symm⟩
  · have hReach : γ.toFeynmanGraph.SupportReachable v e₀.source := hConn hv hu
    obtain ⟨e, heT, hend⟩ := incident_edge_of_reachable_ne hReach hvu
    rw [FeynmanSubgraph.toFeynmanGraph_internalEdges] at heT
    exact ⟨e, heT, hend⟩

/-- **No isolated vertex (resolved).**  Lifted to resolved subgraphs through `forget`
(`forget` preserves vertices, edge-count, and edge endpoints). -/
theorem resolvedSubgraph_vertex_incident_edge_of_connected_pos
    {γ : ResolvedFeynmanSubgraph G}
    (hConn : γ.forget.IsConnected) (hPos : 0 < γ.internalEdges.card)
    {v : VertexId} (hv : v ∈ γ.vertices) :
    ∃ e ∈ γ.internalEdges, e.source = v ∨ e.target = v := by
  have hPosF : 0 < γ.forget.internalEdges.card := by
    rw [ResolvedFeynmanSubgraph.forget_internalEdges, Multiset.card_map]; exact hPos
  have hvF : v ∈ γ.forget.vertices := hv
  obtain ⟨ef, hef, hend⟩ :=
    feynmanSubgraph_vertex_incident_edge_of_connected_pos hConn hPosF hvF
  rw [ResolvedFeynmanSubgraph.forget_internalEdges, Multiset.mem_map] at hef
  obtain ⟨e, heγ, hfe⟩ := hef
  refine ⟨e, heγ, ?_⟩
  rcases hend with h | h
  · left; rw [← hfe] at h; exact h
  · right; rw [← hfe] at h; exact h

/-! ### Step 6C-5 — full component vertex-saturation -/

/-- **Component vertex-saturation.**  If `γ` contains all of `Aout`'s internal edges
and a component `η` is connected with positive edges, then `η`'s vertices lie in
`γ.vertices` (every `η`-vertex is an `η`-edge endpoint, and those edges land in `γ`). -/
theorem component_vertices_subset_parent_of_edges
    (Aout : ResolvedAdmissibleSubgraph G) {η γ : ResolvedFeynmanSubgraph G}
    (hη : η ∈ Aout.elements) (hConn : η.forget.IsConnected)
    (hPos : 0 < η.internalEdges.card)
    (hA : Aout.internalEdges ≤ γ.internalEdges) :
    η.vertices ⊆ γ.vertices := by
  intro v hv
  obtain ⟨e, heη, hend⟩ := resolvedSubgraph_vertex_incident_edge_of_connected_pos hConn hPos hv
  have hEnds := component_edge_endpoints_in_parent Aout hη hA heη
  rcases hend with h | h
  · rw [← h]; exact hEnds.1
  · rw [← h]; exact hEnds.2

/-! ### Step 6C-6 — reverse source-vertex recovery (fresh stars)

With full component saturation, the reverse inclusion of source-vertex recovery
closes.  The only extra input is **star freshness** (`starOf η ∉ G.vertices`), which
rules out a complement vertex coinciding with a star (the residual over-recovery from
Step 6C-2). -/

/-- Membership characterization of the source-vertex recovery. -/
theorem mem_resolvedRemainderSourceVertices
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (δ : ResolvedFeynmanSubgraph (Aout.contractWithStars starOf)) {v : VertexId} :
    v ∈ resolvedRemainderSourceVertices Aout starOf δ ↔
      v ∈ G.vertices ∧ Aout.retargetVertex starOf v ∈ δ.vertices := by
  classical
  unfold resolvedRemainderSourceVertices
  exact Finset.mem_filter

/-- `retargetVertex` on a carrier vertex is its chosen component's star. -/
theorem retargetVertex_eq_star_of_mem (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    {v : VertexId} (hv : v ∈ Aout.vertices) :
    Aout.retargetVertex starOf v = starOf (Aout.componentAt hv) := by
  rw [ResolvedAdmissibleSubgraph.retargetVertex, Aout.componentAt?_of_mem hv]

/-- **Reverse inclusion.**  Under star freshness + connected positive-edge components +
`hA`, a vertex recovered from `γ`'s remnant really lies in `γ`. -/
theorem mem_parent_of_mem_sourceVertices
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (hFresh : ∀ η ∈ Aout.elements, starOf η ∉ G.vertices)
    (hCompCD : ∀ η ∈ Aout.elements, η.forget.IsConnected)
    (hCompPos : ∀ η ∈ Aout.elements, 0 < η.internalEdges.card)
    {γ : ResolvedFeynmanSubgraph G} (hA : Aout.internalEdges ≤ γ.internalEdges)
    {v : VertexId}
    (hv : v ∈ resolvedRemainderSourceVertices Aout starOf
      (resolvedParentRemnant Aout starOf γ)) :
    v ∈ γ.vertices := by
  rw [mem_resolvedRemainderSourceVertices] at hv
  obtain ⟨hvG, hmem⟩ := hv
  by_cases hvA : v ∈ Aout.vertices
  · exact component_vertices_subset_parent_of_edges Aout (Aout.componentAt_mem hvA)
      (hCompCD _ (Aout.componentAt_mem hvA)) (hCompPos _ (Aout.componentAt_mem hvA)) hA
      (Aout.componentAt_vertex_mem hvA)
  · rw [Aout.retargetVertex_of_not_mem starOf hvA, resolvedParentRemnant,
      ResolvedAdmissibleSubgraph.quotientRemainderSubgraph_vertices] at hmem
    obtain ⟨w, hwγ, hweq⟩ := Finset.mem_image.mp hmem
    by_cases hwA : w ∈ Aout.vertices
    · rw [retargetVertex_eq_star_of_mem Aout starOf hwA] at hweq
      have hsG : starOf (Aout.componentAt hwA) ∈ G.vertices := by rw [hweq]; exact hvG
      exact absurd hsG (hFresh _ (Aout.componentAt_mem hwA))
    · rw [Aout.retargetVertex_of_not_mem starOf hwA] at hweq
      rw [← hweq]; exact hwγ

/-- **Source-vertex recovery is exact** (both inclusions). -/
theorem resolvedRemainderSourceVertices_parent_eq
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (hFresh : ∀ η ∈ Aout.elements, starOf η ∉ G.vertices)
    (hCompCD : ∀ η ∈ Aout.elements, η.forget.IsConnected)
    (hCompPos : ∀ η ∈ Aout.elements, 0 < η.internalEdges.card)
    {γ : ResolvedFeynmanSubgraph G} (hA : Aout.internalEdges ≤ γ.internalEdges) :
    resolvedRemainderSourceVertices Aout starOf (resolvedParentRemnant Aout starOf γ)
      = γ.vertices :=
  Finset.Subset.antisymm
    (fun _ hv => mem_parent_of_mem_sourceVertices Aout starOf hFresh hCompCD hCompPos hA hv)
    (subset_resolvedRemainderSourceVertices_parent Aout starOf γ)

/-- **Constructive `remnant_vertex_recovery`.**  Equal remnants force equal source
vertices, via the exact recovery. -/
theorem remnant_vertex_recovery_of_sourceVertices
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (hFresh : ∀ η ∈ Aout.elements, starOf η ∉ G.vertices)
    (hCompCD : ∀ η ∈ Aout.elements, η.forget.IsConnected)
    (hCompPos : ∀ η ∈ Aout.elements, 0 < η.internalEdges.card)
    {γ₁ γ₂ : ResolvedFeynmanSubgraph G}
    (hA₁ : Aout.internalEdges ≤ γ₁.internalEdges)
    (hA₂ : Aout.internalEdges ≤ γ₂.internalEdges)
    (hRem : resolvedParentRemnant Aout starOf γ₁ = resolvedParentRemnant Aout starOf γ₂) :
    γ₁.vertices = γ₂.vertices := by
  rw [← resolvedRemainderSourceVertices_parent_eq Aout starOf hFresh hCompCD hCompPos hA₁,
    hRem, resolvedRemainderSourceVertices_parent_eq Aout starOf hFresh hCompCD hCompPos hA₂]

/-! ### Step 6C-7 — constructive `ResolvedSigmaParentSet` -/

/-- **Concrete σ-index parent set.**  With fresh stars + connected positive-edge
components, any parent set of `Aout`-edge-containing subgraphs is a genuine
`ResolvedSigmaParentSet` — `remnant_vertex_recovery` is now *constructed*, no longer a
hook. -/
def ResolvedSigmaParentSet.ofSaturatedParents
    {Aout : ResolvedAdmissibleSubgraph G}
    {starOf : ResolvedFeynmanSubgraph G → VertexId}
    (hFresh : ∀ η ∈ Aout.elements, starOf η ∉ G.vertices)
    (hCompCD : ∀ η ∈ Aout.elements, η.forget.IsConnected)
    (hCompPos : ∀ η ∈ Aout.elements, 0 < η.internalEdges.card)
    (parents : Finset (ResolvedFeynmanSubgraph G))
    (hA : ∀ γ ∈ parents, Aout.internalEdges ≤ γ.internalEdges) :
    ResolvedSigmaParentSet Aout starOf :=
  ResolvedSigmaParentSet.ofParents parents hA
    (fun _ hγ₁ _ hγ₂ hRem =>
      remnant_vertex_recovery_of_sourceVertices Aout starOf hFresh hCompCD hCompPos
        (hA _ hγ₁) (hA _ hγ₂) hRem)

end GaugeGeometry.QFT.Combinatorial
