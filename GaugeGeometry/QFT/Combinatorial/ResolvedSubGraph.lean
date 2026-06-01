import GaugeGeometry.QFT.Combinatorial.ResolvedFeynmanGraphs
import GaugeGeometry.QFT.Combinatorial.SubGraph

/-!
# Resolved subgraph spine (Track R-4-full, Phase 1a)

The boundary-resolved analogue of `FeynmanSubgraph`, the lowest layer of the full
resolved CK Hopf rebuild.  A `ResolvedFeynmanSubgraph G` carries the same shape as
the flat `FeynmanSubgraph` but over the identity-carrying resolved edge/leg
carriers, and `forget` projects it to a flat `FeynmanSubgraph G.forget`.

The headline compatibility is `forget_toFeynmanGraph`:
`γ.forget.toFeynmanGraph = γ.toResolvedFeynmanGraph.forget` — forgetting commutes
with taking the intrinsic graph.  This is the spine fact the resolved
contraction / coproduct layers (later phases) build on.

Phase 1a only: subgraph + forget + the commuting square.  No admissible subgraph,
contraction, coproduct, or `HopfGen` yet.  Existing flat development untouched.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable {G : ResolvedFeynmanGraph}

/-- A boundary-resolved subgraph of `G`: same shape as `FeynmanSubgraph` but over
the resolved edge/leg carriers (so the persistent `edgeId`/`legId` are retained). -/
structure ResolvedFeynmanSubgraph (G : ResolvedFeynmanGraph) where
  vertices : Finset VertexId
  internalEdges : Multiset ResolvedFeynmanEdge
  externalLegs : Multiset ResolvedExternalLeg
  vertices_subset : vertices ⊆ G.vertices
  internalEdges_le : internalEdges ≤ G.internalEdges
  externalLegs_le : externalLegs ≤ G.externalLegs
  edges_supported : ∀ e ∈ internalEdges, e.source ∈ vertices ∧ e.target ∈ vertices
  legs_supported : ∀ ℓ ∈ externalLegs, ℓ.attachedTo ∈ vertices

namespace ResolvedFeynmanSubgraph

/-- The intrinsic resolved graph of a resolved subgraph. -/
def toResolvedFeynmanGraph (γ : ResolvedFeynmanSubgraph G) : ResolvedFeynmanGraph where
  vertices := γ.vertices
  internalEdges := γ.internalEdges
  externalLegs := γ.externalLegs

@[simp] theorem toResolvedFeynmanGraph_vertices (γ : ResolvedFeynmanSubgraph G) :
    γ.toResolvedFeynmanGraph.vertices = γ.vertices := rfl

@[simp] theorem toResolvedFeynmanGraph_internalEdges (γ : ResolvedFeynmanSubgraph G) :
    γ.toResolvedFeynmanGraph.internalEdges = γ.internalEdges := rfl

@[simp] theorem toResolvedFeynmanGraph_externalLegs (γ : ResolvedFeynmanSubgraph G) :
    γ.toResolvedFeynmanGraph.externalLegs = γ.externalLegs := rfl

/-- Forget the identities of a resolved subgraph, recovering a flat
`FeynmanSubgraph` of the forgotten ambient `G.forget`. -/
def forget (γ : ResolvedFeynmanSubgraph G) : FeynmanSubgraph G.forget where
  vertices := γ.vertices
  internalEdges := γ.internalEdges.map ResolvedFeynmanEdge.forget
  externalLegs := γ.externalLegs.map ResolvedExternalLeg.forget
  vertices_subset := γ.vertices_subset
  internalEdges_le := Multiset.map_le_map γ.internalEdges_le
  externalLegs_le := Multiset.map_le_map γ.externalLegs_le
  edges_supported := by
    intro e' he'
    obtain ⟨e, he, rfl⟩ := Multiset.mem_map.mp he'
    simpa using γ.edges_supported e he
  legs_supported := by
    intro ℓ' hℓ'
    obtain ⟨ℓ, hℓ, rfl⟩ := Multiset.mem_map.mp hℓ'
    simpa using γ.legs_supported ℓ hℓ

@[simp] theorem forget_vertices (γ : ResolvedFeynmanSubgraph G) :
    γ.forget.vertices = γ.vertices := rfl

@[simp] theorem forget_internalEdges (γ : ResolvedFeynmanSubgraph G) :
    γ.forget.internalEdges = γ.internalEdges.map ResolvedFeynmanEdge.forget := rfl

@[simp] theorem forget_externalLegs (γ : ResolvedFeynmanSubgraph G) :
    γ.forget.externalLegs = γ.externalLegs.map ResolvedExternalLeg.forget := rfl

/-- Vertex count of a resolved subgraph. -/
def vertexCount (γ : ResolvedFeynmanSubgraph G) : ℕ := γ.vertices.card

/-- A resolved subgraph is nonempty if it has at least one vertex. -/
def IsNonempty (γ : ResolvedFeynmanSubgraph G) : Prop := 0 < γ.vertexCount

@[simp] theorem vertexCount_def (γ : ResolvedFeynmanSubgraph G) :
    γ.vertexCount = γ.vertices.card := rfl

/-- **Spine compatibility (Phase 1a headline).**  Forgetting a resolved subgraph
and then taking its intrinsic flat graph equals taking the intrinsic resolved
graph and then forgetting: `forget` commutes with `toFeynmanGraph` /
`toResolvedFeynmanGraph`.  Holds by `rfl` (both sides are the flat graph
`{γ.vertices, γ.internalEdges.map forget, γ.externalLegs.map forget}`). -/
theorem forget_toFeynmanGraph (γ : ResolvedFeynmanSubgraph G) :
    γ.forget.toFeynmanGraph = γ.toResolvedFeynmanGraph.forget := rfl

/-- Two resolved subgraphs are disjoint iff their vertex sets are (mirrors the
flat `FeynmanSubgraph.Disjoint`). -/
def Disjoint (γ δ : ResolvedFeynmanSubgraph G) : Prop :=
  _root_.Disjoint γ.vertices δ.vertices

theorem Disjoint.symm {γ δ : ResolvedFeynmanSubgraph G} (h : γ.Disjoint δ) :
    δ.Disjoint γ := _root_.Disjoint.symm h

/-- Disjointness is preserved (in fact reflected, `rfl`) by `forget`: the flat
forgotten subgraphs are disjoint iff the resolved ones are. -/
@[simp] theorem forget_disjoint_iff {γ δ : ResolvedFeynmanSubgraph G} :
    γ.forget.Disjoint δ.forget ↔ γ.Disjoint δ := Iff.rfl

end ResolvedFeynmanSubgraph

/-! ## Phase 1b — resolved admissible subgraph (forest carrier)

The resolved analogue of `AdmissibleSubgraph`: a finite set of resolved
subgraphs that are (i) connected-divergent *after forgetting* and (ii) pairwise
vertex-disjoint.  Divergence is inherited via the forgetful projection — resolved
graphs carry no power-counting of their own; their physical content is read off
`forget`.  Hence `DivergenceMeasure` is required only on the flat ambient
`G.forget`, supplied by the global power-counting environment. -/

variable [∀ H : FeynmanGraph, DivergenceMeasure H]

/-- A boundary-resolved admissible subgraph of `G`: a finite forest of resolved
subgraphs, connected-divergent under `forget`, pairwise vertex-disjoint.  This is
the resolved carrier of components to be contracted in later phases. -/
structure ResolvedAdmissibleSubgraph (G : ResolvedFeynmanGraph) where
  elements : Finset (ResolvedFeynmanSubgraph G)
  isConnectedDivergent : ∀ γ ∈ elements, γ.forget.IsConnectedDivergent
  pairwiseDisjoint :
    ∀ ⦃γ⦄, γ ∈ elements → ∀ ⦃δ⦄, δ ∈ elements → γ ≠ δ → γ.Disjoint δ

namespace ResolvedAdmissibleSubgraph

variable {G : ResolvedFeynmanGraph}

/-- Vertices covered by the components. -/
def vertices (A : ResolvedAdmissibleSubgraph G) : Finset VertexId :=
  A.elements.biUnion (fun γ => γ.vertices)

/-- Internal edges aggregated across the components. -/
def internalEdges (A : ResolvedAdmissibleSubgraph G) : Multiset ResolvedFeynmanEdge :=
  A.elements.sum (fun γ => γ.internalEdges)

/-- External legs aggregated across the components. -/
def externalLegs (A : ResolvedAdmissibleSubgraph G) : Multiset ResolvedExternalLeg :=
  A.elements.sum (fun γ => γ.externalLegs)

/-- All components are vertex-nonempty (a hypothesis the contraction layer needs). -/
def HasNonemptyComponents (A : ResolvedAdmissibleSubgraph G) : Prop :=
  ∀ γ ∈ A.elements, γ.IsNonempty

/-- The pairwise-disjointness predicate, exposed as a named `Prop` for API parity
with the flat `Forest.IsPairwiseDisjoint`. -/
def IsPairwiseDisjoint (A : ResolvedAdmissibleSubgraph G) : Prop :=
  ∀ ⦃γ⦄, γ ∈ A.elements → ∀ ⦃δ⦄, δ ∈ A.elements → γ ≠ δ → γ.Disjoint δ

theorem isPairwiseDisjoint (A : ResolvedAdmissibleSubgraph G) : A.IsPairwiseDisjoint :=
  A.pairwiseDisjoint

/-- **Forget to the flat admissible subgraph.**  Components are forgotten
individually and collected; divergence and pairwise-disjointness transport along
the forgetful projection.  Duplicate forgotten components collapse in the
`Finset.image` — acceptable for the forgetful map. -/
def forget (A : ResolvedAdmissibleSubgraph G) : AdmissibleSubgraph G.forget where
  forest :=
    { elements := A.elements.image ResolvedFeynmanSubgraph.forget
      divergent := by
        intro γ' hγ'
        obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hγ'
        exact (A.isConnectedDivergent δ hδ).isDivergent
      nestedOrDisjoint := by
        intro γ₁' h₁ γ₂' h₂ hne
        obtain ⟨δ₁, hδ₁, rfl⟩ := Finset.mem_image.mp h₁
        obtain ⟨δ₂, hδ₂, rfl⟩ := Finset.mem_image.mp h₂
        exact Or.inr (A.pairwiseDisjoint hδ₁ hδ₂ (fun h => hne (by rw [h]))) }
  isConnectedDivergent := by
    intro γ' hγ'
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hγ'
    exact A.isConnectedDivergent δ hδ

@[simp] theorem forget_elements (A : ResolvedAdmissibleSubgraph G) :
    A.forget.elements = A.elements.image ResolvedFeynmanSubgraph.forget := rfl

/-! ### Phase 1c — resolved contraction spine

`componentAt` picks the component containing a vertex; `retargetVertex` collapses
each component's vertices to a caller-supplied star; `contractWithStars` rewrites
the complement edges/legs through that map.  All mirror the flat
`AdmissibleSubgraph` API.  The headline `forget_contractWithStars` shows that
forgetting the resolved contraction is the flat retarget of the *forgotten*
complement — the honest projection (it does **not** equal the flat
`contractWithStars`, because `forget` does not distribute over multiset
subtraction; that non-distribution is exactly the boundary collapse Track R
repairs). -/

@[simp] theorem mem_vertices {A : ResolvedAdmissibleSubgraph G} {v : VertexId} :
    v ∈ A.vertices ↔ ∃ γ ∈ A.elements, v ∈ γ.vertices := by
  simp [vertices]

/-- The chosen component of `A` containing a vertex `v` of its carrier. -/
noncomputable def componentAt (A : ResolvedAdmissibleSubgraph G)
    {v : VertexId} (hv : v ∈ A.vertices) : ResolvedFeynmanSubgraph G :=
  Classical.choose (mem_vertices.mp hv)

theorem componentAt_mem (A : ResolvedAdmissibleSubgraph G)
    {v : VertexId} (hv : v ∈ A.vertices) :
    A.componentAt hv ∈ A.elements :=
  (Classical.choose_spec (mem_vertices.mp hv)).1

theorem componentAt_vertex_mem (A : ResolvedAdmissibleSubgraph G)
    {v : VertexId} (hv : v ∈ A.vertices) :
    v ∈ (A.componentAt hv).vertices :=
  (Classical.choose_spec (mem_vertices.mp hv)).2

/-- Optional component lookup: the chosen containing component inside the carrier,
`none` outside it. -/
noncomputable def componentAt? (A : ResolvedAdmissibleSubgraph G)
    (v : VertexId) : Option (ResolvedFeynmanSubgraph G) :=
  if hv : v ∈ A.vertices then some (A.componentAt hv) else none

@[simp] theorem componentAt?_of_not_mem (A : ResolvedAdmissibleSubgraph G)
    {v : VertexId} (hv : v ∉ A.vertices) :
    A.componentAt? v = none := by
  unfold componentAt?; rw [dif_neg hv]

theorem componentAt?_of_mem (A : ResolvedAdmissibleSubgraph G)
    {v : VertexId} (hv : v ∈ A.vertices) :
    A.componentAt? v = some (A.componentAt hv) := by
  unfold componentAt?; rw [dif_pos hv]

/-- Vertex retarget: send each component's vertices to its star, fix the rest. -/
noncomputable def retargetVertex (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) (v : VertexId) : VertexId :=
  match A.componentAt? v with
  | some γ => starOf γ
  | none => v

@[simp] theorem retargetVertex_of_not_mem
    (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    {v : VertexId} (hv : v ∉ A.vertices) :
    A.retargetVertex starOf v = v := by
  rw [retargetVertex, componentAt?_of_not_mem A hv]

/-- Star vertices: the image of the components under the star assignment. -/
def starVertices (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) : Finset VertexId :=
  A.elements.image starOf

@[simp] theorem mem_starVertices
    {A : ResolvedAdmissibleSubgraph G}
    {starOf : ResolvedFeynmanSubgraph G → VertexId} {v : VertexId} :
    v ∈ A.starVertices starOf ↔ ∃ γ ∈ A.elements, starOf γ = v := by
  simp [starVertices]

/-- Complement edges of `A`: the internal edges of `G` not lying in any
component (multiset difference), mirroring flat `complementEdges`. -/
def complementEdges (A : ResolvedAdmissibleSubgraph G) : Multiset ResolvedFeynmanEdge :=
  G.internalEdges - A.internalEdges

/-- Retarget an internal edge through `A` (identity-preserving: `edgeId` kept). -/
noncomputable def retargetEdge (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (e : ResolvedFeynmanEdge) : ResolvedFeynmanEdge :=
  e.retarget (A.retargetVertex starOf)

/-- Retarget an external leg through `A` (identity-preserving: `legId` kept). -/
noncomputable def retargetExternalLeg (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (ℓ : ResolvedExternalLeg) : ResolvedExternalLeg :=
  ℓ.retarget (A.retargetVertex starOf)

/-- **Resolved star-contraction.**  Mirrors the flat `contractWithStars`: the
complement edges and all external legs are retargeted through `A`, with each
component collapsed to its star vertex. -/
noncomputable def contractWithStars (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) : ResolvedFeynmanGraph where
  vertices := (G.vertices \ A.vertices) ∪ A.starVertices starOf
  internalEdges := A.complementEdges.map (A.retargetEdge starOf)
  externalLegs := G.externalLegs.map (A.retargetExternalLeg starOf)

@[simp] theorem contractWithStars_vertices
    (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) :
    (A.contractWithStars starOf).vertices =
      (G.vertices \ A.vertices) ∪ A.starVertices starOf := rfl

@[simp] theorem contractWithStars_internalEdges
    (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) :
    (A.contractWithStars starOf).internalEdges =
      A.complementEdges.map (A.retargetEdge starOf) := rfl

@[simp] theorem contractWithStars_externalLegs
    (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) :
    (A.contractWithStars starOf).externalLegs =
      G.externalLegs.map (A.retargetExternalLeg starOf) := rfl

/-- **Forgetful compatibility of the resolved contraction (R-4-link, contraction
level).**  Forgetting the resolved star-contraction equals retargeting the
*forgotten* complement edges / external legs by the same vertex map.  The flat
endpoint/attachment rewrite is the forgetful image of the resolved one.

This is stated as the honest projection onto `A.complementEdges.map forget` (not
onto the flat `A.forget.contractWithStars`): `forget` does **not** commute with
the multiset subtraction defining `complementEdges`, which is precisely the
boundary collapse the resolved carrier prevents. -/
theorem forget_contractWithStars (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) :
    (A.contractWithStars starOf).forget =
      { vertices := (G.vertices \ A.vertices) ∪ A.starVertices starOf
        internalEdges := (A.complementEdges.map ResolvedFeynmanEdge.forget).map
          (fun e => { source := A.retargetVertex starOf e.source,
                      target := A.retargetVertex starOf e.target, sector := e.sector })
        externalLegs := (G.externalLegs.map ResolvedExternalLeg.forget).map
          (fun ℓ => { attachedTo := A.retargetVertex starOf ℓ.attachedTo,
                      sector := ℓ.sector }) } := by
  show ResolvedFeynmanGraph.forget _ = _
  unfold ResolvedFeynmanGraph.forget
  congr 1
  · show (A.complementEdges.map (A.retargetEdge starOf)).map ResolvedFeynmanEdge.forget = _
    rw [Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl (fun e _ => rfl)
  · show (G.externalLegs.map (A.retargetExternalLeg starOf)).map ResolvedExternalLeg.forget = _
    rw [Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl (fun ℓ _ => rfl)

/-! ### Phase 1d — resolved retarget / quotient-remainder subgraph spine

`retargetVertex` sends every ambient vertex into the contracted vertex set;
`retargetSubgraph` / `quotientRemainderSubgraph` lift a source subgraph `γ` into
the contracted graph (the remainder version first deletes the outer forest's
internal edges).  Both mirror the flat
`admissibleSubgraph(Retarget|QuotientRemainder)Subgraph`.  Forget compatibility is
recorded field-wise (honest projection: forget of the resolved remainder is the
flat retarget of the *forgotten* remnant edges/legs). -/

/-- The vertex retarget lands in the contracted vertex set (mirrors flat). -/
theorem retargetVertex_mem_contractWithStars_vertices
    (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    {v : VertexId} (hvG : v ∈ G.vertices) :
    A.retargetVertex starOf v ∈ (A.contractWithStars starOf).vertices := by
  rw [contractWithStars_vertices]
  by_cases hvA : v ∈ A.vertices
  · rw [retargetVertex, componentAt?_of_mem A hvA, Finset.mem_union]
    exact Or.inr (mem_starVertices.mpr ⟨A.componentAt hvA, A.componentAt_mem hvA, rfl⟩)
  · rw [retargetVertex_of_not_mem A starOf hvA, Finset.mem_union]
    exact Or.inl (Finset.mem_sdiff.mpr ⟨hvG, hvA⟩)

/-- The remnant `γ.internalEdges - A.internalEdges` lies in the outer complement
(pure multiset count argument; mirrors flat). -/
theorem sub_internalEdges_le_complementEdges
    (A : ResolvedAdmissibleSubgraph G) (γ : ResolvedFeynmanSubgraph G) :
    γ.internalEdges - A.internalEdges ≤ A.complementEdges := by
  rw [Multiset.le_iff_count]
  intro e
  unfold complementEdges
  rw [Multiset.count_sub, Multiset.count_sub]
  have hle := Multiset.count_le_of_le e γ.internalEdges_le
  omega

/-- Retarget a source subgraph `γ` (whose edges lie in the outer complement) into
the contracted graph.  Mirrors flat `admissibleSubgraphRetargetSubgraph`. -/
noncomputable def retargetSubgraph
    (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (γ : ResolvedFeynmanSubgraph G)
    (hEdges : γ.internalEdges ≤ A.complementEdges) :
    ResolvedFeynmanSubgraph (A.contractWithStars starOf) where
  vertices := γ.vertices.image (A.retargetVertex starOf)
  internalEdges := γ.internalEdges.map (A.retargetEdge starOf)
  externalLegs := γ.externalLegs.map (A.retargetExternalLeg starOf)
  vertices_subset := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨u, hu, rfl⟩
    exact A.retargetVertex_mem_contractWithStars_vertices starOf (γ.vertices_subset hu)
  internalEdges_le := by
    rw [contractWithStars_internalEdges]; exact Multiset.map_le_map hEdges
  externalLegs_le := by
    rw [contractWithStars_externalLegs]; exact Multiset.map_le_map γ.externalLegs_le
  edges_supported := by
    intro e' he'
    rcases Multiset.mem_map.mp he' with ⟨e, he, rfl⟩
    obtain ⟨hs, ht⟩ := γ.edges_supported e he
    exact ⟨Finset.mem_image.mpr ⟨e.source, hs, rfl⟩,
           Finset.mem_image.mpr ⟨e.target, ht, rfl⟩⟩
  legs_supported := by
    intro ℓ' hℓ'
    rcases Multiset.mem_map.mp hℓ' with ⟨ℓ, hℓ, rfl⟩
    exact Finset.mem_image.mpr ⟨ℓ.attachedTo, γ.legs_supported ℓ hℓ, rfl⟩

/-- Retarget the quotient remnant of `γ` (after deleting the outer forest's
internal edges) into the contracted graph.  Mirrors flat
`admissibleSubgraphQuotientRemainderSubgraph`. -/
noncomputable def quotientRemainderSubgraph
    (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (γ : ResolvedFeynmanSubgraph G) :
    ResolvedFeynmanSubgraph (A.contractWithStars starOf) where
  vertices := γ.vertices.image (A.retargetVertex starOf)
  internalEdges := (γ.internalEdges - A.internalEdges).map (A.retargetEdge starOf)
  externalLegs := γ.externalLegs.map (A.retargetExternalLeg starOf)
  vertices_subset := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨u, hu, rfl⟩
    exact A.retargetVertex_mem_contractWithStars_vertices starOf (γ.vertices_subset hu)
  internalEdges_le := by
    rw [contractWithStars_internalEdges]
    exact Multiset.map_le_map (A.sub_internalEdges_le_complementEdges γ)
  externalLegs_le := by
    rw [contractWithStars_externalLegs]; exact Multiset.map_le_map γ.externalLegs_le
  edges_supported := by
    intro e' he'
    rcases Multiset.mem_map.mp he' with ⟨e, he, rfl⟩
    have heγ : e ∈ γ.internalEdges :=
      Multiset.mem_of_le (Multiset.sub_le_self _ _) he
    obtain ⟨hs, ht⟩ := γ.edges_supported e heγ
    exact ⟨Finset.mem_image.mpr ⟨e.source, hs, rfl⟩,
           Finset.mem_image.mpr ⟨e.target, ht, rfl⟩⟩
  legs_supported := by
    intro ℓ' hℓ'
    rcases Multiset.mem_map.mp hℓ' with ⟨ℓ, hℓ, rfl⟩
    exact Finset.mem_image.mpr ⟨ℓ.attachedTo, γ.legs_supported ℓ hℓ, rfl⟩

@[simp] theorem quotientRemainderSubgraph_vertices
    (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (γ : ResolvedFeynmanSubgraph G) :
    (A.quotientRemainderSubgraph starOf γ).vertices =
      γ.vertices.image (A.retargetVertex starOf) := rfl

@[simp] theorem quotientRemainderSubgraph_internalEdges
    (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (γ : ResolvedFeynmanSubgraph G) :
    (A.quotientRemainderSubgraph starOf γ).internalEdges =
      (γ.internalEdges - A.internalEdges).map (A.retargetEdge starOf) := rfl

@[simp] theorem quotientRemainderSubgraph_externalLegs
    (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (γ : ResolvedFeynmanSubgraph G) :
    (A.quotientRemainderSubgraph starOf γ).externalLegs =
      γ.externalLegs.map (A.retargetExternalLeg starOf) := rfl

/-- Forget compatibility (remainder, vertices): the forgotten remainder's vertex
set is the retarget-image of `γ`'s vertices. -/
@[simp] theorem forget_quotientRemainderSubgraph_vertices
    (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (γ : ResolvedFeynmanSubgraph G) :
    (A.quotientRemainderSubgraph starOf γ).forget.vertices =
      γ.vertices.image (A.retargetVertex starOf) := rfl

/-- Forget compatibility (remainder, internal edges): forgetting the resolved
remainder equals the flat endpoint-rewrite of the *forgotten* remnant edges. -/
theorem forget_quotientRemainderSubgraph_internalEdges
    (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (γ : ResolvedFeynmanSubgraph G) :
    (A.quotientRemainderSubgraph starOf γ).forget.internalEdges =
      ((γ.internalEdges - A.internalEdges).map ResolvedFeynmanEdge.forget).map
        (fun e => { source := A.retargetVertex starOf e.source,
                    target := A.retargetVertex starOf e.target, sector := e.sector }) := by
  show ((γ.internalEdges - A.internalEdges).map (A.retargetEdge starOf)).map
      ResolvedFeynmanEdge.forget = _
  rw [Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl (fun e _ => rfl)

/-- Forget compatibility (remainder, external legs). -/
theorem forget_quotientRemainderSubgraph_externalLegs
    (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (γ : ResolvedFeynmanSubgraph G) :
    (A.quotientRemainderSubgraph starOf γ).forget.externalLegs =
      (γ.externalLegs.map ResolvedExternalLeg.forget).map
        (fun ℓ => { attachedTo := A.retargetVertex starOf ℓ.attachedTo,
                    sector := ℓ.sector }) := by
  show (γ.externalLegs.map (A.retargetExternalLeg starOf)).map
      ResolvedExternalLeg.forget = _
  rw [Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl (fun ℓ _ => rfl)

end ResolvedAdmissibleSubgraph

end GaugeGeometry.QFT.Combinatorial
