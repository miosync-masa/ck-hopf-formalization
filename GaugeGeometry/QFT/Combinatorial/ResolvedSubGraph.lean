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

end ResolvedAdmissibleSubgraph

end GaugeGeometry.QFT.Combinatorial
