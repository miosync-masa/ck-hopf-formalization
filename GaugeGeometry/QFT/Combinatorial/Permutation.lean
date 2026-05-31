import GaugeGeometry.QFT.Combinatorial.FeynmanGraphs
import GaugeGeometry.QFT.Combinatorial.SupportGraph
import GaugeGeometry.QFT.Combinatorial.SubGraph
import Mathlib.GroupTheory.Perm.Basic

/-!
# Vertex permutations and graph isomorphism transport

This file introduces the action of `Equiv.Perm VertexId` on Feynman graphs,
Feynman subgraphs, and their associated combinatorial data, together with
the basic invariance lemmas (vertex count, internal edge count, external
leg count, loop number) that such transports preserve.

The action is *left*: for `π : Equiv.Perm VertexId`, the new source vertex
of an edge `e` is `π e.source`.

The main outputs are:

* `FeynmanEdge.map`, `ExternalLeg.map` — transport on individual edges/legs
* `FeynmanGraph.mapPerm` — transport on whole graphs
* `FeynmanSubgraph.mapPerm` — transport on subgraphs
* invariance of `vertexCount`, `internalEdgeCount`, `externalLegCount`,
  `loopNumber`
* a `MulAction (Equiv.Perm VertexId) FeynmanGraph` instance

This file stays on the labeled-multigraph side; the passage to isomorphism
*classes* (i.e. orbit quotients) is deferred to a later file.
-/

namespace GaugeGeometry.QFT.Combinatorial

/-!
### Pointwise transport on edges and legs
-/

namespace FeynmanEdge

/-- Transport an edge along a vertex permutation. -/
def map (π : Equiv.Perm VertexId) (e : FeynmanEdge) : FeynmanEdge where
  source := π e.source
  target := π e.target
  sector := e.sector

@[simp] theorem map_source (π : Equiv.Perm VertexId) (e : FeynmanEdge) :
    (e.map π).source = π e.source := rfl

@[simp] theorem map_target (π : Equiv.Perm VertexId) (e : FeynmanEdge) :
    (e.map π).target = π e.target := rfl

@[simp] theorem map_sector (π : Equiv.Perm VertexId) (e : FeynmanEdge) :
    (e.map π).sector = e.sector := rfl

@[simp] theorem map_one (e : FeynmanEdge) : e.map 1 = e := by
  cases e; rfl

@[simp] theorem map_mul (π σ : Equiv.Perm VertexId) (e : FeynmanEdge) :
    e.map (π * σ) = (e.map σ).map π := by
  cases e; rfl

@[simp] theorem map_isSelfLoop_iff (π : Equiv.Perm VertexId) (e : FeynmanEdge) :
    (e.map π).IsSelfLoop ↔ e.IsSelfLoop := by
  unfold IsSelfLoop
  simp [map]

end FeynmanEdge

namespace ExternalLeg

/-- Transport an external leg along a vertex permutation. -/
def map (π : Equiv.Perm VertexId) (ℓ : ExternalLeg) : ExternalLeg where
  attachedTo := π ℓ.attachedTo
  sector := ℓ.sector

@[simp] theorem map_attachedTo (π : Equiv.Perm VertexId) (ℓ : ExternalLeg) :
    (ℓ.map π).attachedTo = π ℓ.attachedTo := rfl

@[simp] theorem map_sector (π : Equiv.Perm VertexId) (ℓ : ExternalLeg) :
    (ℓ.map π).sector = ℓ.sector := rfl

@[simp] theorem map_one (ℓ : ExternalLeg) : ℓ.map 1 = ℓ := by
  cases ℓ; rfl

@[simp] theorem map_mul (π σ : Equiv.Perm VertexId) (ℓ : ExternalLeg) :
    ℓ.map (π * σ) = (ℓ.map σ).map π := by
  cases ℓ; rfl

end ExternalLeg

/-!
### Transport on graphs
-/

namespace FeynmanGraph

/-- Transport a Feynman graph along a vertex permutation. -/
def mapPerm (π : Equiv.Perm VertexId) (G : FeynmanGraph) : FeynmanGraph where
  vertices := G.vertices.image π
  internalEdges := G.internalEdges.map (FeynmanEdge.map π)
  externalLegs := G.externalLegs.map (ExternalLeg.map π)

@[simp] theorem mapPerm_vertices (π : Equiv.Perm VertexId) (G : FeynmanGraph) :
    (G.mapPerm π).vertices = G.vertices.image π := rfl

@[simp] theorem mapPerm_internalEdges (π : Equiv.Perm VertexId)
    (G : FeynmanGraph) :
    (G.mapPerm π).internalEdges = G.internalEdges.map (FeynmanEdge.map π) := rfl

@[simp] theorem mapPerm_externalLegs (π : Equiv.Perm VertexId)
    (G : FeynmanGraph) :
    (G.mapPerm π).externalLegs = G.externalLegs.map (ExternalLeg.map π) := rfl

@[simp] theorem mapPerm_one (G : FeynmanGraph) : G.mapPerm 1 = G := by
  unfold mapPerm
  have hV : G.vertices.image (1 : Equiv.Perm VertexId) = G.vertices := by
    ext v; simp
  have hI : G.internalEdges.map (FeynmanEdge.map 1) = G.internalEdges := by
    simp [FeynmanEdge.map_one]
  have hE : G.externalLegs.map (ExternalLeg.map 1) = G.externalLegs := by
    simp [ExternalLeg.map_one]
  rw [hV, hI, hE]

theorem mapPerm_mul (π σ : Equiv.Perm VertexId) (G : FeynmanGraph) :
    G.mapPerm (π * σ) = (G.mapPerm σ).mapPerm π := by
  unfold mapPerm
  have hV : G.vertices.image (π * σ) = (G.vertices.image σ).image π := by
    rw [show ((π * σ : Equiv.Perm VertexId) : VertexId → VertexId)
        = (π : VertexId → VertexId) ∘ (σ : VertexId → VertexId) from rfl]
    exact Finset.image_image.symm
  have hI :
      G.internalEdges.map (FeynmanEdge.map (π * σ))
        = (G.internalEdges.map (FeynmanEdge.map σ)).map (FeynmanEdge.map π) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl ?_
    intro e _
    simp [FeynmanEdge.map_mul]
  have hE :
      G.externalLegs.map (ExternalLeg.map (π * σ))
        = (G.externalLegs.map (ExternalLeg.map σ)).map (ExternalLeg.map π) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl ?_
    intro ℓ _
    simp [ExternalLeg.map_mul]
  rw [hV, hI, hE]

/-!
### Invariance of counts under vertex permutations
-/

@[simp] theorem mapPerm_vertexCount (π : Equiv.Perm VertexId) (G : FeynmanGraph) :
    (G.mapPerm π).vertexCount = G.vertexCount := by
  unfold vertexCount
  simp [mapPerm_vertices, Finset.card_image_of_injective _ π.injective]

@[simp] theorem mapPerm_internalEdgeCount (π : Equiv.Perm VertexId)
    (G : FeynmanGraph) :
    (G.mapPerm π).internalEdgeCount = G.internalEdgeCount := by
  unfold internalEdgeCount
  simp [mapPerm_internalEdges]

@[simp] theorem mapPerm_externalLegCount (π : Equiv.Perm VertexId)
    (G : FeynmanGraph) :
    (G.mapPerm π).externalLegCount = G.externalLegCount := by
  unfold externalLegCount
  simp [mapPerm_externalLegs]

@[simp] theorem mapPerm_loopNumber (π : Equiv.Perm VertexId) (G : FeynmanGraph) :
    (G.mapPerm π).loopNumber = G.loopNumber := by
  unfold loopNumber
  simp

/-!
### Transport of well-formedness and adjacency
-/

theorem mapPerm_wellFormed {π : Equiv.Perm VertexId} {G : FeynmanGraph}
    (hG : G.WellFormed) : (G.mapPerm π).WellFormed := by
  refine ⟨?_, ?_⟩
  · intro e' he'
    rcases Multiset.mem_map.mp he' with ⟨e, heG, rfl⟩
    have hsupp := hG.1 e heG
    refine ⟨?_, ?_⟩
    · simp [FeynmanEdge.SupportedOn] at hsupp
      exact Finset.mem_image.mpr ⟨e.source, hsupp.1, rfl⟩
    · simp [FeynmanEdge.SupportedOn] at hsupp
      exact Finset.mem_image.mpr ⟨e.target, hsupp.2, rfl⟩
  · intro ℓ' hℓ'
    rcases Multiset.mem_map.mp hℓ' with ⟨ℓ, hℓG, rfl⟩
    have hsupp := hG.2 ℓ hℓG
    simp [ExternalLeg.SupportedOn] at hsupp
    exact Finset.mem_image.mpr ⟨ℓ.attachedTo, hsupp, rfl⟩

/--
`Adjacent` transports along vertex permutations.
-/
theorem mapPerm_adjacent_iff (π : Equiv.Perm VertexId) (G : FeynmanGraph)
    (u v : VertexId) :
    (G.mapPerm π).Adjacent (π u) (π v) ↔ G.Adjacent u v := by
  unfold Adjacent
  constructor
  · rintro ⟨e', he', hend⟩
    rcases Multiset.mem_map.mp he' with ⟨e, heG, rfl⟩
    refine ⟨e, heG, ?_⟩
    rcases hend with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · left
      exact ⟨π.injective (by simpa using hs),
             π.injective (by simpa using ht)⟩
    · right
      exact ⟨π.injective (by simpa using hs),
             π.injective (by simpa using ht)⟩
  · rintro ⟨e, heG, hend⟩
    refine ⟨e.map π, ?_, ?_⟩
    · exact Multiset.mem_map.mpr ⟨e, heG, rfl⟩
    · rcases hend with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · left; simp [FeynmanEdge.map, hs, ht]
      · right; simp [FeynmanEdge.map, hs, ht]

/-!
### H0.11 — Permutation invariance of 1PI

Support adjacency, reachability, connectedness, bridges, and the 1PI
predicate all transport along vertex permutations. Under the `MulAction`
this says: for every `π : Equiv.Perm VertexId`, `(π • G).IsOnePI ↔
G.IsOnePI`.
-/

/-- `FeynmanEdge.map π` is injective because `π` is. -/
theorem FeynmanEdge_map_injective (π : Equiv.Perm VertexId) :
    Function.Injective (FeynmanEdge.map π) := by
  intro e₁ e₂ h
  have hs : (e₁.map π).source = (e₂.map π).source := congrArg FeynmanEdge.source h
  have ht : (e₁.map π).target = (e₂.map π).target := congrArg FeynmanEdge.target h
  have hsec : (e₁.map π).sector = (e₂.map π).sector := congrArg FeynmanEdge.sector h
  rw [FeynmanEdge.map_source, FeynmanEdge.map_source] at hs
  rw [FeynmanEdge.map_target, FeynmanEdge.map_target] at ht
  rw [FeynmanEdge.map_sector, FeynmanEdge.map_sector] at hsec
  have hs' : e₁.source = e₂.source := π.injective hs
  have ht' : e₁.target = e₂.target := π.injective ht
  cases e₁; cases e₂
  simp_all

/-- Support adjacency transports along vertex permutations. -/
theorem mapPerm_supportAdj_iff (π : Equiv.Perm VertexId) (G : FeynmanGraph)
    (u v : VertexId) :
    (G.mapPerm π).SupportAdj (π u) (π v) ↔ G.SupportAdj u v := by
  unfold SupportAdj
  constructor
  · rintro ⟨hne, e', he', hend⟩
    have hne' : u ≠ v := fun h => hne (by rw [h])
    rcases Multiset.mem_map.mp he' with ⟨e, heG, rfl⟩
    refine ⟨hne', e, heG, ?_⟩
    rcases hend with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · left
      exact ⟨π.injective (by simpa using hs),
             π.injective (by simpa using ht)⟩
    · right
      exact ⟨π.injective (by simpa using hs),
             π.injective (by simpa using ht)⟩
  · rintro ⟨hne, e, heG, hend⟩
    refine ⟨fun h => hne (π.injective h), e.map π, ?_, ?_⟩
    · exact Multiset.mem_map.mpr ⟨e, heG, rfl⟩
    · rcases hend with ⟨hs, ht⟩ | ⟨hs, ht⟩
      · left; simp [FeynmanEdge.map, hs, ht]
      · right; simp [FeynmanEdge.map, hs, ht]

/-- The underlying `SimpleGraph.Adj` of the permuted graph relates `π u`
and `π v` iff the original relates `u` and `v`. -/
theorem mapPerm_toSimpleGraph_adj_iff (π : Equiv.Perm VertexId)
    (G : FeynmanGraph) (u v : VertexId) :
    (G.mapPerm π).toSimpleGraph.Adj (π u) (π v) ↔
      G.toSimpleGraph.Adj u v := by
  simp [toSimpleGraph_adj, mapPerm_supportAdj_iff]

/-- Helper: a reflexive-transitive chain in the permuted graph between
any two vertices `a` and `b` gives a chain in the original graph
between `π.symm a` and `π.symm b`. -/
theorem mapPerm_reflTransGen_symm
    (π : Equiv.Perm VertexId) (G : FeynmanGraph) :
    ∀ {a b : VertexId},
      Relation.ReflTransGen (G.mapPerm π).toSimpleGraph.Adj a b →
        Relation.ReflTransGen G.toSimpleGraph.Adj (π.symm a) (π.symm b) := by
  intro a b h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail x y _ hxy ih =>
    have hAdj : G.toSimpleGraph.Adj (π.symm x) (π.symm y) := by
      have := (mapPerm_toSimpleGraph_adj_iff π G (π.symm x) (π.symm y))
      rw [π.apply_symm_apply, π.apply_symm_apply] at this
      exact this.mp hxy
    exact Relation.ReflTransGen.tail ih hAdj

/-- Helper: a reflexive-transitive chain in the original graph between
`a` and `b` gives a chain in the permuted graph between `π a` and `π b`. -/
theorem mapPerm_reflTransGen
    (π : Equiv.Perm VertexId) (G : FeynmanGraph) :
    ∀ {a b : VertexId},
      Relation.ReflTransGen G.toSimpleGraph.Adj a b →
        Relation.ReflTransGen (G.mapPerm π).toSimpleGraph.Adj (π a) (π b) := by
  intro a b h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail x y _ hxy ih =>
    have hAdj : (G.mapPerm π).toSimpleGraph.Adj (π x) (π y) :=
      (mapPerm_toSimpleGraph_adj_iff π G x y).mpr hxy
    exact Relation.ReflTransGen.tail ih hAdj

/-- Support reachability transports along vertex permutations. -/
theorem mapPerm_supportReachable_iff (π : Equiv.Perm VertexId)
    (G : FeynmanGraph) (u v : VertexId) :
    (G.mapPerm π).SupportReachable (π u) (π v) ↔ G.SupportReachable u v := by
  unfold SupportReachable
  rw [SimpleGraph.reachable_iff_reflTransGen,
      SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    have := mapPerm_reflTransGen_symm π G h
    simpa using this
  · intro h
    exact mapPerm_reflTransGen π G h

/-- Support connectedness is invariant under vertex permutations. -/
theorem mapPerm_isSupportConnected_iff (π : Equiv.Perm VertexId)
    (G : FeynmanGraph) :
    (G.mapPerm π).IsSupportConnected ↔ G.IsSupportConnected := by
  unfold IsSupportConnected
  constructor
  · intro h u v hu hv
    have hu' : π u ∈ (G.mapPerm π).vertices := by
      rw [mapPerm_vertices]; exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
    have hv' : π v ∈ (G.mapPerm π).vertices := by
      rw [mapPerm_vertices]; exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    exact (mapPerm_supportReachable_iff π G u v).mp (h hu' hv')
  · intro h u' v' hu' hv'
    rw [mapPerm_vertices] at hu' hv'
    rcases Finset.mem_image.mp hu' with ⟨u, hu, rfl⟩
    rcases Finset.mem_image.mp hv' with ⟨v, hv, rfl⟩
    exact (mapPerm_supportReachable_iff π G u v).mpr (h hu hv)

/-- `eraseInternalEdge` and `mapPerm` commute. -/
theorem mapPerm_eraseInternalEdge (π : Equiv.Perm VertexId)
    (G : FeynmanGraph) (e : FeynmanEdge) :
    (G.eraseInternalEdge e).mapPerm π =
      (G.mapPerm π).eraseInternalEdge (e.map π) := by
  have hinj : Function.Injective (FeynmanEdge.map π) :=
    FeynmanEdge_map_injective π
  apply FeynmanGraph.mk.injEq _ _ _ _ _ _ |>.mpr
  refine ⟨?_, ?_, ?_⟩
  · -- vertices
    rfl
  · -- internalEdges: use Multiset.map_erase with injectivity
    show (G.internalEdges.erase e).map (FeynmanEdge.map π)
      = (G.internalEdges.map (FeynmanEdge.map π)).erase (e.map π)
    exact Multiset.map_erase (FeynmanEdge.map π) hinj e G.internalEdges
  · -- externalLegs
    rfl

/-- The `IsBridge` predicate transports along vertex permutations. -/
theorem mapPerm_isBridge_iff (π : Equiv.Perm VertexId) (G : FeynmanGraph)
    (e : FeynmanEdge) :
    (G.mapPerm π).IsBridge (e.map π) ↔ G.IsBridge e := by
  unfold IsBridge
  have hinj : Function.Injective (FeynmanEdge.map π) :=
    FeynmanEdge_map_injective π
  have hmem_iff : e.map π ∈ (G.mapPerm π).internalEdges ↔ e ∈ G.internalEdges := by
    rw [mapPerm_internalEdges]
    exact ⟨fun h => by
             rcases Multiset.mem_map.mp h with ⟨e', he', heq⟩
             have : e' = e := hinj heq
             exact this ▸ he',
           fun h => Multiset.mem_map.mpr ⟨e, h, rfl⟩⟩
  have herase :
      ((G.mapPerm π).eraseInternalEdge (e.map π)).IsSupportConnected ↔
        (G.eraseInternalEdge e).IsSupportConnected := by
    rw [← mapPerm_eraseInternalEdge]
    exact mapPerm_isSupportConnected_iff π (G.eraseInternalEdge e)
  rw [hmem_iff, herase]

/-- **H0.11** — The 1PI predicate is invariant under vertex permutations. -/
@[simp] theorem mapPerm_isOnePI_iff (π : Equiv.Perm VertexId) (G : FeynmanGraph) :
    (G.mapPerm π).IsOnePI ↔ G.IsOnePI := by
  unfold IsOnePI
  rw [mapPerm_isSupportConnected_iff]
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro h e he
    have he' : e.map π ∈ (G.mapPerm π).internalEdges := by
      rw [mapPerm_internalEdges]; exact Multiset.mem_map.mpr ⟨e, he, rfl⟩
    intro hbridge
    exact h _ he' ((mapPerm_isBridge_iff π G e).mpr hbridge)
  · intro h e' he'
    rw [mapPerm_internalEdges] at he'
    rcases Multiset.mem_map.mp he' with ⟨e, he, rfl⟩
    intro hbridge
    exact h e he ((mapPerm_isBridge_iff π G e).mp hbridge)

end FeynmanGraph

/-!
### Group action instance

`Equiv.Perm VertexId` acts on `FeynmanGraph` on the left via `mapPerm`.
-/

instance : MulAction (Equiv.Perm VertexId) FeynmanGraph where
  smul π G := G.mapPerm π
  one_smul G := G.mapPerm_one
  mul_smul π σ G := G.mapPerm_mul π σ

@[simp] theorem FeynmanGraph.smul_def (π : Equiv.Perm VertexId) (G : FeynmanGraph) :
    π • G = G.mapPerm π := rfl

/-!
### Transport on subgraphs
-/

namespace FeynmanSubgraph

variable {G : FeynmanGraph}

/-- Transport a Feynman subgraph along a vertex permutation. -/
def mapPerm (π : Equiv.Perm VertexId) (γ : FeynmanSubgraph G) :
    FeynmanSubgraph (G.mapPerm π) where
  vertices := γ.vertices.image π
  internalEdges := γ.internalEdges.map (FeynmanEdge.map π)
  externalLegs := γ.externalLegs.map (ExternalLeg.map π)
  vertices_subset := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨v, hv, rfl⟩
    exact Finset.mem_image.mpr ⟨v, γ.vertices_subset hv, rfl⟩
  internalEdges_le := by
    simp [FeynmanGraph.mapPerm_internalEdges]
    exact Multiset.map_le_map γ.internalEdges_le
  externalLegs_le := by
    simp [FeynmanGraph.mapPerm_externalLegs]
    exact Multiset.map_le_map γ.externalLegs_le
  edges_supported := by
    intro e' he'
    rcases Multiset.mem_map.mp he' with ⟨e, heγ, rfl⟩
    have hsupp := γ.edges_supported e heγ
    refine ⟨?_, ?_⟩
    · simp [FeynmanEdge.SupportedOn] at hsupp
      exact Finset.mem_image.mpr ⟨e.source, hsupp.1, rfl⟩
    · simp [FeynmanEdge.SupportedOn] at hsupp
      exact Finset.mem_image.mpr ⟨e.target, hsupp.2, rfl⟩
  legs_supported := by
    intro ℓ' hℓ'
    rcases Multiset.mem_map.mp hℓ' with ⟨ℓ, hℓγ, rfl⟩
    have hsupp := γ.legs_supported ℓ hℓγ
    simp [ExternalLeg.SupportedOn] at hsupp
    exact Finset.mem_image.mpr ⟨ℓ.attachedTo, hsupp, rfl⟩

@[simp] theorem mapPerm_vertices (π : Equiv.Perm VertexId)
    (γ : FeynmanSubgraph G) :
    (γ.mapPerm π).vertices = γ.vertices.image π := rfl

@[simp] theorem mapPerm_internalEdges (π : Equiv.Perm VertexId)
    (γ : FeynmanSubgraph G) :
    (γ.mapPerm π).internalEdges = γ.internalEdges.map (FeynmanEdge.map π) := rfl

@[simp] theorem mapPerm_externalLegs (π : Equiv.Perm VertexId)
    (γ : FeynmanSubgraph G) :
    (γ.mapPerm π).externalLegs = γ.externalLegs.map (ExternalLeg.map π) := rfl

@[simp] theorem mapPerm_vertexCount (π : Equiv.Perm VertexId)
    (γ : FeynmanSubgraph G) :
    (γ.mapPerm π).vertexCount = γ.vertexCount := by
  unfold vertexCount
  simp [Finset.card_image_of_injective _ π.injective]

@[simp] theorem mapPerm_internalEdgeCount (π : Equiv.Perm VertexId)
    (γ : FeynmanSubgraph G) :
    (γ.mapPerm π).internalEdgeCount = γ.internalEdgeCount := by
  unfold internalEdgeCount
  simp

@[simp] theorem mapPerm_externalLegCount (π : Equiv.Perm VertexId)
    (γ : FeynmanSubgraph G) :
    (γ.mapPerm π).externalLegCount = γ.externalLegCount := by
  unfold externalLegCount
  simp

@[simp] theorem mapPerm_loopNumber (π : Equiv.Perm VertexId)
    (γ : FeynmanSubgraph G) :
    (γ.mapPerm π).loopNumber = γ.loopNumber := by
  unfold loopNumber
  simp

/-!
### Transport of `Disjoint`, `Nested`, `NestedOrDisjoint`

These facts are what allow `Forest.mapPerm` to preserve Zimmermann's
pairwise compatibility condition.
-/

@[simp] theorem mapPerm_disjoint_iff (π : Equiv.Perm VertexId)
    (γ₁ γ₂ : FeynmanSubgraph G) :
    (γ₁.mapPerm π).Disjoint (γ₂.mapPerm π) ↔ γ₁.Disjoint γ₂ := by
  unfold FeynmanSubgraph.Disjoint
  simp only [mapPerm_vertices]
  constructor
  · intro h
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    have hv1' : π v ∈ γ₁.vertices.image π := Finset.mem_image.mpr ⟨v, hv1, rfl⟩
    have hv2' : π v ∈ γ₂.vertices.image π := Finset.mem_image.mpr ⟨v, hv2, rfl⟩
    exact (Finset.disjoint_left.mp h) hv1' hv2'
  · intro h
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    rcases Finset.mem_image.mp hw1 with ⟨v₁, hv₁, rfl⟩
    rcases Finset.mem_image.mp hw2 with ⟨v₂, hv₂, hπ⟩
    have hveq : v₁ = v₂ := π.injective hπ.symm
    subst hveq
    exact (Finset.disjoint_left.mp h) hv₁ hv₂

theorem mapPerm_le_mapPerm {π : Equiv.Perm VertexId}
    {γ₁ γ₂ : FeynmanSubgraph G} (h : γ₁ ≤ γ₂) :
    γ₁.mapPerm π ≤ γ₂.mapPerm π := by
  rw [le_def] at h ⊢
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    rcases Finset.mem_image.mp hw with ⟨v, hv, rfl⟩
    exact Finset.mem_image.mpr ⟨v, h.1 hv, rfl⟩
  · exact Multiset.map_le_map h.2.1
  · exact Multiset.map_le_map h.2.2

theorem le_of_mapPerm_le_mapPerm {π : Equiv.Perm VertexId}
    {γ₁ γ₂ : FeynmanSubgraph G}
    (h : γ₁.mapPerm π ≤ γ₂.mapPerm π) :
    γ₁ ≤ γ₂ := by
  rw [le_def] at h ⊢
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    have hπv : π v ∈ (γ₂.mapPerm π).vertices :=
      h.1 (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
    rcases Finset.mem_image.mp hπv with ⟨v', hv', hπeq⟩
    have : v = v' := π.injective hπeq.symm
    exact this ▸ hv'
  · -- internal edges: use that `Multiset.map (FeynmanEdge.map π)` is injective
    -- because `FeynmanEdge.map π` is injective (since `π` is).
    have hinj : Function.Injective (FeynmanEdge.map π) := by
      intro e₁ e₂ heq
      cases e₁
      cases e₂
      simp [FeynmanEdge.map] at heq
      obtain ⟨hs, ht, hsec⟩ := heq
      simp [hs, ht, hsec]
    exact (Multiset.map_le_map_iff hinj).mp h.2.1
  · have hinj : Function.Injective (ExternalLeg.map π) := by
      intro ℓ₁ ℓ₂ heq
      cases ℓ₁
      cases ℓ₂
      simp [ExternalLeg.map] at heq
      obtain ⟨ha, hsec⟩ := heq
      simp [ha, hsec]
    exact (Multiset.map_le_map_iff hinj).mp h.2.2

@[simp] theorem mapPerm_nested_iff (π : Equiv.Perm VertexId)
    (γ₁ γ₂ : FeynmanSubgraph G) :
    (γ₁.mapPerm π).Nested (γ₂.mapPerm π) ↔ γ₁.Nested γ₂ := by
  unfold FeynmanSubgraph.Nested
  constructor
  · rintro (h | h)
    · exact Or.inl (le_of_mapPerm_le_mapPerm h)
    · exact Or.inr (le_of_mapPerm_le_mapPerm h)
  · rintro (h | h)
    · exact Or.inl (mapPerm_le_mapPerm h)
    · exact Or.inr (mapPerm_le_mapPerm h)

@[simp] theorem mapPerm_nestedOrDisjoint_iff (π : Equiv.Perm VertexId)
    (γ₁ γ₂ : FeynmanSubgraph G) :
    (γ₁.mapPerm π).NestedOrDisjoint (γ₂.mapPerm π) ↔
      γ₁.NestedOrDisjoint γ₂ := by
  unfold FeynmanSubgraph.NestedOrDisjoint
  simp

end FeynmanSubgraph

/-!
### Permutation-invariant divergence measures

A `DivergenceMeasure` on `G` transports to one on `G.mapPerm π` via
`mapPerm`; this transport is expressed by the following invariance class.

Concrete measures (e.g. the MSSM 1-loop measure) should be proven to
satisfy this invariance. Under invariance, `Forest` transports along
vertex permutations.
-/

/--
An instance-level statement that divergence measures on `G` and on
`G.mapPerm π` assign equal degrees to corresponding subgraphs.

This is the minimal data needed to transport `Forest`s along
permutations.
-/
class IsPermInvariantDivergence (G : FeynmanGraph) [DivergenceMeasure G] :
    Prop where
  degree_mapPerm :
    ∀ (π : Equiv.Perm VertexId) [DivergenceMeasure (G.mapPerm π)]
      (γ : FeynmanSubgraph G),
      (DivergenceMeasure.degree (γ.mapPerm π) : Int) =
        DivergenceMeasure.degree γ

namespace FeynmanSubgraph

variable {G : FeynmanGraph}

/--
Under `IsPermInvariantDivergence`, superficial divergence is transported
by `mapPerm`.
-/
theorem mapPerm_isDivergent
    [DivergenceMeasure G] [IsPermInvariantDivergence G]
    {π : Equiv.Perm VertexId} [DivergenceMeasure (G.mapPerm π)]
    {γ : FeynmanSubgraph G} (hγ : γ.IsDivergent) :
    (γ.mapPerm π).IsDivergent := by
  unfold IsDivergent divergenceDegree at hγ ⊢
  rw [IsPermInvariantDivergence.degree_mapPerm π γ]
  exact hγ

end FeynmanSubgraph

namespace Forest

variable {G : FeynmanGraph} [DivergenceMeasure G]

/--
Transport a forest along a vertex permutation `π`, given that the
divergence measure on `G.mapPerm π` agrees with the one on `G` on
corresponding subgraphs.
-/
def mapPerm [IsPermInvariantDivergence G]
    (π : Equiv.Perm VertexId) [DivergenceMeasure (G.mapPerm π)]
    (F : Forest G) : Forest (G.mapPerm π) where
  elements := F.elements.image (FeynmanSubgraph.mapPerm π)
  divergent := by
    intro γ' hγ'
    rcases Finset.mem_image.mp hγ' with ⟨γ, hγ, rfl⟩
    exact FeynmanSubgraph.mapPerm_isDivergent (F.divergent γ hγ)
  nestedOrDisjoint := by
    intro γ₁' h₁ γ₂' h₂ hne
    rcases Finset.mem_image.mp h₁ with ⟨γ₁, hγ₁, rfl⟩
    rcases Finset.mem_image.mp h₂ with ⟨γ₂, hγ₂, rfl⟩
    have hne' : γ₁ ≠ γ₂ := by
      intro h
      apply hne
      rw [h]
    have hcompat := F.nestedOrDisjoint hγ₁ hγ₂ hne'
    exact (FeynmanSubgraph.mapPerm_nestedOrDisjoint_iff π γ₁ γ₂).mpr hcompat

@[simp] theorem mapPerm_elements [IsPermInvariantDivergence G]
    (π : Equiv.Perm VertexId) [DivergenceMeasure (G.mapPerm π)]
    (F : Forest G) :
    (F.mapPerm π).elements =
      F.elements.image (FeynmanSubgraph.mapPerm π) := rfl

end Forest

end GaugeGeometry.QFT.Combinatorial
