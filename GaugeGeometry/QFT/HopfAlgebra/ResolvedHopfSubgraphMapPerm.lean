import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCarrier
import GaugeGeometry.QFT.Combinatorial.ResolvedSubGraph
import GaugeGeometry.QFT.HopfAlgebra.Coproduct

/-!
# R-6b-2a — identity-preserving relabeling of resolved subgraphs

The first geometric piece of the `Δᵣ` well-definedness (R-6b-2): transport a resolved subgraph
along a vertex permutation `σ`, **reusing the same `edgeId`/`legId`-preserving edge/leg relabeling**
(`ResolvedFeynmanEdge.map`/`ResolvedExternalLeg.map`) as `ResolvedFeynmanGraph.mapPerm`.  A resolved
subgraph of `G` becomes a resolved subgraph of `G.mapPerm σ`.

Landed here: `ResolvedFeynmanSubgraph.mapPerm` (+ field simps, `mapPerm_disjoint`), the
forget–mapPerm compatibility bridge `ResolvedFeynmanSubgraph.forget_mapPerm` (HEq — the CD transport
key), and `ResolvedAdmissibleSubgraph.mapPerm` (elements image; disjoint via `mapPerm_disjoint`; CD
via the bridge + flat `FeynmanSubgraph.mapPerm_isConnectedDivergent`).  The `contractWithStars`
equivariance is the next step.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable {G : ResolvedFeynmanGraph}

/-- Transport a resolved subgraph of `G` along a vertex permutation `σ` to a resolved subgraph of
`G.mapPerm σ`, preserving the persistent edge/leg ids (same `ResolvedFeynmanEdge.map`/`.map` used by
`ResolvedFeynmanGraph.mapPerm`). -/
def ResolvedFeynmanSubgraph.mapPerm (σ : Equiv.Perm VertexId)
    (γ : ResolvedFeynmanSubgraph G) : ResolvedFeynmanSubgraph (G.mapPerm σ) where
  vertices := γ.vertices.image σ
  internalEdges := γ.internalEdges.map (ResolvedFeynmanEdge.map σ)
  externalLegs := γ.externalLegs.map (ResolvedExternalLeg.map σ)
  vertices_subset := Finset.image_subset_image γ.vertices_subset
  internalEdges_le := Multiset.map_le_map γ.internalEdges_le
  externalLegs_le := Multiset.map_le_map γ.externalLegs_le
  edges_supported := by
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := Multiset.mem_map.mp he
    obtain ⟨hs, ht⟩ := γ.edges_supported e₀ he₀
    exact ⟨Finset.mem_image_of_mem σ hs, Finset.mem_image_of_mem σ ht⟩
  legs_supported := by
    intro ℓ hℓ
    obtain ⟨ℓ₀, hℓ₀, rfl⟩ := Multiset.mem_map.mp hℓ
    exact Finset.mem_image_of_mem σ (γ.legs_supported ℓ₀ hℓ₀)

@[simp] theorem ResolvedFeynmanSubgraph.mapPerm_vertices (σ : Equiv.Perm VertexId)
    (γ : ResolvedFeynmanSubgraph G) :
    (γ.mapPerm σ).vertices = γ.vertices.image σ := rfl

@[simp] theorem ResolvedFeynmanSubgraph.mapPerm_internalEdges (σ : Equiv.Perm VertexId)
    (γ : ResolvedFeynmanSubgraph G) :
    (γ.mapPerm σ).internalEdges = γ.internalEdges.map (ResolvedFeynmanEdge.map σ) := rfl

@[simp] theorem ResolvedFeynmanSubgraph.mapPerm_externalLegs (σ : Equiv.Perm VertexId)
    (γ : ResolvedFeynmanSubgraph G) :
    (γ.mapPerm σ).externalLegs = γ.externalLegs.map (ResolvedExternalLeg.map σ) := rfl

/-- `mapPerm` preserves disjointness (a resolved subgraph disjointness is vertex disjointness,
and `σ` is injective). -/
theorem ResolvedFeynmanSubgraph.mapPerm_disjoint (σ : Equiv.Perm VertexId)
    {γ δ : ResolvedFeynmanSubgraph G} (h : γ.Disjoint δ) :
    (γ.mapPerm σ).Disjoint (δ.mapPerm σ) := by
  unfold ResolvedFeynmanSubgraph.Disjoint at h ⊢
  simp only [ResolvedFeynmanSubgraph.mapPerm_vertices]
  exact (Finset.disjoint_image σ.injective).mpr h

/-! ## The forget–mapPerm compatibility bridge (the CD transport key) -/

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]

/-- A `HEq` of flat subgraphs from a graph equality plus the three data-field equalities
(the support fields are proof-irrelevant). -/
theorem feynmanSubgraph_heq_of_data {G₁ G₂ : FeynmanGraph} (hg : G₁ = G₂)
    {a : FeynmanSubgraph G₁} {b : FeynmanSubgraph G₂}
    (hv : a.vertices = b.vertices) (hi : a.internalEdges = b.internalEdges)
    (he : a.externalLegs = b.externalLegs) : HEq a b := by
  subst hg
  apply heq_of_eq
  obtain ⟨av, ai, ae, _, _, _, _, _⟩ := a
  obtain ⟨bv, bi, be, _, _, _, _, _⟩ := b
  dsimp only at hv hi he
  subst hv; subst hi; subst he
  rfl

/-- Transport `IsConnectedDivergent` across a `HEq` of subgraphs over equal graphs. -/
theorem feynmanSubgraph_isConnectedDivergent_of_heq {G₁ G₂ : FeynmanGraph} (hg : G₁ = G₂)
    {a : FeynmanSubgraph G₁} {b : FeynmanSubgraph G₂} (hab : HEq a b)
    (hb : b.IsConnectedDivergent) : a.IsConnectedDivergent := by
  subst hg
  obtain rfl := eq_of_heq hab
  exact hb

/-- **R-6b-2c — the forget–mapPerm compatibility bridge.**  Relabeling a resolved subgraph then
forgetting equals forgetting then relabeling (heterogeneously: the index graphs
`(G.mapPerm σ).forget` and `G.forget.mapPerm σ` agree by `ResolvedFeynmanGraph.forget_mapPerm`).
This is the key that lets connected-divergence ride through `mapPerm`. -/
theorem ResolvedFeynmanSubgraph.forget_mapPerm (σ : Equiv.Perm VertexId)
    (γ : ResolvedFeynmanSubgraph G) :
    HEq ((γ.mapPerm σ).forget) (γ.forget.mapPerm σ) := by
  refine feynmanSubgraph_heq_of_data (ResolvedFeynmanGraph.forget_mapPerm σ G) ?_ ?_ ?_
  · simp only [ResolvedFeynmanSubgraph.forget_vertices, ResolvedFeynmanSubgraph.mapPerm_vertices,
      FeynmanSubgraph.mapPerm_vertices]
  · simp only [ResolvedFeynmanSubgraph.forget_internalEdges,
      ResolvedFeynmanSubgraph.mapPerm_internalEdges, FeynmanSubgraph.mapPerm_internalEdges,
      Multiset.map_map]
    exact Multiset.map_congr rfl (fun e _ => by simp)
  · simp only [ResolvedFeynmanSubgraph.forget_externalLegs,
      ResolvedFeynmanSubgraph.mapPerm_externalLegs, FeynmanSubgraph.mapPerm_externalLegs,
      Multiset.map_map]
    exact Multiset.map_congr rfl (fun ℓ _ => by simp)

/-! ## Identity-preserving relabeling of resolved admissible subgraphs -/

/-- Transport a resolved admissible subgraph of `G` along `σ` to one of `G.mapPerm σ`.  Elements
are the relabeled subgraphs; disjointness rides through `mapPerm_disjoint`; connected divergence
rides through the forget–mapPerm bridge + flat `mapPerm_isConnectedDivergent`. -/
noncomputable def ResolvedAdmissibleSubgraph.mapPerm (σ : Equiv.Perm VertexId)
    (A : ResolvedAdmissibleSubgraph G) : ResolvedAdmissibleSubgraph (G.mapPerm σ) where
  elements := A.elements.image (fun γ => γ.mapPerm σ)
  isConnectedDivergent := by
    intro γ' hγ'
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hγ'
    exact feynmanSubgraph_isConnectedDivergent_of_heq (ResolvedFeynmanGraph.forget_mapPerm σ G)
      (ResolvedFeynmanSubgraph.forget_mapPerm σ γ)
      (FeynmanSubgraph.mapPerm_isConnectedDivergent σ (A.isConnectedDivergent γ hγ))
  pairwiseDisjoint := by
    intro γ' hγ' δ' hδ' hne
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hγ'
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hδ'
    exact ResolvedFeynmanSubgraph.mapPerm_disjoint σ
      (A.pairwiseDisjoint hγ hδ (fun h => hne (by rw [h])))

@[simp] theorem ResolvedAdmissibleSubgraph.mapPerm_elements (σ : Equiv.Perm VertexId)
    (A : ResolvedAdmissibleSubgraph G) :
    (A.mapPerm σ).elements = A.elements.image (fun γ => γ.mapPerm σ) := rfl

/-! ## Structural transports of the admissible carrier under `mapPerm`

The pieces `contractWithStars` is built from (`vertices`, `starVertices`, `complementEdges`,
`internalEdges`) all transport along `mapPerm σ` by relabeling — the structural input to the
`contractWithStars` equivariance.  None of these needs `componentAt` (no `Classical.choose`). -/

/-- `ResolvedFeynmanSubgraph.mapPerm σ` is injective (it relabels by the injective `σ`). -/
theorem ResolvedFeynmanSubgraph.mapPerm_injective (σ : Equiv.Perm VertexId) :
    Function.Injective (ResolvedFeynmanSubgraph.mapPerm σ (G := G)) := by
  intro γ δ h
  have hv : γ.vertices.image σ = δ.vertices.image σ := congrArg ResolvedFeynmanSubgraph.vertices h
  have hi : γ.internalEdges.map (ResolvedFeynmanEdge.map σ)
      = δ.internalEdges.map (ResolvedFeynmanEdge.map σ) :=
    congrArg ResolvedFeynmanSubgraph.internalEdges h
  have he : γ.externalLegs.map (ResolvedExternalLeg.map σ)
      = δ.externalLegs.map (ResolvedExternalLeg.map σ) :=
    congrArg ResolvedFeynmanSubgraph.externalLegs h
  have hEi : Function.Injective (ResolvedFeynmanEdge.map σ) := by
    intro a b hab; cases a; cases b
    simp only [ResolvedFeynmanEdge.map, ResolvedFeynmanEdge.mk.injEq] at hab
    obtain ⟨hid, hs, ht, hsec⟩ := hab
    exact ResolvedFeynmanEdge.mk.injEq .. |>.mpr ⟨hid, σ.injective hs, σ.injective ht, hsec⟩
  have hEℓ : Function.Injective (ResolvedExternalLeg.map σ) := by
    intro a b hab; cases a; cases b
    simp only [ResolvedExternalLeg.map, ResolvedExternalLeg.mk.injEq] at hab
    obtain ⟨hid, ha, hsec⟩ := hab
    exact ResolvedExternalLeg.mk.injEq .. |>.mpr ⟨hid, σ.injective ha, hsec⟩
  obtain ⟨γv, γi, γe, _, _, _, _, _⟩ := γ
  obtain ⟨δv, δi, δe, _, _, _, _, _⟩ := δ
  dsimp only at hv hi he
  have hv' : γv = δv := Finset.image_injective σ.injective hv
  have hi' : γi = δi := Multiset.map_injective hEi hi
  have he' : γe = δe := Multiset.map_injective hEℓ he
  subst hv'; subst hi'; subst he'; rfl

/-- The admissible carrier's vertex set transports by relabeling. -/
@[simp] theorem ResolvedAdmissibleSubgraph.mapPerm_vertices (σ : Equiv.Perm VertexId)
    (A : ResolvedAdmissibleSubgraph G) :
    (A.mapPerm σ).vertices = A.vertices.image σ := by
  unfold ResolvedAdmissibleSubgraph.vertices
  rw [ResolvedAdmissibleSubgraph.mapPerm_elements, Finset.biUnion_image, Finset.image_biUnion]
  exact Finset.biUnion_congr rfl (fun γ _ => by simp)

/-- The admissible carrier's aggregated internal edges transport by relabeling. -/
theorem ResolvedAdmissibleSubgraph.mapPerm_internalEdges (σ : Equiv.Perm VertexId)
    (A : ResolvedAdmissibleSubgraph G) :
    (A.mapPerm σ).internalEdges = A.internalEdges.map (ResolvedFeynmanEdge.map σ) := by
  simp only [ResolvedAdmissibleSubgraph.internalEdges, ResolvedAdmissibleSubgraph.mapPerm_elements]
  rw [Finset.sum_image (fun a _ b _ h => ResolvedFeynmanSubgraph.mapPerm_injective σ h)]
  simp only [ResolvedFeynmanSubgraph.mapPerm_internalEdges]
  exact (map_sum (Multiset.mapAddMonoidHom (ResolvedFeynmanEdge.map σ))
    (fun γ => γ.internalEdges) A.elements).symm

/-- For an injective `f`, `Multiset.map f` distributes over multiset subtraction. -/
private theorem multiset_map_sub_of_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    {f : α → β} (hf : Function.Injective f) (s t : Multiset α) :
    (s - t).map f = s.map f - t.map f := by
  ext b
  rw [Multiset.count_sub]
  by_cases hb : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := hb
    rw [Multiset.count_map_eq_count' f _ hf, Multiset.count_map_eq_count' f _ hf,
        Multiset.count_map_eq_count' f _ hf, Multiset.count_sub]
  · have h0 : ∀ m : Multiset α, (m.map f).count b = 0 := fun m => by
      rw [Multiset.count_eq_zero, Multiset.mem_map]; rintro ⟨a, _, rfl⟩; exact hb ⟨a, rfl⟩
    rw [h0, h0, h0]

/-- `ResolvedFeynmanEdge.map σ` is injective (it relabels endpoints by the injective `σ`, keeping
the `edgeId`). -/
theorem ResolvedFeynmanEdge.map_injective (σ : Equiv.Perm VertexId) :
    Function.Injective (ResolvedFeynmanEdge.map σ) := by
  intro a b hab; cases a; cases b
  simp only [ResolvedFeynmanEdge.map, ResolvedFeynmanEdge.mk.injEq] at hab
  obtain ⟨hid, hs, ht, hsec⟩ := hab
  exact ResolvedFeynmanEdge.mk.injEq .. |>.mpr ⟨hid, σ.injective hs, σ.injective ht, hsec⟩

/-- The complement edges transport by relabeling (`map σ` injective, so `map` distributes over the
multiset subtraction). -/
theorem ResolvedAdmissibleSubgraph.mapPerm_complementEdges (σ : Equiv.Perm VertexId)
    (A : ResolvedAdmissibleSubgraph G) :
    (A.mapPerm σ).complementEdges = A.complementEdges.map (ResolvedFeynmanEdge.map σ) := by
  unfold ResolvedAdmissibleSubgraph.complementEdges
  rw [ResolvedAdmissibleSubgraph.mapPerm_internalEdges]
  show G.internalEdges.map (ResolvedFeynmanEdge.map σ)
        - A.internalEdges.map (ResolvedFeynmanEdge.map σ)
      = (G.internalEdges - A.internalEdges).map (ResolvedFeynmanEdge.map σ)
  exact (multiset_map_sub_of_injective (ResolvedFeynmanEdge.map_injective σ)
    G.internalEdges A.internalEdges).symm

/-- The star vertices transport by relabeling, when the transported star assignment `starOf'`
agrees with `σ ∘ starOf` on the relabeled components. -/
theorem ResolvedAdmissibleSubgraph.mapPerm_starVertices (σ : Equiv.Perm VertexId)
    (A : ResolvedAdmissibleSubgraph G)
    {starOf : ResolvedFeynmanSubgraph G → VertexId}
    {starOf' : ResolvedFeynmanSubgraph (G.mapPerm σ) → VertexId}
    (hstar : ∀ γ ∈ A.elements, starOf' (γ.mapPerm σ) = σ (starOf γ)) :
    (A.mapPerm σ).starVertices starOf' = (A.starVertices starOf).image σ := by
  unfold ResolvedAdmissibleSubgraph.starVertices
  rw [ResolvedAdmissibleSubgraph.mapPerm_elements, Finset.image_image, Finset.image_image]
  exact Finset.image_congr (fun γ hγ => by simp only [Function.comp_apply]; exact hstar γ hγ)

end GaugeGeometry.QFT.Combinatorial