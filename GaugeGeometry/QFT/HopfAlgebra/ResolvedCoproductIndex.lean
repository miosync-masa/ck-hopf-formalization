import GaugeGeometry.QFT.Combinatorial.ResolvedSubGraph
import GaugeGeometry.QFT.HopfAlgebra.Coproduct

/-!
# Resolved → flat proper-forest bridge (Track R-4-full, Phase 2b)

HopfAlgebra-level bridge: a resolved proper forest (`ResolvedAdmissibleSubgraph.
IsProperForest`, Phase 2a) **forgets** to a flat proper forest
(`properDisjointAdmissibleDivergentSubgraphs`).  This keeps the Combinatorial
`ResolvedSubGraph.lean` Hopf-free while answering the Phase 2 design question:
*can the resolved coproduct reuse the flat finite index through `forget`?*

**Design conclusion (Phase 2b):** yes.  The linchpin is `forget_injOn_elements`:
on a pairwise-disjoint forest whose components are nonempty, `forget` is injective
on the components (distinct vertex-disjoint nonempty components keep distinct
vertex sets, hence distinct flat images).  Injectivity makes the forgetful image
of the forest a faithful flat forest — aggregates and cardinalities are preserved,
so the feared `edgeId`-collapse does **not** break the proper-forest conditions
after forgetting.  A native resolved finite index is therefore not required for
the pullback; finite enumeration (Phase 2c) can be designed independently.
-/

set_option linter.unusedSectionVars false

namespace GaugeGeometry.QFT.Combinatorial

variable {G : ResolvedFeynmanGraph}
variable [∀ H : FeynmanGraph, DivergenceMeasure H]
variable [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)]

namespace ResolvedAdmissibleSubgraph

/-- Membership in the aggregate internal edges (mirror of flat `mem_internalEdges`). -/
theorem mem_internalEdges {A : ResolvedAdmissibleSubgraph G} {e : ResolvedFeynmanEdge} :
    e ∈ A.internalEdges ↔ ∃ γ ∈ A.elements, e ∈ γ.internalEdges := by
  classical
  show e ∈ (∑ γ ∈ A.elements, γ.internalEdges) ↔ _
  induction A.elements using Finset.induction_on with
  | empty => simp
  | insert γ s hγs ih => simp [Finset.sum_insert, hγs, ih, Multiset.mem_add]

/-- **Linchpin (Phase 2b design fact).**  On a pairwise-disjoint forest with
nonempty components, `forget` is injective on the components: distinct
vertex-disjoint nonempty components keep distinct vertex sets, hence distinct flat
images. -/
theorem forget_injOn_elements (A : ResolvedAdmissibleSubgraph G)
    (hne : A.HasNonemptyComponents) :
    Set.InjOn ResolvedFeynmanSubgraph.forget {γ | γ ∈ A.elements} := by
  intro γ₁ h₁ γ₂ h₂ hfg
  by_contra hcon
  have hdis : _root_.Disjoint γ₁.vertices γ₂.vertices := A.pairwiseDisjoint h₁ h₂ hcon
  have hv : γ₁.vertices = γ₂.vertices := by
    rw [← ResolvedFeynmanSubgraph.forget_vertices γ₁,
      ← ResolvedFeynmanSubgraph.forget_vertices γ₂, hfg]
  rw [← hv] at hdis
  obtain ⟨v, hvmem⟩ := Finset.card_pos.mp (hne γ₁ h₁ : 0 < γ₁.vertices.card)
  exact absurd hvmem (Finset.disjoint_left.mp hdis hvmem)

/-- Forgetting preserves pairwise-disjointness of the forest. -/
theorem forget_isPairwiseDisjoint (A : ResolvedAdmissibleSubgraph G) :
    A.forget.IsPairwiseDisjoint := by
  intro δ₁ hδ₁ δ₂ hδ₂ hne12
  -- `AdmissibleSubgraph.IsPairwiseDisjoint` is `forest.IsPairwiseDisjoint`, so the
  -- memberships arrive as `… ∈ A.forget.forest.elements`; refold to `A.forget.elements`
  -- (defeq) before rewriting with `forget_elements`.
  have hδ₁' : δ₁ ∈ A.elements.image ResolvedFeynmanSubgraph.forget := by
    rw [← forget_elements]; exact hδ₁
  have hδ₂' : δ₂ ∈ A.elements.image ResolvedFeynmanSubgraph.forget := by
    rw [← forget_elements]; exact hδ₂
  obtain ⟨γ₁, hγ₁, rfl⟩ := Finset.mem_image.mp hδ₁'
  obtain ⟨γ₂, hγ₂, rfl⟩ := Finset.mem_image.mp hδ₂'
  have hγ : γ₁ ≠ γ₂ := fun h => hne12 (by rw [h])
  exact (ResolvedFeynmanSubgraph.forget_disjoint_iff).mpr (A.pairwiseDisjoint hγ₁ hγ₂ hγ)

/-- Forgetting preserves forest nonemptiness. -/
theorem forget_isNonempty (A : ResolvedAdmissibleSubgraph G) (h : A.IsNonempty) :
    A.forget.IsNonempty := by
  show (A.forget.elements).Nonempty
  rw [forget_elements]
  exact h.image _

/-- Forgetting preserves componentwise nonemptiness. -/
theorem forget_hasNonemptyComponents (A : ResolvedAdmissibleSubgraph G)
    (h : A.HasNonemptyComponents) : A.forget.HasNonemptyComponents := by
  intro δ hδ
  rw [forget_elements] at hδ
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hδ
  have hγne : γ.IsNonempty := h γ hγ
  simpa [FeynmanSubgraph.IsNonempty, FeynmanSubgraph.vertexCount,
    ResolvedFeynmanSubgraph.IsNonempty, ResolvedFeynmanSubgraph.vertexCount] using hγne

/-- Forgetting preserves componentwise positive internal-edge count. -/
theorem forget_hasPositiveInternalEdgesComponents (A : ResolvedAdmissibleSubgraph G)
    (h : A.HasPositiveInternalEdgesComponents) :
    A.forget.HasPositiveInternalEdgesComponents := by
  intro δ hδ
  rw [forget_elements] at hδ
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hδ
  simpa [ResolvedFeynmanSubgraph.forget_internalEdges, Multiset.card_map] using h γ hγ

/-- Forgetting preserves positivity of the aggregate internal-edge count: a
witness edge in some resolved component forgets to a witness in the forgotten
forest. -/
theorem forget_internalEdges_card_pos (A : ResolvedAdmissibleSubgraph G)
    (h : 0 < A.internalEdges.card) : 0 < A.forget.internalEdges.card := by
  obtain ⟨e, he⟩ := Multiset.card_pos_iff_exists_mem.mp h
  obtain ⟨γ, hγ, heγ⟩ := mem_internalEdges.mp he
  rw [Multiset.card_pos_iff_exists_mem]
  refine ⟨e.forget, ?_⟩
  rw [AdmissibleSubgraph.mem_internalEdges]
  refine ⟨γ.forget, ?_, ?_⟩
  · rw [forget_elements]; exact Finset.mem_image_of_mem _ hγ
  · rw [ResolvedFeynmanSubgraph.forget_internalEdges]
    exact Multiset.mem_map_of_mem _ heγ

/-- **Phase 2b bridge.**  A resolved proper forest forgets to a flat proper forest:
`A.forget ∈ (G.forget).properDisjointAdmissibleDivergentSubgraphs`.  Assembled from
the predicate transfers; injectivity of `forget` on the components is what keeps
the forgetful image faithful.  This is the proper-disjoint object; the extra
`0 < complementEdges.card` filter of `forestCoproductProperForestIndex` is
**deferred** (it needs the resolved `A.internalEdges ≤ G.internalEdges` — mirroring
flat `admissibleSubgraph_internalEdges_le_of_pairwise` — plus the aggregate
`A.forget.internalEdges = A.internalEdges.map forget` from `forget_injOn_elements`;
the card argument then transfers because `forget` preserves multiset cardinality.
Design-wise the bridge is already established: the pullback is viable). -/
theorem forget_mem_properDisjointAdmissibleDivergentSubgraphs
    (A : ResolvedAdmissibleSubgraph G) (hA : A.IsProperForest) :
    A.forget ∈ (G.forget).properDisjointAdmissibleDivergentSubgraphs := by
  rw [FeynmanGraph.mem_properDisjointAdmissibleDivergentSubgraphs]
  refine ⟨?_, A.forget_hasNonemptyComponents hA.2.1,
    A.forget_internalEdges_card_pos hA.2.2.1,
    A.forget_hasPositiveInternalEdgesComponents hA.2.2.2.1⟩
  rw [FeynmanGraph.mem_nonemptyDisjointAdmissibleDivergentSubgraphs]
  refine ⟨?_, A.forget_isNonempty hA.1⟩
  rw [FeynmanGraph.mem_disjointAdmissibleDivergentSubgraphs]
  exact ⟨FeynmanGraph.mem_admissibleDivergentSubgraphs G.forget A.forget,
    A.forget_isPairwiseDisjoint⟩

end ResolvedAdmissibleSubgraph

end GaugeGeometry.QFT.Combinatorial
