import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantScout

/-!
# R-6c-heart-6a-5c-4d — `contractedSourceGraph` self-support (two `reembedAsSubgraph` obligations)

The concrete remnant (`reembedAsSubgraph`, 6a-5c-4c) needs the contracted source forest's own
endpoint well-formedness (`edges_supported` / `legs_supported`) — a `ResolvedFeynmanGraph` carries **no**
such invariant by type, so it cannot come from a generic graph lemma (an arbitrary resolved graph may
have an edge with endpoints outside its vertex set).

It comes instead from the **specific** structure `contractedSourceGraph = B.contractWithStars (…)`: a
`contractWithStars` of a well-formed ambient is itself well-formed, because every retargeted endpoint
lands in the contracted vertex set (`retargetVertex_mem_contractWithStars_vertices`).  The ambient here is
the survivor component's intrinsic graph `o.γ.1.toResolvedFeynmanGraph`, whose well-formedness is exactly
the subgraph invariants `o.γ.1.edges_supported` / `legs_supported`.

Per the HALT, the three containments and `remnantCD` are **not** touched — this only discharges the two
self-support obligations.

Landed:

* `ResolvedAdmissibleSubgraph.contractWithStars_internalEdges_supported` /
  `..._externalLegs_supported` — `contractWithStars` preserves a well-formed ambient (generic);
* `remnant_contractedSource_internalEdges_supported` /
  `remnant_contractedSource_externalLegs_supported` — the two `reembedAsSubgraph` self-support facts,
  automated from the survivor component's subgraph invariants.

No facade, no flat term, no `forgetHopf`.  The three de-contraction containments and `remnantCD` remain.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-5c-4d — `contractWithStars` preserves a well-formed ambient (edges).**  If every
internal edge of `G` has its endpoints in `G.vertices`, then so does every internal edge of
`A.contractWithStars starOf` — each endpoint is a `retargetVertex`, which lands in the contracted vertex
set. -/
theorem ResolvedAdmissibleSubgraph.contractWithStars_internalEdges_supported
    (A : ResolvedAdmissibleSubgraph G) (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (hG : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices) :
    ∀ e ∈ (A.contractWithStars starOf).internalEdges,
      e.source ∈ (A.contractWithStars starOf).vertices ∧
        e.target ∈ (A.contractWithStars starOf).vertices := by
  intro e' he'
  rw [contractWithStars_internalEdges] at he'
  obtain ⟨e, he, rfl⟩ := Multiset.mem_map.mp he'
  have heG : e ∈ G.internalEdges :=
    Multiset.mem_of_le (Multiset.sub_le_self _ _) he
  obtain ⟨hs, ht⟩ := hG e heG
  exact ⟨A.retargetVertex_mem_contractWithStars_vertices starOf hs,
    A.retargetVertex_mem_contractWithStars_vertices starOf ht⟩

/-- **R-6c-heart-6a-5c-4d — `contractWithStars` preserves a well-formed ambient (legs).** -/
theorem ResolvedAdmissibleSubgraph.contractWithStars_externalLegs_supported
    (A : ResolvedAdmissibleSubgraph G) (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (hG : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices) :
    ∀ ℓ ∈ (A.contractWithStars starOf).externalLegs,
      ℓ.attachedTo ∈ (A.contractWithStars starOf).vertices := by
  intro ℓ' hℓ'
  rw [contractWithStars_externalLegs] at hℓ'
  obtain ⟨ℓ, hℓ, rfl⟩ := Multiset.mem_map.mp hℓ'
  exact A.retargetVertex_mem_contractWithStars_vertices starOf (hG ℓ hℓ)

variable {D : ResolvedCoproductProperForestData}

/-- **R-6c-heart-6a-5c-4d — the remnant `reembedAsSubgraph` edge self-support (automated).**  The
contracted source forest's ambient is the survivor component's intrinsic graph, whose edges are supported
by the subgraph invariant `o.γ.1.edges_supported`. -/
theorem remnant_contractedSource_internalEdges_supported
    {s : ResolvedCoassocSplitChoice D G} (o : s.ForestChoiceOccurrence) :
    ∀ e ∈ o.contractedSourceGraph.internalEdges,
      e.source ∈ o.contractedSourceGraph.vertices ∧
        e.target ∈ o.contractedSourceGraph.vertices := by
  unfold ResolvedCoassocSplitChoice.ForestChoiceOccurrence.contractedSourceGraph
  refine ResolvedAdmissibleSubgraph.contractWithStars_internalEdges_supported _ _ ?_
  intro e he
  rw [ResolvedFeynmanSubgraph.toResolvedFeynmanGraph_internalEdges] at he
  rw [ResolvedFeynmanSubgraph.toResolvedFeynmanGraph_vertices]
  exact o.γ.1.edges_supported e he

/-- **R-6c-heart-6a-5c-4d — the remnant `reembedAsSubgraph` leg self-support (automated).** -/
theorem remnant_contractedSource_externalLegs_supported
    {s : ResolvedCoassocSplitChoice D G} (o : s.ForestChoiceOccurrence) :
    ∀ ℓ ∈ o.contractedSourceGraph.externalLegs,
      ℓ.attachedTo ∈ o.contractedSourceGraph.vertices := by
  unfold ResolvedCoassocSplitChoice.ForestChoiceOccurrence.contractedSourceGraph
  refine ResolvedAdmissibleSubgraph.contractWithStars_externalLegs_supported _ _ ?_
  intro ℓ hℓ
  rw [ResolvedFeynmanSubgraph.toResolvedFeynmanGraph_externalLegs] at hℓ
  rw [ResolvedFeynmanSubgraph.toResolvedFeynmanGraph_vertices]
  exact o.γ.1.legs_supported ℓ hℓ

end GaugeGeometry.QFT.Combinatorial
