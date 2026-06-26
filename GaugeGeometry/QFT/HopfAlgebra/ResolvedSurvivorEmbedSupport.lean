import GaugeGeometry.QFT.HopfAlgebra.ResolvedSurvivorEmbed

/-!
# R-6c-heart-6a-2 — the survivor support facts + concrete survivor re-embedding

A subgraph `γ` disjoint from the forest `A` survives `A`'s star-contraction.  This file discharges the
three `reembed` support facts (5c-6a-1) for such a `γ` into `A.contractWithStars starOf`, reducing them
to the two genuine survivor obligations:

* `hdisj : Disjoint γ.vertices A.vertices` (`γ` avoids the contracted region) — gives the vertices and
  external-legs supports outright (the retarget is the identity on `γ`, since its vertices/legs avoid
  `A`);
* `hcompl : γ.internalEdges ≤ A.complementEdges` (`γ`'s edges are not contracted) — gives the internal-
  edges support (same retarget-identity argument).

So `survivorReembed` is the concrete survivor component, with `γ`'s own generator
(`resolvedComponentGen_reembed`).

Landed:

* `reembed_vertices_subset_contractWithStars` / `reembed_externalLegs_le_contractWithStars` /
  `reembed_internalEdges_le_contractWithStars` — the three support facts from `hdisj` (+ `hcompl`);
* `survivorReembed` (+ `_toResolvedFeynmanGraph`, `_gen`) — the concrete survivor with `γ`'s generator.

No facade, no flat term, no `forgetHopf`, no rep/perm.  Discharging `hdisj` / `hcompl` for the actual
right survivors (from `γ ∉ selectedOuter` + the edge-domain) and the remnant embedding are the remaining
work.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-2 — survivor vertices support.**  A `γ` disjoint from `A` has all its vertices in
`G \ A`, hence in the contracted graph. -/
theorem reembed_vertices_subset_contractWithStars (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) (γ : ResolvedFeynmanSubgraph G)
    (hdisj : Disjoint γ.vertices A.vertices) :
    γ.vertices ⊆ (A.contractWithStars starOf).vertices := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices]
  intro v hv
  exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨γ.vertices_subset hv,
    Finset.disjoint_left.mp hdisj hv⟩)

/-- **R-6c-heart-6a-2 — survivor external-legs support.**  The retarget is the identity on `γ`'s legs
(attached off `A`), so `γ`'s legs sit unchanged among the contracted graph's legs. -/
theorem reembed_externalLegs_le_contractWithStars (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) (γ : ResolvedFeynmanSubgraph G)
    (hdisj : Disjoint γ.vertices A.vertices) :
    γ.externalLegs ≤ (A.contractWithStars starOf).externalLegs := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_externalLegs]
  have hmapid : γ.externalLegs.map (A.retargetExternalLeg starOf) = γ.externalLegs := by
    conv_rhs => rw [← Multiset.map_id γ.externalLegs]
    apply Multiset.map_congr rfl
    intro ℓ hℓ
    unfold ResolvedAdmissibleSubgraph.retargetExternalLeg ResolvedExternalLeg.retarget
    rw [A.retargetVertex_of_not_mem starOf (Finset.disjoint_left.mp hdisj (γ.legs_supported ℓ hℓ))]
    rfl
  rw [← hmapid]
  exact Multiset.map_le_map γ.externalLegs_le

/-- **R-6c-heart-6a-2 — survivor internal-edges support.**  The retarget is the identity on `γ`'s edges
(endpoints off `A`), so `γ`'s edges sit unchanged among the contracted complement edges (given they lie
in the complement). -/
theorem reembed_internalEdges_le_contractWithStars (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) (γ : ResolvedFeynmanSubgraph G)
    (hdisj : Disjoint γ.vertices A.vertices) (hcompl : γ.internalEdges ≤ A.complementEdges) :
    γ.internalEdges ≤ (A.contractWithStars starOf).internalEdges := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_internalEdges]
  have hmapid : γ.internalEdges.map (A.retargetEdge starOf) = γ.internalEdges := by
    conv_rhs => rw [← Multiset.map_id γ.internalEdges]
    apply Multiset.map_congr rfl
    intro e he
    obtain ⟨hs, ht⟩ := γ.edges_supported e he
    unfold ResolvedAdmissibleSubgraph.retargetEdge ResolvedFeynmanEdge.retarget
    rw [A.retargetVertex_of_not_mem starOf (Finset.disjoint_left.mp hdisj hs),
      A.retargetVertex_of_not_mem starOf (Finset.disjoint_left.mp hdisj ht)]
    rfl
  rw [← hmapid]
  exact Multiset.map_le_map hcompl

/-- **R-6c-heart-6a-2 — the concrete survivor re-embedding.**  A `γ` disjoint from `A` (with edges in the
complement) re-embedded into `A.contractWithStars starOf`. -/
noncomputable def survivorReembed (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) (γ : ResolvedFeynmanSubgraph G)
    (hdisj : Disjoint γ.vertices A.vertices) (hcompl : γ.internalEdges ≤ A.complementEdges) :
    ResolvedFeynmanSubgraph (A.contractWithStars starOf) :=
  γ.reembed (reembed_vertices_subset_contractWithStars A starOf γ hdisj)
    (reembed_internalEdges_le_contractWithStars A starOf γ hdisj hcompl)
    (reembed_externalLegs_le_contractWithStars A starOf γ hdisj)

@[simp] theorem survivorReembed_toResolvedFeynmanGraph (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) (γ : ResolvedFeynmanSubgraph G)
    (hdisj : Disjoint γ.vertices A.vertices) (hcompl : γ.internalEdges ≤ A.complementEdges) :
    (survivorReembed A starOf γ hdisj hcompl).toResolvedFeynmanGraph = γ.toResolvedFeynmanGraph := rfl

/-- **R-6c-heart-6a-2 — the survivor generator equality.**  The concrete survivor component has `γ`'s own
component generator. -/
theorem resolvedComponentGen_survivorReembed (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) (γ : ResolvedFeynmanSubgraph G)
    (hdisj : Disjoint γ.vertices A.vertices) (hcompl : γ.internalEdges ≤ A.complementEdges)
    (hCD : (survivorReembed A starOf γ hdisj hcompl).forget.IsConnectedDivergent)
    (hCD' : γ.forget.IsConnectedDivergent) :
    resolvedComponentGen (survivorReembed A starOf γ hdisj hcompl) hCD
      = resolvedComponentGen γ hCD' := rfl

end GaugeGeometry.QFT.Combinatorial
