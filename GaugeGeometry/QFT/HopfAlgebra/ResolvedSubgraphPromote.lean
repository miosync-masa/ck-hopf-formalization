import GaugeGeometry.QFT.HopfAlgebra.ResolvedAdmissibleSubgraphOfElements
import GaugeGeometry.QFT.HopfAlgebra.ContractionPreservation

/-!
# R-6c-heart-4 P1 — resolved subgraph promote (no rep/perm layer)

The resolved analogue of the flat pure promote (`feynmanSubgraphPromote`), built WITHOUT the heavy flat
rep/perm transport layer (`feynmanSubgraphRepToComponent` + the canonical permutation preimage).

**Why the rep/perm layer vanishes (the R-6 payoff):** in flat, a forest choice lives on the
*representative* graph `repG (γ.toHopfGen)`, which differs from the component graph by a permutation, so
it must be transported back by `mapPermAdmissibleSubgraphPreimage`.  In resolved, the component generator
is literally `γ.toResolvedFeynmanGraph` (ids are kept, no representative), so the forest choice already
lives in component coordinates — promote is just the inclusion `δ ⊆ γ.toResolvedFeynmanGraph ⊆ G`, a
transitivity of subset/`≤` facts.  No permutation, no transport.

Landed:

* `ResolvedFeynmanSubgraph.promote γ δ` — a subgraph `δ` of the component-as-graph `γ.toResolvedFeynman
  Graph`, reinterpreted as a subgraph of the ambient `G` (same data; support proofs by transitivity)
  (+ `promote_vertices`/`_internalEdges`/`_externalLegs` simp);
* `promote_forget_toFeynmanGraph` — the promote and the component subgraph have the SAME intrinsic flat
  graph (rfl) — the seed for transporting connected-divergence;
* `promote_disjoint` — promote keeps vertices, so disjointness transports.

The **admissible promote** (`ResolvedAdmissibleSubgraph.promote`) promotes every component of an
admissible forest `B` of the component graph into `G`.  CD transports: `IsConnected`/`IsOnePI` are
intrinsic (defeq via `promote_forget_toFeynmanGraph`), and `IsDivergent` (the only ambient-dependent
clause) transports through `IsAmbientInvariantDivergence.degree_self_eq` (the promote and the component
subgraph have the same intrinsic graph, so the same self-degree).

No facade, no flat term, no `forgetHopf`, no rep/perm.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

namespace ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-4 P1 — promote a component-graph subgraph into the ambient.**  A subgraph `δ` of the
component-as-graph `γ.toResolvedFeynmanGraph` is, with the SAME data (ids kept), a subgraph of the
ambient `G`: its vertices/edges/legs are already `δ ⊆ γ ⊆ G` by transitivity.  No rep/perm transport. -/
def promote (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.toResolvedFeynmanGraph) : ResolvedFeynmanSubgraph G where
  vertices := δ.vertices
  internalEdges := δ.internalEdges
  externalLegs := δ.externalLegs
  vertices_subset := δ.vertices_subset.trans γ.vertices_subset
  internalEdges_le := δ.internalEdges_le.trans γ.internalEdges_le
  externalLegs_le := δ.externalLegs_le.trans γ.externalLegs_le
  edges_supported := δ.edges_supported
  legs_supported := δ.legs_supported

@[simp] theorem promote_vertices (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.toResolvedFeynmanGraph) :
    (γ.promote δ).vertices = δ.vertices := rfl

@[simp] theorem promote_internalEdges (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.toResolvedFeynmanGraph) :
    (γ.promote δ).internalEdges = δ.internalEdges := rfl

@[simp] theorem promote_externalLegs (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.toResolvedFeynmanGraph) :
    (γ.promote δ).externalLegs = δ.externalLegs := rfl

/-- The promote and the component subgraph have the SAME intrinsic flat graph (both are
`{δ.vertices, δ.internalEdges.map forget, δ.externalLegs.map forget}`).  Holds by `rfl`; the seed for
transporting connected-divergence (the only non-intrinsic clause is `IsDivergent`). -/
theorem promote_forget_toFeynmanGraph (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.toResolvedFeynmanGraph) :
    (γ.promote δ).forget.toFeynmanGraph = δ.forget.toFeynmanGraph := rfl

/-- Promote preserves disjointness (it keeps the vertex set). -/
theorem promote_disjoint (γ : ResolvedFeynmanSubgraph G)
    {δ₁ δ₂ : ResolvedFeynmanSubgraph γ.toResolvedFeynmanGraph} (h : δ₁.Disjoint δ₂) :
    (γ.promote δ₁).Disjoint (γ.promote δ₂) := h

/-- **R-6c-heart-4 P1 — promote transports connected-divergence.**  The promoted component has the same
intrinsic flat graph as `δ` (so `IsConnected`/`IsOnePI` are defeq), and its `IsDivergent` transports via
`IsAmbientInvariantDivergence.degree_self_eq` (same self-degree). -/
theorem promote_forget_isConnectedDivergent [∀ H : FeynmanGraph, DivergenceMeasure H]
    [IsAmbientInvariantDivergence] (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.toResolvedFeynmanGraph)
    (h : δ.forget.IsConnectedDivergent) : (γ.promote δ).forget.IsConnectedDivergent := by
  refine ⟨h.1, h.2.1, ?_⟩
  have hdeg : DivergenceMeasure.degree ((γ.promote δ).forget)
      = DivergenceMeasure.degree (δ.forget) := by
    rw [← IsAmbientInvariantDivergence.degree_self_eq ((γ.promote δ).forget),
      ← IsAmbientInvariantDivergence.degree_self_eq (δ.forget)]
    rfl
  show 0 ≤ FeynmanSubgraph.divergenceDegree _
  unfold FeynmanSubgraph.divergenceDegree
  rw [hdeg]
  exact h.2.2

end ResolvedFeynmanSubgraph

variable [∀ H : FeynmanGraph, DivergenceMeasure H] [IsAmbientInvariantDivergence]

namespace ResolvedAdmissibleSubgraph

/-- **R-6c-heart-4 P1 — promote an admissible forest of the component-graph into the ambient.**  Promote
every component of an admissible forest `B` of `γ.toResolvedFeynmanGraph` into `G` (via the subgraph
promote).  CD transports via `promote_forget_isConnectedDivergent`; pairwise-disjointness via
`promote_disjoint`. -/
noncomputable def promote (γ : ResolvedFeynmanSubgraph G)
    (B : ResolvedAdmissibleSubgraph γ.toResolvedFeynmanGraph) : ResolvedAdmissibleSubgraph G :=
  ResolvedAdmissibleSubgraph.ofElements
    (B.elements.image (fun δ => γ.promote δ))
    (by
      intro ε hε
      obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hε
      exact γ.promote_forget_isConnectedDivergent δ (B.isConnectedDivergent δ hδ))
    (by
      intro ε₁ hε₁ ε₂ hε₂ hne
      obtain ⟨δ₁, hδ₁, rfl⟩ := Finset.mem_image.mp hε₁
      obtain ⟨δ₂, hδ₂, rfl⟩ := Finset.mem_image.mp hε₂
      exact γ.promote_disjoint (B.pairwiseDisjoint hδ₁ hδ₂ (fun h => hne (by rw [h]))))

@[simp] theorem promote_elements (γ : ResolvedFeynmanSubgraph G)
    (B : ResolvedAdmissibleSubgraph γ.toResolvedFeynmanGraph) :
    (ResolvedAdmissibleSubgraph.promote γ B).elements
      = B.elements.image (fun δ => γ.promote δ) := rfl

end ResolvedAdmissibleSubgraph

end GaugeGeometry.QFT.Combinatorial
