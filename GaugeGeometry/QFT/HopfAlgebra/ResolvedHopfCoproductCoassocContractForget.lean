import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRetargetForget
import GaugeGeometry.QFT.HopfAlgebra.ResolvedCoproductIndex

/-!
# R-6c-body-422 — the resolved↔flat contraction forget-commutativity (PROVED)

Four-hundred-and-twenty-second genuine-body step — the full pure-`forget` graph equality of the `hCD` impedance match:
forgetting the resolved star-contraction equals the FLAT contraction of the forgotten forest with the descended star.
This closes the resolved-side bookkeeping; from here the resolved data may be forgotten entirely and only "two fresh
allocators on the same flat forest" remain (body-423).

* `multiset_map_sub_of_le` — the generic BOUNDED multiset map-subtraction `(t - s).map f = t.map f - s.map f` for `s ≤ t`
  (via `Multiset.countP_sub`; NO injectivity of `f` — exactly what edge-`forget` needs, per body-421's guard);
* `forget_complementEdges_eq` — `A.forget.complementEdges = A.complementEdges.map forget` (from the bounded lemma +
  `A.internalEdges ≤ G.internalEdges` + `forget_internalEdges_eq_map`);
* `forget_contractWithStars_resolvedStar` — `(A.contractWithStars resolvedStar).forget = A.forget.contractWithStars
  resolvedStarOnForget`, assembled field-by-field: vertices from body-420/421, internal edges from the complement
  correspondence + body-421's `retargetVertex_forget_eq`, external legs likewise; proof fields by irrelevance.

Per the HALT: NO canonical star, NO CD, NO class equality is introduced — this is pure commutativity.  Body-423 renames
`resolvedStarOnForget` to the flat canonical `A.forget.componentFreshStar` (a `σ = id`-specialised correcting permutation
between two fresh flat allocators), giving the class equality, then the flat CD + iso-invariance yields `hCD`, then the
RawW assembly + real supported `W`.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` /
singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

/-- **R-6c-body-422 — bounded multiset map-subtraction.**  For `s ≤ t`, `map f` distributes over the truncated
subtraction — WITHOUT any injectivity of `f` (the count on each side is a `countP`, and `Multiset.countP_sub` closes it
because `s ≤ t`).  This is the honest tool for the non-injective edge-`forget`. -/
theorem multiset_map_sub_of_le {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β)
    {s t : Multiset α} (h : s ≤ t) : (t - s).map f = t.map f - s.map f := by
  ext y
  simp only [Multiset.count_sub, Multiset.count_map, ← Multiset.countP_eq_card_filter]
  exact Multiset.countP_sub h _

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false

/-- **R-6c-body-422 — complement edges commute with forget.**  `forget` kills edge ids (non-injective), so this is the
bounded map-subtraction, NOT `map_sub_of_injective`. -/
theorem forget_complementEdges_eq {G : ResolvedFeynmanGraph} (A : ResolvedAdmissibleSubgraph G)
    (hne : A.HasNonemptyComponents) :
    A.forget.complementEdges = A.complementEdges.map ResolvedFeynmanEdge.forget := by
  rw [AdmissibleSubgraph.complementEdges, ResolvedAdmissibleSubgraph.complementEdges,
    ResolvedAdmissibleSubgraph.forget_internalEdges_eq_map A hne,
    multiset_map_sub_of_le ResolvedFeynmanEdge.forget A.internalEdges_le]
  rfl

/-- **R-6c-body-422 ∎ — forgetting the resolved contraction is the flat contraction of the forgotten forest.**  Pure
`forget`-commutativity; assembled from the vertex / star-vertex / complement-edge correspondences and body-421's
retarget agreement. -/
theorem forget_contractWithStars_resolvedStar {G : ResolvedFeynmanGraph}
    (A : ResolvedAdmissibleSubgraph G) (hpf : A.IsProperForest) :
    (A.contractWithStars (resolvedComponentFreshStar G A)).forget
      = A.forget.contractWithStars (resolvedStarOnForget A) := by
  rw [ResolvedAdmissibleSubgraph.forget_contractWithStars]
  have hv : (G.vertices \ A.vertices) ∪ A.starVertices (resolvedComponentFreshStar G A)
      = (G.forget.vertices \ A.forget.vertices) ∪ A.forget.starVertices (resolvedStarOnForget A) := by
    rw [forget_vertices_eq, starVertices_forget_eq A hpf]
    rfl
  have hi : (A.complementEdges.map ResolvedFeynmanEdge.forget).map
        (fun e => ({ source := A.retargetVertex (resolvedComponentFreshStar G A) e.source,
                     target := A.retargetVertex (resolvedComponentFreshStar G A) e.target,
                     sector := e.sector } : FeynmanEdge))
      = A.forget.complementEdges.map (A.forget.retargetEdge (resolvedStarOnForget A)) := by
    rw [forget_complementEdges_eq A hpf.2.1]
    simp only [Multiset.map_map]
    refine Multiset.map_congr rfl (fun e _ => ?_)
    simp only [Function.comp_apply, AdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.forget,
      retargetVertex_forget_eq A hpf]
  have he : (G.externalLegs.map ResolvedExternalLeg.forget).map
        (fun l => ({ attachedTo := A.retargetVertex (resolvedComponentFreshStar G A) l.attachedTo,
                     sector := l.sector } : ExternalLeg))
      = G.forget.externalLegs.map (A.forget.retargetExternalLeg (resolvedStarOnForget A)) := by
    rw [show G.forget.externalLegs = G.externalLegs.map ResolvedExternalLeg.forget from rfl]
    simp only [Multiset.map_map]
    refine Multiset.map_congr rfl (fun l _ => ?_)
    simp only [Function.comp_apply, AdmissibleSubgraph.retargetExternalLeg, ResolvedExternalLeg.forget,
      retargetVertex_forget_eq A hpf]
  exact congr (congr (congrArg FeynmanGraph.mk hv) hi) he

end GaugeGeometry.QFT.Combinatorial
