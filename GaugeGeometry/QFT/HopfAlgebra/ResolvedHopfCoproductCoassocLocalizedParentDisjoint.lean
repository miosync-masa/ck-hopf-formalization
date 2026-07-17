import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLocalizedParentRetarget

/-!
# R-6c-body-330 — D4 CLOSED: localized-parent disjointness + injectivity (PROVED, consumes star-freshness)

Three-hundred-and-thirtieth genuine-body step — Front-1 D4, closed.  Distinct quotient components (vertex-disjoint) yield
vertex-DISJOINT localized parents (given the `starOf_fresh` datum), hence distinct parents (with nonemptiness) — the
outer-mixing choice is well-defined on the domain.

## Banked here

* `localizedParent_star_mem` — for `v ∈ z.1.1.vertices` in `parent(δ)`, the star of `v`'s outer component lies in
  `δ.vertices` (either `v` is in a touched component whose star ∈ δ, or `v` retargets to itself ∈ δ — impossible by
  `starOf_fresh`, since an actual `z.1.1`-vertex is not a star).  The mixed-case engine.
* `localizedParent_pairwiseDisjoint` — `Disjoint δ.vertices δ'.vertices → Disjoint parent(δ).vertices parent(δ').vertices`
  (consumes `ResolvedCanonicalStarFacts`): a shared parent vertex `v` either (out/out) retargets to `v ∈ δ ∩ δ'`, or
  (in `z.1.1`) has `starOf (component v) ∈ δ.vertices ∩ δ'.vertices` — both contradict disjointness.
* `localizedParent_ne` — distinct disjoint quotient components (with `δ` star-touching for nonemptiness) give DISTINCT
  parents: else `parent(δ).vertices` is self-disjoint hence empty, contradicting `localizedParent_vertices_nonempty`.

## D4 is closed under the supplied CK datums

`localizedParent_pairwiseDisjoint`/`_ne` consume `ResolvedCanonicalStarFacts` (`starOf_fresh`) and — for `_ne` —
`ResolvedMeasureLeafSupply` (`cd_nonempty`).  Both are concrete-model CK/allocation datums (star-freshness is
canonical-star-allocation, NOT carrier closure; `cd_nonempty` is measure geometry), joining the Front-1 tier.  The
outer-mixing geometry's D4 well-definedness is now a THEOREM modulo these named datums.

Per the HALT: D4 is closed; only vertices are compared (no external-leg / legLift comparison); nonemptiness is the
measure-derived one (body-329), NOT `IsConnectedDivergent`-direct; no `q.choice` is built; `ForestIdx`/carrier untouched;
parent CD unused; no facade, no flat term, no `forgetHopf`.  STATUS: the touched-geometry `forward_outer_value` assembly
(D5+M3) and the multi-star Region/Tags/choice adapter remain; Front-1 is NOT yet fully assembled.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-330 — the star-membership engine.**  For a `z.1.1`-vertex `v` of `parent(δ)`, the star of `v`'s outer
component lies in `δ.vertices` (the mixed case, closed by `starOf_fresh`). -/
theorem localizedParent_star_mem (F : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    {v : VertexId} (hvz : v ∈ z.1.1.vertices)
    (hv : v ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices) :
    D.starOf G z.1.1 (z.1.1.componentAt hvz) ∈ δ.vertices := by
  have hret := localizedParentVertex_retargets z δ datum hE hL hv
  by_cases htf : v ∈ (touchedOuterForest z δ).vertices
  · rw [ResolvedAdmissibleSubgraph.mem_vertices] at htf
    obtain ⟨A, hA, hvA⟩ := htf
    have hAz : A ∈ z.1.1.elements := by
      rw [touchedOuterForest_elements] at hA; exact (mem_touchedOuterComponents.mp hA).1
    have hAcomp : A = z.1.1.componentAt hvz := by
      by_contra hAne
      exact Finset.disjoint_left.mp
        (z.1.1.pairwiseDisjoint hAz (z.1.1.componentAt_mem hvz) hAne) hvA
        (z.1.1.componentAt_vertex_mem hvz)
    rw [retargetVertex_eq_star_of_mem_element (touchedOuterForest z δ) (D.starOf G z.1.1) hA hvA] at hret
    rw [← hAcomp]; exact hret
  · rw [ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ htf] at hret
    exfalso
    have hvcontract := δ.vertices_subset hret
    rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hvcontract
    rcases hvcontract with hc | hs
    · exact (Finset.mem_sdiff.mp hc).2 hvz
    · rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hs
      obtain ⟨B, hB, hBv⟩ := hs
      have hvG : v ∈ G.vertices :=
        (z.1.1.componentAt hvz).vertices_subset (z.1.1.componentAt_vertex_mem hvz)
      exact F.starOf_fresh G z.1.1 B hB (hBv ▸ hvG)

/-- **R-6c-body-330 — localized parents of disjoint quotient components are vertex-disjoint** (consumes `starOf_fresh`). -/
theorem localizedParent_pairwiseDisjoint (F : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G)
    (δ δ' : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ) (datum' : ResolvedTouchedLegLiftDatum z δ')
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    (hdisj : Disjoint δ.vertices δ'.vertices) :
    Disjoint (localizedParentWithTouchedLegs z δ datum hE hL).vertices
      (localizedParentWithTouchedLegs z δ' datum' hE hL).vertices := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  by_cases hvz : v ∈ z.1.1.vertices
  · exact Finset.disjoint_left.mp hdisj
      (localizedParent_star_mem F z δ datum hE hL hvz hv)
      (localizedParent_star_mem F z δ' datum' hE hL hvz hv')
  · have h1 : v ∉ (touchedOuterForest z δ).vertices := fun h => hvz (touchedOuterForest_vertices_subset z h)
    have h2 : v ∉ (touchedOuterForest z δ').vertices := fun h => hvz (touchedOuterForest_vertices_subset z h)
    have hret := localizedParentVertex_retargets z δ datum hE hL hv
    have hret' := localizedParentVertex_retargets z δ' datum' hE hL hv'
    rw [ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ h1] at hret
    rw [ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ h2] at hret'
    exact Finset.disjoint_left.mp hdisj hret hret'

/-- **R-6c-body-330 — distinct disjoint quotient components give distinct localized parents** (D4 injectivity;
consumes `starOf_fresh` + `cd_nonempty`). -/
theorem localizedParent_ne (F : ResolvedCanonicalStarFacts D) (Measure : ResolvedMeasureLeafSupply D)
    (z : ForestBlockCodType D G)
    (δ δ' : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ) (datum' : ResolvedTouchedLegLiftDatum z δ')
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    (htouch : ¬ Disjoint δ.vertices (z.1.1.starVertices (D.starOf G z.1.1)))
    (hdisj : Disjoint δ.vertices δ'.vertices) :
    localizedParentWithTouchedLegs z δ datum hE hL
      ≠ localizedParentWithTouchedLegs z δ' datum' hE hL := by
  intro heq
  have hpd := localizedParent_pairwiseDisjoint F z δ δ' datum datum' hE hL hdisj
  have hne := localizedParent_vertices_nonempty Measure z δ datum hE hL htouch
  rw [heq] at hpd hne
  obtain ⟨w, hw⟩ := hne
  exact Finset.disjoint_left.mp hpd hw hw

end GaugeGeometry.QFT.Combinatorial
