import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocComplementCountBackbone

/-!
# R-6c-body-432 — the component-owner count lemma; the left region count-exclusion (PROVED)

Four-hundred-and-thirty-second genuine-body step — the load-bearing prerequisite for the three region count-exclusions
(body-431's remaining obligation).  Per the plan: proving `count e region < count e G` for each region separately does
NOT let one sum over the union, because an edge could a priori be counted in several components.  The fix is to show
first that **an edge is owned by at most one component** (pairwise-disjointness), so its multiplicity in the union equals
its multiplicity in its single owner.

* `count_internalEdges_eq_of_mem_component` — the generic owner lemma: for a pairwise-disjoint admissible forest `Raw`,
  if `A ∈ Raw.elements` and `e ∈ A.internalEdges`, then `count e Raw.internalEdges = count e A.internalEdges`.  Any other
  component `B` with `e ∈ B.internalEdges` would put `e.source ∈ A.vertices ∩ B.vertices` (via `edges_supported`),
  contradicting `Raw.pairwiseDisjoint`; so every non-owner term of the `Finset.sum` vanishes (`Finset.sum_eq_single`).

* `leftRegion_component_count_lt` — the LEFT region count-exclusion, cashed through the owner lemma at the OUTER forest:
  a `leftRegion` component is an outer component (body-430 `leftRegion_elements_subset`), so its count of the body-430
  residual preimage equals the outer's (owner lemma on `z.1.1`), which is `< count e G.internalEdges` because
  `e ∈ z.1.1.complementEdges` (body-431 `count_lt_of_mem_complementEdges`).

The right/forest region count-exclusions (retarget correspondence + `parent` touched/preimage decomposition) reuse this
same owner lemma and are the dedicated next body; the union assembly then reads: the union owner is a left / right /
forest component, each bounded `< count e G` — combined with `count_internalEdges_eq_of_mem_component` on `regionRawUnion`
this gives the body-431 witness bound.

Per the HALT/guards: everything stays in `count` (no `∉`/nodup); the owner lemma is the multiplicity-safe bridge that
lets per-region bounds sum; `EdgeIdsUnique` is untouched here (its retarget role is the right/forest body).  No facade, no
flat term, no `forgetHopf`, no rep/perm, and NO strict `star_mapPerm` / `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false

namespace ResolvedAdmissibleSubgraph

variable {G : ResolvedFeynmanGraph}

/-- **R-6c-body-432 — an internal edge is owned by at most one component.**  In a pairwise-disjoint admissible forest,
the multiplicity of an edge in the whole forest equals its multiplicity in the single component that carries it. -/
theorem count_internalEdges_eq_of_mem_component {Raw : ResolvedAdmissibleSubgraph G}
    {A : ResolvedFeynmanSubgraph G} (hA : A ∈ Raw.elements)
    {e : ResolvedFeynmanEdge} (he : e ∈ A.internalEdges) :
    Multiset.count e Raw.internalEdges = Multiset.count e A.internalEdges := by
  show Multiset.count e (Raw.elements.sum (fun γ => γ.internalEdges)) = _
  rw [Multiset.count_sum']
  refine Finset.sum_eq_single A (fun B hB hBA => ?_) (fun hnA => absurd hA hnA)
  by_contra h
  have heB : e ∈ B.internalEdges := Multiset.count_pos.mp (Nat.pos_of_ne_zero h)
  exact Finset.disjoint_left.mp (Raw.pairwiseDisjoint hA hB hBA.symm)
    (A.edges_supported e he).1 (B.edges_supported e heB).1

end ResolvedAdmissibleSubgraph

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-body-432 — the left region count-exclusion.**  A component of `leftRegion` carrying the body-430 residual
preimage `e` counts it strictly less than the ambient `G` does: the component is an outer component, so its count equals
the outer's (owner lemma), which is `< count e G` since `e ∈ z.1.1.complementEdges`. -/
theorem leftRegion_component_count_lt
    (P : ResolvedCarrierProperProvider D)
    (z : ForestBlockCodType D G)
    {A : ResolvedFeynmanSubgraph G} (hA : A ∈ (leftRegion z).elements)
    (he : quotientResidualEdgePreimage P z ∈ A.internalEdges) :
    Multiset.count (quotientResidualEdgePreimage P z) A.internalEdges
      < Multiset.count (quotientResidualEdgePreimage P z) G.internalEdges := by
  have hAouter : A ∈ z.1.1.elements := leftRegion_elements_subset z hA
  have howner := ResolvedAdmissibleSubgraph.count_internalEdges_eq_of_mem_component hAouter he
  have hlt := ResolvedAdmissibleSubgraph.count_lt_of_mem_complementEdges
    (quotientResidualEdgePreimage_mem_complement P z)
  omega

end GaugeGeometry.QFT.Combinatorial
