import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerRawM3
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMeasureLeaves
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCanonicalStarFacts

/-!
# R-6c-body-329 — D4: the parent-vertex retarget crux (PROVED) + nonempty + disjointness verdict

Three-hundred-and-twenty-ninth genuine-body step — Front-1 D4, the parent injectivity/disjointness front.  It banks the
geometric CRUX (`localizedParentVertex_retargets`: every custom-parent vertex retargets into `δ.vertices`) and the
parent-nonemptiness (from the supplied `cd_nonempty`), and pins the disjointness verdict: the four-term parent-vertex
disjointness closes only WITH the star-freshness datum `starOf_fresh` (the mixed cross-term is not closed by
`Disjoint δ.vertices δ'.vertices` alone).

## Banked here

* `localizedParentVertex_retargets` — every `v ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices` has
  `(touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) v ∈ δ.vertices`.  The three parent-vertex disjuncts
  (touched fiber / edge-preimage / leg-preimage) each retarget into `δ.vertices` — via `touchedOuterForest_starTouch`
  (325), `quotientEdgePreimage_map` + `edges_supported`, and `datum.map_eq` + `legs_supported` respectively.  This is the
  honest geometric heart of D4.
* `localizedParent_vertices_nonempty` — from the supplied `Measure.cd_nonempty` (a touched component is CD, so nonempty;
  its vertices lie in the parent).  Nonempty is DERIVABLE from `cd_nonempty` (body-1 measure datum), NOT a new datum.

## D4 disjointness verdict — needs `starOf_fresh` (a supplied CK datum)

For distinct `δ, δ'` with `Disjoint δ.vertices δ'.vertices`, a shared parent vertex `v` splits into three cases:
* **both untouched** — `retargetVertex v = v` for both, so `v ∈ δ.vertices ∩ δ'.vertices` — contradiction.  CLOSES.
* **both touched** — `v` in touched components `A, A'`; `z.1.1.pairwiseDisjoint` forces `A = A'`, then
  `touchedOuterComponents_disjoint` (316) contradicts.  CLOSES.
* **mixed** (`v ∈` touched-comp `A` of `δ`, but `v ∉` forest of `δ'`) — `ret_δ v = starOf A ∈ δ.vertices` while
  `ret_δ' v = v ∈ δ'.vertices`; since `v ∈ A.vertices ⊆ z.1.1.vertices`, `contractWithStars_vertices` forces
  `v ∈ z.1.1.starVertices`, i.e. `v = starOf B` for some `B ∈ z.1.1.elements`.  `Disjoint δ.vertices δ'.vertices` ALONE
  gives NO contradiction here — it needs `starOf_fresh` (`ResolvedCanonicalStarFacts.starOf_fresh` at `(G, z.1.1)`:
  `starOf B ∉ G.vertices`), contradicting `v ∈ A.vertices ⊆ G.vertices`.  So the mixed term is a genuine gap without
  freshness.

Hence `localizedParent_pairwiseDisjoint` and `localizedParent_injective` require the star-freshness datum (the multi-star
analog of the single-star `star_not_mem_vertices` kernel field).  Star-freshness is a legitimate concrete-model CK datum
(the canonical star allocation is fresh), joining the Front-1 tier — but D4 is NOT closable from vertex disjointness of the
quotient components alone.  Injectivity (from disjoint + nonempty) suffices for outer-mixing choice well-definedness.

Per the HALT: only the retarget crux + nonempty are proved; the full `localizedParent_pairwiseDisjoint` / `_injective` are
the body-330 target (consuming `starOf_fresh`); no `q.choice` is built; no legLift-heavy leg reasoning beyond `datum.map_eq`;
`ForestIdx`/carrier untouched; parent CD unused; no facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-329 — D4 crux: every parent vertex retargets into `δ`.**  Each of the three parent-vertex disjuncts
(touched fiber / edge-preimage / leg-preimage) sends `v` into `δ.vertices` under the touched-forest retarget. -/
theorem localizedParentVertex_retargets (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    {v : VertexId} (hv : v ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices) :
    (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) v ∈ δ.vertices := by
  obtain ⟨-, hdisj⟩ := Finset.mem_filter.mp hv
  rcases hdisj with htouch | hedge | hleg
  · rw [ResolvedAdmissibleSubgraph.mem_vertices] at htouch
    obtain ⟨A, hA, hvA⟩ := htouch
    rw [retargetVertex_eq_star_of_mem_element (touchedOuterForest z δ) (D.starOf G z.1.1) hA hvA]
    exact touchedOuterForest_starTouch z hA
  · obtain ⟨e, he, hv_eq⟩ := hedge
    have hmem : (touchedOuterForest z δ).retargetEdge (D.starOf G z.1.1) e
        ∈ (touchedLocalComponent z δ).internalEdges := by
      rw [← quotientEdgePreimage_map (touchedOuterForest z δ) (D.starOf G z.1.1)
        (touchedLocalComponent z δ)]
      exact Multiset.mem_map_of_mem _ he
    obtain ⟨hs, ht⟩ := (touchedLocalComponent z δ).edges_supported _ hmem
    rcases hv_eq with rfl | rfl
    · exact hs
    · exact ht
  · obtain ⟨ℓ, hℓ, rfl⟩ := hleg
    have hmem : (touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1) ℓ
        ∈ (touchedLocalComponent z δ).externalLegs := by
      rw [← datum.map_eq]; exact Multiset.mem_map_of_mem _ hℓ
    exact (touchedLocalComponent z δ).legs_supported _ hmem

/-- **R-6c-body-329 — the custom parent is vertex-nonempty** on a star-touching `δ`.  From the supplied `cd_nonempty`
(a touched component is connected-divergent, hence has a vertex, which lies in the parent). -/
theorem localizedParent_vertices_nonempty (Measure : ResolvedMeasureLeafSupply D)
    (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    (htouch : ¬ Disjoint δ.vertices (z.1.1.starVertices (D.starOf G z.1.1))) :
    (localizedParentWithTouchedLegs z δ datum hE hL).vertices.Nonempty := by
  obtain ⟨A, hA⟩ := touchedOuterForest_nonempty z htouch
  obtain ⟨w, hw⟩ := Measure.cd_nonempty A ((touchedOuterForest z δ).isConnectedDivergent A hA)
  exact ⟨w, touchedLegs_component_vertices_subset (datum := datum) (hE := hE) (hL := hL) hA hw⟩

end GaugeGeometry.QFT.Combinatorial
