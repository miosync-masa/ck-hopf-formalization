import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSupportedCarrierEmptying
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCanonicalStarFacts
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfSubgraphMapPerm

/-!
# R-6c-body-403 — the equivariant fresh-star no-go audit (PROVED obstruction)

Four-hundred-and-third genuine-body step — the interface-consistency audit that catches a fatal incompatibility BEFORE
building `W`.  `D.star_mapPerm` (strict equivariance) and `Fstar.starOf_fresh` (freshness) CANNOT be simultaneously
inhabited on a non-trivial forest over a supported graph — the standard nominal-set obstruction: there is no strictly
equivariant fresh-name choice.

## The obstruction

For `η ∈ A.elements`, put `s := D.starOf G A η`; freshness gives `s ∉ G.vertices`.  Pick `t ≠ s`, `t ∉ G.vertices`, and
`σ := Equiv.swap s t`.  With ambient support, `σ` fixes every vertex / edge-endpoint / leg-attachment of `G`, so the
whole configuration is fixed: `G.mapPerm σ = G`, `A.mapPerm σ = A`, `η.mapPerm σ = η` (hence `D.starOf` of the permuted
configuration equals `s`).  But `star_mapPerm` forces `s = σ s = swap s t s = t`, contradicting `s ≠ t`.

* `strict_star_mapPerm_freshness_inconsistent` — the PROVED contradiction from `star_mapPerm` + the config-fixity `hfix`
  (`D.starOf` of the swapped configuration is unchanged) + `t ≠ s`;
* `resolvedGraph_mapPerm_swap_eq_self` — the concrete graph-fixity feasibility from ambient support (`σ` fixes a
  supported graph); the `hfix` premise's graph half, PROVED (the admissible/component halves are the resolved
  `mapPerm`-transport of the same data over the fixed graph).

## Verdict

`body-400`'s conditional theorem and `body-402`'s supported-carrier emptying are SOUND, but `W + Fstar` with STRICT
`star_mapPerm` is an **inconsistent interface** on non-trivial forests — not a merely unbuilt datum.  The canonical path
must WEAKEN strict `star_mapPerm` to one of the existing actual-σ-cover shapes: a star-renaming extension, a correcting
permutation `starPerm`, or alpha-equivalence.  Building `W` under strict `star_mapPerm` would open "a window that issues a
certificate that cannot exist".

Per the HALT: only the obstruction + the graph-fixity feasibility are landed; `W` is NOT built (it would be
inconsistent); the weakening of `star_mapPerm` is the next front.  No facade, no flat term, no `forgetHopf`, no rep/perm,
and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-403 — strict equivariance + freshness are inconsistent** (given the swap fixes the star of the swapped
configuration — the ambient-support config-fixity).  The star of the swapped configuration is both `s` (by fixity) and
`σ s = t` (by `star_mapPerm`), but `s ≠ t`. -/
theorem strict_star_mapPerm_freshness_inconsistent
    {G : ResolvedFeynmanGraph} (A : ResolvedAdmissibleSubgraph G) (η : ResolvedFeynmanSubgraph G)
    (hη : η ∈ A.elements) (t : VertexId) (ht : t ≠ D.starOf G A η)
    (hfix : D.starOf (G.mapPerm (Equiv.swap (D.starOf G A η) t))
        (A.mapPerm (Equiv.swap (D.starOf G A η) t)) (η.mapPerm (Equiv.swap (D.starOf G A η) t))
      = D.starOf G A η) :
    False := by
  have key := D.star_mapPerm G (Equiv.swap (D.starOf G A η) t) A η hη
  rw [hfix, Equiv.swap_apply_left] at key
  exact ht key.symm

/-- **R-6c-body-403 — a support-fixing swap fixes a supported graph** (the graph half of the config-fixity, PROVED from
ambient support). -/
theorem resolvedGraph_mapPerm_swap_eq_self {G : ResolvedFeynmanGraph}
    (hE : AmbientEdgesSupported G) (hL : AmbientLegsSupported G)
    {s t : VertexId} (hs : s ∉ G.vertices) (ht : t ∉ G.vertices) :
    G.mapPerm (Equiv.swap s t) = G := by
  have hfix : ∀ v ∈ G.vertices, (Equiv.swap s t) v = v := fun v hv =>
    Equiv.swap_apply_of_ne_of_ne (fun h => hs (h ▸ hv)) (fun h => ht (h ▸ hv))
  have hedge : ∀ e ∈ G.internalEdges, ResolvedFeynmanEdge.map (Equiv.swap s t) e = e := by
    rintro ⟨eid, es, et, esec⟩ he
    obtain ⟨hse, hte⟩ := hE _ he
    simp only [ResolvedFeynmanEdge.map, hfix es hse, hfix et hte]
  have hleg : ∀ ℓ ∈ G.externalLegs, ResolvedExternalLeg.map (Equiv.swap s t) ℓ = ℓ := by
    rintro ⟨lid, lat, lsec⟩ hℓ
    simp only [ResolvedExternalLeg.map, hfix lat (hL _ hℓ)]
  obtain ⟨Gv, Gi, Ge⟩ := G
  have hV : Gv.image (Equiv.swap s t) = Gv := by
    rw [Finset.image_congr (g := id) fun v hv => hfix v hv, Finset.image_id]
  have hI : Gi.map (ResolvedFeynmanEdge.map (Equiv.swap s t)) = Gi := by
    rw [Multiset.map_congr rfl hedge, Multiset.map_id']
  have hLg : Ge.map (ResolvedExternalLeg.map (Equiv.swap s t)) = Ge := by
    rw [Multiset.map_congr rfl hleg, Multiset.map_id']
  show ResolvedFeynmanGraph.mk (Gv.image (Equiv.swap s t))
    (Gi.map (ResolvedFeynmanEdge.map (Equiv.swap s t)))
    (Ge.map (ResolvedExternalLeg.map (Equiv.swap s t))) = ResolvedFeynmanGraph.mk Gv Gi Ge
  rw [hV, hI, hLg]

end GaugeGeometry.QFT.Combinatorial
