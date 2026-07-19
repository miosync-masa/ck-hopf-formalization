import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocResidualCountTransport
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteRightRegion
import GaugeGeometry.QFT.HopfAlgebra.ResolvedSurvivorEmbed

/-!
# R-6c-body-434 — the right region count-exclusion (PROVED)

Four-hundred-and-thirty-fourth genuine-body step — the right survivor's count bound, closed with only body-337's
concrete `rightReembed` (no abstract survivor, no round-trip, no forward-quotient).

## Right identity

A star-avoiding survivor `δ ∈ rightDomain z` has `δ.vertices ∩ outer.starVertices = ∅`; so an internal edge of `δ` has
both endpoints in `δ.vertices`, hence outside `outer.vertices` (they are not on a star — `starAvoiding_notMem_outer`), so
the through-`outer` retarget is the identity on it (`retargetVertex_of_not_mem`):

```text
rightDomain_retargetEdge_eq :  e ∈ δ.internalEdges →  outer.retargetEdge star e = e
```

## Right count bound

The `rightReembed` re-embedding keeps the same data (`reembed.internalEdges = δ.internalEdges`, `rfl`), so the owner
component's count of the body-430 residual preimage `e` transports down through the owner lemma (body-432) at the quotient
forest and the residual count transport (body-433):

```text
count e (rightReembed z δ).internalEdges
  = count e   δ.internalEdges                         (reembed rfl)
  = count e_q δ.internalEdges                          (e = e_q : right identity + preimage_spec)
  = count e_q z.2.1.internalEdges                      (owner lemma on the quotient forest z.2.1, body-432)
  < count e_q quotientAmbient.internalEdges            (e_q ∈ z.2.1.complementEdges, body-431 count_lt)
  = count e   outer.complementEdges                    (residual count transport, body-433)
  ≤ count e   G.internalEdges                          (complement ≤ ambient)
```

Per the HALT/guards: `V.Survivor` / survivor round-trip / forward-quotient are NOT used; everything stays in `count`
(no `∉`); the retarget injectivity used is body-433's residual `InjOn`, not global; the right and forest counts are NOT
added here (the raw-owner classification is a single step in the final assembly).  No facade, no flat term, no
`forgetHopf`, no rep/perm, and NO strict `star_mapPerm` / `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-body-434 — the star-avoiding retarget identity.**  An internal edge of a right survivor `δ` is fixed by the
through-outer retarget: both endpoints avoid the outer forest, so `retargetVertex` is the identity on them. -/
theorem rightDomain_retargetEdge_eq (z : ForestBlockCodType D G)
    (δ : {x // x ∈ rightDomain z}) {e : ResolvedFeynmanEdge} (he : e ∈ δ.1.internalEdges) :
    z.1.1.retargetEdge (D.starOf G z.1.1) e = e := by
  have hstar : Disjoint δ.1.vertices (z.1.1.starVertices (D.starOf G z.1.1)) :=
    (Finset.mem_filter.mp δ.2).2
  obtain ⟨hs, ht⟩ := δ.1.edges_supported e he
  have hsource := starAvoiding_notMem_outer z δ.1 hstar hs
  have htarget := starAvoiding_notMem_outer z δ.1 hstar ht
  show e.retarget (z.1.1.retargetVertex (D.starOf G z.1.1)) = e
  simp only [ResolvedFeynmanEdge.retarget,
    ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem z.1.1 (D.starOf G z.1.1) hsource,
    ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem z.1.1 (D.starOf G z.1.1) htarget]

/-- **R-6c-body-434 ∎ — the right region count-exclusion.**  A `rightRegion` owner component carrying the body-430
residual preimage `e` counts it strictly less than the ambient `G` does. -/
theorem rightRegion_component_count_lt (hId : G.EdgeIdsUnique)
    (P : ResolvedCarrierProperProvider D)
    (z : ForestBlockCodType D G)
    {A : ResolvedFeynmanSubgraph G} (hA : A ∈ (rightRegion z).elements)
    (he : quotientResidualEdgePreimage P z ∈ A.internalEdges) :
    Multiset.count (quotientResidualEdgePreimage P z) A.internalEdges
      < Multiset.count (quotientResidualEdgePreimage P z) G.internalEdges := by
  rw [rightRegion_elements] at hA
  obtain ⟨δ, -, hδ_eq⟩ := Finset.mem_image.mp hA
  subst hδ_eq
  -- `he : e ∈ (rightReembed z δ).internalEdges`, defeq to `e ∈ δ.1.internalEdges`
  have heδ : quotientResidualEdgePreimage P z ∈ δ.1.internalEdges := he
  have hident := rightDomain_retargetEdge_eq z δ heδ
  have hspec := quotientResidualEdgePreimage_spec P z
  -- `e = e_q`
  have heq : quotientResidualEdgePreimage P z = quotientResidualEdge P z := hident.symm.trans hspec
  have hδz21 : δ.1 ∈ z.2.1.elements := (Finset.mem_filter.mp δ.2).1
  have he_q_δ : quotientResidualEdge P z ∈ δ.1.internalEdges := heq ▸ heδ
  have h2 := ResolvedAdmissibleSubgraph.count_internalEdges_eq_of_mem_component hδz21 he_q_δ
  have h3 := ResolvedAdmissibleSubgraph.count_lt_of_mem_complementEdges
    (quotientResidualEdge_mem_complement P z)
  have h4 := ResolvedAdmissibleSubgraph.count_complementEdges_eq_count_contractWithStars hId z.1.1
    (D.starOf G z.1.1) (quotientResidualEdgePreimage_mem_complement P z)
  rw [quotientResidualEdgePreimage_spec P z] at h4
  have h5 : Multiset.count (quotientResidualEdgePreimage P z) z.1.1.complementEdges
      ≤ Multiset.count (quotientResidualEdgePreimage P z) G.internalEdges := by
    show Multiset.count _ (G.internalEdges - z.1.1.internalEdges) ≤ _
    rw [Multiset.count_sub]; omega
  rw [heq] at h4 h5
  show Multiset.count (quotientResidualEdgePreimage P z) δ.1.internalEdges
    < Multiset.count (quotientResidualEdgePreimage P z) G.internalEdges
  rw [heq]
  omega

end GaugeGeometry.QFT.Combinatorial
