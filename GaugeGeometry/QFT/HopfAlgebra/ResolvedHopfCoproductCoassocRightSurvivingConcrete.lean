import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightSurviving

/-!
# R-6c-heart-6a-7b — RIGHT surviving transport from vertex-containment connectors

`ResolvedRightSurvivingSupply` (6a-6d-1) asks for the two surviving-vertex transports.  This file reduces
them — by an actual proof — to four named **vertex-containment connectors**, isolating the genuine geometry
into containment facts while the transport logic (the `contractWithStars` vertex-set case analysis) is
discharged here.

The four connectors (`A := s.1.1` input outer, `A' := selectedOuter`, `B' := quotientForest`,
`QB := A'.contractWithStars`):

1. `selectedOuter_vertices_subset` — `A'.vertices ⊆ A.vertices`;
2. `quotientForest_avoids_outer_survivors` — an outer-surviving vertex (`∈ G`, `∉ A`) is outside `B'`;
3. `selectedOuter_starVertices_subset_quotientForest` — `A'`'s stars are re-contracted by `B'`
   (`A'.starVertices ⊆ B'.vertices`);
4. `outer_minus_selectedOuter_in_quotientForest` — a vertex outside `A'` and outside `B'` is outside `A`
   (the `A \ A'` part is absorbed into `B'`).

`surviving_to` uses (1)+(2); `surviving_from` uses (3) [excludes the star case] + (4).

Per the HALT, the four containments are NOT proved (the genuine geometry, kept as supply fields); no
`starToStar` / `retargetVertex_eq` / `edge_domain_eq`.

Landed:

* `ResolvedRightSurvivingContainmentSupply D G imageOf` — the four containment connectors;
* `.toRightSurvivingSupply` — `surviving_to` / `surviving_from` PROVED from them.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-7b — the right surviving-containment connectors.**  The four vertex-containment facts
behind the surviving transport (genuine geometry, kept as fields). -/
structure ResolvedRightSurvivingContainmentSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- The selected outer forest's vertices sit in the input outer forest. -/
  selectedOuter_vertices_subset : ∀ s : ResolvedCoassocSplitChoice D G,
    (imageOf s).selectedOuter.1.vertices ⊆ s.1.1.vertices
  /-- An outer-surviving vertex avoids the quotient forest. -/
  quotientForest_avoids_outer_survivors : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    v ∈ G.vertices → v ∉ s.1.1.vertices → v ∉ (imageOf s).quotientForest.vertices
  /-- The selected outer forest's stars are re-contracted by the quotient forest. -/
  selectedOuter_starVertices_subset_quotientForest : ∀ s : ResolvedCoassocSplitChoice D G,
    (imageOf s).selectedOuter.1.starVertices (D.starOf G (imageOf s).selectedOuter.1)
      ⊆ (imageOf s).quotientForest.vertices
  /-- A vertex outside the selected outer and outside the quotient forest is outside the input outer. -/
  outer_minus_selectedOuter_in_quotientForest : ∀ (s : ResolvedCoassocSplitChoice D G) {w : VertexId},
    w ∈ G.vertices → w ∉ (imageOf s).selectedOuter.1.vertices →
    w ∉ (imageOf s).quotientForest.vertices → w ∉ s.1.1.vertices

/-- **R-6c-heart-6a-7b — the surviving transport, PROVED from the containment connectors.** -/
def ResolvedRightSurvivingContainmentSupply.toRightSurvivingSupply
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (C : ResolvedRightSurvivingContainmentSupply D G imageOf) :
    ResolvedRightSurvivingSupply D G imageOf where
  surviving_to := fun s {v} hv => by
    refine ⟨?_, ?_⟩
    · rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices]
      exact Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨hv.1, fun hvA' => hv.2 (C.selectedOuter_vertices_subset s hvA')⟩)
    · exact C.quotientForest_avoids_outer_survivors s hv.1 hv.2
  surviving_from := fun s {w} hw => by
    have hwQB := hw.1
    rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hwQB
    rcases hwQB with hsurv | hstar
    · rw [Finset.mem_sdiff] at hsurv
      exact ⟨hsurv.1, C.outer_minus_selectedOuter_in_quotientForest s hsurv.1 hsurv.2 hw.2⟩
    · exact absurd (C.selectedOuter_starVertices_subset_quotientForest s hstar) hw.2

end GaugeGeometry.QFT.Combinatorial
