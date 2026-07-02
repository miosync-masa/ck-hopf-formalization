import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteVertexTransport
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightSurvivingConcrete

/-!
# R-6c-leaf-17 — three-route vertex transport connector (mismatch-corrected)

Thirteenth leaf-body discharge (RIGHT side).  `ResolvedThreeRouteVertexTransportSupply` (6a-9d) has three
fields; this connector reduces them to the correct post-mismatch boundary:

* `survivingOriginal_to` — DISCHARGED from the two *correct* surviving containments
  (`selectedOuter_vertices_subset` + `quotientForest_avoids_outer_survivors`), replaying the 6a-7b
  `surviving_to` proof (`contractWithStars_vertices` + `mem_sdiff`).  It does NOT use the
  `selectedOuter_starVertices_subset_quotientForest` field, which the 6a-8c-0 left-granularity analysis found
  **false** — so that field is deliberately absent here.
* `leftStar_toSurvivor` / `twoStageSurvivor_cases` — the genuine three-route facts (a left-primitive one-stage
  star becomes a two-stage *survivor*, not a quotient star; and the two-stage survivors are exactly the
  original survivors plus the left `δ`-stars).  Kept as fields.

So the transport boundary is `{2 correct containments} + {2 three-route facts}` — no false containment.

Per the HALT, the two containments and the two three-route facts are supply fields; Retarget / Perm / Sector
untouched.

Landed:

* `ResolvedThreeRouteTransportConnector D G imageOf` — 2 containments + `leftStar_toSurvivor` +
  `twoStageSurvivor_cases`;
* `.toTransportSupply : ResolvedThreeRouteVertexTransportSupply D G imageOf`.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-leaf-17 — the mismatch-corrected three-route transport connector.**  Two correct surviving
containments + the two genuine three-route facts. -/
structure ResolvedThreeRouteTransportConnector (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- The selected outer forest's vertices sit in the input outer forest. -/
  selectedOuter_vertices_subset : ∀ s : ResolvedCoassocSplitChoice D G,
    (imageOf s).selectedOuter.1.vertices ⊆ s.1.1.vertices
  /-- An outer-surviving vertex avoids the quotient forest. -/
  quotientForest_avoids_outer_survivors : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    v ∈ G.vertices → v ∉ s.1.1.vertices → v ∉ (imageOf s).quotientForest.vertices
  /-- A left-primitive one-stage star is a two-stage survivor (NOT a quotient star — the 6a-8c-0 fix). -/
  leftStar_toSurvivor : ∀ (s : ResolvedCoassocSplitChoice D G) (i : OneStageStarIndex D G s),
    i.isLeft → isContractSurvivingVertex (imageOf s).quotientForest i.vertex
  /-- A two-stage surviving vertex is an original survivor or a left-primitive `δ`-star. -/
  twoStageSurvivor_cases : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    isContractSurvivingVertex (imageOf s).quotientForest v →
      isContractSurvivingVertex s.1.1 v ∨
        ∃ i : OneStageStarIndex D G s, i.isLeft ∧ i.vertex = v

/-- **R-6c-leaf-17 — the three-route vertex transport supply from the connector.**  `survivingOriginal_to`
is proved from the two correct containments (the 6a-7b `surviving_to` replay). -/
def ResolvedThreeRouteTransportConnector.toTransportSupply
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (T : ResolvedThreeRouteTransportConnector D G imageOf) :
    ResolvedThreeRouteVertexTransportSupply D G imageOf where
  survivingOriginal_to := fun s {v} hv => by
    refine ⟨?_, ?_⟩
    · rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices]
      exact Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨hv.1, fun hvA' => hv.2 (T.selectedOuter_vertices_subset s hvA')⟩)
    · exact T.quotientForest_avoids_outer_survivors s hv.1 hv.2
  leftStar_toSurvivor := T.leftStar_toSurvivor
  twoStageSurvivor_cases := T.twoStageSurvivor_cases

end GaugeGeometry.QFT.Combinatorial
