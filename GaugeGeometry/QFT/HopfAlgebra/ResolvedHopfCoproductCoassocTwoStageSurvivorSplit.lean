import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTransportLeaves

/-!
# R-6c-body-11 — two-stage survivor split (Transport exhaustiveness, from two connectors)

Eleventh genuine-body step, closing the Transport three routes: every two-stage survivor is either an original
input-outer survivor or a left-primitive `δ`-star (the exact converse of body-10's `left_star_survives`).

A two-stage survivor `v` is a vertex of `selectedOuter.contractWithStars` not in the quotient forest.  The
quotient graph's vertices split (`contractWithStars_vertices`) into `(G.vertices \ selectedOuter) ∪
selectedOuter.starVertices`:

* `v ∈ G.vertices \ selectedOuter` — if `v ∉ s.1.1` it is an ORIGINAL survivor; if `v ∈ s.1.1` (but ∉
  selectedOuter) it would be in the quotient forest (`inside_not_selected_in_quotient`), contradicting `v ∉
  quotientForest` — so this sub-case is impossible.
* `v ∈ selectedOuter.starVertices` — a selected-outer star not in the quotient forest comes from a
  LEFT-primitive component (`selected_star_survivor_is_left`).

The two exclusion/recovery facts are genuine vertex-region geometry, kept as supply fields.

Per the HALT, the two connectors are supply fields; the quotient-star equivalence / retarget untouched.

Landed:

* `ResolvedTwoStageSurvivorSplitSupply D G imageOf` — `inside_not_selected_in_quotient` +
  `selected_star_survivor_is_left`;
* `.two_stage_survivor_split` — the Transport exhaustiveness fact.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}

/-- **R-6c-body-11 — the two-stage survivor split supply.**  The two vertex-region exclusion/recovery facts. -/
structure ResolvedTwoStageSurvivorSplitSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- A `G`-vertex in the input outer but outside the selected outer is re-contracted into the quotient forest. -/
  inside_not_selected_in_quotient : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    v ∈ G.vertices → v ∈ s.1.1.vertices → v ∉ (imageOf s).selectedOuter.1.vertices →
      v ∈ (imageOf s).quotientForest.vertices
  /-- A selected-outer star not in the quotient forest comes from a left-primitive component. -/
  selected_star_survivor_is_left : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    v ∈ (imageOf s).selectedOuter.1.starVertices (D.starOf G (imageOf s).selectedOuter.1) →
      v ∉ (imageOf s).quotientForest.vertices →
      ∃ i : OneStageStarIndex D G s, i.isLeft ∧ i.vertex = v

/-- **R-6c-body-11 — the Transport `two_stage_survivor_split` (three-route exhaustiveness). -/
theorem ResolvedTwoStageSurvivorSplitSupply.two_stage_survivor_split
    (S : ResolvedTwoStageSurvivorSplitSupply D G imageOf) (s : ResolvedCoassocSplitChoice D G)
    {v : VertexId} (hsurv : isContractSurvivingVertex (imageOf s).quotientForest v) :
    isContractSurvivingVertex s.1.1 v ∨ ∃ i : OneStageStarIndex D G s, i.isLeft ∧ i.vertex = v := by
  obtain ⟨hvQG, hvQF⟩ := hsurv
  simp only [ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union,
    Finset.mem_sdiff] at hvQG
  rcases hvQG with ⟨hvG, hvNotSel⟩ | hvStar
  · by_cases hvA : v ∈ s.1.1.vertices
    · exact absurd (S.inside_not_selected_in_quotient s hvG hvA hvNotSel) hvQF
    · exact Or.inl ⟨hvG, hvA⟩
  · exact Or.inr (S.selected_star_survivor_is_left s hvStar hvQF)

end GaugeGeometry.QFT.Combinatorial
