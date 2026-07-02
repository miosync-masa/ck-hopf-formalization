import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorSurjectivityBody

/-!
# R-6c-body-4 — Sector index surjectivity (both PROVED)

Fourth genuine-body step, discharging body-3's two index surjectivities OUTRIGHT.  `OneStageStarIndex` is just
`η` + `hη` (a component of `s.1.1`), so an index is built directly from a component of `rightComponents` /
`forestComponents`:

* `sector_right_index_surj` — every `γ ∈ rightComponents` is `r.toRightComponent` for `r := ⟨⟨γ.1.1, γ.1.2⟩,
  isRight⟩` (`isRight = s.isRightPrimitive γ.1` from the filter membership); the equality is `Subtype.ext rfl`.
* `sector_forest_index_surj` — every `γ ∈ forestComponents` has `f.toOccurrence = forestComponentOccurrence γ`
  for `f := ⟨⟨γ.1.1, γ.1.2⟩, isForest⟩`; both occurrences are `⟨γ.1, Classical.choose _, _⟩` over the SAME
  `∃ B, choiceAt γ.1 = inr B`, so equal by `rfl` (proof-irrelevance of `Classical.choose`).

So the leaf-30 `occurrence_match` and the body-3 index surjectivities are all discharged by these two.

Per the HALT, `elements_eq` untouched; these are the localized `componentPartition` reductions.

Landed:

* `sector_right_index_surj` / `sector_forest_index_surj` — both PROVED.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

open scoped Classical

/-- **R-6c-body-4 — right index surjectivity.**  Every right-primitive component is a `RightPrimitiveIndex`'s
`toRightComponent`. -/
theorem sector_right_index_surj (s : ResolvedCoassocSplitChoice D G)
    (γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents}) :
    ∃ r : RightPrimitiveIndex D G s, r.toRightComponent = γ := by
  refine ⟨⟨⟨γ.1.1, γ.1.2⟩, (Finset.mem_filter.mp γ.2).2⟩, ?_⟩
  apply Subtype.ext; rfl

/-- **R-6c-body-4 — forest index surjectivity.**  Every forest-choice component's occurrence is a
`ForestPrimitiveIndex`'s `toOccurrence`. -/
theorem sector_forest_index_surj (s : ResolvedCoassocSplitChoice D G)
    (γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.forestComponents}) :
    ∃ f : ForestPrimitiveIndex D G s, f.toOccurrence = s.forestComponentOccurrence γ :=
  ⟨⟨⟨γ.1.1, γ.1.2⟩, (Finset.mem_filter.mp γ.2).2⟩, rfl⟩

end GaugeGeometry.QFT.Combinatorial
