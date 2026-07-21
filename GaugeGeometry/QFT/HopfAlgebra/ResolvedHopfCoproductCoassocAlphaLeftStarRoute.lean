import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaStarVertexRecover
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftPartition
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftPrimitiveFactor

/-!
# R-6c-body-519 — canonical left-star rename route audit + corrected route foundation (PROVED)

Five-hundred-and-nineteenth genuine-body step — a body-446-grade re-audit.  The legacy `leftStar_toSurvivor` carries a
left star by the IDENTITY on `VertexId`, but the two star values genuinely differ: a one-stage star is
`i.vertex = D.starOf G q.1.1.1 i.η` (the star relative to the INPUT outer), while the star living in the stage-1 quotient
graph is `D.starOf G (selectedOuterRawOf q.1) i.η` (relative to the SELECTED outer).  The canonical allocator depends on
the forest argument, so `sourceLeftStar ≠ targetLeftStar` in general — proving their equality would REINTRODUCE the
body-446 non-existence certificate.  So the left route is CORRECTED: it maps the input-outer star to the corresponding
selected-outer star, NOT the identity.

## The audit (Step 1) — two genuinely different stars, NEVER assumed equal

* `sourceLeftStar q i := D.starOf G q.1.1.1 i.η` (input outer);
* `targetLeftStar q i := D.starOf G (selectedOuterRawOf q.1) i.η` (selected outer).

Their equality is NEITHER assumed NOR proved.

## The corrected route foundation (Steps 2/3/6, this body)

* `leftIndex_mem_selectedOuter` — `i.isLeft → i.η ∈ selectedOuterRawOf` (`isLeftPrimitive_iff_leftSelectedConcrete` →
  `leftOf` → the `leftOf ∪ promotedOf` union);
* `targetLeftStar_mem_selectedOuterContractGraph` — `targetLeftStar ∈ selectedOuterContractGraph.vertices` (it is a
  `starVertices` element; NO equality with `sourceLeftStar`);
* `correctedLeftTarget_injective` — `targetLeftStar q i = targetLeftStar q j → i = j` (`starOf_injective` on the
  selected outer + `OneStageStarIndex` extensionality).

The corrected-left survivor property `targetLeftStar_not_mem_correctedQuotient` (and the packaged
`correctedLeftStar_toSurvivor`) — the genuine dispatch (survivor components inside `G.vertices` vs the fresh
`targetLeftStar`; corrected-remnant promoted-stars separated by `starOf_injective` + `leftOf`/`promotedOf` disjointness) —
is the named residual for the next body; it is NOT built here.

Per the HALT/guards: `sourceLeftStar = targetLeftStar` is NOT required; the legacy `ResolvedLeftStarSurvivalSupply` is NOT
inhabited; local permutations are NOT composed; no raw `∀ s`; no `corrected = uncorrected` graph equality; the
`not_mem`-survivor dispatch is named, NOT claimed; `quot_eq` / global `σ` / field equalities / full correspondence are NOT
entered; strict `StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc claim.  No facade, no flat term, no
`forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {G : ResolvedFeynmanGraph}
  (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G)

/-- **R-6c-body-519 — the input-outer star** (`i.vertex`; the legacy identity route's source). -/
noncomputable def sourceLeftStar
    (i : OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1) : VertexId :=
  canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1 i.η

/-- **R-6c-body-519 — the selected-outer star** (the corrected route's target; NOT assumed equal to `sourceLeftStar`). -/
noncomputable def targetLeftStar
    (i : OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1) : VertexId :=
  canonicalUniqueSupportedCarrierProperSupply.toData.starOf G
    ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf q.1)
    i.η

/-- **R-6c-body-519 ∎ — a left index's component is in the selected outer.** -/
theorem leftIndex_mem_selectedOuter
    (i : OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1) (hL : i.isLeft) :
    i.η ∈ ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
      q.1).elements := by
  have hlsc : ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 i.η :=
    (ResolvedCoassocSplitChoice.isLeftPrimitive_iff_leftSelectedConcrete q.1 i.toComponent).mp hL
  simp only [ResolvedForestPromoteSupply.selectedOuterRawOf, ResolvedAdmissibleSubgraph.union_elements,
    Finset.mem_union]
  left
  show i.η ∈ ((resolvedConcreteLeftSelectionSupply canonicalUniqueSupportedCarrierProperSupply.toData G).leftOf q.1).elements
  rw [resolved_leftOf_elements_eq]
  exact Finset.mem_filter.mpr ⟨i.hη, hlsc⟩

/-- **R-6c-body-519 ∎ — the corrected target star is a stage-1 quotient-graph vertex.**  NO equality with `sourceLeftStar`. -/
theorem targetLeftStar_mem_selectedOuterContractGraph
    (i : OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1) (hL : i.isLeft) :
    targetLeftStar q i ∈ (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1).vertices := by
  rw [ResolvedCoassocSplitChoice.selectedOuterContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union]
  exact Or.inr (ResolvedAdmissibleSubgraph.mem_starVertices.mpr
    ⟨i.η, leftIndex_mem_selectedOuter q i hL, rfl⟩)

/-- **R-6c-body-519 ∎ — the corrected left target is injective** (on left indices). -/
theorem correctedLeftTarget_injective
    (i j : OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1)
    (hLi : i.isLeft) (hLj : j.isLeft) (heq : targetLeftStar q i = targetLeftStar q j) : i = j := by
  have hη : i.η = j.η :=
    canonicalUniqueStarFactsOfW'.starOf_injective G
      ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf q.1)
      (leftIndex_mem_selectedOuter q i hLi) (leftIndex_mem_selectedOuter q j hLj) heq
  obtain ⟨ηi, hηi⟩ := i
  obtain ⟨ηj, hηj⟩ := j
  cases hη
  rfl

end GaugeGeometry.QFT.Combinatorial
