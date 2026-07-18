import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarLeftBridge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedVertices
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftSelectConcrete

/-!
# R-6c-body-373 — Front-3 bank-2 fully sealed: `leftSelected_not_representedByTouched` PROVED (no `hLeftSound` gate)

Three-hundred-and-seventy-third genuine-body step — the true seal of bank-2.  Body-372 left the SOUND direction as the
gate `hLeftSound`; but that is NOT a concrete-model inhabitant — it is a GEOMETRY THEOREM derivable from
`cd_nonempty` + `pairwiseDisjoint` + `parent_remnantComponent` + M3.  This body proves it, so `hLeftSound` disappears
from the final gate list.

`leftSelected_not_representedByTouched`: a left-selected component (`choiceAt = inl true`) is unrepresented.  A
`representedByTouched` witness recovers (body-274) an occurrence `o` whose parent is `M.parent δ = o.γ.1`
(`parent_remnantComponent`); M3 + the promote transport (body-371) put `γ` in `promotedComponentElements o.γ`, so
`γ.vertices ⊆ o.γ.1.vertices` (`promotedComponentElements_vertices_subset_parent`).  Then `γ = o.γ.1` is impossible
(`inl true` vs `inr B`, `not_leftSelectedConcrete_of_inr`), and `γ ≠ o.γ.1` contradicts `q.outer.pairwiseDisjoint` +
`Measure.cd_nonempty` (a nonempty subset of a disjoint set) — the exact `cross_disjoint_leftOf_promotedOf` pattern.

Landed axiom-clean: `leftSelected_not_representedByTouched`, `left_sound_value_of_multiStar_geometry`,
`resolvedMultiStarLeftBridgeOfGeometry`.

Per the HALT: the SOUND geometry theorem is proved (no `hLeftSound` gate remains); bank-2's six bridges are now GENUINELY
sealed with NO provable theorem smuggled as a model assumption; the remaining bank-3 gates are exactly `legLift` /
`innerStar_agrees` / `OccInv` / `parent_remnantComponent` / `hSurvivorComponent`.  No facade, no flat term, no
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

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

namespace ResolvedMultiStarDecontractionSupply

variable (M : ResolvedMultiStarDecontractionSupply D)
  {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-373 — a left-selected component is unrepresented** (the SOUND geometry theorem). -/
theorem leftSelected_not_representedByTouched (OccInv : ResolvedForestOccurrenceInversionSupply M)
    (Measure : ResolvedMeasureLeafSupply D) (P : ResolvedValueQuotientRegionSplitSupply Fmem V)
    (parent_remnantComponent : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
      (δ : {x // x ∈ forestDomain (fwdMapFilteredValue Fmem V q)}),
      HEq (V.Remnant.remnant.remnantComponent q.1 o) δ.1 →
      M.parent (fwdMapFilteredValue Fmem V q) δ = o.γ.1)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) (γ : ResolvedFeynmanSubgraph G)
    (hls : ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 γ) :
    ¬ representedByTouched (fwdMapFilteredValue Fmem V q) γ := by
  rintro ⟨δ, hδ, hγt⟩
  obtain ⟨γ_fc, -, hoeq⟩ := Finset.mem_image.mp ((P.forestDomain_value_mem q δ).mp hδ)
  set δs : {x // x ∈ forestDomain (fwdMapFilteredValue Fmem V q)} := ⟨δ, hδ⟩ with hδs
  set o := ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 γ_fc with ho
  have hp : M.parent (fwdMapFilteredValue Fmem V q) δs = o.γ.1 :=
    parent_remnantComponent q o δs (heq_of_eq hoeq)
  have hi : HEq (M.innerIdx (fwdMapFilteredValue Fmem V q) δs) o.B :=
    M.innerIdx_occurrence OccInv (fwdMapFilteredValue Fmem V q) δs q.1 o hp
  -- γ ∈ promotedComponentElements o.γ
  have hγt2 : γ ∈ ResolvedCoassocSplitChoice.promotedComponentElements q.1 o.γ := by
    rw [ResolvedCoassocSplitChoice.promotedComponentElements_inr q.1 o.hchoice,
      ← promote_elements_congr hp (M.innerIdx (fwdMapFilteredValue Fmem V q) δs) o.B hi]
    show γ ∈ (ResolvedAdmissibleSubgraph.promote
      (localizedParentWithTouchedLegs (fwdMapFilteredValue Fmem V q) δs.1
        (M.legLift (fwdMapFilteredValue Fmem V q) δs) (M.hE (fwdMapFilteredValue Fmem V q)) (M.hL (fwdMapFilteredValue Fmem V q)))
      (innerRaw (fwdMapFilteredValue Fmem V q) δs.1
        (M.legLift (fwdMapFilteredValue Fmem V q) δs) (M.hE (fwdMapFilteredValue Fmem V q)) (M.hL (fwdMapFilteredValue Fmem V q)))).elements
    rw [promote_innerRaw_elements (fwdMapFilteredValue Fmem V q) δs.1
      (M.legLift (fwdMapFilteredValue Fmem V q) δs) (M.hE (fwdMapFilteredValue Fmem V q)) (M.hL (fwdMapFilteredValue Fmem V q))]
    exact hγt
  have hsub : γ.vertices ⊆ o.γ.1.vertices :=
    ResolvedCoassocSplitChoice.promotedComponentElements_vertices_subset_parent q.1 hγt2
  obtain ⟨hγO, hch⟩ := hls
  by_cases hEq : γ = o.γ.1
  · exact ResolvedCoassocSplitChoice.not_leftSelectedConcrete_of_inr q.1 o.γ.2 o.hchoice
      (hEq ▸ ⟨hγO, hch⟩)
  · have hdisj : _root_.Disjoint γ.vertices o.γ.1.vertices := q.1.1.1.pairwiseDisjoint hγO o.γ.2 hEq
    obtain ⟨v, hv⟩ := Measure.cd_nonempty γ (q.1.1.1.isConnectedDivergent γ hγO)
    exact Finset.disjoint_left.mp hdisj hv (hsub hv)

/-- **R-6c-body-373 — the SOUND direction, fully proved** (`hLeftSound` discharged). -/
theorem left_sound_value_of_multiStar_geometry (OccInv : ResolvedForestOccurrenceInversionSupply M)
    (Measure : ResolvedMeasureLeafSupply D) (P : ResolvedValueQuotientRegionSplitSupply Fmem V)
    (parent_remnantComponent : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
      (δ : {x // x ∈ forestDomain (fwdMapFilteredValue Fmem V q)}),
      HEq (V.Remnant.remnant.remnantComponent q.1 o) δ.1 →
      M.parent (fwdMapFilteredValue Fmem V q) δ = o.γ.1)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) (γ : ResolvedFeynmanSubgraph G)
    (hls : ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 γ) :
    γ ∈ (multiStarLeft.leftResidual (fwdMapFilteredValue Fmem V q)).elements := by
  rw [multiStarLeft, ResolvedLeftResidualConstructionValueSupply.leftResidual_elements_eq,
    Finset.mem_filter]
  refine ⟨?_, M.leftSelected_not_representedByTouched OccInv Measure P parent_remnantComponent q γ hls⟩
  have hleft : γ ∈ ((resolvedConcreteForestPromoteSupply D G).leftOf q.1).elements := by
    show γ ∈ q.1.1.1.elements.filter (ResolvedCoassocSplitChoice.leftSelectedConcrete q.1)
    exact Finset.mem_filter.mpr ⟨hls.choose, hls⟩
  exact (@Finset.mem_union _ (Classical.decEq _) _ _ _).mpr (Or.inl hleft)

/-- **R-6c-body-373 — the multi-star LEFT bridge with NO `hLeftSound` gate.** -/
noncomputable def resolvedMultiStarLeftBridgeOfGeometry
    (OccInv : ResolvedForestOccurrenceInversionSupply M) (Measure : ResolvedMeasureLeafSupply D)
    (P : ResolvedValueQuotientRegionSplitSupply Fmem V)
    (parent_remnantComponent : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
      (δ : {x // x ∈ forestDomain (fwdMapFilteredValue Fmem V q)}),
      HEq (V.Remnant.remnant.remnantComponent q.1 o) δ.1 →
      M.parent (fwdMapFilteredValue Fmem V q) δ = o.γ.1) :
    ResolvedLeftResidualValueCoreBridgeSupply Fmem V :=
  M.resolvedMultiStarLeftBridge OccInv P parent_remnantComponent
    (fun {_G} q γ hls =>
      M.left_sound_value_of_multiStar_geometry OccInv Measure P parent_remnantComponent q γ hls)

end ResolvedMultiStarDecontractionSupply

end GaugeGeometry.QFT.Combinatorial
