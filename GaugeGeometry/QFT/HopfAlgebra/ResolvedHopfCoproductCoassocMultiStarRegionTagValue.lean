import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTouchedChoiceAlignment
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarRegionCross

/-!
# R-6c-body-341 — the multi-star region-tag converter: raw forward outer on the actual model wiring (PROVED)

Three-hundred-and-forty-first genuine-body step — the concrete `ResolvedRegionTagValueSupply` on the
multi-star wiring.  It ELIMINATES body-340's three wiring hypotheses by concrete definitions and normalizes
the residual to exactly the **six forward-map bridge laws** + `recovered_raw_mem`:

```text
Region.componentToRight   := rightReembed            (body-337)
Region.componentToForest  := M.parent                (body-332)
Left.representedInQuotient := representedByTouched    (body-323)
forestTag                  := M.forestTag            (body-333)
pairwise / exclusivities   := body-338
raw-union carrier membership := recovered_raw_mem    (supplied gate)
```

so body-340's `hLeft := rfl`, `hForest := rfl`, `hTag := body-339`, giving

```lean
selectedOuterRawOf ((multiStarRegionTagValueSupply …).recoveredPreimageValue z) = z.1.1
```

on the real multi-star model, with the residual EXACTLY the six sound/complete bridges + `recovered_raw_mem`.

Per the HALT: the raw forward outer is complete on the multi-star wiring; the six sound/complete leaves and
`recovered_raw_mem` remain SUPPLIED model gates (genuine forward-map obligations); the forward quotient and
the forward-image `forestTag_agrees` are NOT touched.  No facade, no flat term, no `forgetHopf`, no rep/perm,
and NO `promote_collapse` / singleton / floor-297 anywhere.
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
set_option linter.unusedVariables false

/-- **R-6c-body-341 — the concrete multi-star region core** (body-337 right + body-332 forest). -/
noncomputable def multiStarRegion (M : ResolvedMultiStarDecontractionSupply D)
    (Fstar : ResolvedCanonicalStarFacts D) : ResolvedRegionConstructionFromSectorValueSupply D where
  componentToRight := fun z δ => rightReembed z δ
  rightComponentCD := fun z δ => (resolvedConcreteRightRegion D).rightComponentCD z δ
  rightComponentDisjoint := fun z => (resolvedConcreteRightRegion D).rightComponentDisjoint z
  componentToForest := fun z δ => M.parent z δ
  forestComponentCD := fun z δ => M.parentCD z δ
  forestComponentDisjoint := fun z γ₁ hγ₁ γ₂ hγ₂ hne => by
    obtain ⟨δ₁, -, rfl⟩ := Finset.mem_image.mp hγ₁
    obtain ⟨δ₂, -, rfl⟩ := Finset.mem_image.mp hγ₂
    exact localizedParent_pairwiseDisjoint Fstar z δ₁.1 δ₂.1 (M.legLift z δ₁) (M.legLift z δ₂)
      (M.hE _) (M.hL _)
      (z.2.1.pairwiseDisjoint (Finset.mem_filter.mp δ₁.2).1 (Finset.mem_filter.mp δ₂.2).1
        (fun h => hne (congrArg (M.parent z) (Subtype.ext h))))

/-- **R-6c-body-341 — the concrete multi-star left core** (`representedInQuotient := representedByTouched`). -/
def multiStarLeft : ResolvedLeftResidualConstructionValueSupply D where
  representedInQuotient := fun z γ => representedByTouched z γ

/-- **R-6c-body-341 — the concrete region-tag supply on the multi-star wiring.**  The six forward-map bridge
laws and `recovered_raw_mem` are received as supplied gates; everything else is the body-337/338/339/M
construction. -/
noncomputable def multiStarRegionTagValueSupply (M : ResolvedMultiStarDecontractionSupply D)
    (Fstar : ResolvedCanonicalStarFacts D) (Measure : ResolvedMeasureLeafSupply D)
    {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
    (right_sound : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (δ : {x // x ∈ rightDomain (fwdMapFilteredValue Fmem V q)}),
      rightPrimSelected q.1 (rightReembed (fwdMapFilteredValue Fmem V q) δ))
    (right_complete : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (γ : ResolvedFeynmanSubgraph G), rightPrimSelected q.1 γ →
      ∃ δ : {x // x ∈ rightDomain (fwdMapFilteredValue Fmem V q)},
        rightReembed (fwdMapFilteredValue Fmem V q) δ = γ)
    (forest_sound : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (δ : {x // x ∈ forestDomain (fwdMapFilteredValue Fmem V q)}),
      forestChoiceSelected q.1 (M.parent (fwdMapFilteredValue Fmem V q) δ))
    (forest_complete : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (γ : ResolvedFeynmanSubgraph G), forestChoiceSelected q.1 γ →
      ∃ δ : {x // x ∈ forestDomain (fwdMapFilteredValue Fmem V q)},
        M.parent (fwdMapFilteredValue Fmem V q) δ = γ)
    (left_sound : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (γ : ResolvedFeynmanSubgraph G), ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 γ →
      γ ∈ leftResidualTouched (fwdMapFilteredValue Fmem V q))
    (left_complete : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (γ : ResolvedFeynmanSubgraph G), γ ∈ leftResidualTouched (fwdMapFilteredValue Fmem V q) →
      ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 γ)
    (rrm : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      regionRawUnion M Fstar z ∈ D.carrier G) :
    ResolvedRegionTagValueSupply Fmem V where
  Closure :=
    { Assembly :=
        { Region := multiStarRegion M Fstar
          Left := multiStarLeft
          right_sound_value := right_sound
          right_complete_value := right_complete
          forest_sound_value := forest_sound
          forest_complete_value := forest_complete
          left_sound_value := left_sound
          left_complete_value := left_complete }
      selected := Fmem
      left_right_disjoint := fun z γ hγ δ hδ _ => left_right_cross z hγ hδ
      left_forest_disjoint := fun z γ hγ δ hδ _ => left_forest_cross M Fstar z hγ hδ
      right_forest_disjoint := fun z γ hγ δ hδ _ => right_forest_cross M z hγ hδ
      recovered_raw_mem := rrm }
  forestTag := fun z γ h => M.forestTag Fstar z ⟨γ.1, h⟩
  right_notMem_left := fun z γ hr =>
    right_notMem_left (fun H => Measure.toConnectedDivergentNonemptySupply H) z hr
  forest_notMem_left := fun z γ hf =>
    forest_notMem_left (fun H => Measure.toConnectedDivergentNonemptySupply H) M Fstar z hf
  forest_notMem_right := fun z γ hf =>
    forest_notMem_right (fun H => Measure.toConnectedDivergentNonemptySupply H) M Fstar z hf

/-- **R-6c-body-341 — the raw forward outer on the actual multi-star wiring** (body-340, wirings discharged). -/
theorem multiStar_selectedOuterRawOf_eq (M : ResolvedMultiStarDecontractionSupply D)
    (Fstar : ResolvedCanonicalStarFacts D) (Measure : ResolvedMeasureLeafSupply D)
    {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
    (right_sound : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (δ : {x // x ∈ rightDomain (fwdMapFilteredValue Fmem V q)}),
      rightPrimSelected q.1 (rightReembed (fwdMapFilteredValue Fmem V q) δ))
    (right_complete : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (γ : ResolvedFeynmanSubgraph G), rightPrimSelected q.1 γ →
      ∃ δ : {x // x ∈ rightDomain (fwdMapFilteredValue Fmem V q)},
        rightReembed (fwdMapFilteredValue Fmem V q) δ = γ)
    (forest_sound : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (δ : {x // x ∈ forestDomain (fwdMapFilteredValue Fmem V q)}),
      forestChoiceSelected q.1 (M.parent (fwdMapFilteredValue Fmem V q) δ))
    (forest_complete : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (γ : ResolvedFeynmanSubgraph G), forestChoiceSelected q.1 γ →
      ∃ δ : {x // x ∈ forestDomain (fwdMapFilteredValue Fmem V q)},
        M.parent (fwdMapFilteredValue Fmem V q) δ = γ)
    (left_sound : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (γ : ResolvedFeynmanSubgraph G), ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 γ →
      γ ∈ leftResidualTouched (fwdMapFilteredValue Fmem V q))
    (left_complete : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (γ : ResolvedFeynmanSubgraph G), γ ∈ leftResidualTouched (fwdMapFilteredValue Fmem V q) →
      ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 γ)
    (rrm : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      regionRawUnion M Fstar z ∈ D.carrier G)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf
        ((multiStarRegionTagValueSupply M Fstar Measure right_sound right_complete forest_sound
          forest_complete left_sound left_complete rrm).recoveredPreimageValue z) = z.1.1 :=
  (multiStarRegionTagValueSupply M Fstar Measure right_sound right_complete forest_sound
      forest_complete left_sound left_complete rrm).selectedOuterRawOf_eq M Fstar Measure z rfl rfl
    (fun γ _ h' => M.promote_forestTag_elements Fstar z ⟨γ.1, h'⟩)

end GaugeGeometry.QFT.Combinatorial
