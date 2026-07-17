import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForwardOuterValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedForestTagBiUnion

/-!
# R-6c-body-340 — touched choice alignment: `selectedOuterRawOf(recovered) = z.1.1` (PROVED, closure-conditional)

Three-hundred-and-fortieth genuine-body step — the choice-alignment arrest.  Over ANY value-root tag supply
`T : ResolvedRegionTagValueSupply Fmem V` (its `Closure` — the region bridge, the six sound/complete leaves,
and `recovered_raw_mem` — is received as a SUPPLIED gate), plus three wiring facts that a concrete multi-star
`T` discharges (left-residual shape, forest-region shape, and the forest-tag transport of body-339), the two
region equalities and the raw-outer equality are PROVED with NO `promote_collapse`, NO floor-297:

```text
leftOf (recoveredPreimageValue z) .elements     = leftResidualTouched z          (pure tag, body-282)
promotedOf (recoveredPreimageValue z) .elements = promotedTouchedUnion z         (biUnion via body-339)
selectedOuterRawOf (recoveredPreimageValue z)   = z.1.1                          (body-334 union + ext_elements)
```

## The wiring gates (discharged by a concrete `T`, NOT free)

* `hLeft` — `(Assembly.Left.leftResidual z).elements = leftResidualTouched z` (`representedInQuotient := representedByTouched`).
* `hForest` — `(Assembly.Region.forestRecovered z).elements = (forestRecoveredMulti z).elements` (`componentToForest := parent`).
* `hTag` — `(promote γ.1 (T.forestTag z γ hf).1).elements = touchedOuterComponents z (forestSource ⟨γ.1, h'⟩)` — this IS
  body-339's `promote_forestTag_elements` at `T.forestTag := M.forestTag`; the transport (the `promote_collapse`
  replacement) is done in body-339, so here it is honest wiring, not a re-assumption of the crux.

## The `leftOf` proof is the body-282 pure tag; the `promotedOf` proof is the body-339 biUnion

`leftOf` filters `unionOuterValue` by `leftSelectedConcrete`; `right_tag` / `forest_tag` exclude the non-left tags,
`left_tag` includes the left ones — exactly body-289's `leftOf_recovered_eq`, re-keyed to `T`.  `promotedOf` is the
`inl → ∅` biUnion collapse whose forest branch is `hTag` (→ `touchedOuterComponents`), reindexed against
`forestDomain` by `forestSource` / `forestSource_parent` (`Measure`) to body-334's `promotedTouchedUnion`.

Per the HALT: the choice alignment is PROVED, but `T`'s `Closure` (the region bridge, the six sound/complete
leaves, `recovered_raw_mem`) and the wiring stay SUPPLIED gates; the forward quotient and the forward-image
`forestTag_agrees` are NOT touched.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
`promote_collapse` / singleton / floor-297 anywhere.
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

namespace ResolvedRegionTagValueSupply

variable {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-340 — the reconstruction's `choiceAt` is `recoverChoiceValue`** (`rfl`, body-289 shape). -/
theorem choiceAt_recovered_eq' (T : ResolvedRegionTagValueSupply Fmem V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Closure.unionOuterValue z).1.elements}) :
    ResolvedCoassocSplitChoice.choiceAt (T.recoveredPreimageValue z) γ
      = T.recoverChoiceValue z γ (Finset.mem_attach _ _) :=
  rfl

/-- **R-6c-body-340 — `leftOf(recovered) = leftResidualTouched`** (pure tag, body-282). -/
theorem leftOf_elements_eq_leftResidualTouched (T : ResolvedRegionTagValueSupply Fmem V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (hLeft : (T.Closure.Assembly.Left.leftResidual z).elements = leftResidualTouched z) :
    ((resolvedConcreteForestPromoteSupply D G).leftOf (T.recoveredPreimageValue z)).elements
      = leftResidualTouched z := by
  rw [← hLeft]
  have hLe : ((resolvedConcreteForestPromoteSupply D G).leftOf
        (T.recoveredPreimageValue z)).elements
      = (T.Closure.unionOuterValue z).1.elements.filter
          (ResolvedCoassocSplitChoice.leftSelectedConcrete (T.recoveredPreimageValue z)) := rfl
  rw [hLe]
  ext γ
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hmemU, hγmem, htag⟩
    rcases (T.Closure.mem_unionOuterValue_iff z γ).mp hmemU with hl | hr | hf
    · exact hl
    · exact absurd (Sum.inl.inj ((T.right_tag z ⟨γ, hmemU⟩ hr).symm.trans
        ((T.choiceAt_recovered_eq' z ⟨γ, hmemU⟩).symm.trans htag))) (by decide)
    · obtain ⟨B, hB⟩ := T.forest_tag z ⟨γ, hmemU⟩ hf
      exact absurd (hB.symm.trans ((T.choiceAt_recovered_eq' z ⟨γ, hmemU⟩).symm.trans htag)) (by simp)
  · intro hl
    have hmemU : γ ∈ (T.Closure.unionOuterValue z).1.elements :=
      (T.Closure.mem_unionOuterValue_iff z γ).mpr (Or.inl hl)
    exact ⟨hmemU, hmemU,
      (T.choiceAt_recovered_eq' z ⟨γ, hmemU⟩).trans (T.left_tag z ⟨γ, hmemU⟩ hl)⟩

/-- **R-6c-body-340 — `promotedOf(recovered) = promotedTouchedUnion`** (biUnion via body-339, NO `promote_collapse`). -/
theorem promotedOf_elements_eq_promotedTouchedUnion (M : ResolvedMultiStarDecontractionSupply D)
    (Fstar : ResolvedCanonicalStarFacts D) (Measure : ResolvedMeasureLeafSupply D)
    (T : ResolvedRegionTagValueSupply Fmem V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (hForest : (T.Closure.Assembly.Region.forestRecovered z).elements
      = (M.forestRecoveredMulti Fstar z).elements)
    (hTag : ∀ (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Closure.unionOuterValue z).1.elements})
      (hf : γ.1 ∈ (T.Closure.Assembly.Region.forestRecovered z).elements)
      (h' : γ.1 ∈ (M.forestRecoveredMulti Fstar z).elements),
      (ResolvedAdmissibleSubgraph.promote γ.1 (T.forestTag z γ hf).1).elements
        = touchedOuterComponents z (M.forestSource Fstar z ⟨γ.1, h'⟩).1) :
    ((resolvedConcreteForestPromoteSupply D G).promotedOf (T.recoveredPreimageValue z)).elements
      = M.promotedTouchedUnion z := by
  have hpe : ((resolvedConcreteForestPromoteSupply D G).promotedOf
        (T.recoveredPreimageValue z)).elements
      = (T.Closure.unionOuterValue z).1.elements.attach.biUnion
        (ResolvedCoassocSplitChoice.promotedComponentElements (T.recoveredPreimageValue z)) := rfl
  rw [hpe]
  ext x
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨γ, -, hx⟩
    rcases (T.Closure.mem_unionOuterValue_iff z γ.1).mp γ.2 with hl | hr | hf
    · exfalso
      rw [show ResolvedCoassocSplitChoice.promotedComponentElements
            (T.recoveredPreimageValue z) γ = ∅ from by
          unfold ResolvedCoassocSplitChoice.promotedComponentElements
          rw [(T.choiceAt_recovered_eq' z γ).trans (T.left_tag z γ hl)]] at hx
      simp at hx
    · exfalso
      rw [show ResolvedCoassocSplitChoice.promotedComponentElements
            (T.recoveredPreimageValue z) γ = ∅ from by
          unfold ResolvedCoassocSplitChoice.promotedComponentElements
          rw [(T.choiceAt_recovered_eq' z γ).trans (T.right_tag z γ hr)]] at hx
      simp at hx
    · have h' : γ.1 ∈ (M.forestRecoveredMulti Fstar z).elements := by rw [← hForest]; exact hf
      rw [ResolvedCoassocSplitChoice.promotedComponentElements_inr _
          ((T.choiceAt_recovered_eq' z γ).trans (by
            rw [ResolvedRegionTagValueSupply.recoverChoiceValue,
              if_neg (T.forest_notMem_left z γ hf),
              if_neg (T.forest_notMem_right z γ hf), dif_pos hf])),
        hTag γ hf h'] at hx
      unfold ResolvedMultiStarDecontractionSupply.promotedTouchedUnion
      rw [Finset.mem_biUnion]
      refine ⟨M.forestSource Fstar z ⟨γ.1, h'⟩, Finset.mem_attach _ _, ?_⟩
      rw [M.promote_parent_innerIdx_elements]; exact hx
  · intro hx
    unfold ResolvedMultiStarDecontractionSupply.promotedTouchedUnion at hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨δ, -, hxδ⟩ := hx
    rw [M.promote_parent_innerIdx_elements] at hxδ
    have hmemMulti : M.parent z δ ∈ (M.forestRecoveredMulti Fstar z).elements := by
      rw [M.forestRecoveredMulti_elements Fstar z]
      exact Finset.mem_image.mpr ⟨δ, Finset.mem_attach _ _, rfl⟩
    have hf : M.parent z δ ∈ (T.Closure.Assembly.Region.forestRecovered z).elements := by
      rw [hForest]; exact hmemMulti
    have hmemU : M.parent z δ ∈ (T.Closure.unionOuterValue z).1.elements :=
      (T.Closure.mem_unionOuterValue_iff z (M.parent z δ)).mpr (Or.inr (Or.inr hf))
    refine ⟨⟨M.parent z δ, hmemU⟩, Finset.mem_attach _ _, ?_⟩
    rw [ResolvedCoassocSplitChoice.promotedComponentElements_inr _
        ((T.choiceAt_recovered_eq' z ⟨M.parent z δ, hmemU⟩).trans (by
          rw [ResolvedRegionTagValueSupply.recoverChoiceValue,
            if_neg (T.forest_notMem_left z ⟨M.parent z δ, hmemU⟩ hf),
            if_neg (T.forest_notMem_right z ⟨M.parent z δ, hmemU⟩ hf), dif_pos hf])),
      hTag ⟨M.parent z δ, hmemU⟩ hf hmemMulti,
      M.forestSource_parent Fstar Measure z δ hmemMulti]
    exact hxδ

/-- **R-6c-body-340 — the raw-outer element equality** (body-334 union). -/
theorem selectedOuterRawOf_elements_eq (M : ResolvedMultiStarDecontractionSupply D)
    (Fstar : ResolvedCanonicalStarFacts D) (Measure : ResolvedMeasureLeafSupply D)
    (T : ResolvedRegionTagValueSupply Fmem V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (hLeft : (T.Closure.Assembly.Left.leftResidual z).elements = leftResidualTouched z)
    (hForest : (T.Closure.Assembly.Region.forestRecovered z).elements
      = (M.forestRecoveredMulti Fstar z).elements)
    (hTag : ∀ (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Closure.unionOuterValue z).1.elements})
      (hf : γ.1 ∈ (T.Closure.Assembly.Region.forestRecovered z).elements)
      (h' : γ.1 ∈ (M.forestRecoveredMulti Fstar z).elements),
      (ResolvedAdmissibleSubgraph.promote γ.1 (T.forestTag z γ hf).1).elements
        = touchedOuterComponents z (M.forestSource Fstar z ⟨γ.1, h'⟩).1) :
    ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf
        (T.recoveredPreimageValue z)).elements = z.1.1.elements := by
  rw [ResolvedForestPromoteSupply.selectedOuterRawOf, ResolvedAdmissibleSubgraph.union_elements,
    T.leftOf_elements_eq_leftResidualTouched z hLeft,
    T.promotedOf_elements_eq_promotedTouchedUnion M Fstar Measure z hForest hTag]
  ext a
  simp only [Finset.mem_union]
  rw [← M.leftResidual_union_promotedTouched z]
  simp only [Finset.mem_union]

/-- **R-6c-body-340 — the raw-outer equality** (`ext_elements`; choice alignment arrested). -/
theorem selectedOuterRawOf_eq (M : ResolvedMultiStarDecontractionSupply D)
    (Fstar : ResolvedCanonicalStarFacts D) (Measure : ResolvedMeasureLeafSupply D)
    (T : ResolvedRegionTagValueSupply Fmem V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (hLeft : (T.Closure.Assembly.Left.leftResidual z).elements = leftResidualTouched z)
    (hForest : (T.Closure.Assembly.Region.forestRecovered z).elements
      = (M.forestRecoveredMulti Fstar z).elements)
    (hTag : ∀ (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Closure.unionOuterValue z).1.elements})
      (hf : γ.1 ∈ (T.Closure.Assembly.Region.forestRecovered z).elements)
      (h' : γ.1 ∈ (M.forestRecoveredMulti Fstar z).elements),
      (ResolvedAdmissibleSubgraph.promote γ.1 (T.forestTag z γ hf).1).elements
        = touchedOuterComponents z (M.forestSource Fstar z ⟨γ.1, h'⟩).1) :
    (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf (T.recoveredPreimageValue z)
      = z.1.1 :=
  ResolvedAdmissibleSubgraph.ext_elements
    (T.selectedOuterRawOf_elements_eq M Fstar Measure z hLeft hForest hTag)

end ResolvedRegionTagValueSupply

end GaugeGeometry.QFT.Combinatorial
