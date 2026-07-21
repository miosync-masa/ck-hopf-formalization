import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRegionAssembly
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTouchedChoiceAlignment
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaForwardGeometry

/-!
# R-6c-body-490 — the alpha raw-outer identity (`houter`) on the canonical alpha `Tags` (PROVED)

Four-hundred-and-ninetieth genuine-body step — the pure tag-geometry half of the forward identities.  Body-340's tag
alignment is mirrored to the alpha `Tags` (body-477/488): the reconstructed choice's re-promoted outer is the original
outer, `selectedOuterRawOf (Tags.recoveredPreimageAlphaValue z) = z.1.1`, with NO `Data` / membership / raw quotient /
`hround`.

* `choiceAt_recovered_alpha_eq` — the `rfl` bridge `choiceAt (recoveredPreimageAlphaValue z) = recoverChoiceAlphaValue z`;
* `leftOf_alpha_elements_eq_leftResidualTouched` — `leftOf(recovered) = leftResidualTouched` (pure alpha tags);
* `promotedOf_alpha_elements_eq_promotedTouchedUnion` — `promotedOf(recovered) = promotedTouchedUnion` (biUnion via the
  canonical `forestTag = M.forestTag`);
* `selectedOuterRawOf_alpha_elements_eq` / `multiStar_selectedOuterRawOf_alpha_eq` — the outer element / subgraph identity;
* `canonicalMultiStar_alpha_houter` — the canonical specialization on body-488's tags (`hLeft` / `hForest` `rfl`, `hTag`
  from `M.promote_forestTag_elements`).

Per the HALT/guards: the raw quotient collection is NOT built; the raw `hround` is NOT consumed; the mixed `p_R` / `p_L`
exclusions are NOT entered; NO `Data` / `qz`; the body-478 `Data`-dependent forward-outer theorem is NOT detoured through;
strict `StarProm` / `InnerStarRaw` NOT restored; body-445 stays a valid conditional.  NOT the unconditional theorem.  No
facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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
set_option maxHeartbeats 1600000

namespace ResolvedRegionTagAlphaValueSupply

variable {Fmem : ResolvedSelectedOuterFilteredMemSupply D}
  {V : ResolvedFilteredConcreteSummandValueSupply D}

/-- **R-6c-body-490 — the alpha choice-at-the-reconstruction bridge** (`rfl`). -/
theorem choiceAt_recovered_alpha_eq (T : ResolvedRegionTagAlphaValueSupply Fmem V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Closure.unionOuterAlphaValue z).1.elements}) :
    ResolvedCoassocSplitChoice.choiceAt (T.recoveredPreimageAlphaValue z) γ
      = T.recoverChoiceAlphaValue z γ (Finset.mem_attach _ _) :=
  rfl

/-- **R-6c-body-490 — `leftOf(recovered) = leftResidualTouched`** (pure alpha tags, body-340 mirror). -/
theorem leftOf_alpha_elements_eq_leftResidualTouched (T : ResolvedRegionTagAlphaValueSupply Fmem V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (hLeft : (T.Closure.Assembly.Left.leftResidual z).elements = leftResidualTouched z) :
    ((resolvedConcreteForestPromoteSupply D G).leftOf (T.recoveredPreimageAlphaValue z)).elements
      = leftResidualTouched z := by
  rw [← hLeft]
  have hLe : ((resolvedConcreteForestPromoteSupply D G).leftOf
        (T.recoveredPreimageAlphaValue z)).elements
      = (T.Closure.unionOuterAlphaValue z).1.elements.filter
          (ResolvedCoassocSplitChoice.leftSelectedConcrete (T.recoveredPreimageAlphaValue z)) := rfl
  rw [hLe]
  ext γ
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hmemU, hγmem, htag⟩
    rcases (T.Closure.mem_unionOuterAlphaValue_iff z γ).mp hmemU with hl | hr | hf
    · exact hl
    · exact absurd (Sum.inl.inj ((T.right_tag_alpha z ⟨γ, hmemU⟩ hr).symm.trans
        ((T.choiceAt_recovered_alpha_eq z ⟨γ, hmemU⟩).symm.trans htag))) (by decide)
    · obtain ⟨B, hB⟩ := T.forest_tag_alpha z ⟨γ, hmemU⟩ hf
      exact absurd (hB.symm.trans ((T.choiceAt_recovered_alpha_eq z ⟨γ, hmemU⟩).symm.trans htag)) (by simp)
  · intro hl
    have hmemU : γ ∈ (T.Closure.unionOuterAlphaValue z).1.elements :=
      (T.Closure.mem_unionOuterAlphaValue_iff z γ).mpr (Or.inl hl)
    exact ⟨hmemU, hmemU,
      (T.choiceAt_recovered_alpha_eq z ⟨γ, hmemU⟩).trans (T.left_tag_alpha z ⟨γ, hmemU⟩ hl)⟩

/-- **R-6c-body-490 — `promotedOf(recovered) = promotedTouchedUnion`** (biUnion via the canonical `forestTag`, body-340
mirror). -/
theorem promotedOf_alpha_elements_eq_promotedTouchedUnion
    (M : ResolvedMultiStarDecontractionSupply D) (Fstar : ResolvedCanonicalStarFacts D)
    (Measure : ResolvedMeasureLeafSupply D) (T : ResolvedRegionTagAlphaValueSupply Fmem V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (hForest : (T.Closure.Assembly.Region.forestRecovered z).elements
      = (M.forestRecoveredMulti Fstar z).elements)
    (hTag : ∀ (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Closure.unionOuterAlphaValue z).1.elements})
      (hf : γ.1 ∈ (T.Closure.Assembly.Region.forestRecovered z).elements)
      (h' : γ.1 ∈ (M.forestRecoveredMulti Fstar z).elements),
      (ResolvedAdmissibleSubgraph.promote γ.1 (T.forestTag z γ hf).1).elements
        = touchedOuterComponents z (M.forestSource Fstar z ⟨γ.1, h'⟩).1) :
    ((resolvedConcreteForestPromoteSupply D G).promotedOf (T.recoveredPreimageAlphaValue z)).elements
      = M.promotedTouchedUnion z := by
  have hpe : ((resolvedConcreteForestPromoteSupply D G).promotedOf
        (T.recoveredPreimageAlphaValue z)).elements
      = (T.Closure.unionOuterAlphaValue z).1.elements.attach.biUnion
        (ResolvedCoassocSplitChoice.promotedComponentElements (T.recoveredPreimageAlphaValue z)) := rfl
  rw [hpe]
  ext x
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨γ, -, hx⟩
    rcases (T.Closure.mem_unionOuterAlphaValue_iff z γ.1).mp γ.2 with hl | hr | hf
    · exfalso
      rw [show ResolvedCoassocSplitChoice.promotedComponentElements
            (T.recoveredPreimageAlphaValue z) γ = ∅ from by
          unfold ResolvedCoassocSplitChoice.promotedComponentElements
          rw [(T.choiceAt_recovered_alpha_eq z γ).trans (T.left_tag_alpha z γ hl)]] at hx
      simp at hx
    · exfalso
      rw [show ResolvedCoassocSplitChoice.promotedComponentElements
            (T.recoveredPreimageAlphaValue z) γ = ∅ from by
          unfold ResolvedCoassocSplitChoice.promotedComponentElements
          rw [(T.choiceAt_recovered_alpha_eq z γ).trans (T.right_tag_alpha z γ hr)]] at hx
      simp at hx
    · have h' : γ.1 ∈ (M.forestRecoveredMulti Fstar z).elements := by rw [← hForest]; exact hf
      rw [ResolvedCoassocSplitChoice.promotedComponentElements_inr _
          ((T.choiceAt_recovered_alpha_eq z γ).trans (by
            rw [ResolvedRegionTagAlphaValueSupply.recoverChoiceAlphaValue,
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
    have hmemU : M.parent z δ ∈ (T.Closure.unionOuterAlphaValue z).1.elements :=
      (T.Closure.mem_unionOuterAlphaValue_iff z (M.parent z δ)).mpr (Or.inr (Or.inr hf))
    refine ⟨⟨M.parent z δ, hmemU⟩, Finset.mem_attach _ _, ?_⟩
    rw [ResolvedCoassocSplitChoice.promotedComponentElements_inr _
        ((T.choiceAt_recovered_alpha_eq z ⟨M.parent z δ, hmemU⟩).trans (by
          rw [ResolvedRegionTagAlphaValueSupply.recoverChoiceAlphaValue,
            if_neg (T.forest_notMem_left z ⟨M.parent z δ, hmemU⟩ hf),
            if_neg (T.forest_notMem_right z ⟨M.parent z δ, hmemU⟩ hf), dif_pos hf])),
      hTag ⟨M.parent z δ, hmemU⟩ hf hmemMulti,
      M.forestSource_parent Fstar Measure z δ hmemMulti]
    exact hxδ

/-- **R-6c-body-490 — the raw-outer element equality** (body-334 union, alpha). -/
theorem selectedOuterRawOf_alpha_elements_eq
    (M : ResolvedMultiStarDecontractionSupply D) (Fstar : ResolvedCanonicalStarFacts D)
    (Measure : ResolvedMeasureLeafSupply D) (T : ResolvedRegionTagAlphaValueSupply Fmem V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (hLeft : (T.Closure.Assembly.Left.leftResidual z).elements = leftResidualTouched z)
    (hForest : (T.Closure.Assembly.Region.forestRecovered z).elements
      = (M.forestRecoveredMulti Fstar z).elements)
    (hTag : ∀ (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Closure.unionOuterAlphaValue z).1.elements})
      (hf : γ.1 ∈ (T.Closure.Assembly.Region.forestRecovered z).elements)
      (h' : γ.1 ∈ (M.forestRecoveredMulti Fstar z).elements),
      (ResolvedAdmissibleSubgraph.promote γ.1 (T.forestTag z γ hf).1).elements
        = touchedOuterComponents z (M.forestSource Fstar z ⟨γ.1, h'⟩).1) :
    ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf
        (T.recoveredPreimageAlphaValue z)).elements = z.1.1.elements := by
  rw [ResolvedForestPromoteSupply.selectedOuterRawOf, ResolvedAdmissibleSubgraph.union_elements,
    T.leftOf_alpha_elements_eq_leftResidualTouched z hLeft,
    T.promotedOf_alpha_elements_eq_promotedTouchedUnion M Fstar Measure z hForest hTag]
  ext a
  simp only [Finset.mem_union]
  rw [← M.leftResidual_union_promotedTouched z]
  simp only [Finset.mem_union]

/-- **R-6c-body-490 — the alpha raw-outer identity** (`ext_elements`). -/
theorem multiStar_selectedOuterRawOf_alpha_eq
    (M : ResolvedMultiStarDecontractionSupply D) (Fstar : ResolvedCanonicalStarFacts D)
    (Measure : ResolvedMeasureLeafSupply D) (T : ResolvedRegionTagAlphaValueSupply Fmem V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (hLeft : (T.Closure.Assembly.Left.leftResidual z).elements = leftResidualTouched z)
    (hForest : (T.Closure.Assembly.Region.forestRecovered z).elements
      = (M.forestRecoveredMulti Fstar z).elements)
    (hTag : ∀ (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Closure.unionOuterAlphaValue z).1.elements})
      (hf : γ.1 ∈ (T.Closure.Assembly.Region.forestRecovered z).elements)
      (h' : γ.1 ∈ (M.forestRecoveredMulti Fstar z).elements),
      (ResolvedAdmissibleSubgraph.promote γ.1 (T.forestTag z γ hf).1).elements
        = touchedOuterComponents z (M.forestSource Fstar z ⟨γ.1, h'⟩).1) :
    (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf (T.recoveredPreimageAlphaValue z)
      = z.1.1 :=
  ResolvedAdmissibleSubgraph.ext_elements
    (T.selectedOuterRawOf_alpha_elements_eq M Fstar Measure z hLeft hForest hTag)

end ResolvedRegionTagAlphaValueSupply

/-- **R-6c-body-490 ∎ — the canonical alpha `houter`.**  The alpha raw-outer identity on the body-488 canonical tags, with
`hLeft` / `hForest` `rfl` and `hTag` from `M.promote_forestTag_elements`. -/
theorem canonicalMultiStar_alpha_houter
    {Fmem : ResolvedSelectedOuterFilteredMemSupply canonicalUniqueSupportedCarrierProperSupply.toData}
    (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
    (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
    (OccRaw : ResolvedForestOccurrenceInversionValueSupply ValueGeometry.toCoreBuild.toValueCore)
    (Split : ResolvedAlphaValueQuotientRegionSplitSupply Fmem VBuild.toCanonicalFilteredValue)
    {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G) :
    (resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
        ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z)
      = z.1.1 :=
  (canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).multiStar_selectedOuterRawOf_alpha_eq
    (ValueGeometry.toCoreBuild.toValueCore.toDecontractionSupply
      (canonicalUniqueInnerRawCarrierClosureSupply ValueGeometry.toCoreBuild.toValueCore))
    canonicalUniqueStarFactsOfW' VBuild.Measure z rfl rfl
    (fun γ _ h' =>
      (ValueGeometry.toCoreBuild.toValueCore.toDecontractionSupply
        (canonicalUniqueInnerRawCarrierClosureSupply ValueGeometry.toCoreBuild.toValueCore)).promote_forestTag_elements
        canonicalUniqueStarFactsOfW' z ⟨γ.1, h'⟩)

end GaugeGeometry.QFT.Combinatorial
