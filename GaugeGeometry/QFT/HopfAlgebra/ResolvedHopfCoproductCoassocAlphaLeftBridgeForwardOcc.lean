import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaLeftBridge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaOccurrenceInversionInhabit

/-!
# R-6c-body-504 — alpha LEFT bridge migrated onto the faithful forward socket (PROVED)

Five-hundred-and-fourth genuine-body step — proof-ownership re-plumbing (the mathematics is body-503's).  The body-487
left-bridge consumers are re-issued as `_forwardOcc` PARALLELS driven by body-502/503's faithful socket
`ResolvedForwardForestOccurrenceInversionAlphaValueSupply` instead of the legacy `∀ s` `OccInv`.  The swap is a drop-in:
`M.innerIdx_occurrence OccInv (fwd q) δ q.1 o hp` and `ForwardOcc.occurrence_inner_idx_alpha q δ o hp` have the SAME type
`HEq (M.innerIdx (fwd q) δ) o.B`, so the body-487 proofs port verbatim.

The legacy body-487 declarations stay non-destructively as valid conditionals; these are additive parallels.  The canonical
specialization `resolvedCanonicalMultiStarLeftAlphaBridge_forwardOcc` supplies body-503's canonical `ForwardOcc` (built
from `VBuild` / `ValueGeometry` / `E`), so NO `toForestOccurrenceInversionSupply … OccRaw` and NO legacy `OccRaw` argument.

## Migrated (Step 1.A)

```text
promoted_mem_representedByTouched_alpha_forwardOcc
leftSelected_not_representedByTouched_alpha_forwardOcc
left_sound_alpha_of_multiStar_geometry_forwardOcc
resolvedMultiStarLeftAlphaBridge_forwardOcc
resolvedCanonicalMultiStarLeftAlphaBridge_forwardOcc   (canonical, OccRaw-free)
```

Step 1.B (body-493 forest exact-B), Step 1.C (body-495 remnant correspondence), and Steps 2/3 (faithful Tags / round-trip
/ coassoc wrapper) are the body-505 continuation (per the plan's safe-stop — the LEFT bridge is a self-contained first
slice; the full assembly threading is deferred rather than rushed).

Per the HALT/guards: the legacy `∀ s` `OccRaw` is NOT canonically inhabited; `toForestOccurrenceInversionSupply … OccRaw`
is NOT used in the new path; body-489 is NOT reverse-used for `hidx`; nothing is back-computed from body-492 quotient HEq
or coassoc; corrected permutations are NOT compared; `quot_eq` / `legComplete` are NOT entered; the old body-487/495
theorems stay valid conditionals (NON-destructive); strict `StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc
claim.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

variable {D : ResolvedCoproductProperForestData}

namespace ResolvedMultiStarDecontractionSupply

variable (M : ResolvedMultiStarDecontractionSupply D)
  {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedFilteredConcreteSummandValueSupply D}

/-- **R-6c-body-504 — `promoted_mem_representedByTouched`, on the faithful socket** (body-487 mirror, `ForwardOcc` drives
the exact-B). -/
theorem promoted_mem_representedByTouched_alpha_forwardOcc
    (ForwardOcc : ResolvedForwardForestOccurrenceInversionAlphaValueSupply M Fmem V)
    (Split : ResolvedAlphaValueQuotientRegionSplitSupply Fmem V)
    (parent_remnantComponent : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
      (δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem V q)}),
      HEq (V.Remnant.remnant.remnantComponent q.1 o) δ.1 →
      M.parent (fwdMapFilteredAlphaValue Fmem V q) δ = o.γ.1)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γc : ResolvedFeynmanSubgraph G) (hmem : γc ∈ ResolvedCoassocSplitChoice.promotedElements q.1) :
    representedByTouched (fwdMapFilteredAlphaValue Fmem V q) γc := by
  obtain ⟨η, hη⟩ := ResolvedCoassocSplitChoice.mem_promotedElements hmem
  rcases hc : ResolvedCoassocSplitChoice.choiceAt q.1 η with b | Bη
  · rw [ResolvedCoassocSplitChoice.promotedComponentElements, hc] at hη
    exact absurd hη (by simp)
  · rw [ResolvedCoassocSplitChoice.promotedComponentElements_inr q.1 hc] at hη
    have hfc : η ∈ ResolvedCoassocSplitChoice.forestComponents q.1 :=
      Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, ⟨Bη, hc⟩⟩
    set o := ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 ⟨η, hfc⟩ with ho
    have hoB : o.B = Bη := Sum.inr.inj (o.hchoice.symm.trans hc)
    have hδmem : V.Remnant.remnant.remnantComponent q.1 o
        ∈ (V.Remnant.remnant.remnantForest q.1).elements :=
      Finset.mem_image.mpr ⟨⟨η, hfc⟩, Finset.mem_attach _ _, rfl⟩
    set δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem V q)} :=
      ⟨V.Remnant.remnant.remnantComponent q.1 o, (Split.forestDomain_value_mem_alpha q _).mpr hδmem⟩ with hδ
    have hp : M.parent (fwdMapFilteredAlphaValue Fmem V q) δ = o.γ.1 :=
      parent_remnantComponent q o δ HEq.rfl
    have hi : HEq (M.innerIdx (fwdMapFilteredAlphaValue Fmem V q) δ) o.B :=
      ForwardOcc.occurrence_inner_idx_alpha q δ o hp
    refine ⟨δ.1, δ.2, ?_⟩
    rw [← promote_innerRaw_elements (fwdMapFilteredAlphaValue Fmem V q) δ.1
      (M.legLift (fwdMapFilteredAlphaValue Fmem V q) δ) (M.hE (fwdMapFilteredAlphaValue Fmem V q))
      (M.hL (fwdMapFilteredAlphaValue Fmem V q))]
    show γc ∈ (ResolvedAdmissibleSubgraph.promote (M.parent (fwdMapFilteredAlphaValue Fmem V q) δ)
      (M.innerIdx (fwdMapFilteredAlphaValue Fmem V q) δ).1).elements
    rw [promote_elements_congr hp (M.innerIdx (fwdMapFilteredAlphaValue Fmem V q) δ) o.B hi, hoB]
    exact hη

/-- **R-6c-body-504 — `leftSelected_not_representedByTouched`, on the faithful socket** (body-487 mirror). -/
theorem leftSelected_not_representedByTouched_alpha_forwardOcc
    (ForwardOcc : ResolvedForwardForestOccurrenceInversionAlphaValueSupply M Fmem V)
    (Measure : ResolvedMeasureLeafSupply D)
    (Split : ResolvedAlphaValueQuotientRegionSplitSupply Fmem V)
    (parent_remnantComponent : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
      (δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem V q)}),
      HEq (V.Remnant.remnant.remnantComponent q.1 o) δ.1 →
      M.parent (fwdMapFilteredAlphaValue Fmem V q) δ = o.γ.1)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) (γ : ResolvedFeynmanSubgraph G)
    (hls : ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 γ) :
    ¬ representedByTouched (fwdMapFilteredAlphaValue Fmem V q) γ := by
  rintro ⟨δ, hδ, hγt⟩
  obtain ⟨γ_fc, -, hoeq⟩ := Finset.mem_image.mp ((Split.forestDomain_value_mem_alpha q δ).mp hδ)
  set δs : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem V q)} := ⟨δ, hδ⟩ with hδs
  set o := ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 γ_fc with ho
  have hp : M.parent (fwdMapFilteredAlphaValue Fmem V q) δs = o.γ.1 :=
    parent_remnantComponent q o δs (heq_of_eq hoeq)
  have hi : HEq (M.innerIdx (fwdMapFilteredAlphaValue Fmem V q) δs) o.B :=
    ForwardOcc.occurrence_inner_idx_alpha q δs o hp
  have hγt2 : γ ∈ ResolvedCoassocSplitChoice.promotedComponentElements q.1 o.γ := by
    rw [ResolvedCoassocSplitChoice.promotedComponentElements_inr q.1 o.hchoice,
      ← promote_elements_congr hp (M.innerIdx (fwdMapFilteredAlphaValue Fmem V q) δs) o.B hi]
    show γ ∈ (ResolvedAdmissibleSubgraph.promote
      (localizedParentWithTouchedLegs (fwdMapFilteredAlphaValue Fmem V q) δs.1
        (M.legLift (fwdMapFilteredAlphaValue Fmem V q) δs) (M.hE (fwdMapFilteredAlphaValue Fmem V q))
        (M.hL (fwdMapFilteredAlphaValue Fmem V q)))
      (innerRaw (fwdMapFilteredAlphaValue Fmem V q) δs.1
        (M.legLift (fwdMapFilteredAlphaValue Fmem V q) δs) (M.hE (fwdMapFilteredAlphaValue Fmem V q))
        (M.hL (fwdMapFilteredAlphaValue Fmem V q)))).elements
    rw [promote_innerRaw_elements (fwdMapFilteredAlphaValue Fmem V q) δs.1
      (M.legLift (fwdMapFilteredAlphaValue Fmem V q) δs) (M.hE (fwdMapFilteredAlphaValue Fmem V q))
      (M.hL (fwdMapFilteredAlphaValue Fmem V q))]
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

/-- **R-6c-body-504 — the SOUND direction, on the faithful socket** (body-487 mirror). -/
theorem left_sound_alpha_of_multiStar_geometry_forwardOcc
    (ForwardOcc : ResolvedForwardForestOccurrenceInversionAlphaValueSupply M Fmem V)
    (Measure : ResolvedMeasureLeafSupply D)
    (Split : ResolvedAlphaValueQuotientRegionSplitSupply Fmem V)
    (parent_remnantComponent : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
      (δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem V q)}),
      HEq (V.Remnant.remnant.remnantComponent q.1 o) δ.1 →
      M.parent (fwdMapFilteredAlphaValue Fmem V q) δ = o.γ.1)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) (γ : ResolvedFeynmanSubgraph G)
    (hls : ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 γ) :
    γ ∈ (multiStarLeft.leftResidual (fwdMapFilteredAlphaValue Fmem V q)).elements := by
  rw [multiStarLeft, ResolvedLeftResidualConstructionValueSupply.leftResidual_elements_eq,
    Finset.mem_filter]
  refine ⟨?_, M.leftSelected_not_representedByTouched_alpha_forwardOcc ForwardOcc Measure Split
    parent_remnantComponent q γ hls⟩
  have hleft : γ ∈ ((resolvedConcreteForestPromoteSupply D G).leftOf q.1).elements := by
    show γ ∈ q.1.1.1.elements.filter (ResolvedCoassocSplitChoice.leftSelectedConcrete q.1)
    exact Finset.mem_filter.mpr ⟨hls.choose, hls⟩
  exact (@Finset.mem_union _ (Classical.decEq _) _ _ _).mpr (Or.inl hleft)

/-- **R-6c-body-504 — the alpha LEFT sound/complete bridge, on the faithful socket** (body-487 mirror). -/
noncomputable def resolvedMultiStarLeftAlphaBridge_forwardOcc
    (ForwardOcc : ResolvedForwardForestOccurrenceInversionAlphaValueSupply M Fmem V)
    (Measure : ResolvedMeasureLeafSupply D)
    (Split : ResolvedAlphaValueQuotientRegionSplitSupply Fmem V)
    (parent_remnantComponent : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
      (δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem V q)}),
      HEq (V.Remnant.remnant.remnantComponent q.1 o) δ.1 →
      M.parent (fwdMapFilteredAlphaValue Fmem V q) δ = o.γ.1) :
    ResolvedLeftResidualAlphaValueCoreBridgeSupply Fmem V where
  Construction := multiStarLeft
  left_sound_value := fun {_G} q γ hls =>
    M.left_sound_alpha_of_multiStar_geometry_forwardOcc ForwardOcc Measure Split parent_remnantComponent q γ hls
  left_complete_value := fun {G} q γ hlr => by
    rw [multiStarLeft, ResolvedLeftResidualConstructionValueSupply.leftResidual_elements_eq,
      Finset.mem_filter] at hlr
    obtain ⟨hmemO, hnr⟩ := hlr
    rcases (@Finset.mem_union _ (Classical.decEq _) _ _ _).mp hmemO with hleft | hprom
    · exact leftSelectedConcrete_of_mem_leftOf q.1 γ hleft
    · exact absurd (M.promoted_mem_representedByTouched_alpha_forwardOcc ForwardOcc Split
        parent_remnantComponent q γ hprom) hnr

end ResolvedMultiStarDecontractionSupply

/-- **R-6c-body-504 ∎ — the canonical alpha LEFT bridge, OccRaw-FREE.**  body-503's canonical faithful `ForwardOcc`
replaces the legacy `toForestOccurrenceInversionSupply … OccRaw`; no `OccRaw` argument. -/
noncomputable def resolvedCanonicalMultiStarLeftAlphaBridge_forwardOcc
    (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
    (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    (Split : ResolvedAlphaValueQuotientRegionSplitSupply
      (canonicalUniqueSelectedOuterFilteredMemSupply_of_measure VBuild.Measure E)
      VBuild.toCanonicalFilteredValue) :
    ResolvedLeftResidualAlphaValueCoreBridgeSupply
      (canonicalUniqueSelectedOuterFilteredMemSupply_of_measure VBuild.Measure E)
      VBuild.toCanonicalFilteredValue :=
  (ValueGeometry.toCoreBuild.toValueCore.toDecontractionSupply
      (canonicalUniqueInnerRawCarrierClosureSupply
        ValueGeometry.toCoreBuild.toValueCore)).resolvedMultiStarLeftAlphaBridge_forwardOcc
    (canonicalForwardForestOccurrenceInversionAlphaValueSupply VBuild ValueGeometry E)
    VBuild.Measure Split
    (fun q o δ hδ =>
      (canonicalParentRemnantSectionAlphaValue VBuild ValueGeometry).parent_remnantComponent q o δ hδ)

end GaugeGeometry.QFT.Combinatorial
