import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaParentSection
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarForestBridge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaValueForwardLayer

/-!
# R-6c-body-486 — the alpha forest sound/complete bridge (six-bridge assembly, 4/6 closed) (PROVED)

Four-hundred-and-eighty-sixth genuine-body step — stage 3 of the body-445 migration campaign.  With the corrected parent
section complete (body-485), the forest sound/complete bridge is a COMPLETE pure-assembly mirror of body-370 — no strict
`StarProm`, no `Wiring`, no `Concrete` family, not even `OccRaw`.  The parent-recovery datum is body-485's derived section,
which reads only the alpha `V`'s corrected remnant.

* `ResolvedForestRegionAlphaValueCoreBridgeSupply` — the alpha forest bridge (body-278 shape, forward image
  `fwdMapFilteredAlphaValue`);
* `forestRecovered_forward_alpha_membership` — the sound/complete pair as a membership iff;
* `resolvedMultiStarForestAlphaBridge` — body-370 mirrored: `forest_sound_value` / `forest_complete_value` from the raw
  parent datum + `Split.forestDomain_value_mem_alpha`, over `fwdMapFilteredAlphaValue`, NO new geometry;
* `resolvedCanonicalMultiStarForestAlphaBridge` — the canonical alpha `VBuild` specialization (`Core` / `Closure` / `M`
  from the value geometry, `Parent := canonicalParentRemnantSectionAlphaValue` (body-485), `Fstar :=
  canonicalUniqueStarFactsOfW'`); `StarProm` / `Wiring` / `Concrete` / `Ids` are NOT returned to the caller (`Ids` was
  already discharged from `W'` inside the body-485 parent theorem);
* `resolvedCanonicalMultiStarForestAlphaBridge_construction` — the body-475 assembly projection anchor (`Construction =
  multiStarRegion M Fstar`, `rfl`): the two fields drop straight into `forest_sound_value` / `forest_complete_value`.

Per the HALT/guards: the left bridge is NOT entered; `OccRaw` is NOT consumed; the whole alpha assembly is NOT built; the
tags / closure / round-trip are NOT constructed; the corrected round-trip (body-461) is NOT mixed in; strict `StarProm` /
`InnerStarRaw` / `Wiring` NOT restored; body-445 stays a valid conditional.  NOT the unconditional theorem.  No facade, no
flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-486 — the alpha forest region core bridge supply** (body-278 shape, over `fwdMapFilteredAlphaValue`). -/
structure ResolvedForestRegionAlphaValueCoreBridgeSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedFilteredConcreteSummandValueSupply D) where
  /-- The S-free region construction core (body-277). -/
  Construction : ResolvedRegionConstructionFromSectorValueSupply D
  /-- Alpha remnant soundness: `componentToForest` lands in `q`'s forest-choice components. -/
  forest_sound_value : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue F V q)}),
    forestChoiceSelected q.1 (Construction.componentToForest (fwdMapFilteredAlphaValue F V q) δ)
  /-- Alpha remnant completeness: every forest-choice component is a `componentToForest` image. -/
  forest_complete_value : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : ResolvedFeynmanSubgraph G),
    forestChoiceSelected q.1 γ →
    ∃ δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue F V q)},
      Construction.componentToForest (fwdMapFilteredAlphaValue F V q) δ = γ

/-- **R-6c-body-486 — the alpha forest region membership bridge** (body-278 shape, `⟨sound, complete⟩` via image). -/
theorem ResolvedForestRegionAlphaValueCoreBridgeSupply.forestRecovered_forward_alpha_membership
    {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedFilteredConcreteSummandValueSupply D}
    (B : ResolvedForestRegionAlphaValueCoreBridgeSupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) (γ : ResolvedFeynmanSubgraph G) :
    γ ∈ (B.Construction.forestRecovered (fwdMapFilteredAlphaValue F V q)).elements
      ↔ forestChoiceSelected q.1 γ := by
  rw [ResolvedRegionConstructionFromSectorValueSupply.forestRecovered_elements_eq]
  constructor
  · intro h
    obtain ⟨δ, _, rfl⟩ := Finset.mem_image.mp h
    exact B.forest_sound_value q δ
  · intro hγ
    obtain ⟨δ, hδ⟩ := B.forest_complete_value q γ hγ
    exact Finset.mem_image.mpr ⟨δ, Finset.mem_attach _ _, hδ⟩

/-- **R-6c-body-486 — the alpha forest sound/complete bridge over the multi-star region core** (body-370 mirrored).  The
`parent_remnantComponent` datum is the raw parent-recovery function (body-485 supplies it canonically). -/
noncomputable def resolvedMultiStarForestAlphaBridge (M : ResolvedMultiStarDecontractionSupply D)
    (Fstar : ResolvedCanonicalStarFacts D)
    {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedFilteredConcreteSummandValueSupply D}
    (Split : ResolvedAlphaValueQuotientRegionSplitSupply Fmem V)
    (parent_remnantComponent : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
      (δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem V q)}),
      HEq (V.Remnant.remnant.remnantComponent q.1 o) δ.1 →
      M.parent (fwdMapFilteredAlphaValue Fmem V q) δ = o.γ.1) :
    ResolvedForestRegionAlphaValueCoreBridgeSupply Fmem V where
  Construction := multiStarRegion M Fstar
  forest_sound_value := fun {G} q δ => by
    show forestChoiceSelected q.1 (M.parent (fwdMapFilteredAlphaValue Fmem V q) δ)
    have hmem := (Split.forestDomain_value_mem_alpha q δ.1).mp δ.2
    obtain ⟨γ, -, hγeq⟩ := Finset.mem_image.mp hmem
    rw [parent_remnantComponent q (ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 γ) δ (heq_of_eq hγeq)]
    exact forestChoiceSelected_of_occurrence q.1 (ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 γ)
  forest_complete_value := fun {G} q γ_bare hfc => by
    obtain ⟨hγ, B, hch⟩ := hfc
    have hmemfc : (⟨γ_bare, hγ⟩ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
        ∈ ResolvedCoassocSplitChoice.forestComponents q.1 :=
      Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, ⟨B, hch⟩⟩
    refine ⟨⟨V.Remnant.remnant.remnantComponent q.1
      (ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 ⟨⟨γ_bare, hγ⟩, hmemfc⟩),
      (Split.forestDomain_value_mem_alpha q _).mpr (Finset.mem_image.mpr
        ⟨⟨⟨γ_bare, hγ⟩, hmemfc⟩, Finset.mem_attach _ _, rfl⟩)⟩, ?_⟩
    show M.parent (fwdMapFilteredAlphaValue Fmem V q) _ = γ_bare
    exact parent_remnantComponent q
      (ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 ⟨⟨γ_bare, hγ⟩, hmemfc⟩) _ HEq.rfl

/-- **R-6c-body-486 — the canonical alpha `VBuild` forest bridge specialization.**  `Core` / `Closure` / `M` from the value
geometry; `Parent := canonicalParentRemnantSectionAlphaValue` (body-485); `Fstar := canonicalUniqueStarFactsOfW'`.  No
`StarProm` / `Wiring` / `Concrete` / `Ids` returned to the caller. -/
noncomputable def resolvedCanonicalMultiStarForestAlphaBridge
    {Fmem : ResolvedSelectedOuterFilteredMemSupply canonicalUniqueSupportedCarrierProperSupply.toData}
    (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
    (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
    (Split : ResolvedAlphaValueQuotientRegionSplitSupply Fmem VBuild.toCanonicalFilteredValue) :
    ResolvedForestRegionAlphaValueCoreBridgeSupply Fmem VBuild.toCanonicalFilteredValue :=
  resolvedMultiStarForestAlphaBridge
    (ValueGeometry.toCoreBuild.toValueCore.toDecontractionSupply
      (canonicalUniqueInnerRawCarrierClosureSupply ValueGeometry.toCoreBuild.toValueCore))
    canonicalUniqueStarFactsOfW' Split
    (fun q o δ hδ =>
      (canonicalParentRemnantSectionAlphaValue VBuild ValueGeometry).parent_remnantComponent q o δ hδ)

/-- **R-6c-body-486 — the body-475 assembly projection anchor** (`rfl`).  The canonical forest bridge's `Construction` is
exactly the assembly's `Region := multiStarRegion M Fstar`, so its two fields drop straight into `forest_sound_value` /
`forest_complete_value`. -/
theorem resolvedCanonicalMultiStarForestAlphaBridge_construction
    {Fmem : ResolvedSelectedOuterFilteredMemSupply canonicalUniqueSupportedCarrierProperSupply.toData}
    (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
    (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
    (Split : ResolvedAlphaValueQuotientRegionSplitSupply Fmem VBuild.toCanonicalFilteredValue) :
    (resolvedCanonicalMultiStarForestAlphaBridge VBuild ValueGeometry Split).Construction
      = multiStarRegion
          (ValueGeometry.toCoreBuild.toValueCore.toDecontractionSupply
            (canonicalUniqueInnerRawCarrierClosureSupply ValueGeometry.toCoreBuild.toValueCore))
          canonicalUniqueStarFactsOfW' :=
  rfl

end GaugeGeometry.QFT.Combinatorial
