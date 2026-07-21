import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCanonicalAlphaWrapper
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarRightBridgeAssembly
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaValueForwardLayer

/-!
# R-6c-body-483 — the alpha right sound/complete bridge (six-bridge assembly, 2/6 closed) (PROVED)

Four-hundred-and-eighty-third genuine-body step — stage 2 of the body-445 migration campaign.  This body closes the RIGHT
two of the six-bridge assembly canonically ON THE ALPHA `V`, touching NO corrected parent geometry — the right pair is
proved from the alpha `V`'s survivor ownership alone (body-368's component section + body-472's alpha region split), with
the survivor-component gate a pure `rfl` for the canonical alpha `VBuild`.

* `ResolvedRightRegionAlphaValueCoreBridgeSupply` — the alpha right bridge (body-278 shape, forward image
  `fwdMapFilteredAlphaValue`);
* `rightReembed_survivorComponent_alpha` — body-368's component section over the alpha forward image (verbatim, the `fwd`
  structure is never read);
* `resolvedMultiStarRightAlphaBridge` — body-369 mirrored: `right_sound_value` / `right_complete_value` from the section +
  `Split.rightDomain_value_mem_alpha`, over `fwdMapFilteredAlphaValue`, NO new geometry;
* `resolvedCanonicalMultiStarRightAlphaBridge` — the canonical alpha `VBuild` specialization (`Core`/`Closure`/`M` from the
  value geometry, `Measure := VBuild.Measure`, `Fstar := canonicalUniqueStarFactsOfW'`, `hSurvivorComponent := rfl`); the
  alpha constructor builds `Survivor` from the SAME `Measure`, so no independent survivor gate is reintroduced;
* `resolvedCanonicalMultiStarRightAlphaBridge_construction` — the body-475 assembly projection anchor (`Construction =
  multiStarRegion M Fstar`, `rfl`): the two fields drop straight into `right_sound_value` / `right_complete_value`;
* `ResolvedRightRegionValueCoreBridgeSupply.toAlpha` — the legacy compatibility adapter over `V.toFiltered` (`rfl`).

Per the HALT/guards: the forest / left bridges are NOT entered; parent reconstruction is NOT entered; the corrected remnant
round-trip is NOT consumed; the alpha closure / tags / round-trip are NOT assembled; NO `StarProm`-style field is added;
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

/-- **R-6c-body-483 — the alpha right region core bridge supply** (body-278 shape, over `fwdMapFilteredAlphaValue`). -/
structure ResolvedRightRegionAlphaValueCoreBridgeSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedFilteredConcreteSummandValueSupply D) where
  /-- The S-free region construction core (body-277). -/
  Construction : ResolvedRegionConstructionFromSectorValueSupply D
  /-- Alpha survivor soundness: `componentToRight` lands in `q`'s right-primitive components. -/
  right_sound_value : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (δ : {x // x ∈ rightDomain (fwdMapFilteredAlphaValue F V q)}),
    rightPrimSelected q.1 (Construction.componentToRight (fwdMapFilteredAlphaValue F V q) δ)
  /-- Alpha survivor completeness: every right-primitive component is a `componentToRight` image. -/
  right_complete_value : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : ResolvedFeynmanSubgraph G),
    rightPrimSelected q.1 γ →
    ∃ δ : {x // x ∈ rightDomain (fwdMapFilteredAlphaValue F V q)},
      Construction.componentToRight (fwdMapFilteredAlphaValue F V q) δ = γ

/-- **R-6c-body-483 — the right-sector component section over the alpha forward image** (body-368 verbatim; the `fwd`
structure is never read, only `δ.1 = survivorComponent`). -/
theorem rightReembed_survivorComponent_alpha (Measure : ResolvedMeasureLeafSupply D)
    {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedFilteredConcreteSummandValueSupply D}
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : {y : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements} //
      y ∈ ResolvedCoassocSplitChoice.rightComponents q.1})
    (δ : {x // x ∈ rightDomain (fwdMapFilteredAlphaValue Fmem V q)})
    (hδ : δ.1 = (survivorSupply_of_measure Measure G).survivorComponent q.1 γ) :
    rightReembed (fwdMapFilteredAlphaValue Fmem V q) δ = γ.1.1 := by
  apply ResolvedFeynmanSubgraph.ext
  · show δ.1.vertices = γ.1.1.vertices
    rw [hδ]; rfl
  · show δ.1.internalEdges = γ.1.1.internalEdges
    rw [hδ]; rfl
  · show δ.1.externalLegs = γ.1.1.externalLegs
    rw [hδ]; rfl

/-- **R-6c-body-483 — the alpha right sound/complete bridge over the multi-star region core** (body-369 mirrored). -/
noncomputable def resolvedMultiStarRightAlphaBridge (M : ResolvedMultiStarDecontractionSupply D)
    (Fstar : ResolvedCanonicalStarFacts D) (Measure : ResolvedMeasureLeafSupply D)
    {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedFilteredConcreteSummandValueSupply D}
    (Split : ResolvedAlphaValueQuotientRegionSplitSupply Fmem V)
    (hSurvivorComponent : ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G)
      (γ : {y : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements} //
        y ∈ ResolvedCoassocSplitChoice.rightComponents s}),
      V.Survivor.survivor.survivorComponent s γ = (survivorSupply_of_measure Measure G).survivorComponent s γ) :
    ResolvedRightRegionAlphaValueCoreBridgeSupply Fmem V where
  Construction := multiStarRegion M Fstar
  right_sound_value := fun {G} q δ => by
    show rightPrimSelected q.1 (rightReembed (fwdMapFilteredAlphaValue Fmem V q) δ)
    have hmem := (Split.rightDomain_value_mem_alpha q δ.1).mp δ.2
    obtain ⟨γ, -, hγeq⟩ := Finset.mem_image.mp hmem
    have hδ : δ.1 = (survivorSupply_of_measure Measure G).survivorComponent q.1 γ := by
      rw [← hγeq]; exact hSurvivorComponent q.1 γ
    rw [rightReembed_survivorComponent_alpha Measure q γ δ hδ]
    exact ⟨γ.1.2, (Finset.mem_filter.mp γ.2).2⟩
  right_complete_value := fun {G} q γ_bare hrp => by
    obtain ⟨hγ, hch⟩ := hrp
    have hmemrc : (⟨γ_bare, hγ⟩ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
        ∈ ResolvedCoassocSplitChoice.rightComponents q.1 :=
      Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hch⟩
    refine ⟨⟨V.Survivor.survivor.survivorComponent q.1 ⟨⟨γ_bare, hγ⟩, hmemrc⟩,
      (Split.rightDomain_value_mem_alpha q _).mpr (Finset.mem_image.mpr
        ⟨⟨⟨γ_bare, hγ⟩, hmemrc⟩, Finset.mem_attach _ _, rfl⟩)⟩, ?_⟩
    show rightReembed (fwdMapFilteredAlphaValue Fmem V q) _ = γ_bare
    exact rightReembed_survivorComponent_alpha Measure q ⟨⟨γ_bare, hγ⟩, hmemrc⟩ _
      (hSurvivorComponent q.1 ⟨⟨γ_bare, hγ⟩, hmemrc⟩)

/-- **R-6c-body-483 — the canonical alpha `VBuild` right bridge specialization.**  `Core` / `Closure` / `M` from the value
geometry; `Measure := VBuild.Measure`; `Fstar := canonicalUniqueStarFactsOfW'`; the survivor gate is `rfl` because the
alpha constructor builds `Survivor` from the SAME `Measure`. -/
noncomputable def resolvedCanonicalMultiStarRightAlphaBridge
    {Fmem : ResolvedSelectedOuterFilteredMemSupply canonicalUniqueSupportedCarrierProperSupply.toData}
    (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
    (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
    (Split : ResolvedAlphaValueQuotientRegionSplitSupply Fmem VBuild.toCanonicalFilteredValue) :
    ResolvedRightRegionAlphaValueCoreBridgeSupply Fmem VBuild.toCanonicalFilteredValue :=
  resolvedMultiStarRightAlphaBridge
    (ValueGeometry.toCoreBuild.toValueCore.toDecontractionSupply
      (canonicalUniqueInnerRawCarrierClosureSupply ValueGeometry.toCoreBuild.toValueCore))
    canonicalUniqueStarFactsOfW' VBuild.Measure Split
    (fun _s _γ => rfl)

/-- **R-6c-body-483 — the body-475 assembly projection anchor** (`rfl`).  The canonical right bridge's `Construction` is
exactly the assembly's `Region := multiStarRegion M Fstar`, so its two fields drop straight into `right_sound_value` /
`right_complete_value`. -/
theorem resolvedCanonicalMultiStarRightAlphaBridge_construction
    {Fmem : ResolvedSelectedOuterFilteredMemSupply canonicalUniqueSupportedCarrierProperSupply.toData}
    (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
    (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
    (Split : ResolvedAlphaValueQuotientRegionSplitSupply Fmem VBuild.toCanonicalFilteredValue) :
    (resolvedCanonicalMultiStarRightAlphaBridge VBuild ValueGeometry Split).Construction
      = multiStarRegion
          (ValueGeometry.toCoreBuild.toValueCore.toDecontractionSupply
            (canonicalUniqueInnerRawCarrierClosureSupply ValueGeometry.toCoreBuild.toValueCore))
          canonicalUniqueStarFactsOfW' :=
  rfl

/-- **R-6c-body-483 — the legacy compatibility adapter.**  An old right bridge (body-278) becomes the alpha right bridge
over `V.toFiltered` (`fwdMapFilteredAlphaValue F V.toFiltered = fwdMapFilteredValue F V`, `rfl`). -/
def ResolvedRightRegionValueCoreBridgeSupply.toAlpha
    {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
    (B : ResolvedRightRegionValueCoreBridgeSupply Fmem V) :
    ResolvedRightRegionAlphaValueCoreBridgeSupply Fmem V.toFiltered where
  Construction := B.Construction
  right_sound_value := B.right_sound_value
  right_complete_value := B.right_complete_value

end GaugeGeometry.QFT.Combinatorial
