import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarRightBridge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarRegionTagValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionValueCoreBridge

/-!
# R-6c-body-369 — Front-3 bank-2: the right sound/complete bridge + survivor-forest wiring (PROVED)

Three-hundred-and-sixty-ninth genuine-body step — the right sound/complete bridge, DERIVED (not re-fielded) from
body-368's component section + body-274's forward-image set correspondence, with a single pointwise gate
`hSurvivorComponent` (the survivor component wiring, `rfl` for a concrete `V`).  The same gate banks body-360's
survivor-forest collection wiring (`image_congr`), so `hSurvivor` never remains a separate obligation.

* `rightSurvivorForest_wiring` — `(V.Survivor.survivor.rightSurvivorForest s).elements = ((measure).rightSurvivorForest s).elements`;
* `resolvedMultiStarRightBridge` — `ResolvedRightRegionValueCoreBridgeSupply F V`, `Construction := multiStarRegion`,
  `right_sound_value` / `right_complete_value` both from body-368 + body-274.

Per the HALT: only the right pair + its wiring is banked; body-345/347's recovered-only results are NOT used; no `T` /
cover / `hround` / carrier; sound/complete are DERIVED from the one section; no `V` equality beyond the pointwise
`survivorComponent` wiring.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` /
singleton / floor-297.
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

/-- **R-6c-body-369 — survivor-forest collection wiring** (body-360's `hSurvivor`, from the pointwise gate). -/
theorem rightSurvivorForest_wiring (Measure : ResolvedMeasureLeafSupply D)
    {V : ResolvedConcreteSummandValueSupply D}
    (hSurvivorComponent : ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G)
      (γ : {y : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements} //
        y ∈ ResolvedCoassocSplitChoice.rightComponents s}),
      V.Survivor.survivor.survivorComponent s γ = (survivorSupply_of_measure Measure G).survivorComponent s γ)
    {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G) :
    (V.Survivor.survivor.rightSurvivorForest s).elements
      = ((survivorSupply_of_measure Measure G).rightSurvivorForest s).elements :=
  Finset.image_congr (fun γ _ => hSurvivorComponent s γ)

/-- **R-6c-body-369 — the right sound/complete bridge over the multi-star region core.** -/
noncomputable def resolvedMultiStarRightBridge (M : ResolvedMultiStarDecontractionSupply D)
    (Fstar : ResolvedCanonicalStarFacts D) (Measure : ResolvedMeasureLeafSupply D)
    {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
    (P : ResolvedValueQuotientRegionSplitSupply Fmem V)
    (hSurvivorComponent : ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G)
      (γ : {y : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements} //
        y ∈ ResolvedCoassocSplitChoice.rightComponents s}),
      V.Survivor.survivor.survivorComponent s γ = (survivorSupply_of_measure Measure G).survivorComponent s γ) :
    ResolvedRightRegionValueCoreBridgeSupply Fmem V where
  Construction := multiStarRegion M Fstar
  right_sound_value := fun {G} q δ => by
    show rightPrimSelected q.1 (rightReembed (fwdMapFilteredValue Fmem V q) δ)
    have hmem := (P.rightDomain_value_mem q δ.1).mp δ.2
    obtain ⟨γ, -, hγeq⟩ := Finset.mem_image.mp hmem
    have hδ : δ.1 = (survivorSupply_of_measure Measure G).survivorComponent q.1 γ := by
      rw [← hγeq]; exact hSurvivorComponent q.1 γ
    rw [rightReembed_survivorComponent Measure q γ δ hδ]
    exact ⟨γ.1.2, (Finset.mem_filter.mp γ.2).2⟩
  right_complete_value := fun {G} q γ_bare hrp => by
    obtain ⟨hγ, hch⟩ := hrp
    have hmemrc : (⟨γ_bare, hγ⟩ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
        ∈ ResolvedCoassocSplitChoice.rightComponents q.1 :=
      Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hch⟩
    refine ⟨⟨V.Survivor.survivor.survivorComponent q.1 ⟨⟨γ_bare, hγ⟩, hmemrc⟩,
      (P.rightDomain_value_mem q _).mpr (Finset.mem_image.mpr
        ⟨⟨⟨γ_bare, hγ⟩, hmemrc⟩, Finset.mem_attach _ _, rfl⟩)⟩, ?_⟩
    show rightReembed (fwdMapFilteredValue Fmem V q) _ = γ_bare
    exact rightReembed_survivorComponent Measure q ⟨⟨γ_bare, hγ⟩, hmemrc⟩ _
      (hSurvivorComponent q.1 ⟨⟨γ_bare, hγ⟩, hmemrc⟩)

end GaugeGeometry.QFT.Combinatorial
