import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarRegionTagValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestBridgeConstructionAudit
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionValueCoreBridge

/-!
# R-6c-body-370 — Front-3 bank-2: the forest sound/complete bridge, reduced to the parent-recovery datum (PROVED)

Three-hundred-and-seventieth genuine-body step — the forest bridge.  Unlike the right sector (body-368, where the
`survivorReembed`/`rightReembed` round-trip was `rfl`), the forest sector's `componentToForest := M.parent` is a
DE-CONTRACTION, and its `externalLegs := datum.legs` are the generic occurrence-faithful `legLift` preimage — NOT pinned
to the occurrence's own outer component.

**Audit verdict.**  `M.parent (remnantComponent o) = o.γ.1` (the parent-recovery section) is NOT derivable from
`V.Remnant.remnantInj` (which only gives occurrence-parent uniqueness, not the identity) nor from body-358 (the reverse
`remnantComponent (parent δ, innerIdx δ) = δ`) nor body-343 (which PRESUMES `hparent`) nor `forestSource` (which presumes
`γ` is already a parent image — circular).  Body-305's "`remnantInj` forces it" verdict was for the OLD parent-inverse
`componentToForest`; the multi-star `M.parent` de-contraction needs a genuine `legLift`-occurrence leg coherence.  So
`parent_remnantComponent` is an HONEST model datum (the forward-image de-contraction section), taken as an explicit
gate here — NOT assumed inside a supply.

Both bridge directions reduce to that ONE datum, via body-274's `forestDomain_value_mem` + body-305's
`forestChoiceSelected_of_occurrence`:

* `resolvedMultiStarForestBridge` — `ResolvedForestRegionValueCoreBridgeSupply F V`, `Construction := multiStarRegion`,
  `forest_sound_value` / `forest_complete_value` both from `parent_remnantComponent` + body-274 + body-305.

Per the HALT: sound/complete are reduced to the one parent-recovery datum; the datum is DECLARED honest (not proved from
`remnantInj`); no forest supply is filled with an unjustified assumption; body-345/347 recovered-only results are NOT
used; no `T` / cover / `hround` / carrier; the LEFT bridge is next.  No facade, no flat term, no `forgetHopf`, no
rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-370 — the forest sound/complete bridge over the multi-star region core**, reduced to the honest
parent-recovery datum `parent_remnantComponent`. -/
noncomputable def resolvedMultiStarForestBridge (M : ResolvedMultiStarDecontractionSupply D)
    (Fstar : ResolvedCanonicalStarFacts D)
    {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
    (P : ResolvedValueQuotientRegionSplitSupply Fmem V)
    (parent_remnantComponent : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
      (δ : {x // x ∈ forestDomain (fwdMapFilteredValue Fmem V q)}),
      HEq (V.Remnant.remnant.remnantComponent q.1 o) δ.1 →
      M.parent (fwdMapFilteredValue Fmem V q) δ = o.γ.1) :
    ResolvedForestRegionValueCoreBridgeSupply Fmem V where
  Construction := multiStarRegion M Fstar
  forest_sound_value := fun {G} q δ => by
    show forestChoiceSelected q.1 (M.parent (fwdMapFilteredValue Fmem V q) δ)
    have hmem := (P.forestDomain_value_mem q δ.1).mp δ.2
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
      (P.forestDomain_value_mem q _).mpr (Finset.mem_image.mpr
        ⟨⟨⟨γ_bare, hγ⟩, hmemfc⟩, Finset.mem_attach _ _, rfl⟩)⟩, ?_⟩
    show M.parent (fwdMapFilteredValue Fmem V q) _ = γ_bare
    exact parent_remnantComponent q (ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 ⟨⟨γ_bare, hγ⟩, hmemfc⟩) _ HEq.rfl

end GaugeGeometry.QFT.Combinatorial
