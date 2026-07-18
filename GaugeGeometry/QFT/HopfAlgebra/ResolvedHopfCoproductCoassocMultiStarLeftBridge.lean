import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarPromotedRepresented
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftResidualImageTagAudit
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftResidualValueBridge

/-!
# R-6c-body-372 — Front-3 bank-2: the multi-star LEFT sound/complete bridge (PROVED) — bank-2 sealed

Three-hundred-and-seventy-second genuine-body step — the LEFT bridge, closing the six forward-map bridges of the
multi-star `T` construction.  The COMPLETE direction is fully proved from body-371's `promoted_mem_representedByTouched`
(the promoted case contradicts the `leftResidual` filter) + the definitional `leftSelectedConcrete_of_mem_leftOf` (the
`leftOf` case); the SOUND direction is the honest gate `hLeftSound` (`leftSelectedConcrete → γ ∈ leftResidual`,
decomposing to `γ ∈ leftOf ⊆ selectedOuterRaw` + `leftSelected_not_representedByTouched` — the latter provable from
`cd_nonempty` + `pairwiseDisjoint` + the `inl true`/`inr B` choice split; kept as one gate here, NOT `OccInv`-consuming).

* `resolvedMultiStarLeftBridge` — `ResolvedLeftResidualValueCoreBridgeSupply F V`, `Construction := multiStarLeft`.

Per the HALT: the LEFT pair is banked, sealing bank-2's six bridges; `complete` consumes body-371 (hence indirectly
`OccInv`); `sound` consumes only `leftSelected_not_representedByTouched`; the right bridge is NOT needed; no `T` / cover
/ carrier / forward round-trip.  The `selectedOuterRaw = leftOf ∪ promotedOf` split uses `Finset.mem_union` on the
goal-side instance (DecidableEq diamond).  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
`promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-372 — the multi-star LEFT sound/complete bridge**, sealing bank-2's six forward-map bridges. -/
noncomputable def resolvedMultiStarLeftBridge (OccInv : ResolvedForestOccurrenceInversionSupply M)
    (P : ResolvedValueQuotientRegionSplitSupply Fmem V)
    (parent_remnantComponent : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
      (δ : {x // x ∈ forestDomain (fwdMapFilteredValue Fmem V q)}),
      HEq (V.Remnant.remnant.remnantComponent q.1 o) δ.1 →
      M.parent (fwdMapFilteredValue Fmem V q) δ = o.γ.1)
    (hLeftSound : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (γ : ResolvedFeynmanSubgraph G), ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 γ →
      γ ∈ (multiStarLeft.leftResidual (fwdMapFilteredValue Fmem V q)).elements) :
    ResolvedLeftResidualValueCoreBridgeSupply Fmem V where
  Construction := multiStarLeft
  left_sound_value := fun {G} q γ hls => hLeftSound q γ hls
  left_complete_value := fun {G} q γ hlr => by
    rw [multiStarLeft, ResolvedLeftResidualConstructionValueSupply.leftResidual_elements_eq,
      Finset.mem_filter] at hlr
    obtain ⟨hmemO, hnr⟩ := hlr
    rcases (@Finset.mem_union _ (Classical.decEq _) _ _ _).mp hmemO with hleft | hprom
    · exact leftSelectedConcrete_of_mem_leftOf q.1 γ hleft
    · exact absurd (M.promoted_mem_representedByTouched OccInv P parent_remnantComponent q γ hprom) hnr

end ResolvedMultiStarDecontractionSupply

end GaugeGeometry.QFT.Combinatorial
