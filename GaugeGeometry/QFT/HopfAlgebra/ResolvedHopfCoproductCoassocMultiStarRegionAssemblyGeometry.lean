import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftBridgeGeometry
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarRightBridgeAssembly
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarRegionTagValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredRegionValueAssembly

/-!
# R-6c-body-392 — bank-3b: the six-bridge multi-star region assembly + the body-341 Tags wiring (PROVED)

Three-hundred-and-ninety-second genuine-body step — the assembly that bundles the right (369), forest (390-derived), and
left (391-derived) bridges into the single body-280 `ResolvedRecoveredRegionValueBridgeAssemblySupply`, then wires its
six sound/complete projections straight into body-341's `multiStarRegionTagValueSupply` Tags socket.  No new record: the
three `Construction`s all agree by `defeq` (`multiStarRegion M Fstar` for right/forest, `multiStarLeft` for left).

* `resolvedMultiStarRegionBridgeAssembly` — the six-bridge assembly over the value core;
* `multiStarRegionTagValueSupplyOfGeometry` — body-341's region-tag supply, its six leaves discharged by the assembly;
* `multiStar_selectedOuterRawOf_eq_of_geometry` — body-341's `houter` (`selectedOuterRawOf(recovered) = z.1.1`) fed the
  assembly's six projections.

Per the HALT: the six sound/complete fields leave the residual; `hSurvivorComponent` is the shared right-bridge /
quotient-wiring model gate; `OccRaw` and cross-ambient `StarProm` are the remaining honest geometry; `rrm`
(`recovered_raw_mem`) stays the ONE unresolved carrier-closure obligation; NO new geometry, transport, or parent gate.
So body-341's "six bridges + `recovered_raw_mem`" shrinks to `recovered_raw_mem` alone.  No facade, no flat term, no
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

variable {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
  {Concrete : ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G),
    ResolvedConcreteRemnantReembedSupply D G s}

/-- **R-6c-body-392 — the six-bridge multi-star region assembly.**  Right (369) + forest (390) + left (391) bundled into
the body-280 assembly record; the three constructions agree by `defeq`. -/
noncomputable def resolvedMultiStarRegionBridgeAssembly
    (Core : ResolvedMultiStarDecontractionValueCoreSupply D)
    (Closure : ResolvedMultiStarInnerRawCarrierClosureSupply Core)
    (CarrierProper : ResolvedCarrierProperProvider D)
    (Ids : ResolvedFilteredForestBlockUniqueIdSupply D)
    (Fstar : ResolvedCanonicalStarFacts D)
    (StarProm : ResolvedPromotedStarCoherenceValueSupply Fmem V)
    (Wiring : ResolvedRemnantComponentValueWiringSupply V Concrete)
    (OccRaw : ResolvedForestOccurrenceInversionValueSupply Core)
    (Measure : ResolvedMeasureLeafSupply D)
    (Split : ResolvedValueQuotientRegionSplitSupply Fmem V)
    (hSurvivorComponent : ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G)
      (γ : {y : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements} //
        y ∈ ResolvedCoassocSplitChoice.rightComponents s}),
      V.Survivor.survivor.survivorComponent s γ = (survivorSupply_of_measure Measure G).survivorComponent s γ) :
    ResolvedRecoveredRegionValueBridgeAssemblySupply Fmem V :=
  let M := Core.toDecontractionSupply Closure
  let RightB := resolvedMultiStarRightBridge M Fstar Measure Split hSurvivorComponent
  let ForestB := resolvedMultiStarForestBridgeOfGeometry Core Closure CarrierProper Ids Fstar StarProm Wiring Split
  let LeftB := resolvedMultiStarLeftBridgeOfValueGeometry Core Closure CarrierProper Ids Fstar StarProm Wiring
    OccRaw Measure Split
  { Region := multiStarRegion M Fstar
    Left := multiStarLeft
    right_sound_value := RightB.right_sound_value
    right_complete_value := RightB.right_complete_value
    forest_sound_value := ForestB.forest_sound_value
    forest_complete_value := ForestB.forest_complete_value
    left_sound_value := LeftB.left_sound_value
    left_complete_value := LeftB.left_complete_value }

/-- **R-6c-body-392 — body-341's region-tag supply, six leaves discharged by the assembly.** -/
noncomputable def multiStarRegionTagValueSupplyOfGeometry
    (Core : ResolvedMultiStarDecontractionValueCoreSupply D)
    (Closure : ResolvedMultiStarInnerRawCarrierClosureSupply Core)
    (CarrierProper : ResolvedCarrierProperProvider D)
    (Ids : ResolvedFilteredForestBlockUniqueIdSupply D)
    (Fstar : ResolvedCanonicalStarFacts D)
    (StarProm : ResolvedPromotedStarCoherenceValueSupply Fmem V)
    (Wiring : ResolvedRemnantComponentValueWiringSupply V Concrete)
    (OccRaw : ResolvedForestOccurrenceInversionValueSupply Core)
    (Measure : ResolvedMeasureLeafSupply D)
    (Split : ResolvedValueQuotientRegionSplitSupply Fmem V)
    (hSurvivorComponent : ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G)
      (γ : {y : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements} //
        y ∈ ResolvedCoassocSplitChoice.rightComponents s}),
      V.Survivor.survivor.survivorComponent s γ = (survivorSupply_of_measure Measure G).survivorComponent s γ)
    (rrm : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      regionRawUnion (Core.toDecontractionSupply Closure) Fstar z ∈ D.carrier G) :
    ResolvedRegionTagValueSupply Fmem V :=
  let A := resolvedMultiStarRegionBridgeAssembly Core Closure CarrierProper Ids Fstar StarProm Wiring
    OccRaw Measure Split hSurvivorComponent
  multiStarRegionTagValueSupply (Core.toDecontractionSupply Closure) Fstar Measure
    A.right_sound_value A.right_complete_value A.forest_sound_value A.forest_complete_value
    A.left_sound_value A.left_complete_value rrm

/-- **R-6c-body-392 — body-341's `houter` fed the assembly's six projections.** -/
theorem multiStar_selectedOuterRawOf_eq_of_geometry
    (Core : ResolvedMultiStarDecontractionValueCoreSupply D)
    (Closure : ResolvedMultiStarInnerRawCarrierClosureSupply Core)
    (CarrierProper : ResolvedCarrierProperProvider D)
    (Ids : ResolvedFilteredForestBlockUniqueIdSupply D)
    (Fstar : ResolvedCanonicalStarFacts D)
    (StarProm : ResolvedPromotedStarCoherenceValueSupply Fmem V)
    (Wiring : ResolvedRemnantComponentValueWiringSupply V Concrete)
    (OccRaw : ResolvedForestOccurrenceInversionValueSupply Core)
    (Measure : ResolvedMeasureLeafSupply D)
    (Split : ResolvedValueQuotientRegionSplitSupply Fmem V)
    (hSurvivorComponent : ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G)
      (γ : {y : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements} //
        y ∈ ResolvedCoassocSplitChoice.rightComponents s}),
      V.Survivor.survivor.survivorComponent s γ = (survivorSupply_of_measure Measure G).survivorComponent s γ)
    (rrm : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      regionRawUnion (Core.toDecontractionSupply Closure) Fstar z ∈ D.carrier G)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf
        ((multiStarRegionTagValueSupplyOfGeometry Core Closure CarrierProper Ids Fstar StarProm Wiring
          OccRaw Measure Split hSurvivorComponent rrm).recoveredPreimageValue z) = z.1.1 :=
  let A := resolvedMultiStarRegionBridgeAssembly Core Closure CarrierProper Ids Fstar StarProm Wiring
    OccRaw Measure Split hSurvivorComponent
  multiStar_selectedOuterRawOf_eq (Core.toDecontractionSupply Closure) Fstar Measure
    A.right_sound_value A.right_complete_value A.forest_sound_value A.forest_complete_value
    A.left_sound_value A.left_complete_value rrm z

end GaugeGeometry.QFT.Combinatorial
