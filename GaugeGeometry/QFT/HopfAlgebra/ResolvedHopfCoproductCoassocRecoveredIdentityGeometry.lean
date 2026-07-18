import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarRegionAssemblyGeometry
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredIdentityRoot
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarRemnantRoundTripGate
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarDefinitionalWiring
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerStarCoherenceValue

/-!
# R-6c-body-393 — bank-3b: the fully wired recovered-identity root (PROVED)

Three-hundred-and-ninety-third genuine-body step — the assembly that connects body-392's region-tag supply into
body-361's `toRecoveredIdentitySupply`, producing a single `ResolvedMultiStarRecoveredIdentitySupply` with all five
bridges (`houter` / `hRight` / `hForest` / `hround` / `hSurvivor`) DERIVED, so the caller no longer supplies them.

Shared internals:

```text
M      := Core.toDecontractionSupply Closure
OccInv := Core.toForestOccurrenceInversionSupply Closure OccRaw     -- exact-B side (once)
StarCoh:= Core.toInnerStarCoherenceSupply Closure StarRaw           -- inner-star coherence
T      := multiStarRegionTagValueSupplyOfGeometry … rrm             -- body-392 Tags
houter := multiStar_selectedOuterRawOf_eq_of_geometry … rrm         -- body-392
```

`hRight` / `hForest` are body-366's `rfl` wirings; `hSurvivor` is body-369's collection wiring; `hround` is body-367's
remnant round-trip (its positivity is `CarrierProper`'s component positivity at `z.2.1` transported through
`touchedLocalComponent_internalEdges`), moved from the concrete remnant to the abstract `V` remnant by the body-384
`Wiring`.  `hround` does NOT re-consume `OccInv` — `hidx` is already supplied by body-361; `OccInv` is used ONCE, on
the exact-`B` (`forestTag_agrees`) side.

Per the HALT: this is the FULLY WIRED identity, NOT an unconditional theorem — `StarRaw` / `OccRaw` / `StarProm` /
`Wiring` / `hSurvivorComponent` / `rrm` / the carrier `Closure` are still honest inputs (surfaced, not hidden); the six
bridges + the parent gate + `hRight` / `hForest` / `hround` / `hSurvivor` leave the caller.  No facade, no flat term, no
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

/-- **R-6c-body-393 — the fully wired recovered-identity root.**  Body-392's region-tag supply plugged into body-361's
`toRecoveredIdentitySupply`; the five bridges are all derived. -/
noncomputable def recoveredIdentitySupplyOfValueGeometry
    (Core : ResolvedMultiStarDecontractionValueCoreSupply D)
    (Closure : ResolvedMultiStarInnerRawCarrierClosureSupply Core)
    (CarrierProper : ResolvedCarrierProperProvider D)
    (Ids : ResolvedFilteredForestBlockUniqueIdSupply D)
    (Fstar : ResolvedCanonicalStarFacts D)
    (StarProm : ResolvedPromotedStarCoherenceValueSupply Fmem V)
    (StarRaw : ResolvedInnerStarCoherenceValueSupply Core)
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
    ResolvedMultiStarRecoveredIdentitySupply (Core.toDecontractionSupply Closure) Fstar Fmem V :=
  let M := Core.toDecontractionSupply Closure
  let OccInv := Core.toForestOccurrenceInversionSupply Closure OccRaw
  let StarCoh := Core.toInnerStarCoherenceSupply Closure StarRaw
  let T := multiStarRegionTagValueSupplyOfGeometry Core Closure CarrierProper Ids Fstar StarProm Wiring
    OccRaw Measure Split hSurvivorComponent rrm
  let houter := fun {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) =>
    multiStar_selectedOuterRawOf_eq_of_geometry Core Closure CarrierProper Ids Fstar StarProm Wiring
      OccRaw Measure Split hSurvivorComponent rrm z
  M.toRecoveredIdentitySupply Fstar OccInv Measure T houter
    (fun z => M.multiStar_rightRecovered_wiring Fstar z)
    (fun z => M.multiStar_forestRecovered_wiring Fstar z)
    (fun z γ δ hparent hidx =>
      (heq_of_eq (Wiring.remnantComponent_eq (T.recoveredPreimageValue z)
        (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageValue z) γ))).trans
        (M.multiStar_remnant_roundtrip Fstar StarCoh z δ (Concrete (T.recoveredPreimageValue z))
          (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageValue z) γ)
          hparent hidx
          (by rw [touchedLocalComponent_internalEdges]
              exact (CarrierProper.carrier_isProperForest _ z.2.1 z.2.2).2.2.2.1 δ.1
                (Finset.mem_filter.mp δ.2).1)
          (houter z)))
    (fun z => rightSurvivorForest_wiring Measure hSurvivorComponent (T.recoveredPreimageValue z))

end GaugeGeometry.QFT.Combinatorial
