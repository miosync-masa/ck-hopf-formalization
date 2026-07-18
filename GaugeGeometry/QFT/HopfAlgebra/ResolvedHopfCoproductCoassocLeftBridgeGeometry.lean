import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocParentRemnantGeometry
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarLeftGeometry
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestOccurrenceInversionValue

/-!
# R-6c-body-391 — bank-3b: the multi-star LEFT bridge fed by the derived parent section (PROVED)

Three-hundred-and-ninety-first genuine-body step — the LEFT analogue of body-390's forest-bridge rewire.  No left proof
is re-proved: this is a pure converter that plugs body-390's DERIVED parent section (`parent_remnantComponent` is now a
theorem, not a datum) into body-373's `resolvedMultiStarLeftBridgeOfGeometry`, so the caller no longer supplies the
parent gate.

* `resolvedMultiStarLeftBridgeOfValueGeometry` — the left residual bridge over the value core, with the parent gate
  eliminated (assembled from the three projections via body-390).

The three design points:

* `parent_remnantComponent` is NOT returned to a caller argument — it is discharged internally by body-390;
* `OccRaw` (the raw occurrence inversion, body-380) IS kept — it is essential to the LEFT M3 / exact-`B` route and is
  distinct from the parent reconstruction;
* `Closure` is used ONLY for the type-lifting of `M` and `OccInv` (carrier membership), NEVER in a geometry proof.

Per the HALT: the forest bridge (390) and now the left bridge are both derived with NO old parent gate; the parent
reconstruction datum is fully eliminated from the residual; the remaining LEFT-side model data are `OccRaw` and the
cross-ambient `StarProm`; `Ids` stays the `q`-local base-model ownership gate.  No facade, no flat term, no `forgetHopf`,
no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-391 — the multi-star LEFT bridge over the value core, with the parent gate eliminated.**  The derived
parent section (body-390) is plugged into body-373's `resolvedMultiStarLeftBridgeOfGeometry`. -/
noncomputable def resolvedMultiStarLeftBridgeOfValueGeometry
    (Core : ResolvedMultiStarDecontractionValueCoreSupply D)
    (Closure : ResolvedMultiStarInnerRawCarrierClosureSupply Core)
    (CarrierProper : ResolvedCarrierProperProvider D)
    (Ids : ResolvedFilteredForestBlockUniqueIdSupply D)
    (Fstar : ResolvedCanonicalStarFacts D)
    (StarProm : ResolvedPromotedStarCoherenceValueSupply Fmem V)
    (Wiring : ResolvedRemnantComponentValueWiringSupply V Concrete)
    (OccRaw : ResolvedForestOccurrenceInversionValueSupply Core)
    (Measure : ResolvedMeasureLeafSupply D)
    (Split : ResolvedValueQuotientRegionSplitSupply Fmem V) :
    ResolvedLeftResidualValueCoreBridgeSupply Fmem V :=
  (Core.toDecontractionSupply Closure).resolvedMultiStarLeftBridgeOfGeometry
    (Core.toForestOccurrenceInversionSupply Closure OccRaw) Measure Split
    (Core.toParentRemnantSection Closure
      (resolvedParentRemnantSectionValue Core CarrierProper Ids Fstar StarProm Wiring))

end GaugeGeometry.QFT.Combinatorial
