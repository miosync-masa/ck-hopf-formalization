import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLegCompleteValueCore
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAmbientSupportScopeRepair
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarRegionAssemblyGeometry

/-!
# R-6c-body-399 — the coherent value-core / carrier-closure assembly (PROVED)

Three-hundred-and-ninety-ninth genuine-body step — the coherent bundles that carry body-395's `Core` and its carrier
closures to body-394's sockets, with the body-397/398 live-`z` ambient support wired IN so no global graph support ever
re-enters a signature.  No concrete fact is proved — these are the honest gates bundled type-faithfully, with the
`legComplete` ⟷ `parentCD` coupling and the `Closure` ⟷ `recovered_raw_mem` sharing preserved.

* `ResolvedMultiStarValueCoreConstructionSupply D` — `Ambient` (body-397 gate) + `legComplete` (body-376 CK condition) +
  `parentCD` (reading the CANONICAL leg-lift built from the SAME `legComplete`, NOT a re-input `legLift`);
* `.toValueCore` — `valueCore_of_legComplete` fed `Ambient` through `liveAmbient_edges_supported` / `_legs_supported`
  (no bridging: `Ambient → live hE/hL → valueCore_of_legComplete`);
* `ResolvedMultiStarCarrierClosureBundleSupply Core Fstar` — a thin dependency-preserving bundle of `Closure` (body-377)
  + `recovered_raw_mem` (body-341's `rrm`), both over the SAME `Core.toDecontractionSupply Closure`.

Per the HALT: `legComplete` / `parentCD` / `innerRaw_mem` (inside `Closure`) / `recovered_raw_mem` stay HONEST FIELDS;
`Ambient` is body-397's `z.1.2`-scoped support gate (NOT `∀ G, WellFormed G`); the `Core` / `Closure` / `rrm` handed to
body-394 are pure projections; no concrete fact is discharged.  No facade, no flat term, no `forgetHopf`, no rep/perm,
and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-399 — the coherent value-core construction supply.**  The ambient-support gate + the CK leg-completeness
+ the coupled parent CD, from which the `innerRaw_mem`-free value core is assembled with live-`z` support. -/
structure ResolvedMultiStarValueCoreConstructionSupply (D : ResolvedCoproductProperForestData) where
  /-- The `z.1.2`-scoped carrier-ambient support gate (body-397 — NOT `∀ G, WellFormed G`). -/
  Ambient : ResolvedCarrierAmbientSupportSupply D
  /-- The CK leg-completeness condition per touched quotient component (body-376). -/
  legComplete : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z}),
    touchedLegComplete z δ.1
  /-- The de-contracted parent is connected-divergent — reading the CANONICAL leg-lift built from `legComplete` and the
  live-`z` ambient support (NOT a re-input `legLift`). -/
  parentCD : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z}),
    (localizedParentWithTouchedLegs z δ.1
      (touchedLegLiftDatum_of_complete z δ.1 (legComplete z δ))
      (liveAmbient_edges_supported Ambient z)
      (liveAmbient_legs_supported Ambient z)).forget.IsConnectedDivergent

/-- **R-6c-body-399 — the value core from the coherent construction** (`Ambient → live hE/hL → valueCore_of_legComplete`,
no bridge). -/
noncomputable def ResolvedMultiStarValueCoreConstructionSupply.toValueCore
    (C : ResolvedMultiStarValueCoreConstructionSupply D) :
    ResolvedMultiStarDecontractionValueCoreSupply D :=
  valueCore_of_legComplete
    (liveAmbient_edges_supported C.Ambient)
    (liveAmbient_legs_supported C.Ambient)
    C.legComplete C.parentCD

/-- **R-6c-body-399 — the carrier-closure bundle.**  `Closure` (body-377) + `recovered_raw_mem` (body-341's `rrm`),
both over the SAME `Core.toDecontractionSupply Closure`. -/
structure ResolvedMultiStarCarrierClosureBundleSupply
    (Core : ResolvedMultiStarDecontractionValueCoreSupply D) (Fstar : ResolvedCanonicalStarFacts D) where
  /-- The inner-raw carrier closure (body-377). -/
  Closure : ResolvedMultiStarInnerRawCarrierClosureSupply Core
  /-- The region raw-union lies in the carrier (body-341's `recovered_raw_mem`), over the SAME de-contraction supply. -/
  recovered_raw_mem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    regionRawUnion (Core.toDecontractionSupply Closure) Fstar z ∈ D.carrier G

end GaugeGeometry.QFT.Combinatorial
