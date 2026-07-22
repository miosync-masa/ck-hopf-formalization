import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaQuotientMemSaturated
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSaturatedCarrier
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSaturatedSelectedOuter
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaCarrierLegSaturation
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaValueGeometryDecompose
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCanonicalUniqueConstructions
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarCoreClosureAssembly

/-!
# R-6c-body-541 — the `W″` canonical alpha construction ROOT (PROVED)

Five-hundred-and-forty-first genuine-body step — the single-owner `W″` construction ROOT.  With `W″`'s combinatorial
carrier ownership complete (body-540: `Fmem` / `recoveredRawUnion` / `innerRaw` closure / corrected-quotient membership +
the carrier-closure bundle all DERIVED FROM `W″` MEMBERSHIP), this body assembles the `W″` value-geometry / core owner.
The point of the construction is that `legComplete` is NO LONGER an independent record field: it is a THEOREM of `W″`
membership (Step 2), fed by body-533's membership-derived `LegModel` (`canonicalLegSaturatedExternalLegSaturationSupply`).
The ONLY remaining honest physics field is `Parent` (the inverse-decontraction / divergence-closure CD law).

## The single-owner assembly

* **Step 1 — `ambientSupportOfW''`.**  The `W″` carrier-ambient support gate, a body-445 (`ambientSupportOfW'`) replay
  routed through `canonicalLegSaturatedCarrier_mem_W'` — a `W″` member sits inside a `W′` member, whose ambient support is
  `canonicalUniqueSupportedCarrier_ambientSupported`.
* **Step 2 — `legComplete` DERIVED FROM MEMBERSHIP.**  `canonicalLegSaturated_touchedLegSaturated` mirrors body-531's
  `canonicalTouchedLegSaturationSupply.saturated`, but feeds body-533's membership-derived `LegModel`
  (`canonicalLegSaturatedExternalLegSaturationSupply`) rather than an independent `LegModel` argument — so NO leg-model
  hypothesis survives.  `canonicalLegSaturated_touchedLegComplete` closes it with body-530's
  `touchedLegComplete_of_saturated` (the upper inclusion is body-320).
* **Step 3 — `ResolvedCanonicalLegSaturatedDecontractionCDSupply`.**  A body-530
  (`ResolvedCanonicalUniqueDecontractionCDSupply`) replay over `W″`, reading the Step-2 canonical lift and
  `ambientSupportOfW''`.  This is the ONLY physics field; there is NO `legLift` / `legComplete` field.
* **Step 4 — `.toCoreBuild` / `.toValueCore`.**  Feeds the same Step-2 `legComplete` theorem and `ambientSupportOfW''`
  into body-399's `ResolvedMultiStarValueCoreConstructionSupply`; the value core is PROJECTED FROM `Parent` ONLY.
* **Step 5 — `ResolvedCanonicalLegSaturatedAlphaConstructionSupply E`.**  The minimal single-owner root: `Measure` +
  `Parent`.  `Core` is issued ONCE (`R.Parent.toValueCore`); `ClosureBundle` (body-540), `Fmem` (body-534), and
  `quotient_mem` (body-540) all read the SAME `R.Core` owner.

## Scoreboard (`W″` construction root)

```text
LegModel                ABSORBED (body-540 / body-533)  — no independent field
ValueGeometry aggregate GONE           — legComplete DERIVED from W″ membership (Step 2)
value Core              CONSTRUCTED FROM Parent ONLY (Step 4)
carrier ClosureBundle   SAME OWNER R.Core (Step 5)
Fmem / quotient_mem     DERIVED from membership (Step 5)
```

Conceptual final root: **Combinatorics = all from `W″` membership; Physics = `Measure` / `E` / `Parent`;
Representation = `rep*`.**

## Step 6 — migration audit for bodies 511–529 (the upcoming `W″` re-key campaign)

This body does NOT enter the `quot_eq` / round-trip / coassoc migration; the following is a classification only, to scope
the campaign.  `quot_eq` is NOT cast from the `W′` theorem, and NO `W′`↔`W″` `q` adapter / cast bridge is built here.

| Body / decl | Kind | Verdict |
| --- | --- | --- |
| 511 `canonicalFiltered_quot_eq_of_contract_class_eq` | `W′`-canonical specialization (keyed to `canonicalUniqueSupportedCarrierProperSupply`) | `W″` **RE-ISSUE** |
| 511 `ResolvedCanonicalFilteredContractClassEqSupply.toQuotEqConstructionSupply` | proof-owner adapter | **PROJECTION/RFL** |
| 512 `ResolvedCanonicalFilteredContractTwiceFieldSupply.toContractClassEqSupply` | proof-owner adapter | **PROJECTION/RFL** |
| 513 `globalPermExtension` / `contractStarPerm` / `contractStarPerm_on_vertices` | `W′`-canonical (keyed to `Measure`/`E` correspondence over `W′`) | `W″` **RE-ISSUE** |
| 514–520 corrected-left / two-stage-survivor geometry | genuine two-stage contraction geometry (D-parametric core) | mostly **REUSE**; `W′`-pinned wrappers **RE-ISSUE** |
| 521 `correctedTwoStageSurvivor_cases` | D-generic partition geometry | **REUSE** (no re-issue) |
| 522–523 `canonicalCorrectedContractVertexCorrespondence` / `...CorrespondenceSupply` (`ThreeRouteInverse`) | `W′`-canonical specialization | `W″` **RE-ISSUE** |
| 524 `canonicalCorrectedContractRetargetDomainSupply` (`QuotEqDischarged`) | `W′`-canonical specialization | `W″` **RE-ISSUE** |
| 525–526 `correctedRetargetRhs` / `canonicalCorrected_retargetVertex_eq_on_G` | D-generic retarget-coordinate algebra | **REUSE** (D-generic theorem) |
| 527 `selectedOuter_count_eq_*` | D-generic count algebra | **REUSE** |
| 528 `canonicalCorrectedQuotientRaw_internalEdges_eq_inputResidual` | D-generic residual algebra | **REUSE** |
| 529 `canonicalCorrected_internalEdges_domain` / `...ContractTwiceFieldSupply` / `...ContractClassEqSupply` / `...QuotEqConstructionSupply` | `W′`-canonical specialization (owner-pinned) | `W″` **RE-ISSUE** |
| 529 `coassoc_gen_of_canonicalMultiStar_alpha_construction_discharged` | `W′`-canonical final wrapper | `W″` **RE-ISSUE** (the migration terminus) |

Buckets: **D-generic theorem → REUSE** (525–528, 521, count/residual algebra); **`W′` canonical specialization → `W″`
RE-ISSUE** (511 quot_eq, 513 perm, 522–524, 529 discharged chain + final wrapper); **proof-owner wrapper →
PROJECTION/RFL** (the `.toContractClassEqSupply` / `.toQuotEqConstructionSupply` adapters); **genuine new geometry → NONE
expected** (the two-stage partition is already established; no new geometric fact is anticipated for the re-key).

Per the HALT/guards: `legComplete` is the Step-2 membership-derived theorem — NO `legLift` / `legComplete` FIELD is
reintroduced; `Parent` is the ONLY physics field and is NOT derived from forward preservation; `Core` is issued ONCE and
`ClosureBundle` / `Fmem` / `quotient_mem` read the SAME owner; NO `quot_eq` / contract-correspondence / alpha-tags /
round-trip / coassoc migration is entered; NO `W′`↔`W″` cast bridge is built; strict `StarProm` / `InnerStarRaw` stay
ZERO; NO unconditional-coassoc claim.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO new datum field /
socket beyond the honest `Parent` law.
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

/-! ## Step 1 — the `W″` carrier-ambient support gate (body-445 `ambientSupportOfW'` replay). -/

/-- **R-6c-body-541 — `W″` supplies the carrier-ambient support gate.**  A `W″` member sits inside a `W′` member
(`canonicalLegSaturatedCarrier_mem_W'`), whose ambient support is `canonicalUniqueSupportedCarrier_ambientSupported`. -/
def ambientSupportOfW'' :
    ResolvedCarrierAmbientSupportSupply canonicalLegSaturatedCarrierProperSupply.toData where
  edges_supported_of_mem := fun hA =>
    (canonicalUniqueSupportedCarrier_ambientSupported (canonicalLegSaturatedCarrier_mem_W' hA)).1
  legs_supported_of_mem := fun hA =>
    (canonicalUniqueSupportedCarrier_ambientSupported (canonicalLegSaturatedCarrier_mem_W' hA)).2

/-! ## Step 2 — `legComplete` DERIVED FROM `W″` MEMBERSHIP (body-531 mirror, membership `LegModel`). -/

/-- **R-6c-body-541 ∎ — every touched `W″` quotient component's forest legs saturate into it.**  A body-531
(`canonicalTouchedLegSaturationSupply.saturated`) replay whose leg-model side is body-533's membership-derived
`canonicalLegSaturatedExternalLegSaturationSupply` — so NO independent `LegModel` hypothesis survives. -/
theorem canonicalLegSaturated_touchedLegSaturated {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z}) :
    touchedLegSaturated z δ.1 :=
  le_trans (touchedOuter_externalLegs_map_le_componentFilter z δ.1)
    (canonicalLegSaturatedExternalLegSaturationSupply.externalLegs_saturated_of_mem z.2.2
      (Finset.mem_of_mem_filter _ δ.2))

/-- **R-6c-body-541 ∎ — `touchedLegComplete` DERIVED FROM `W″` MEMBERSHIP.**  Saturation (Step 2) + body-530's upper
inclusion (body-320).  This is the canonical leg lift; there is NO `legLift` / `legComplete` field. -/
theorem canonicalLegSaturated_touchedLegComplete {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z}) :
    touchedLegComplete z δ.1 :=
  touchedLegComplete_of_saturated (canonicalLegSaturated_touchedLegSaturated z δ)

/-! ## Step 3 — the Parent-only physics socket (body-530 `ResolvedCanonicalUniqueDecontractionCDSupply` mirror). -/

/-- **R-6c-body-541 — the `W″` divergent-decontraction closure supply.**  The de-contracted parent — via the Step-2
membership-derived canonical leg-lift and `ambientSupportOfW''` — is connected-divergent.  This is the ONLY honest physics
field; NO `legLift` / `legComplete` field appears. -/
structure ResolvedCanonicalLegSaturatedDecontractionCDSupply where
  /-- The de-contracted parent (via the `W″`-membership leg-lift) is connected-divergent. -/
  parentCD : ∀ {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z}),
    (localizedParentWithTouchedLegs z δ.1
      (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
      (liveAmbient_edges_supported ambientSupportOfW'' z)
      (liveAmbient_legs_supported ambientSupportOfW'' z)).forget.IsConnectedDivergent

/-! ## Step 4 — the generic value-core assembly (body-399 `ResolvedMultiStarValueCoreConstructionSupply`). -/

/-- **R-6c-body-541 — the `W″` value-geometry root becomes the coherent `CoreBuild`.**  `Ambient := ambientSupportOfW''`,
`legComplete := canonicalLegSaturated_touchedLegComplete` (Step 2), `parentCD := Parent.parentCD` (Step 3, built on the
SAME canonical lift). -/
def ResolvedCanonicalLegSaturatedDecontractionCDSupply.toCoreBuild
    (Parent : ResolvedCanonicalLegSaturatedDecontractionCDSupply) :
    ResolvedMultiStarValueCoreConstructionSupply canonicalLegSaturatedCarrierProperSupply.toData where
  Ambient := ambientSupportOfW''
  legComplete := fun z δ => canonicalLegSaturated_touchedLegComplete z δ
  parentCD := fun z δ => Parent.parentCD z δ

/-- **R-6c-body-541 — the `W″` value core, PROJECTED FROM `Parent` ONLY.** -/
noncomputable def ResolvedCanonicalLegSaturatedDecontractionCDSupply.toValueCore
    (Parent : ResolvedCanonicalLegSaturatedDecontractionCDSupply) :
    ResolvedMultiStarDecontractionValueCoreSupply canonicalLegSaturatedCarrierProperSupply.toData :=
  Parent.toCoreBuild.toValueCore

/-! ## Step 5 — the minimal single-owner `W″` construction root. -/

/-- **R-6c-body-541 — the single-owner `W″` alpha construction root.**  The ONLY explicit data: the value-side `Measure`
and the honest `Parent` physics law.  Everything else (`Core` / `ClosureBundle` / `Fmem` / `quotient_mem`) is DERIVED and
reads the SAME owner. -/
structure ResolvedCanonicalLegSaturatedAlphaConstructionSupply
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H) where
  /-- The value-side measure leaf (the honest CK measure). -/
  Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData
  /-- The inverse-decontraction / divergence-closure physics law — the ONLY honest model field. -/
  Parent : ResolvedCanonicalLegSaturatedDecontractionCDSupply

/-- **R-6c-body-541 — the SINGLE value-core owner.**  Issued ONCE from `Parent`; every downstream owner reads THIS. -/
noncomputable def ResolvedCanonicalLegSaturatedAlphaConstructionSupply.Core
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    ResolvedMultiStarDecontractionValueCoreSupply canonicalLegSaturatedCarrierProperSupply.toData :=
  R.Parent.toValueCore

/-- **R-6c-body-541 — the `W″` `Fmem`, DERIVED from the measure (body-534).** -/
noncomputable def ResolvedCanonicalLegSaturatedAlphaConstructionSupply.Fmem
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    ResolvedSelectedOuterFilteredMemSupply canonicalLegSaturatedCarrierProperSupply.toData :=
  canonicalLegSaturatedSelectedOuterFilteredMemSupply_of_measure R.Measure E

/-- **R-6c-body-541 — the `W″` carrier-closure bundle (body-540), reading the SAME `R.Core` owner.** -/
noncomputable def ResolvedCanonicalLegSaturatedAlphaConstructionSupply.ClosureBundle
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    ResolvedMultiStarCarrierClosureBundleSupply R.Core canonicalLegSaturatedStarFacts :=
  canonicalLegSaturatedMultiStarCarrierClosureBundleSupply R.Measure E R.Core

/-- **R-6c-body-541 — the `W″` corrected-quotient membership (body-540), DERIVED.** -/
theorem ResolvedCanonicalLegSaturatedAlphaConstructionSupply.quotient_mem
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G) :
    canonicalCorrectedQuotientRaw R.Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
        canonicalLegSaturatedStarFacts q.1
      ∈ canonicalLegSaturatedCarrierProperSupply.toData.carrier
          (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) :=
  canonicalLegSaturatedCorrectedQuotient_mem R.Measure E q

end GaugeGeometry.QFT.Combinatorial
