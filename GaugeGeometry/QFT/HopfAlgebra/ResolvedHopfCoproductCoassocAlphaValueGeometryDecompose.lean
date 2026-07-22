import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCanonicalUniqueConstructions
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTouchedLocalizationLeg

/-!
# R-6c-body-530 — `ValueGeometry` ownership audit + faithful decomposition (PROVED)

Five-hundred-and-thirtieth genuine-body step — with `quot_eq` discharged (body-529), the remaining construction/model
residual is `ResolvedCanonicalUniqueMultiStarValueGeometrySupply` (`legComplete` + `parentCD`).  This body decomposes it
into two MINIMAL CK-model laws and, crucially, reduces `legComplete`'s two-inclusion `touchedLegComplete` to ONE law: its
UPPER inclusion is already DERIVABLE from body-320.

## Usage map (fields NOT expanded past their direct consumers)

| Field | Direct role | Verdict |
| --- | --- | --- |
| `legComplete` | the canonical `ResolvedTouchedLegLiftDatum` | two inclusions ↦ ONE (`touchedLegSaturated`) |
| `parentCD` | the de-contracted parent's `IsConnectedDivergent` | inverse-decontraction closure law (audited) |

The legacy `ValueGeometry` stays a valid conditional (NOT broken).

## The leg decomposition

`touchedLegComplete z δ = (touchedOuterForest legs ↦ δ) ∧ (δ ↦ G legs)`.  The SECOND conjunct is
`canonical_touchedLegComplete_upper` — `touchedContractedExternalLegs_le` (body-320) with the RHS unfolded by
`contractWithStars_externalLegs`.  So the TRUE residual is the FIRST conjunct alone:
`touchedLegSaturated z δ := touchedOuterForest legs.map (retarget) ≤ δ.externalLegs`;
`touchedLegComplete_of_saturated` / `touchedLegComplete_iff_saturated` complete the reduction.

## The faithful sockets

* `ResolvedCanonicalUniqueTouchedLegSaturationSupply` (`saturated`, the external-leg saturation law) → `.toLegComplete`;
* `ResolvedCanonicalUniqueDecontractionCDSupply Leg` (`parentCD`, the divergent-decontraction closure law, reading the
  SAME canonical lift) → `.toValueGeometry`.

## Parent-CD direction verdict (audit only — NOT discharged)

`Measure.contract_preserves_CD : parent CD → contracted quotient CD`; the `parentCD` residual is the INVERSE
(quotient component + inserted forest → de-contracted parent CD).  The direction is OPPOSITE, so `parentCD` MUST NOT be
fabricated from `Measure.contract_preserves_CD`.  Its consumer scope is threefold — forward-`q` parent reconstruction /
recovered-tag path / generic codomain/orphan `z`; while a generic `z` remains, `parentCD` MUST NOT be back-computed from
the forward round-trip (that is circular).

Attainment: `ValueGeometry` aggregate DECOMPOSED; leg upper inclusion DERIVED (body-320); leg true residual
`touchedLegSaturated` (ONE law); `parentCD` the inverse-decontraction CD law.  Both are CK-concrete-model laws
(external-leg saturation / divergent-insertion closure), NOT construction artifacts.

Per the HALT/guards: saturation is NOT claimed proved from a generic carrier; `parentCD` is NOT derived from `Measure`'s
forward preservation; nothing is back-computed from orphan-cover / coassoc; the final coassoc wrapper is NOT re-issued; NO
typeclass-ification; strict `StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc claim.  No facade, no flat
term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-! ## Step 2 — the upper inclusion, DERIVED (body-320) -/

/-- **R-6c-body-530 ∎ — the leg upper coverage.**  `δ.externalLegs ≤ G.externalLegs.map (retarget)` — body-320's
`touchedContractedExternalLegs_le` with the RHS unfolded. -/
theorem canonical_touchedLegComplete_upper (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))) :
    δ.externalLegs
      ≤ G.externalLegs.map ((touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1)) := by
  have h := touchedContractedExternalLegs_le z δ
  rwa [ResolvedAdmissibleSubgraph.contractWithStars_externalLegs] at h

/-! ## Step 3 — the true residual: ONE saturation law -/

/-- **R-6c-body-530 — the external-leg saturation residual** (the FIRST conjunct of `touchedLegComplete`). -/
def touchedLegSaturated (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))) : Prop :=
  (touchedOuterForest z δ).externalLegs.map ((touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1))
    ≤ δ.externalLegs

/-- **R-6c-body-530 ∎ — saturation gives completeness** (the upper inclusion is body-320). -/
theorem touchedLegComplete_of_saturated {z : ForestBlockCodType D G}
    {δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))}
    (h : touchedLegSaturated z δ) : touchedLegComplete z δ :=
  ⟨h, canonical_touchedLegComplete_upper z δ⟩

/-- **R-6c-body-530 ∎ — completeness ⇔ saturation** (the two-inclusion condition is exactly one). -/
theorem touchedLegComplete_iff_saturated {z : ForestBlockCodType D G}
    {δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))} :
    touchedLegComplete z δ ↔ touchedLegSaturated z δ :=
  ⟨fun h => h.1, touchedLegComplete_of_saturated⟩

/-! ## Step 4 — the faithful model sockets -/

/-- **R-6c-body-530 — the external-leg saturation supply** (the leg law, over `W'`). -/
structure ResolvedCanonicalUniqueTouchedLegSaturationSupply where
  /-- Every touched quotient component's forest legs saturate into it. -/
  saturated : ∀ {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z}),
    touchedLegSaturated z δ.1

/-- **R-6c-body-530 ∎ — leg saturation → leg completeness.** -/
theorem ResolvedCanonicalUniqueTouchedLegSaturationSupply.toLegComplete
    (Leg : ResolvedCanonicalUniqueTouchedLegSaturationSupply)
    {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z}) :
    touchedLegComplete z δ.1 :=
  touchedLegComplete_of_saturated (Leg.saturated z δ)

/-- **R-6c-body-530 — the divergent-decontraction closure supply** (the `parentCD` law, reading the SAME canonical
lift). -/
structure ResolvedCanonicalUniqueDecontractionCDSupply
    (Leg : ResolvedCanonicalUniqueTouchedLegSaturationSupply) where
  /-- The de-contracted parent (via the saturation-derived leg-lift) is connected-divergent. -/
  parentCD : ∀ {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z}),
    (localizedParentWithTouchedLegs z δ.1
      (touchedLegLiftDatum_of_complete z δ.1 (Leg.toLegComplete z δ))
      (liveAmbient_edges_supported ambientSupportOfW' z)
      (liveAmbient_legs_supported ambientSupportOfW' z)).forget.IsConnectedDivergent

/-- **R-6c-body-530 ∎ — the two model laws reassemble `ValueGeometry`.**  Projection only. -/
def ResolvedCanonicalUniqueDecontractionCDSupply.toValueGeometry
    {Leg : ResolvedCanonicalUniqueTouchedLegSaturationSupply}
    (Parent : ResolvedCanonicalUniqueDecontractionCDSupply Leg) :
    ResolvedCanonicalUniqueMultiStarValueGeometrySupply where
  legComplete := Leg.toLegComplete
  parentCD := Parent.parentCD

end GaugeGeometry.QFT.Combinatorial
