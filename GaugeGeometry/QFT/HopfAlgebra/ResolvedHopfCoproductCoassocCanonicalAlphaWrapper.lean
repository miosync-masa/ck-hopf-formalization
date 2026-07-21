import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaBijectionSide
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCanonicalUniqueConstructions

/-!
# R-6c-body-482 — the canonical-`W'` alpha completion wrapper (migration campaign, stage 1) (PROVED)

Four-hundred-and-eighty-second genuine-body step — stage 1 of the body-445 migration campaign.  This body does NOT rewrite
body-445; it builds the alpha completion wrapper over the canonical unique-ID carrier `W'` and X-rays the FINAL residual in
the new (filtered, `Forward`-free) type, fixing the shape with the old `V` / strict cross-ambient sockets removed from the
signature FIRST.

* `ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply` — the named wrapper of the body-471 alpha-native filtered
  value constructor at the canonical `W'` arguments (`D := W'.toData`, `CarrierProper := W'.toCarrierProperProvider`,
  `Fstar := canonicalUniqueStarFactsOfW'`);
* `toCanonicalFilteredValue` — the projection publishing the body-470 filtered `V` root
  (`.toFilteredConcreteSummandValueSupply`);
* `coassoc_gen_of_canonical_unique_alpha_roundtrip` — the round-trip-normalized native `Δᵣ`-coassociativity, a
  projection-only application of body-481's `coassoc_gen_of_recovered_preimage_alpha_value` with
  `carrier_isProperForest := W'.toCarrierProperProvider.carrier_isProperForest`.

## Socket audit — the new signature's remaining hypotheses (the further-purified ledger)

```text
remaining:
  Fmem                            filtered selected-outer carrier membership (implicit model parameter)
  AlphaVBuild                     ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply
    - Measure                       value-side measure leaf (honest V ownership)
    - survivorInj / survivorGen     survivor Finset injectivity / reembed generator
    - filtered quotient_mem / quot_eq   body-469 filtered quotient ownership (Quotient projection)
  AlphaRoundTrip                  ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply
    - alpha region / forward geometry leaves   (Data: tags + membership + forward_outer/quotient)
    - forest_value_eq               the forest-component exact-value leaf
  rep / repCD / rep_gen           base-model representatives

internalized by the canonical W' (no longer in the signature):
  D (:= W'.toData), Fstar (:= canonicalUniqueStarFactsOfW'), CarrierProper (:= W'.toCarrierProperProvider),
  the id-uniqueness roots, the carrier closure, the ambient support.
```

## Status vs old body-445

* old **total** `VBuild` (`ResolvedConcreteSummandValueConstructionSupply`) → alpha **filtered** `VBuild`
  (`ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply`); the quotient ownership is the body-469 FILTERED
  `Quotient`, not the total-`q` construction;
* strict `StarProm` (`ResolvedPromotedStarCoherenceValueSupply`) / `InnerStarRaw`
  (`ResolvedInnerStarCoherenceValueSupply`) — the cross-ambient sockets — are GONE from the theorem signature (replaced by
  the corrected-permutation constructions banked in bodies 446–468, and now absorbed into the alpha `Remnant` transport);
* `ValueGeometry` / `OccRaw` / `Split` have NOT become unnecessary — they are slated to REAPPEAR, decomposed into the
  canonical construction of `AlphaRoundTrip` (from bodies 446–468's corrected geometry), one leaf at a time WITHOUT a
  strict socket, starting body-483;
* body-445 stays a valid conditional theorem — it is NOT edited or replaced here.

Per the HALT/guards: `AlphaRoundTrip` is NOT canonically constructed yet; NO claim that `ValueGeometry` / `OccRaw` /
`Split` are unnecessary; body-445 is NOT edited or replaced; the 71-file in-place migration is NOT started; this is NOT the
unconditional coassoc; strict `StarProm` / `InnerStarRaw` NOT restored; body-445 stays a valid conditional.  No facade, no
flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-482 — the canonical-`W'` alpha-native filtered value construction supply.**  The body-471 constructor at
the canonical unique-ID carrier's arguments. -/
abbrev ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply :=
  ResolvedAlphaNativeFilteredValueConstructionSupply
    canonicalUniqueSupportedCarrierProperSupply.toData
    canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
    canonicalUniqueStarFactsOfW'

/-- **R-6c-body-482 — the canonical filtered `V` projection.**  Publishes the body-470 filtered summand value root. -/
noncomputable def ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply.toCanonicalFilteredValue
    (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply) :
    ResolvedFilteredConcreteSummandValueSupply canonicalUniqueSupportedCarrierProperSupply.toData :=
  ResolvedAlphaNativeFilteredValueConstructionSupply.toFilteredConcreteSummandValueSupply
    canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
    canonicalUniqueStarFactsOfW'
    VBuild

/-- **R-6c-body-482 ∎ — canonical-`W'` round-trip-normalized native `Δᵣ`-coassociativity.**  A projection-only
application of body-481's `coassoc_gen_of_recovered_preimage_alpha_value`: the old total `V` root and the strict
cross-ambient `StarProm` / `InnerStarRaw` sockets are GONE from this signature; the final residual is the alpha filtered
`VBuild` + the alpha `R` round-trip aggregate. -/
theorem coassoc_gen_of_canonical_unique_alpha_roundtrip
    {Fmem : ResolvedSelectedOuterFilteredMemSupply canonicalUniqueSupportedCarrierProperSupply.toData}
    (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
    (R : ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply Fmem VBuild.toCanonicalFilteredValue)
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x))
    (x : ResolvedHopfGen) :
    canonicalUniqueSupportedCarrierProperSupply.toData.coassocLeft (MvPolynomial.X x)
      = canonicalUniqueSupportedCarrierProperSupply.toData.coassocRight (MvPolynomial.X x) :=
  coassoc_gen_of_recovered_preimage_alpha_value R
    canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider.carrier_isProperForest
    rep repCD rep_gen x

end GaugeGeometry.QFT.Combinatorial
