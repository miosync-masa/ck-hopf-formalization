import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaQuotientMemComplete
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocContractTwiceQuotEq

/-!
# R-6c-body-511 — filtered `quot_eq` scope audit + class-equality reduction (PROVED)

Five-hundred-and-eleventh genuine-body step — normalizing the last pure construction artifact `quot_eq` to a single
graph-CLASS equality, WITHOUT touching `ValueGeometry`.  Body-110/111's `resolved_rightTerm_eq_of_class_eq` already teaches
that a `rightTerm` equality between two carrier members reduces to their contract-with-stars classes being equal.  So
`quot_eq` — `(supply G).rightTerm q.1.1 = (supply H).rightTerm ⟨canonicalCorrectedQuotientRaw …, mem⟩` — reduces to the
canonical filtered contract-twice class equality.

## The filtered reduction (Step 1)

`canonicalFiltered_quot_eq_of_contract_class_eq` — given the class equality `hclass` between `q`'s outer contract-with-stars
and the corrected quotient's contract-with-stars, `resolved_rightTerm_eq_of_class_eq` (body-110/111) discharges the body-501
`quot_eq` target verbatim (`A := q.1.1`, `B := ⟨canonicalCorrectedQuotientRaw …, canonicalCorrectedQuotient_mem …⟩`).

## The faithful filtered socket (Step 2)

`ResolvedCanonicalFilteredContractClassEqSupply Measure E` — the single field `contract_class_eq` over a FILTERED `q` only
(no lift to arbitrary raw split choice, no body-468 total-quotient no-go).  Its `toQuotEqConstructionSupply` (Measure) →
body-501's quotEq root, shrinking that root's honest field from `quot_eq` to `contract_class_eq` — a graph-class equality,
which is exactly the contract-twice geometry already built in bodies 27–49.

## Status

`quot_eq` is now a THEOREM modulo the single class equality `contract_class_eq`.  The class-equality construction from the
existing three-field contract-twice geometry (`branchRightGraph` / `imageInnerRightGraph` / the per-remnant local
permutations) is the next body's audit target (safe-stop: the reduction + socket are banked; the field-level class-equality
residual is named, NOT yet claimed derivable).

Per the HALT/guards: no raw total quotient ownership is revived; no `corrected = uncorrected` graph equality is asserted; no
equality between distinct local permutations is required; nothing is back-computed from coassoc / `rightTerm`;
`ValueGeometry` / `legComplete` / `parentCD` are NOT entered; `quot_eq` is NOT recorded as GONE (only reduced); the legacy
bodies stay valid conditionals; strict `StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc claim.  No facade, no
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

/-- **R-6c-body-511 ∎ — filtered `quot_eq` from the contract-with-stars class equality.**  body-110/111's rightTerm/class
reduction at the canonical filtered `q`. -/
theorem canonicalFiltered_quot_eq_of_contract_class_eq
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G)
    (hclass :
      (q.1.1.1.contractWithStars (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)).toResolvedClass
        = ((canonicalCorrectedQuotientRaw Measure
              canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
              canonicalUniqueStarFactsOfW' q.1).contractWithStars
            (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
              (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
              (canonicalCorrectedQuotientRaw Measure
                canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
                canonicalUniqueStarFactsOfW' q.1))).toResolvedClass) :
    (canonicalUniqueSupportedCarrierProperSupply.toData.supply G).rightTerm q.1.1
      = (canonicalUniqueSupportedCarrierProperSupply.toData.supply
            (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)).rightTerm
          ⟨canonicalCorrectedQuotientRaw Measure
              canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
              canonicalUniqueStarFactsOfW' q.1,
            canonicalCorrectedQuotient_mem Measure E q⟩ :=
  resolved_rightTerm_eq_of_class_eq q.1.1
    ⟨canonicalCorrectedQuotientRaw Measure
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
        canonicalUniqueStarFactsOfW' q.1,
      canonicalCorrectedQuotient_mem Measure E q⟩
    hclass

/-- **R-6c-body-511 — the faithful filtered contract-twice class-equality socket.**  A single field over a FILTERED `q`
(no raw `∀ s` lift); the honest residual `quot_eq` reduces to this graph-class equality. -/
structure ResolvedCanonicalFilteredContractClassEqSupply
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H) where
  /-- The outer's contract-with-stars class equals the corrected quotient's — over a filtered `q` only. -/
  contract_class_eq : ∀ {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G),
    (q.1.1.1.contractWithStars (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)).toResolvedClass
      = ((canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1).contractWithStars
          (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
            (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
            (canonicalCorrectedQuotientRaw Measure
              canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
              canonicalUniqueStarFactsOfW' q.1))).toResolvedClass

/-- **R-6c-body-511 ∎ — the class-equality socket → body-501's quotEq root.**  `quot_eq` is filled from the class
equality; the quotEq root's honest field is thereby `contract_class_eq`. -/
noncomputable def ResolvedCanonicalFilteredContractClassEqSupply.toQuotEqConstructionSupply
    {Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData}
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (C : ResolvedCanonicalFilteredContractClassEqSupply Measure E) :
    ResolvedCanonicalUniqueAlphaFilteredQuotEqConstructionSupply E where
  Measure := Measure
  quot_eq := fun {_G} q => canonicalFiltered_quot_eq_of_contract_class_eq Measure E q (C.contract_class_eq q)

end GaugeGeometry.QFT.Combinatorial
