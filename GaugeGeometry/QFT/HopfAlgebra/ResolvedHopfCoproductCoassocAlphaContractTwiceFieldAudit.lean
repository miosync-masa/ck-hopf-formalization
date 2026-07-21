import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaQuotEqClassReduction
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocContractTwiceShared

/-!
# R-6c-body-512 — corrected contract-twice geometry ownership audit + field-level residual socket (PROVED)

Five-hundred-and-twelfth genuine-body step — the pre-implementation ownership audit for `quot_eq`'s sole residual
`contract_class_eq` (body-511).  `quot_eq` is NOT recorded as GONE; this body pins EXACTLY which existing bodies-27–49
layer the class equality reuses, and banks the precise field-level residual.

## Audit verdict — the abstraction level of bodies 27–49

* `ResolvedRemnantContractGeometrySupply` (body-6a-4c) — **ABSTRACTED, per-occurrence `starPerm o`.**  Its three field
  equalities are `(remnantComponent o).vertices = (o.contractedSourceGraph.mapPerm (starPerm o)).vertices` etc. — a
  PER-OCCURRENCE local permutation, EXACTLY the corrected family's `promotedStarCorrectingPerm Fstar s o` shape (bodies
  456–467).  So `correctedRemnantComponent` + `correctedRemnantComponent_vertices/internalEdges/externalLegs_eq_promoted`
  slot straight in.  VERDICT: **REUSABLE** (no `corrected = uncorrected` bridge, no distinct-permutation equality).
* `ResolvedContractTwiceOnceGeometrySupply` (body-5c-2b-1) — takes ONE GLOBAL `starPerm s` and three WHOLE-GRAPH field
  equalities `(branchRightGraph s).vertices = ((imageInnerRightGraph imageOf s).mapPerm (starPerm s)).vertices` etc.
  `branchRightGraph s = s.1.1.contractWithStars` (`rfl`); `imageInnerRightGraph imageOf s =
  (imageOf s).quotientForest.contractWithStars` (`rfl`).  VERDICT: **GLOBAL-PERM ASSEMBLY** — the whole-graph `σ` must be
  assembled from the per-remnant local `starPerm o` (disjoint supports via body-464 family disjointness) + identity on
  survivors.  NOT an obstruction (the remnants are pairwise disjoint), but genuine assembly work — the next body's target.

So the residual is NOT a term-ownership question and NOT a permutation-equality question: it is the three WHOLE-GRAPH field
equalities between `q`'s outer contract-with-stars and the corrected quotient's, under one assembled `σ`.

## The field-level residual socket (banked)

`ResolvedCanonicalFilteredContractTwiceFieldSupply Measure E` — `starPerm` + the three whole-graph field equalities over a
FILTERED `q`.  `toContractClassEqSupply` (via `toResolvedClass_eq_of_mapPerm_fields`) → body-511's class-equality socket,
so the whole quotEq residual is now the three field equalities.  Existing corrected assets to feed the next body's `σ`
assembly: `promotedStarCorrectingPerm` / `correctedRemnantComponent_*_eq_promoted` (per-remnant) + `correctedRemnant
Component_disjoint` (body-464) for disjoint extension + survivor identity.

## Status

`quot_eq` ⟵ `contract_class_eq` (body-511) ⟵ three whole-graph field equalities + assembled `σ` (this body).  The `σ`
assembly from the per-remnant local perms is the SOLE named residual; `quot_eq` is NOT claimed derivable yet.

Per the HALT/guards: no raw quotient membership is required; no `corrected = uncorrected` graph equality is asserted; no
equality between distinct local permutations is required; local perms are NOT treated as one global perm without the
disjoint-extension assembly; nothing is back-computed from `rightTerm` / coassoc; `ValueGeometry` is NOT entered; the
unresolved field-equality residual is named precisely and NOT claimed derived; strict `StarProm` / `InnerStarRaw` stay
ZERO; NO unconditional-coassoc claim.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` /
singleton / floor-297.
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

/-- **R-6c-body-512 — the faithful filtered contract-twice FIELD socket.**  One global `starPerm` per filtered `q` plus the
three whole-graph field equalities between `q`'s outer contract-with-stars and the corrected quotient's.  This is the exact
residual of `quot_eq` after body-511's class reduction. -/
structure ResolvedCanonicalFilteredContractTwiceFieldSupply
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H) where
  /-- The assembled global star permutation (per filtered `q`). -/
  starPerm : ∀ {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G), Equiv.Perm VertexId
  /-- Whole-graph vertices agreement (outer contract-with-stars = relabeled corrected quotient contract-with-stars). -/
  vertices_eq : ∀ {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G),
    (q.1.1.1.contractWithStars (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices
      = (((canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1).contractWithStars
          (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
            (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
            (canonicalCorrectedQuotientRaw Measure
              canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
              canonicalUniqueStarFactsOfW' q.1))).mapPerm (starPerm q)).vertices
  /-- Whole-graph internal-edges agreement. -/
  internalEdges_eq : ∀ {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G),
    (q.1.1.1.contractWithStars (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)).internalEdges
      = (((canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1).contractWithStars
          (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
            (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
            (canonicalCorrectedQuotientRaw Measure
              canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
              canonicalUniqueStarFactsOfW' q.1))).mapPerm (starPerm q)).internalEdges
  /-- Whole-graph external-legs agreement. -/
  externalLegs_eq : ∀ {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G),
    (q.1.1.1.contractWithStars (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)).externalLegs
      = (((canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1).contractWithStars
          (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
            (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
            (canonicalCorrectedQuotientRaw Measure
              canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
              canonicalUniqueStarFactsOfW' q.1))).mapPerm (starPerm q)).externalLegs

/-- **R-6c-body-512 ∎ — the field socket → body-511's class-equality socket.**  The three whole-graph field equalities give
the contract-with-stars class equality (`toResolvedClass_eq_of_mapPerm_fields`), hence `quot_eq`. -/
noncomputable def ResolvedCanonicalFilteredContractTwiceFieldSupply.toContractClassEqSupply
    {Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData}
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (C : ResolvedCanonicalFilteredContractTwiceFieldSupply Measure E) :
    ResolvedCanonicalFilteredContractClassEqSupply Measure E where
  contract_class_eq := fun {_G} q =>
    ResolvedFeynmanGraph.toResolvedClass_eq_of_mapPerm_fields (C.starPerm q)
      (C.vertices_eq q) (C.internalEdges_eq q) (C.externalLegs_eq q)

end GaugeGeometry.QFT.Combinatorial
