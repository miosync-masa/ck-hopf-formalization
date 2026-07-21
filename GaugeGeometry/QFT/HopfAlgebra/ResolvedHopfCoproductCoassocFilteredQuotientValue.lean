import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCorrectedQuotientOwnershipAudit

/-!
# R-6c-body-469 — the faithful filtered quotient value root (IMPLEMENTATION)

Four-hundred-and-sixty-ninth genuine-body step — NOT a mathematics body: it fixes the explicit corrected quotient value
and the faithful FILTERED quotient-ownership interface, retyping the two genuinely-owned fields (`quotient_mem`,
`quot_eq`) to a filtered `q` (the body-468 no-go: a `∀ raw q` version is inconsistent with the canonical `W'`).  The `W'`
five-condition proof stays honest ownership — it is NOT proved here.

* `canonicalCorrectedQuotientRaw` — the explicit quotient value `(rightSurvivorForest s).union (remnantForest s)`
  (the cross is body-467, the element-disjointness body-468); no membership needed;
* `ResolvedFilteredQuotientOwnershipSupply` — the two honest quotient-owned fields `quotient_mem` / `quot_eq`, both over a
  FILTERED `q` (every quotient-owned field is filtered — leaving one raw would reinstate the defect);
* `ResolvedFilteredQuotientOwnershipSupply.quotientForestRaw` / `.union_eq` — DERIVED (def / `rfl`), keeping value and
  membership in single ownership.

Per the HALT/guards: NO `W'` five-condition proof for `quotient_mem`; NO contract-twice geometry for `quot_eq`; the OLD
`ResolvedConcreteSummandValueSupply` / body-445 are NOT edited; the new filtered V root superseding + the filtered forward
map are the next body; strict `StarProm` / `InnerStarRaw` NOT used; body-445 stays a valid conditional.  NOT the
unconditional theorem.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton /
floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {D : ResolvedCoproductProperForestData}
  (Measure : ResolvedMeasureLeafSupply D) (CarrierProper : ResolvedCarrierProperProvider D)
  (Fstar : ResolvedCanonicalStarFacts D)

/-- **R-6c-body-469 — the explicit corrected quotient value.**  Survivor ∪ corrected remnant (cross = body-467). -/
noncomputable def canonicalCorrectedQuotientRaw {G : ResolvedFeynmanGraph}
    (s : ResolvedCoassocSplitChoice D G) : ResolvedAdmissibleSubgraph s.selectedOuterContractGraph :=
  ((survivorSupply_of_measure Measure G).rightSurvivorForest s).union
    ((canonicalCorrectedRemnantComponentSupply Fstar CarrierProper).remnantForest s)
    ((canonicalCorrectedQuotientForestCrossSupply Fstar Measure CarrierProper).cross s)

/-- **R-6c-body-469 — the faithful filtered quotient-ownership interface.**  The two honest quotient-owned fields, both
over a FILTERED `q`. -/
structure ResolvedFilteredQuotientOwnershipSupply
    (D : ResolvedCoproductProperForestData) (Measure : ResolvedMeasureLeafSupply D)
    (CarrierProper : ResolvedCarrierProperProvider D) (Fstar : ResolvedCanonicalStarFacts D) where
  /-- The quotient value is a carrier forest of the quotient graph — over a filtered `q` only. -/
  quotient_mem : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G),
    canonicalCorrectedQuotientRaw Measure CarrierProper Fstar q.1
      ∈ D.carrier (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
  /-- The right-term agreement — over a filtered `q` only. -/
  quot_eq : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G),
    (D.supply G).rightTerm q.1.1
      = (D.supply (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)).rightTerm
          ⟨canonicalCorrectedQuotientRaw Measure CarrierProper Fstar q.1, quotient_mem q⟩

/-- **R-6c-body-469 — DERIVED: the quotient forest index** (value + membership in single ownership). -/
noncomputable def ResolvedFilteredQuotientOwnershipSupply.quotientForestRaw
    (Q : ResolvedFilteredQuotientOwnershipSupply D Measure CarrierProper Fstar)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) :
    (D.supply (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)).ForestIdx :=
  ⟨canonicalCorrectedQuotientRaw Measure CarrierProper Fstar q.1, Q.quotient_mem q⟩

/-- **R-6c-body-469 ∎ — DERIVED (`rfl`): the quotient forest is the survivor ∪ remnant union.** -/
theorem ResolvedFilteredQuotientOwnershipSupply.union_eq
    (Q : ResolvedFilteredQuotientOwnershipSupply D Measure CarrierProper Fstar)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) :
    (ResolvedFilteredQuotientOwnershipSupply.quotientForestRaw Measure CarrierProper Fstar Q q).1
      = ((survivorSupply_of_measure Measure G).rightSurvivorForest q.1).union
          ((canonicalCorrectedRemnantComponentSupply Fstar CarrierProper).remnantForest q.1)
          ((canonicalCorrectedQuotientForestCrossSupply Fstar Measure CarrierProper).cross q.1) :=
  rfl

end GaugeGeometry.QFT.Combinatorial
