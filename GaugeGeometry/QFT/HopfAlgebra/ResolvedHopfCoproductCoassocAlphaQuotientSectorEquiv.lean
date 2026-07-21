import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaCorrectedQuotientImage
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientStarCodomain
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCorrectedQuotientOwnershipAudit

/-!
# R-6c-body-515 — q-local corrected quotient sector equivalences (codomain + assembly) (PROVED)

Five-hundred-and-fifteenth genuine-body step — the combinatorial-heart assembly, built ENTIRELY q-local: the quotient-star
equivalence between the non-left one-stage stars and the corrected quotient's components, with NO raw `∀ s` image/quotient
ownership (the `imageOf`-parameterized `TwoStageStarIndex` machinery would force totality; the q-local subtype
`{δ // δ ∈ (canonicalCorrectedQuotientRaw q.1).elements}` avoids it).

## The faithful q-local sector supply

`ResolvedCanonicalFilteredQuotientSectorEquivSupply Measure E` — the two genuine sector bijections over a FILTERED `q`:

* `rightEquiv q : RightPrimitiveIndex … q.1 ≃ {δ // δ ∈ (survivorSupply_of_measure Measure G).rightSurvivorForest q.1}`
  (the right-survivor sector — `survivorInj_of_measure`, body-498, the residual);
* `forestEquiv q : ForestPrimitiveIndex … q.1 ≃ {δ // δ ∈ (canonicalCorrectedRemnantComponentSupply …).remnantForest q.1}`
  (the remnant sector — `correctedRemnantComponent_forestOccurrence_injective`, body-466, the residual).

## The DERIVED codomain split + quotient-star equivalence (this body)

* `codomainEquiv q` — the `Right ⊔ Remnant` split of the corrected quotient's components, `disjointUnionSubtypeEquiv` fed
  body-469's `canonicalCorrectedSurvivorRemnant_elements_disjoint` (the survivor/remnant element sets are disjoint;
  `canonicalCorrectedQuotientRaw = survivor.union remnant` so `.elements = survivor ∪ remnant`).  NO `p_L` stand-in.
* `quotientStarEquiv q` — `quotientDomainEquiv q.1` ∘ `(rightEquiv q).sumCongr (forestEquiv q)` ∘ `(codomainEquiv q).symm`
  — the faithful q-local mirror of `quotientStarEquivOf`, `{i // i.hasQuotientStar} ≃ {δ // δ ∈ corrected quotient}`.

The two sector `Equiv`s are the sole residual (`rightEquiv` INJECTIVE from `survivorInj_of_measure`, SURJECTIVE from the
`rightSurvivorForest` image; `forestEquiv` INJECTIVE from `correctedRemnantComponent_forestOccurrence_injective`,
SURJECTIVE from the `remnantForest` image — every owner domain the FILTERED `q` only).  They are named, NOT built here.

Per the HALT/guards: no raw `∀ s` quotient/image ownership (the `imageOf`-`TwoStageStarIndex` path is avoided — the target
is the q-local component subtype); local `promotedStarCorrectingPerm` is NOT composed; no equality between distinct local
permutations; the family geometry is NOT reduced to bare `mapPerm` invariance; nothing is back-computed from coassoc /
`rightTerm`; the two sector `Equiv`s are named residuals (NOT claimed derived); `quot_eq` / `ValueGeometry` are NOT
entered; strict `StarProm` / `InnerStarRaw` stay ZERO; the legacy `∀ s` sector supplies are NOT inhabited.  No facade, no
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

/-- **R-6c-body-515 — the faithful q-local sector equivalence supply** (the two sector bijections; the codomain split and
the quotient-star equivalence are derived). -/
structure ResolvedCanonicalFilteredQuotientSectorEquivSupply
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H) where
  /-- The right-survivor sector bijection (over the filtered `q`). -/
  rightEquiv : ∀ {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G),
    RightPrimitiveIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1
      ≃ {δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) //
          δ ∈ ((survivorSupply_of_measure Measure G).rightSurvivorForest q.1).elements}
  /-- The remnant sector bijection (over the filtered `q`). -/
  forestEquiv : ∀ {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G),
    ForestPrimitiveIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1
      ≃ {δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) //
          δ ∈ ((canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
              canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantForest q.1).elements}

namespace ResolvedCanonicalFilteredQuotientSectorEquivSupply

variable {Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData}
  {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}

/-- **R-6c-body-515 ∎ — the DERIVED codomain split** (`disjointUnionSubtypeEquiv` at body-469's disjointness). -/
noncomputable def codomainEquiv (_C : ResolvedCanonicalFilteredQuotientSectorEquivSupply Measure E)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) :
    {δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) //
        δ ∈ (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1).elements}
      ≃ ({δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) //
            δ ∈ ((survivorSupply_of_measure Measure G).rightSurvivorForest q.1).elements}
        ⊕ {δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) //
            δ ∈ ((canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
                canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantForest q.1).elements}) :=
  (Equiv.subtypeEquivRight (fun δ => by
      simp only [canonicalCorrectedQuotientRaw, ResolvedAdmissibleSubgraph.union_elements,
        Finset.mem_union])).trans
    (disjointUnionSubtypeEquiv
      (canonicalCorrectedSurvivorRemnant_elements_disjoint canonicalUniqueStarFactsOfW' Measure
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider q.1))

/-- **R-6c-body-515 ∎ — the faithful q-local quotient-star equivalence** (mirror of `quotientStarEquivOf`, no `∀ s`). -/
noncomputable def quotientStarEquiv (C : ResolvedCanonicalFilteredQuotientSectorEquivSupply Measure E)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) :
    {i : OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1 // i.hasQuotientStar}
      ≃ {δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) //
          δ ∈ (canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1).elements} :=
  (quotientDomainEquiv q.1).trans
    (((C.rightEquiv q).sumCongr (C.forestEquiv q)).trans (C.codomainEquiv q).symm)

end ResolvedCanonicalFilteredQuotientSectorEquivSupply

end GaugeGeometry.QFT.Combinatorial
