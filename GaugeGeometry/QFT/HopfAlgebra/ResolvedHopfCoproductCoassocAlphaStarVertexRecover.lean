import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaForestSectorEquiv
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocStarIndexRecover
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocStarVertexPartition

/-!
# R-6c-body-518 — q-local canonical star-vertex recoveries + quotient-star vertex equivalence (PROVED)

Five-hundred-and-eighteenth genuine-body step — lifting body-517's component-level `quotientStarEquiv` to the vertex level,
so the next body's three-route correspondence sees a single bijection, not a case split.  Both recoveries reuse the generic
`resolvedStarVertexEquivIndex` (star vertices ↔ components under an injective `starOf`); NO legacy `imageOf` /
`TwoStageStarIndex` total family.

* `canonicalOneStageStarRecover q : {v // isContractStarVertex q.1.1.1 (starOf) v} ≃ OneStageStarIndex … q.1` —
  `resolvedStarVertexEquivIndex` at the input outer (`starOf_injective` from `canonicalUniqueStarFactsOfW'`) then the
  structural `oneStageStarIndexEquivSubtype`;
* `canonicalCorrectedTwoStageStarRecover q : {w // isContractStarVertex (corrected quotient) (corrected star) w} ≃
  {δ // δ ∈ corrected quotient}` — `resolvedStarVertexEquivIndex` at the corrected quotient (same injectivity), directly
  on the q-local component subtype (no `TwoStageStarIndex`/`imageOf`);
* `canonicalCorrectedQuotientStarVertexEquiv q` — body-517's `quotientStarEquiv` ∘ `(two-stage recover).symm`:
  `{i // i.hasQuotientStar} ≃ {w // isContractStarVertex (corrected quotient) (corrected star) w}`, the non-left star's
  destination star vertex.

The three-route partition (`survivingOriginal_to` / `leftStar_toSurvivor` / `twoStageSurvivor_cases`) and the full vertex
correspondence are NOT entered (body-519+).

Per the HALT/guards: no raw `imageOf` / `TwoStageStarIndex` total family is revived; `q`'s filtered membership is read once;
local correcting permutations are NOT used / compared / composed; no `corrected = uncorrected` graph equality; `quot_eq` /
global `σ` / field equalities are NOT entered; strict `StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc
claim.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-518 ∎ — the one-stage star-vertex recovery.**  `{v // contract star of the input outer} ≃
OneStageStarIndex`. -/
noncomputable def canonicalOneStageStarRecover {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) :
    {v : VertexId // isContractStarVertex q.1.1.1
        (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v}
      ≃ OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1 :=
  (resolvedStarVertexEquivIndex q.1.1.1
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)
      (fun γ₁ h₁ γ₂ h₂ heq =>
        canonicalUniqueStarFactsOfW'.starOf_injective G q.1.1.1 h₁ h₂ heq)).trans
    (oneStageStarIndexEquivSubtype q.1).symm

/-- **R-6c-body-518 ∎ — the corrected two-stage star-vertex recovery.**  `{w // contract star of the corrected quotient}
≃ corrected quotient components` — directly on the q-local subtype, no `TwoStageStarIndex`. -/
noncomputable def canonicalCorrectedTwoStageStarRecover
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) :
    {w : VertexId // isContractStarVertex
        (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1)
        (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
          (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
          (canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1)) w}
      ≃ {δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) //
          δ ∈ (canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1).elements} :=
  resolvedStarVertexEquivIndex
    (canonicalCorrectedQuotientRaw Measure
      canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
      canonicalUniqueStarFactsOfW' q.1)
    (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
      (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
      (canonicalCorrectedQuotientRaw Measure
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
        canonicalUniqueStarFactsOfW' q.1))
    (fun γ₁ h₁ γ₂ h₂ heq =>
      canonicalUniqueStarFactsOfW'.starOf_injective
        (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
        (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1) h₁ h₂ heq)

/-- **R-6c-body-518 ∎ — the completed quotient-star VERTEX equivalence** (non-left star ↦ its corrected-quotient star
vertex). -/
noncomputable def canonicalCorrectedQuotientStarVertexEquiv
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) :
    {i : OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1 // i.hasQuotientStar}
      ≃ {w : VertexId // isContractStarVertex
          (canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1)
          (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
            (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
            (canonicalCorrectedQuotientRaw Measure
              canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
              canonicalUniqueStarFactsOfW' q.1)) w} :=
  (canonicalCorrectedQuotientStarEquiv Measure E q).trans
    (canonicalCorrectedTwoStageStarRecover Measure q).symm

end GaugeGeometry.QFT.Combinatorial
