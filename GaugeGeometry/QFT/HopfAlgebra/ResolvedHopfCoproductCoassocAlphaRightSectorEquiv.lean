import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaQuotientSectorEquiv
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorIndexBridge

/-!
# R-6c-body-516 — q-local right sector `Equiv` inhabitant (PROVED)

Five-hundred-and-sixteenth genuine-body step — discharging body-515's `rightEquiv` field to a canonical theorem: the
right-primitive one-stage stars biject with the corrected quotient's right-survivor components, over a FILTERED `q` only.

`canonicalCorrectedRightSectorEquiv Measure q : RightPrimitiveIndex … q.1 ≃ {δ // δ ∈ rightSurvivorForest … q.1}`

* `toFun` — `RightPrimitiveIndex.toRightComponent` then `survivorSupply_of_measure … .survivorComponent`, landing in the
  `rightSurvivorForest` image;
* injective — body-498's `survivorInj_of_measure` directly (NO ID-uniqueness / global-gap re-proof), lifted by
  `Subtype.ext`;
* surjective — the `rightSurvivorForest` image membership recovers the primitive witness (`Finset.mem_image`), matched by
  `Subtype.ext`.

The forest sector and the full body-515 supply / correspondence are NOT entered (body-517+).

Per the HALT/guards: ID-uniqueness / global-gap are NOT re-proved; the owner domain is the FILTERED `q` only; local
`promotedStarCorrectingPerm` is NOT touched; no `corrected = uncorrected` equality; the full supply / vertex
correspondence / σ are NOT entered; `quot_eq` / `ValueGeometry` are NOT entered; strict `StarProm` / `InnerStarRaw` stay
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

/-- **R-6c-body-516 — the structural equivalence** `RightPrimitiveIndex ≃ rightComponents` (both directions `rfl`). -/
noncomputable def rightPrimitiveIndexEquivComponents
    {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice canonicalUniqueSupportedCarrierProperSupply.toData G) :
    RightPrimitiveIndex canonicalUniqueSupportedCarrierProperSupply.toData G s
      ≃ {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents} where
  toFun := fun r => r.toRightComponent
  invFun := fun c => ⟨⟨c.1.1, c.1.2⟩, (Finset.mem_filter.mp c.2).2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- **R-6c-body-516 — the survivor image equivalence** `rightComponents ≃ rightSurvivorForest components`
(`survivorComponent` injective by body-498, surjective by the image). -/
noncomputable def rightComponentsEquivSurvivor
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) :
    {x : {y : ResolvedFeynmanSubgraph G // y ∈ q.1.1.1.elements} // x ∈ ResolvedCoassocSplitChoice.rightComponents q.1}
      ≃ {δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) //
          δ ∈ ((survivorSupply_of_measure Measure G).rightSurvivorForest q.1).elements} where
  toFun := fun c =>
    ⟨(survivorSupply_of_measure Measure G).survivorComponent q.1 c, by
      rw [ResolvedRightSurvivorSupply.rightSurvivorForest_elements]
      exact Finset.mem_image.mpr ⟨c, Finset.mem_attach _ _, rfl⟩⟩
  invFun := fun δ =>
    (Finset.mem_image.mp (show δ.1 ∈ (ResolvedCoassocSplitChoice.rightComponents q.1).attach.image
        ((survivorSupply_of_measure Measure G).survivorComponent q.1) by
      rw [← ResolvedRightSurvivorSupply.rightSurvivorForest_elements]; exact δ.2)).choose
  left_inv := fun c => by
    have h : ((survivorSupply_of_measure Measure G).survivorComponent q.1 c)
        ∈ (ResolvedCoassocSplitChoice.rightComponents q.1).attach.image
          ((survivorSupply_of_measure Measure G).survivorComponent q.1) := by
      rw [← ResolvedRightSurvivorSupply.rightSurvivorForest_elements]
      rw [ResolvedRightSurvivorSupply.rightSurvivorForest_elements]
      exact Finset.mem_image.mpr ⟨c, Finset.mem_attach _ _, rfl⟩
    obtain ⟨hmem, hspec⟩ := (Finset.mem_image.mp h).choose_spec
    exact survivorInj_of_measure Measure q.1 (Finset.mem_image.mp h).choose hmem c
      (Finset.mem_attach _ _) hspec
  right_inv := fun δ => Subtype.ext (Finset.mem_image.mp
    (show δ.1 ∈ (ResolvedCoassocSplitChoice.rightComponents q.1).attach.image
        ((survivorSupply_of_measure Measure G).survivorComponent q.1) by
      rw [← ResolvedRightSurvivorSupply.rightSurvivorForest_elements]; exact δ.2)).choose_spec.2

/-- **R-6c-body-516 ∎ — the q-local right sector equivalence** (body-515's `rightEquiv` field, discharged). -/
noncomputable def canonicalCorrectedRightSectorEquiv
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) :
    RightPrimitiveIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1
      ≃ {δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) //
          δ ∈ ((survivorSupply_of_measure Measure G).rightSurvivorForest q.1).elements} :=
  (rightPrimitiveIndexEquivComponents q.1).trans (rightComponentsEquivSurvivor Measure q)

end GaugeGeometry.QFT.Combinatorial
