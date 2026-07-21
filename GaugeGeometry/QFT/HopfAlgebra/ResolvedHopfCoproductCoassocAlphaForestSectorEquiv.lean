import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRightSectorEquiv
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCorrectedRemnantSupplyBuild

/-!
# R-6c-body-517 — q-local corrected forest sector `Equiv` + canonical supply (PROVED)

Five-hundred-and-seventeenth genuine-body step — discharging body-515's last field `forestEquiv` to a canonical theorem and
INHABITING the sector supply, closing the socket.  The forest-choice one-stage stars biject with the corrected quotient's
remnant components, over a FILTERED `q` only — the same two-step shape as body-516's right sector.

* `forestPrimitiveIndexEquivComponents s : ForestPrimitiveIndex ≃ forestComponents` (both directions `rfl`);
* `forestComponentsEquivRemnant Measure q : forestComponents ≃ remnant components` (`correctedRemnantComponent ∘
  forestComponentOccurrence` — injective by body-466 `correctedRemnantComponent_forestOccurrence_injective`, surjective by
  the `remnantForest` image);
* `canonicalCorrectedForestSectorEquiv` := the `.trans`;
* `canonicalCorrectedQuotientSectorEquivSupply Measure E` := `⟨body-516, body-517⟩` — body-515's supply, INHABITED;
* `canonicalCorrectedQuotientStarEquiv Measure E q` := the supply's `quotientStarEquiv` — the completed q-local bijection
  `{i // i.hasQuotientStar} ≃ {δ // δ ∈ corrected quotient}`, the non-left star's unique destination.

The full vertex correspondence / three-route point laws / global `σ` / whole-graph field equalities / `quot_eq` are NOT
entered (next body).

Per the HALT/guards: injectivity source is body-466, surjectivity source the `remnantForest` image, owner domain the
FILTERED `q` only; no full vertex correspondence / three-route point laws / global `σ` / whole-graph field equality /
`quot_eq`; no raw `∀ s` supply; local permutations are NOT compared or composed; no `corrected = uncorrected` graph
equality; strict `StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc claim.  No facade, no flat term, no
`forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-517 — the structural equivalence** `ForestPrimitiveIndex ≃ forestComponents` (both directions `rfl`). -/
noncomputable def forestPrimitiveIndexEquivComponents
    {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice canonicalUniqueSupportedCarrierProperSupply.toData G) :
    ForestPrimitiveIndex canonicalUniqueSupportedCarrierProperSupply.toData G s
      ≃ {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.forestComponents} where
  toFun := fun f => ⟨f.i.toComponent, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, f.hF⟩⟩
  invFun := fun c => ⟨⟨c.1.1, c.1.2⟩, (Finset.mem_filter.mp c.2).2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- **R-6c-body-517 — the remnant image equivalence** `forestComponents ≃ remnant components`
(`correctedRemnantComponent ∘ forestComponentOccurrence` injective by body-466, surjective by the image). -/
noncomputable def forestComponentsEquivRemnant
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) :
    {x : {y : ResolvedFeynmanSubgraph G // y ∈ q.1.1.1.elements} // x ∈ ResolvedCoassocSplitChoice.forestComponents q.1}
      ≃ {δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) //
          δ ∈ ((canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
              canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantForest q.1).elements} where
  toFun := fun γ =>
    ⟨(canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1
        (ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 γ), by
      rw [ResolvedRemnantComponentSupply.remnantForest_elements]
      exact Finset.mem_image.mpr ⟨γ, Finset.mem_attach _ _, rfl⟩⟩
  invFun := fun δ =>
    (Finset.mem_image.mp (show δ.1 ∈ (ResolvedCoassocSplitChoice.forestComponents q.1).attach.image
        (fun γ => (canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1
          (ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 γ)) by
      rw [← ResolvedRemnantComponentSupply.remnantForest_elements]; exact δ.2)).choose
  left_inv := fun γ => by
    have h : ((canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1
          (ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 γ))
        ∈ (ResolvedCoassocSplitChoice.forestComponents q.1).attach.image
          (fun γ => (canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1
            (ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 γ)) := by
      rw [← ResolvedRemnantComponentSupply.remnantForest_elements,
        ResolvedRemnantComponentSupply.remnantForest_elements]
      exact Finset.mem_image.mpr ⟨γ, Finset.mem_attach _ _, rfl⟩
    exact correctedRemnantComponent_forestOccurrence_injective q.1 canonicalUniqueStarFactsOfW'
      canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
      (Finset.mem_image.mp h).choose_spec.2
  right_inv := fun δ => Subtype.ext (Finset.mem_image.mp
    (show δ.1 ∈ (ResolvedCoassocSplitChoice.forestComponents q.1).attach.image
        (fun γ => (canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1
          (ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 γ)) by
      rw [← ResolvedRemnantComponentSupply.remnantForest_elements]; exact δ.2)).choose_spec.2

/-- **R-6c-body-517 ∎ — the q-local forest sector equivalence** (body-515's `forestEquiv` field, discharged). -/
noncomputable def canonicalCorrectedForestSectorEquiv
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) :
    ForestPrimitiveIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1
      ≃ {δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) //
          δ ∈ ((canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
              canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantForest q.1).elements} :=
  (forestPrimitiveIndexEquivComponents q.1).trans (forestComponentsEquivRemnant Measure q)

/-- **R-6c-body-517 ∎ — the canonical sector supply, INHABITED** (body-515's socket, closed). -/
noncomputable def canonicalCorrectedQuotientSectorEquivSupply
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H) :
    ResolvedCanonicalFilteredQuotientSectorEquivSupply Measure E where
  rightEquiv := fun q => canonicalCorrectedRightSectorEquiv Measure q
  forestEquiv := fun q => canonicalCorrectedForestSectorEquiv Measure q

/-- **R-6c-body-517 ∎ — the completed q-local quotient-star equivalence** (the non-left star's unique destination). -/
noncomputable def canonicalCorrectedQuotientStarEquiv
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) :
    {i : OneStageStarIndex canonicalUniqueSupportedCarrierProperSupply.toData G q.1 // i.hasQuotientStar}
      ≃ {δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) //
          δ ∈ (canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1).elements} :=
  (canonicalCorrectedQuotientSectorEquivSupply Measure E).quotientStarEquiv q

end GaugeGeometry.QFT.Combinatorial
