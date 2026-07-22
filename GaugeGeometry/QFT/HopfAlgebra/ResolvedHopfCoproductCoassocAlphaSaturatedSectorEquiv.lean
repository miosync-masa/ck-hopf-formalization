import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSaturatedConstructionRoot
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaCorrectedQuotientImage
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRightSectorEquiv
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaForestSectorEquiv
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaQuotientSectorEquiv

/-!
# R-6c-body-542 — the `W″` q-local corrected-quotient sector equivalences (PROVED)

Five-hundred-and-forty-second genuine-body step — the FIRST of the `W″` re-key campaign (542 image + sector / 543
star-recovery + left + partition / 544 three-route / 545 global-`σ` + field + `quot_eq` / 546 occurrence + round-trip +
final wrapper).  This body re-issues the image / sector-equivalence owner for `W″` by reading the single construction
owner `R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E` (body-541), re-keying bodies 514–517 from `W′` to
`W″`.

**NEW GEOMETRY = ZERO.**  The sector geometry is body-514–517's, re-issued in the `W″` owner's coordinates.  Every
substitution is mechanical: `canonicalUniqueSupportedCarrierProperSupply → canonicalLegSaturatedCarrierProperSupply`,
`canonicalUniqueStarFactsOfW' → canonicalLegSaturatedStarFacts`, and the filtered-mem supply is read off
`R.Fmem` (= body-534's `canonicalLegSaturatedSelectedOuterFilteredMemSupply_of_measure R.Measure E`).  All the sector
helper lemmas (`survivorInj_of_measure`, `survivorSupply_of_measure`, `canonicalCorrectedRemnantComponentSupply`,
`correctedRemnantComponent_forestOccurrence_injective`, `canonicalCorrectedSurvivorRemnant_elements_disjoint`,
`RightPrimitiveIndex` / `ForestPrimitiveIndex` / `OneStageStarIndex`, `quotientDomainEquiv`,
`disjointUnionSubtypeEquiv`, the `rightSurvivorForest_elements` / `remnantForest_elements` image lemmas, and the
`rightComponents` / `forestComponents` / `forestComponentOccurrence` split geometry) are D-GENERIC and apply UNCHANGED
with the `W″` `Measure` / `Fstar` / `CarrierProper`.

## Deliverables

* **Step 1 — `canonicalLegSaturatedCorrectedQuotientImage R q`** — the `W″` corrected quotient image (body-514
  re-key), plus its three `rfl` projection anchors.  The carrier tag is `R.Fmem.mem_of_mem_forestBlockDomFinset`; the
  quotient value is `canonicalCorrectedQuotientRaw R.Measure … canonicalLegSaturatedStarFacts q.1`.  `R.quotient_mem`
  is NOT read (the image VALUE does not need it).
* **Step 2 — structural primitive-index equivalences** (`legSaturatedRightPrimitiveIndexEquivComponents` /
  `legSaturatedForestPrimitiveIndexEquivComponents`, both directions `rfl`).
* **Step 3 — image equivalences** (`legSaturatedRightComponentsEquivSurvivor` /
  `legSaturatedForestComponentsEquivRemnant`, injective by body-498 / body-466, surjective by the image).
* **Step 4 — q-local sector equivs + supply** (`canonicalLegSaturatedRightSectorEquiv` /
  `canonicalLegSaturatedForestSectorEquiv`; the re-keyed
  `ResolvedCanonicalLegSaturatedFilteredQuotientSectorEquivSupply` with `codomainEquiv` / `quotientStarEquiv`).
* **Step 5 — the canonical inhabitant** (`canonicalLegSaturatedCorrectedQuotientSectorEquivSupply R` reading the SAME
  `R.Measure` owner, and `canonicalLegSaturatedCorrectedQuotientStarEquiv R q` — the non-left star's unique
  destination).

Per the HALT/guards: NO star-vertex recovery / left route / partition / three-route / whole-vertex correspondence /
global `σ` / `quot_eq` (later bodies 543–546); NO `W′`↔`W″` `q` adapter / cast; nothing reverse-engineered from
`R.quotient_mem`; local permutations are NOT compared; no strict sockets; the D-generic helpers are reused directly
with the `W″` `Measure` / `Fstar` / `CarrierProper` and NO `W′` decl is modified; strict `StarProm` / `InnerStarRaw`
stay ZERO; NO unconditional-coassoc claim.  No facade, no flat term, no `forgetHopf`, no rep/perm.
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

/-! ## Step 1 — the `W″` corrected quotient image (body-514 `canonicalCorrectedQuotientImage` re-key). -/

/-- **R-6c-body-542 ∎ — the `W″` canonical corrected quotient image at a filtered `q`.**  Membership from the
construction owner's `R.Fmem` (= body-534's `canonicalLegSaturatedSelectedOuterFilteredMemSupply_of_measure`); the
quotient value is `canonicalCorrectedQuotientRaw R.Measure … canonicalLegSaturatedStarFacts`.  `R.quotient_mem` is NOT
read — the image VALUE construction does not need it. -/
noncomputable def canonicalLegSaturatedCorrectedQuotientImage
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G) :
    ResolvedCoassocQuotientImage canonicalLegSaturatedCarrierProperSupply.toData G :=
  ⟨⟨(resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf q.1,
      R.Fmem.mem_of_mem_forestBlockDomFinset q.1 q.2⟩,
    canonicalCorrectedQuotientRaw R.Measure
      canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
      canonicalLegSaturatedStarFacts q.1⟩

/-- **R-6c-body-542 — projection: the image's selected outer is the raw selected outer** (`rfl`). -/
theorem canonicalLegSaturatedCorrectedQuotientImage_selectedOuter
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G) :
    (canonicalLegSaturatedCorrectedQuotientImage R q).selectedOuter.1
      = (resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf q.1 :=
  rfl

/-- **R-6c-body-542 — projection: the image's quotient forest is the corrected quotient** (`rfl`). -/
theorem canonicalLegSaturatedCorrectedQuotientImage_quotientForest
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G) :
    (canonicalLegSaturatedCorrectedQuotientImage R q).quotientForest
      = canonicalCorrectedQuotientRaw R.Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1 :=
  rfl

/-- **R-6c-body-542 — projection: the image's quotient graph is the selected-outer contract graph** (`rfl`). -/
theorem canonicalLegSaturatedCorrectedQuotientImage_quotientGraph
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G) :
    resolvedCoassocQuotientGraph (canonicalLegSaturatedCorrectedQuotientImage R q)
      = ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1 :=
  rfl

/-! ## Step 2 — the structural primitive-index equivalences (body-516/517 re-key, both directions `rfl`). -/

/-- **R-6c-body-542 — the structural equivalence** `RightPrimitiveIndex ≃ rightComponents` (both directions `rfl`). -/
noncomputable def legSaturatedRightPrimitiveIndexEquivComponents
    {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice canonicalLegSaturatedCarrierProperSupply.toData G) :
    RightPrimitiveIndex canonicalLegSaturatedCarrierProperSupply.toData G s
      ≃ {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents} where
  toFun := fun r => r.toRightComponent
  invFun := fun c => ⟨⟨c.1.1, c.1.2⟩, (Finset.mem_filter.mp c.2).2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- **R-6c-body-542 — the structural equivalence** `ForestPrimitiveIndex ≃ forestComponents` (both directions `rfl`). -/
noncomputable def legSaturatedForestPrimitiveIndexEquivComponents
    {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice canonicalLegSaturatedCarrierProperSupply.toData G) :
    ForestPrimitiveIndex canonicalLegSaturatedCarrierProperSupply.toData G s
      ≃ {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.forestComponents} where
  toFun := fun f => ⟨f.i.toComponent, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, f.hF⟩⟩
  invFun := fun c => ⟨⟨c.1.1, c.1.2⟩, (Finset.mem_filter.mp c.2).2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-! ## Step 3 — the image equivalences (body-516/517 re-key; injective by body-498/466, surjective by the image). -/

/-- **R-6c-body-542 — the survivor image equivalence** `rightComponents ≃ rightSurvivorForest components`
(`survivorComponent` injective by body-498, surjective by the image). -/
noncomputable def legSaturatedRightComponentsEquivSurvivor
    (Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G) :
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

/-- **R-6c-body-542 — the remnant image equivalence** `forestComponents ≃ remnant components`
(`correctedRemnantComponent ∘ forestComponentOccurrence` injective by body-466, surjective by the image). -/
noncomputable def legSaturatedForestComponentsEquivRemnant
    (Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G) :
    {x : {y : ResolvedFeynmanSubgraph G // y ∈ q.1.1.1.elements} // x ∈ ResolvedCoassocSplitChoice.forestComponents q.1}
      ≃ {δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) //
          δ ∈ ((canonicalCorrectedRemnantComponentSupply canonicalLegSaturatedStarFacts
              canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider).remnantForest q.1).elements} where
  toFun := fun γ =>
    ⟨(canonicalCorrectedRemnantComponentSupply canonicalLegSaturatedStarFacts
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1
        (ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 γ), by
      rw [ResolvedRemnantComponentSupply.remnantForest_elements]
      exact Finset.mem_image.mpr ⟨γ, Finset.mem_attach _ _, rfl⟩⟩
  invFun := fun δ =>
    (Finset.mem_image.mp (show δ.1 ∈ (ResolvedCoassocSplitChoice.forestComponents q.1).attach.image
        (fun γ => (canonicalCorrectedRemnantComponentSupply canonicalLegSaturatedStarFacts
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1
          (ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 γ)) by
      rw [← ResolvedRemnantComponentSupply.remnantForest_elements]; exact δ.2)).choose
  left_inv := fun γ => by
    have h : ((canonicalCorrectedRemnantComponentSupply canonicalLegSaturatedStarFacts
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1
          (ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 γ))
        ∈ (ResolvedCoassocSplitChoice.forestComponents q.1).attach.image
          (fun γ => (canonicalCorrectedRemnantComponentSupply canonicalLegSaturatedStarFacts
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1
            (ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 γ)) := by
      rw [← ResolvedRemnantComponentSupply.remnantForest_elements,
        ResolvedRemnantComponentSupply.remnantForest_elements]
      exact Finset.mem_image.mpr ⟨γ, Finset.mem_attach _ _, rfl⟩
    exact correctedRemnantComponent_forestOccurrence_injective q.1 canonicalLegSaturatedStarFacts
      canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
      (Finset.mem_image.mp h).choose_spec.2
  right_inv := fun δ => Subtype.ext (Finset.mem_image.mp
    (show δ.1 ∈ (ResolvedCoassocSplitChoice.forestComponents q.1).attach.image
        (fun γ => (canonicalCorrectedRemnantComponentSupply canonicalLegSaturatedStarFacts
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider).remnantComponent q.1
          (ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 γ)) by
      rw [← ResolvedRemnantComponentSupply.remnantForest_elements]; exact δ.2)).choose_spec.2

/-! ## Step 4 — the q-local sector equivalences + the re-keyed faithful sector supply. -/

/-- **R-6c-body-542 ∎ — the q-local right sector equivalence** (`W″` re-key of body-516). -/
noncomputable def canonicalLegSaturatedRightSectorEquiv
    (Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G) :
    RightPrimitiveIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1
      ≃ {δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) //
          δ ∈ ((survivorSupply_of_measure Measure G).rightSurvivorForest q.1).elements} :=
  (legSaturatedRightPrimitiveIndexEquivComponents q.1).trans (legSaturatedRightComponentsEquivSurvivor Measure q)

/-- **R-6c-body-542 ∎ — the q-local forest sector equivalence** (`W″` re-key of body-517). -/
noncomputable def canonicalLegSaturatedForestSectorEquiv
    (Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G) :
    ForestPrimitiveIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1
      ≃ {δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) //
          δ ∈ ((canonicalCorrectedRemnantComponentSupply canonicalLegSaturatedStarFacts
              canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider).remnantForest q.1).elements} :=
  (legSaturatedForestPrimitiveIndexEquivComponents q.1).trans (legSaturatedForestComponentsEquivRemnant Measure q)

/-- **R-6c-body-542 — the faithful q-local `W″` sector equivalence supply** (body-515 re-key; the two sector
bijections, with the codomain split and quotient-star equivalence derived). -/
structure ResolvedCanonicalLegSaturatedFilteredQuotientSectorEquivSupply
    (Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H) where
  /-- The right-survivor sector bijection (over the filtered `q`). -/
  rightEquiv : ∀ {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G),
    RightPrimitiveIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1
      ≃ {δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) //
          δ ∈ ((survivorSupply_of_measure Measure G).rightSurvivorForest q.1).elements}
  /-- The remnant sector bijection (over the filtered `q`). -/
  forestEquiv : ∀ {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G),
    ForestPrimitiveIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1
      ≃ {δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) //
          δ ∈ ((canonicalCorrectedRemnantComponentSupply canonicalLegSaturatedStarFacts
              canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider).remnantForest q.1).elements}

namespace ResolvedCanonicalLegSaturatedFilteredQuotientSectorEquivSupply

variable {Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData}
  {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}

/-- **R-6c-body-542 ∎ — the DERIVED codomain split** (`disjointUnionSubtypeEquiv` at body-469's disjointness). -/
noncomputable def codomainEquiv (_C : ResolvedCanonicalLegSaturatedFilteredQuotientSectorEquivSupply Measure E)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G) :
    {δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) //
        δ ∈ (canonicalCorrectedQuotientRaw Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1).elements}
      ≃ ({δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) //
            δ ∈ ((survivorSupply_of_measure Measure G).rightSurvivorForest q.1).elements}
        ⊕ {δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) //
            δ ∈ ((canonicalCorrectedRemnantComponentSupply canonicalLegSaturatedStarFacts
                canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider).remnantForest q.1).elements}) :=
  (Equiv.subtypeEquivRight (fun δ => by
      simp only [canonicalCorrectedQuotientRaw, ResolvedAdmissibleSubgraph.union_elements,
        Finset.mem_union])).trans
    (disjointUnionSubtypeEquiv
      (canonicalCorrectedSurvivorRemnant_elements_disjoint canonicalLegSaturatedStarFacts Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider q.1))

/-- **R-6c-body-542 ∎ — the faithful q-local quotient-star equivalence** (mirror of `quotientStarEquivOf`, no `∀ s`). -/
noncomputable def quotientStarEquiv (C : ResolvedCanonicalLegSaturatedFilteredQuotientSectorEquivSupply Measure E)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G) :
    {i : OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1 // i.hasQuotientStar}
      ≃ {δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) //
          δ ∈ (canonicalCorrectedQuotientRaw Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
            canonicalLegSaturatedStarFacts q.1).elements} :=
  (quotientDomainEquiv q.1).trans
    (((C.rightEquiv q).sumCongr (C.forestEquiv q)).trans (C.codomainEquiv q).symm)

end ResolvedCanonicalLegSaturatedFilteredQuotientSectorEquivSupply

/-! ## Step 5 — the canonical inhabitant reading the SAME `R` owner. -/

/-- **R-6c-body-542 ∎ — the canonical `W″` sector supply, INHABITED** (reading `R.Measure`). -/
noncomputable def canonicalLegSaturatedCorrectedQuotientSectorEquivSupply
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) :
    ResolvedCanonicalLegSaturatedFilteredQuotientSectorEquivSupply R.Measure E where
  rightEquiv := fun q => canonicalLegSaturatedRightSectorEquiv R.Measure q
  forestEquiv := fun q => canonicalLegSaturatedForestSectorEquiv R.Measure q

/-- **R-6c-body-542 ∎ — the completed q-local `W″` quotient-star equivalence** (the non-left star's unique
destination), reading the SAME `R.Measure` owner. -/
noncomputable def canonicalLegSaturatedCorrectedQuotientStarEquiv
    {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}
    (R : ResolvedCanonicalLegSaturatedAlphaConstructionSupply E) {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G) :
    {i : OneStageStarIndex canonicalLegSaturatedCarrierProperSupply.toData G q.1 // i.hasQuotientStar}
      ≃ {δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) //
          δ ∈ (canonicalCorrectedQuotientRaw R.Measure
            canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
            canonicalLegSaturatedStarFacts q.1).elements} :=
  (canonicalLegSaturatedCorrectedQuotientSectorEquivSupply R).quotientStarEquiv q

end GaugeGeometry.QFT.Combinatorial
