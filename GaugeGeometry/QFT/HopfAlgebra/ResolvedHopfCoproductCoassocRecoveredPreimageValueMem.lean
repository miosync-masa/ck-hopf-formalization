import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterUnionRegionTagValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFilteredDomMembership

/-!
# R-6c-body-283 — the raw preimage lies in the filtered domain (PROVED)

Two-hundred-and-eighty-third genuine-body step — the branch-agnostic reconstruction `recoveredPreimageValue` (body-282)
lands in `forestBlockDomFinset`.  The preimage VALUE is the same on both branches; only the MEMBERSHIP proof splits on
the classifier `resolvedIsForestImage`:

* **forest** (`resolvedIsForestImage z`): a forest component of `z` injects into `unionOuterValue z`, its
  `recoverChoiceValue` is `inr Bᵧ` (body-282 `forest_tag`), so the choice `isForestCarryingChoice` — membership via
  `mem_forestBlockDomFinset_of_isForestCarrying` (body-256);
* **mixed** (`¬ resolvedIsForestImage z`): the choice is not the all-right `p_R` nor the all-left `p_L` — membership via
  `mem_forestBlockDomFinset_of_ne` (body-256).  `¬ isForestCarrying` is NOT sufficient here; `mixed_ne_pR` /
  `mixed_ne_pL` are the honest classifier leaves (primitive-mixture nontriviality).

## The supply

`ResolvedRecoveredPreimageValueMemSupply F V` carries body-282's tags plus `forest_nonempty` (the forest region is
nonempty on a forest image) and the two mixed inequalities `mixed_ne_pR` / `mixed_ne_pL`.  `.forest_isForestCarrying` /
`.forestPreimage_mem` / `.mixedPreimage_mem` discharge both branches.

Per the HALT: only the filtered-domain membership is proved (both branches); NO round-trip, NO forward reconstruction
(`forward_outer` / `forward_quotient` are body-284 leaves); the value is always `recoveredPreimageValue`.  No `S` /
`Forward` / legacy in any declaration type.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-283 — the raw preimage membership supply.**  Body-282's tags + the forest-nonemptiness and the two
mixed extremal inequalities (honest classifier leaves). -/
structure ResolvedRecoveredPreimageValueMemSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) where
  /-- The value-root region tags (body-282). -/
  Tags : ResolvedRegionTagValueSupply F V
  /-- On a forest image, the forest region is nonempty. -/
  forest_nonempty : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    resolvedIsForestImage z.1 z.2 → (Tags.Closure.Assembly.Region.forestRecovered z).elements.Nonempty
  /-- On a mixed image, the reconstructed choice is not the all-right `p_R` (honest classifier leaf). -/
  mixed_ne_pR : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ¬ resolvedIsForestImage z.1 z.2 →
      (Tags.recoveredPreimageValue z).2 ≠ (fun _ _ => Sum.inl false)
  /-- On a mixed image, the reconstructed choice is not the all-left `p_L` (honest classifier leaf). -/
  mixed_ne_pL : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ¬ resolvedIsForestImage z.1 z.2 →
      (Tags.recoveredPreimageValue z).2 ≠ (fun _ _ => Sum.inl true)

namespace ResolvedRecoveredPreimageValueMemSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-283 — a forest component injects into the outer union.** -/
theorem forestRecovered_mem_unionOuterValue (R : ResolvedRecoveredPreimageValueMemSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) {δ : ResolvedFeynmanSubgraph G}
    (hδ : δ ∈ (R.Tags.Closure.Assembly.Region.forestRecovered z).elements) :
    δ ∈ (R.Tags.Closure.unionOuterValue z).1.elements := by
  simp only [ResolvedRegionValueClosureSupply.unionOuterValue, recoveredRawUnion,
    ResolvedAdmissibleSubgraph.union_elements]
  exact @Finset.mem_union_right _ (Classical.decEq _) _ _ _ hδ

/-- **R-6c-body-283 — the forest branch's `isForestCarryingChoice`.**  From a nonempty forest region + body-282's
`forest_tag` (`inr Bᵧ`). -/
theorem forest_isForestCarrying (R : ResolvedRecoveredPreimageValueMemSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) (h : resolvedIsForestImage z.1 z.2) :
    isForestCarryingChoice (R.Tags.recoveredPreimageValue z).1 (R.Tags.recoveredPreimageValue z).2 := by
  obtain ⟨δ, hδ⟩ := R.forest_nonempty z h
  have hδu : δ ∈ (R.Tags.Closure.unionOuterValue z).1.elements :=
    R.forestRecovered_mem_unionOuterValue z hδ
  obtain ⟨B, hB⟩ := R.Tags.forest_tag z ⟨δ, hδu⟩ hδ
  exact ⟨⟨δ, hδu⟩, Finset.mem_attach _ _, B, hB⟩

/-- **R-6c-body-283 — forest-branch filtered-domain membership.** -/
theorem forestPreimage_mem (R : ResolvedRecoveredPreimageValueMemSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) (h : resolvedIsForestImage z.1 z.2) :
    R.Tags.recoveredPreimageValue z ∈ forestBlockDomFinset G :=
  mem_forestBlockDomFinset_of_isForestCarrying _ (R.forest_isForestCarrying z h)

/-- **R-6c-body-283 — mixed-branch filtered-domain membership.** -/
theorem mixedPreimage_mem (R : ResolvedRecoveredPreimageValueMemSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) (h : ¬ resolvedIsForestImage z.1 z.2) :
    R.Tags.recoveredPreimageValue z ∈ forestBlockDomFinset G :=
  mem_forestBlockDomFinset_of_ne _ (R.mixed_ne_pR z h) (R.mixed_ne_pL z h)

end ResolvedRecoveredPreimageValueMemSupply

end GaugeGeometry.QFT.Combinatorial
