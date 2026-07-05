import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRoundTripComponentPartition

/-!
# R-6c-body-162 — selectedOuter partition proof: the forward outer partition via `leftOf` ⊔ `promotedOf`

Hundred-and-sixty-second genuine-body step, reducing body-160's forward-outer element partition to the
`selectedOuterOf = leftOf ⊔ promotedOf` decomposition.  The selected outer of the recovered split choice is the
union of its left-selected components and its promoted forests, so `selectedOuter_partition` (`selectedOuterOf
(recovered).elements = A.elements`) reduces to "`leftOf ∪ promotedOf = A`" at the component level.

## The structural decomposition (PROVED)

`selectedOuterOf ⟨A', p⟩ .1 = (leftOf ⟨A', p⟩) .union (promotedOf ⟨A', p⟩)` definitionally (the concrete image
supply's `selectedOuterRawOf`, bodies 105/128), so at the membership level

```text
γ ∈ (selectedOuterOf (recovered)).1.elements ↔ γ ∈ (leftOf (recovered)).elements ∨ γ ∈ (promotedOf (recovered)).elements
```

is proved by unfolding `selectedOuterOf` / `selectedOuterRawOf` and `Finset.mem_union` (`selectedOuter_mem_iff`).
This absorbs the `Finset` `DecidableEq` instance diamond via `simp` at the membership level (no union `rfl`).

## The reduction

`ResolvedSelectedOuterPartitionSupply D S Region` fields the single component partition

```text
leftOf_promotedOf_partition : (γ ∈ leftOf (recovered) ∨ γ ∈ promotedOf (recovered)) ↔ γ ∈ A.elements
```

— the "`leftOf ∪ promotedOf = A`" fact.  Then `.selectedOuter_partition` is **proved** by `Finset.ext` +
`selectedOuter_mem_iff` + this partition, discharging body-160's `selectedOuter_partition` and hence (through
body-160 → 154 → …) the forward-outer round-trip.

The `leftOf_promotedOf_partition` further decomposes (region-wise) into: `leftOf (recovered) = leftResidual` (the
`inl true` tags), `promotedOf (recovered) = ` the promoted forests of the `inr` choices (`forestRecovered`), and
`A = leftResidual ∪ (promoted part)` (the target partition) — the `inl false` right-primitive part contributes to
neither, as expected.  These are the residual `selectedOuterOf` region facts, fielded here as the one combined
partition.

Per the HALT: the structural `leftOf ⊔ promotedOf` decomposition is proved (`Finset.ext` membership, no union
`rfl`); the promoted-forest / left-selection region equality is fielded as the combined partition; no round-trip
beyond `selectedOuter_partition` is entered.

Landed:

* `selectedOuter_mem_iff` — the structural `selectedOuterOf = leftOf ⊔ promotedOf` membership (PROVED);
* `ResolvedSelectedOuterPartitionSupply D S Region` — the `leftOf ∪ promotedOf = A` partition;
* `.selectedOuter_partition` — body-160's forward-outer element partition (PROVED from the partition).

Toolkit body (like body-160).  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **R-6c-body-162 — the structural `selectedOuterOf = leftOf ⊔ promotedOf` membership.**  The selected outer of a
split choice is the union of its left-selected components and its promoted forests. -/
theorem selectedOuter_mem_iff {S : ResolvedConcreteSummandBundleSupply D}
    (Region : ResolvedRegionChoiceRoundTripSupply D S) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) (γ : ResolvedFeynmanSubgraph G) :
    γ ∈ ((S.Forward.imageSupply G).selectedOuterOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1.elements
      ↔ γ ∈ ((S.Forward.imageSupply G).leftSelection.leftOf
          (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
        ∨ γ ∈ ((S.Forward.imageSupply G).promotedOf
          (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements := by
  simp only [ResolvedCoassocSelectedOuterImageSupply.selectedOuterOf,
    ResolvedCoassocSelectedOuterSupply.toSelectedOuterOf,
    ResolvedCoassocSelectedOuterImageSupply.toSelectedOuterSupply,
    ResolvedCoassocSelectedOuterImageSupply.promoteSupply,
    ResolvedForestPromoteSupply.selectedOuterRawOf,
    ResolvedSplitChoiceLeftSelectionSupply.toPromoteSupply,
    ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union]

/-- **R-6c-body-162 — the selected-outer partition supply.**  The single component partition `leftOf ∪ promotedOf =
A` for the recovered split choice. -/
structure ResolvedSelectedOuterPartitionSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- `leftOf ∪ promotedOf = A` at the component level. -/
  leftOf_promotedOf_partition : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : ResolvedFeynmanSubgraph G),
    (γ ∈ ((S.Forward.imageSupply G).leftSelection.leftOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
      ∨ γ ∈ ((S.Forward.imageSupply G).promotedOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements)
    ↔ γ ∈ z.1.1.elements

/-- **R-6c-body-162 — body-160's forward-outer element partition from the `leftOf ∪ promotedOf = A` partition.** -/
theorem ResolvedSelectedOuterPartitionSupply.selectedOuter_partition
    {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}
    (P : ResolvedSelectedOuterPartitionSupply D S Region) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) :
    ((S.Forward.imageSupply G).selectedOuterOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1.elements
      = z.1.1.elements := by
  ext γ
  rw [selectedOuter_mem_iff Region z γ]
  exact P.leftOf_promotedOf_partition z γ

end GaugeGeometry.QFT.Combinatorial
