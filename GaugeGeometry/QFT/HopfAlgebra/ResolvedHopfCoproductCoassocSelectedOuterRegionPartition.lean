import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterPartitionProof

/-!
# R-6c-body-167 — selected-outer region partition: `leftOf ∪ promotedOf = A` split into three region facts

Hundred-and-sixty-seventh genuine-body step, splitting body-162's forward-outer partition into three region-local
equalities.  The `leftOf ∪ promotedOf = A` fact of the recovered split choice reduces to: `leftOf` is the
`leftResidual` region, `promotedOf` is the `forestRecovered` region, and `leftResidual ∪ forestRecovered = A` (the
target partition — the right-primitive `rightRecovered` region does not contribute to the selected outer).

## The split (PROVED)

`ResolvedSelectedOuterRegionPartitionSupply D S Region` fields the three region facts:

* `leftOf_recovered_eq` — `(leftOf recovered).elements = (leftResidual z).elements`: the left-selected components
  of the recovered choice (`inl true`) are exactly the `leftResidual` region;
* `promotedOf_recovered_eq` — `(promotedOf recovered).elements = (forestRecovered z).elements`: the promoted
  forests (`inr`) are exactly the `forestRecovered` region;
* `target_outer_partition` — `(γ ∈ leftResidual ∨ γ ∈ forestRecovered) ↔ γ ∈ A.elements`: the left residual and
  forest parents partition the target outer `A` (the `inl false` right-primitive `rightRecovered` region is *not*
  in `A` — it went into the quotient `B`, not the outer).

Then `leftOf_promotedOf_partition` (body-162's field) is **proved** by `rw` of the two region equalities into the
membership disjunction, then `target_outer_partition`; `.toSelectedOuterPartitionSupply` produces body-162's
`ResolvedSelectedOuterPartitionSupply`, and hence the forward-outer round-trip.

So the forward-outer partition is now entirely in region-local vocabulary: `leftOf = leftResidual`,
`promotedOf = forestRecovered`, and `leftResidual ∪ forestRecovered = A` — the residual is these three region
facts (the `leftOf` / `promotedOf` region equalities are the sector left-selection / promotion round-trips; the
target partition is the "`A` = left residual + forest parents" fact awaiting the sector image characterisation).

Per the HALT: the region facts (`leftOf` / `promotedOf` element equalities, target partition) are fielded; the
`leftOf ∪ promotedOf = A` partition is proved from them by `rw`; the sector left-selection / promotion round-trips
are not entered.

Landed:

* `ResolvedSelectedOuterRegionPartitionSupply D S Region` — the three region facts;
* `.leftOf_promotedOf_partition` — body-162's partition (PROVED from the three);
* `.toSelectedOuterPartitionSupply` — body-162's supply (→ the forward-outer round-trip).

Toolkit body (like body-162/163).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-167 — the selected-outer region-partition supply.**  The three region facts splitting `leftOf ∪
promotedOf = A`: `leftOf = leftResidual`, `promotedOf = forestRecovered`, and `leftResidual ∪ forestRecovered =
A`. -/
structure ResolvedSelectedOuterRegionPartitionSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- The left-selected components are the left-residual region. -/
  leftOf_recovered_eq : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ((S.Forward.imageSupply G).leftSelection.leftOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
      = (Region.Union.leftResidual z).elements
  /-- The promoted forests are the forest-recovered region. -/
  promotedOf_recovered_eq : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ((S.Forward.imageSupply G).promotedOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
      = (Region.Union.forestRecovered z).elements
  /-- The left residual and forest parents partition the target outer `A`. -/
  target_outer_partition : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : ResolvedFeynmanSubgraph G),
    (γ ∈ (Region.Union.leftResidual z).elements ∨ γ ∈ (Region.Union.forestRecovered z).elements)
      ↔ γ ∈ z.1.1.elements

namespace ResolvedSelectedOuterRegionPartitionSupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-167 — body-162's `leftOf_promotedOf_partition` from the three region facts.** -/
theorem leftOf_promotedOf_partition (P : ResolvedSelectedOuterRegionPartitionSupply D S Region)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) (γ : ResolvedFeynmanSubgraph G) :
    (γ ∈ ((S.Forward.imageSupply G).leftSelection.leftOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
      ∨ γ ∈ ((S.Forward.imageSupply G).promotedOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements)
    ↔ γ ∈ z.1.1.elements := by
  rw [P.leftOf_recovered_eq z, P.promotedOf_recovered_eq z]
  exact P.target_outer_partition z γ

/-- **R-6c-body-167 — body-162's selected-outer partition supply from the region facts.** -/
def toSelectedOuterPartitionSupply (P : ResolvedSelectedOuterRegionPartitionSupply D S Region) :
    ResolvedSelectedOuterPartitionSupply D S Region where
  leftOf_promotedOf_partition := fun {G} z γ => P.leftOf_promotedOf_partition z γ

end ResolvedSelectedOuterRegionPartitionSupply

end GaugeGeometry.QFT.Combinatorial
