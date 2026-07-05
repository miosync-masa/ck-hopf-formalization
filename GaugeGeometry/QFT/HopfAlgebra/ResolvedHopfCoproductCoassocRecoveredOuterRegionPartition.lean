import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredOuterPartitionProof

/-!
# R-6c-body-168 — recovered outer region partition: `leftResidual ∪ rightRecovered ∪ forestRecovered = A'` split

Hundred-and-sixty-eighth genuine-body step, the backward-outer twin of body-167.  Body-163's region partition
`leftResidual ∪ rightRecovered ∪ forestRecovered = A'` (on the forward image `fwdMap q`) is reduced to the
component classification of the original outer `A' = q.1`: each component of `A'` lands in exactly one of the three
recovered regions, by its choice tag.

## The split (PROVED)

`ResolvedRecoveredOuterRegionPartitionSupply D S Region` fields the single component membership partition

```text
recovered_region_membership :
  (γ ∈ leftResidual (fwdMap q) ∨ γ ∈ rightRecovered (fwdMap q) ∨ γ ∈ forestRecovered (fwdMap q))
    ↔ γ ∈ A'.elements
```

— "the three recovered regions of the forward image partition the original outer `A'`'s components".  Since every
component `γ` of `A'` has a choice tag `q.2 γ ∈ Bool ⊕ ForestIdx`, it lands in exactly one region: `inl true` →
`leftResidual`, `inl false` → `rightRecovered`, `inr Bᵧ` → `forestRecovered`.  (The membership form is used rather
than three filter equalities to avoid the dependent `q.2 γ` tag, per the plan.)

Then `recovered_region_partition` (body-163's field) is **proved** by `Finset.ext` + `Finset.mem_union` +
`or_assoc` + this membership; `.toRecoveredOuterPartitionSupply` produces body-163's
`ResolvedRecoveredOuterPartitionSupply`, and hence the backward-outer round-trip.

So the backward-outer partition is now in region-local vocabulary, symmetric with body-167 (`leftOf ∪ promotedOf =
A`): both outer round-trips reduce to region membership facts.  The residual is the single
`recovered_region_membership` — the fact that the recovered regions of a forward image classify `A'`'s components
by their tags, awaiting the sector image characterisation (`componentToRight` / `componentToForest` recover the
right-primitive / forest-choice components).

Per the HALT: the `componentToRight` / `componentToForest` sector inverse laws are not entered; the region
partition is reduced to the component membership (`Finset.ext` + `mem_union`); the tag-filter equalities are kept as
the one membership fact.

Landed:

* `ResolvedRecoveredOuterRegionPartitionSupply D S Region` — the component membership partition;
* `.recovered_region_partition` — body-163's partition (PROVED);
* `.toRecoveredOuterPartitionSupply` — body-163's supply (→ the backward-outer round-trip).

Toolkit body (like body-167).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-168 — the recovered-outer region-partition supply.**  The component membership partition: the three
recovered regions of the forward image classify `A'`'s components by their tags. -/
structure ResolvedRecoveredOuterRegionPartitionSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- The three recovered regions of the forward image partition `A'`'s components. -/
  recovered_region_membership : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : ResolvedFeynmanSubgraph G),
    (γ ∈ (Region.Union.leftResidual (fwdMap S q)).elements
        ∨ γ ∈ (Region.Union.rightRecovered (fwdMap S q)).elements
        ∨ γ ∈ (Region.Union.forestRecovered (fwdMap S q)).elements)
      ↔ γ ∈ q.1.1.elements

namespace ResolvedRecoveredOuterRegionPartitionSupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-168 — body-163's `recovered_region_partition` from the component membership.** -/
theorem recovered_region_partition (P : ResolvedRecoveredOuterRegionPartitionSupply D S Region)
    {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G) :
    (Region.Union.leftResidual (fwdMap S q)).elements
        ∪ (Region.Union.rightRecovered (fwdMap S q)).elements
        ∪ (Region.Union.forestRecovered (fwdMap S q)).elements
      = q.1.1.elements := by
  ext γ
  simp only [Finset.mem_union, or_assoc]
  exact P.recovered_region_membership q γ

/-- **R-6c-body-168 — body-163's recovered-outer partition supply from the component membership.** -/
def toRecoveredOuterPartitionSupply (P : ResolvedRecoveredOuterRegionPartitionSupply D S Region) :
    ResolvedRecoveredOuterPartitionSupply D S Region where
  recovered_region_partition := fun {G} q => P.recovered_region_partition q

end ResolvedRecoveredOuterRegionPartitionSupply

end GaugeGeometry.QFT.Combinatorial
