import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRoundTripComponentPartition

/-!
# R-6c-body-163 — recovered outer partition proof: the backward outer partition via the region union

Hundred-and-sixty-third genuine-body step, the backward-outer twin of body-162.  Body-160's backward-outer element
partition (`unionOuter (forward q).elements = A'.elements`) is reduced, through body-145's `union_eq`, to the
single region partition `leftResidual ∪ rightRecovered ∪ forestRecovered = A'` on the forward image.

## The reduction (PROVED)

For `z = fwdMap q = ⟨selectedOuterOf q, quotientForest q⟩` the recovered outer is `unionOuter z`, and
`union_eq z` gives `(unionOuter z).1.elements = leftResidual z ∪ rightRecovered z ∪ forestRecovered z` (body-145,
the concrete union).  So `recoveredOuter_partition` reduces to

```text
recovered_region_partition : leftResidual (fwdMap q) ∪ rightRecovered (fwdMap q) ∪ forestRecovered (fwdMap q)
                               = q.1.1.elements
```

— "the three regions of the forward image reconstruct the original outer `A'`" — and
`.recoveredOuter_partition` is **proved** by `(union_eq (fwdMap q)).trans (recovered_region_partition q)`, discharging
body-160's `recoveredOuter_partition` and hence (through body-160 → 154 → …) the backward-outer round-trip.

The `recovered_region_partition` further decomposes region-wise: `leftResidual (fwdMap q)` recovers the
left-primitive components of `A'`, `rightRecovered (fwdMap q)` its right-primitive components (from the survivors),
and `forestRecovered (fwdMap q)` its forest-choice parents (from the remnants) — the component-wise sector
round-trips, fielded here as the one combined partition.

Per the HALT: the reduction goes through `union_eq` (no `Finset.union` `rfl` / instance diamond — the `trans` uses
the proved `union_eq`); the region partition is fielded (its component-wise sector round-trip is not entered); no
round-trip beyond `recoveredOuter_partition` is entered.

Landed:

* `ResolvedRecoveredOuterPartitionSupply D S Region` — the region partition of the forward image;
* `.recoveredOuter_partition` — body-160's backward-outer element partition (PROVED via `union_eq`).

Toolkit body (like body-162).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-163 — the recovered-outer partition supply.**  The single region partition
`leftResidual ∪ rightRecovered ∪ forestRecovered = A'` on the forward image `fwdMap q`. -/
structure ResolvedRecoveredOuterPartitionSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- The three regions of the forward image reconstruct the original outer `A'` at the component level. -/
  recovered_region_partition : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    (Region.Union.leftResidual (fwdMap S q)).elements
        ∪ (Region.Union.rightRecovered (fwdMap S q)).elements
        ∪ (Region.Union.forestRecovered (fwdMap S q)).elements
      = q.1.1.elements

/-- **R-6c-body-163 — body-160's backward-outer element partition from the region partition** (via `union_eq`). -/
theorem ResolvedRecoveredOuterPartitionSupply.recoveredOuter_partition
    {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}
    (P : ResolvedRecoveredOuterPartitionSupply D S Region) {G : ResolvedFeynmanGraph}
    (q : ForestBlockDomType D G) :
    (Region.Union.unionOuter (fwdMap S q)).1.elements = q.1.1.elements :=
  (Region.Union.union_eq (fwdMap S q)).trans (P.recovered_region_partition q)

end GaugeGeometry.QFT.Combinatorial
