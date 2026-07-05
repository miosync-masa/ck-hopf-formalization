import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionConstructionFromSector
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftResidualConstruction
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionPartitionDisjoint
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredOuterMembership
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRoundTripComponentPartition

/-!
# R-6c-body-161 — region construction map: the in-source region-contents inventory (docs anchor)

Hundred-and-sixty-first genuine-body step, a documentation anchor (no new geometry).  After bodies 155–160 the
three regions of the recovered outer forest are built concretely and the union assembly / outer round-trips are
reduced to element-level content.  This module records the region-construction chain and the residual region
leaves in the source tree, importing the region-contents modules so the map stays type-checked.  The reader-facing
narrative is `CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies 155–160"; the proof-dependency map is
`CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c bodies 155–160".

## Region construction chain (all axiom-clean `[propext, Classical.choice, Quot.sound]`)

```text
ResolvedRegionConstructionFromSectorSupply   (body-156: rightRecovered / forestRecovered = sector images)
ResolvedLeftResidualConstructionSupply       (body-157: leftResidual = filter of A by ¬ represented)
ResolvedRegionPartitionSupply                (body-158: hcross_lr / hcross_lrf from 3 pairwise disjoints)
ResolvedRecoveredOuterCarrierSupply          (body-159: recovered_outer_mem carrier leaf)
ResolvedRoundTripComponentPartitionSupply    (body-160: outer round-trips → element partitions)
   .toConcreteRoundTripObligationSupply → ResolvedConcreteRoundTripObligationSupply (body-154)
   → RegionRoundTripReduction (147) → WitnessSplitBranchCombiner (144) → … → BijectionProvider (131) → coassoc_gen
```

## Proved / reduced

* `rightRecovered` / `forestRecovered` element shapes (`ofElements` images, `rfl`) and `leftResidual`
  (filter of `A`, `rfl`) — bodies 156/157;
* `union_eq` (body-153, `Finset.ext` + `union_elements`); the two cross-disjointnesses from the three pairwise
  disjointnesses (body-158);
* the carrier membership isolated as one leaf `recovered_outer_mem` (body-159);
* the two outer round-trips reduced to element partitions (body-160, `Subtype.ext` + `ext_elements`).

## Residual region leaves (the honest floor)

* **element partitions** (body-160) — `selectedOuter_partition` (`selectedOuterOf(recovered) = A`),
  `recoveredOuter_partition` (`unionOuter(forward) = A'`);
* **heterogeneous round-trips** (body-160) — `forward_quotient` (B-reconstruction), `backward_choice` (p-recovery),
  each needing the sector `componentToRight` / `componentToForest` round-trip;
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **sector maps** (body-156) — `componentToRight` / `componentToForest` + their `CD` / disjointness — and
  `representedInQuotient` (body-157);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract `vertices_eq`, measure,
  star/global-gap kernel, survivor/remnant Inj/Gen, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

## Note

The bijection's proof-shape remains entirely closed; the current work is the local component-partition and sector
round-trip providers.  No declarations beyond this docstring anchor; the imports keep the map honest against the
source.  No facade, no flat term, no `forgetHopf`.
-/
