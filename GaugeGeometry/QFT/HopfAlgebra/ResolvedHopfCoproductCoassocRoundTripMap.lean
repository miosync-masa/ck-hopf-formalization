import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterPartitionProof
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredOuterPartitionProof
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredChoiceRoundTrip
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredQuotientRoundTrip

/-!
# R-6c-body-166 — round-trip map: the in-source four-round-trip inventory (docs anchor)

Hundred-and-sixty-sixth genuine-body step, a documentation anchor (no new geometry).  After bodies 162–165 each of
the four round-trip obligations is reduced to a single region partition or region-`HEq` leaf; the round-trip
proof-shape is entirely closed.  This module records the four-round-trip chain and the residual leaves in the
source tree, importing the round-trip modules so the map stays type-checked.  The reader-facing narrative is
`CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies 161–165"; the proof-dependency map is `CK_HOPF_DEPENDENCY_GRAPH.md`
§"R-6c bodies 161–165".

## The four round-trips (all axiom-clean `[propext, Classical.choice, Quot.sound]`)

```text
forward outer     body-162  selectedOuterOf(recovered) = A   via  selectedOuterOf = leftOf ⊔ promotedOf  (PROVED)
backward outer    body-163  unionOuter(forward) = A'         via  union_eq + region partition            (PROVED)
backward choice   body-164  HEq (recoverChoice(forward)) q.2   region tags recover p                     (leaf)
forward quotient  body-165  HEq (quotientForest(recovered)) B  survivors ⊔ remnants recover B            (leaf)
```

## Chain

```text
162 (selectedOuter_partition) / 163 (recoveredOuter_partition) / 164 (backward_choice) / 165 (forward_quotient)
   → RoundTripComponentPartition (160) → ConcreteRoundTripObligations (154) → RegionRoundTripReduction (147)
   → WitnessSplitBranchCombiner (144) → WitnessSplitConcrete (141) → WitnessSplitCoverSupply (139)
   → BijectionProvider (131) → coassoc_gen
```

## Residual (the honest floor)

* **region partitions** — `leftOf_promotedOf_partition` (body-162, `leftOf ∪ promotedOf = A`) and
  `recovered_region_partition` (body-163, `leftResidual ∪ rightRecovered ∪ forestRecovered = A'`);
* **`HEq` transports** — `backward_choice_heq` (body-164) and `forward_quotient_heq` (body-165);
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **sector maps** (body-156, `componentToRight` / `componentToForest` + `CD` / disjointness) and
  `representedInQuotient` (body-157);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract `vertices_eq`, measure,
  star/global-gap kernel, survivor/remnant Inj/Gen, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

## Note

The round-trip proof-shape is entirely closed; the current work is splitting the region partitions into
region-local sector facts.  No declarations beyond this docstring anchor; the imports keep the map honest against
the source.  No facade, no flat term, no `forgetHopf`.
-/
