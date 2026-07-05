import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterRegionPartition
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredOuterRegionPartition

/-!
# R-6c-body-169 — outer partition map: the in-source outer-partition inventory (docs anchor)

Hundred-and-sixty-ninth genuine-body step, a documentation anchor (no new geometry).  After bodies 167/168 the two
outer round-trip partitions are split into region-local facts.  This module records the outer-partition chain and
the residual leaves in the source tree, importing the two split modules so the map stays type-checked.  The
reader-facing narrative is `CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies 166–168"; the proof-dependency map is
`CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c bodies 166–168".

## The two outer partitions, split (all axiom-clean `[propext, Classical.choice, Quot.sound]`)

```text
forward outer   body-167  selectedOuter(recovered) = leftOf ⊔ promotedOf = A
   reduced to:  leftOf_recovered_eq      (leftOf recovered).elements = leftResidual .elements   (inl true)
                promotedOf_recovered_eq  (promotedOf recovered).elements = forestRecovered .elements (inr)
                target_outer_partition   (γ ∈ leftResidual ∨ γ ∈ forestRecovered) ↔ γ ∈ A.elements
backward outer  body-168  unionOuter(forward q) = A' = q.1
   reduced to:  recovered_region_membership
                (γ ∈ leftResidual ∨ γ ∈ rightRecovered ∨ γ ∈ forestRecovered) ↔ γ ∈ A'.elements
```

## Chain

```text
167 (leftOf_promotedOf_partition) → SelectedOuterPartition (162) → 160 → 154 → 147 → witnessSplit → coassoc_gen
168 (recovered_region_partition) → RecoveredOuterPartition (163) → 160 → 154 → 147 → witnessSplit → coassoc_gen
```

## Residual (the honest floor)

* **region partition facts** — `leftOf_recovered_eq`, `promotedOf_recovered_eq`, `target_outer_partition`
  (body-167) and `recovered_region_membership` (body-168);
* **`HEq` transports** — `backward_choice_heq` (body-164), `forward_quotient_heq` (body-165);
* **sector bridge** — `rightRecovered` / `forestRecovered` = the `componentToRight` / `componentToForest` images
  (body-156), `representedInQuotient` (body-157), and the sector round-trips linking the region equalities to the
  `q.2` tags;
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract `vertices_eq`, measure,
  star/global-gap kernel, survivor/remnant Inj/Gen, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

## Note

Both outer partitions are region-local; the current work is the sector bridge (starting with the survivor /
`right` side).  No declarations beyond this docstring anchor; the imports keep the map honest against the source.
No facade, no flat term, no `forgetHopf`.
-/
