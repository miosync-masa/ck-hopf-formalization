import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestRecoveredBridge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestParentCarrier
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedForestRecoveryScout

/-!
# R-6c-body-187 — forest recovery deep map: the deep leaf isolated to two inclusions (docs anchor)

Hundred-and-eighty-seventh genuine-body step, a documentation anchor (no new geometry).  After bodies 183–186 the
forest-recovery box (body-179) is driven down to a single geometric obstruction, split into two inclusions gated on
a concrete `componentToForest` / `promote` compatibility.  This module records that state and the residual leaves,
importing the three decomposition modules so the map stays type-checked.  Reader-facing narrative:
`CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies 183–186"; proof-dependency map:
`CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c bodies 183–186".

## The forest-recovery box, opened (all axiom-clean `[propext, Classical.choice, Quot.sound]`)

```text
body-183  forest-recovery box → three leaves:
            forestRecovered_eq            abstract union region ↔ body-156 componentToForest image
            parent_mem_carrier            a forest parent lands in A
            promoted_eq_forestRecovered   the deep de-contraction round-trip
          (forestRecovered_mem / promoted_region_eq PROVED from the leaves → body-179's supply)
body-184  forestRecovered_eq + leftResidual_eq become rfl by building the outer union from the concrete
          region constructions (body-156 right/forest + body-157 left)
body-185  parent_mem_carrier reduced to forestComponentMem (each componentToForest parent ∈ A),
          read off by Finset.mem_image
body-186  promoted_eq_forestRecovered split by Finset.Subset.antisymm into:
            forestRecovered_subset_promoted   LIGHT
            promoted_subset_forestRecovered   HEAVY
```

## The negative finding (body-186 — canonical statement)

```text
This is not supplied by the sector inverse laws alone.
Sector inverse relates componentToForest to the quotient-side remnant components (forestToComponent).
It does NOT connect componentToForest with promote / de-contraction into G.
The remaining proof requires concrete componentToForest / forestTag / promote compatibility.
```

`promote` (de-contraction into the ambient `G`) is never related to `componentToForest` by any existing lemma; the
product-level de-contraction facts live on the quotient side at the polynomial/class level.  So this is the
genuinely fresh geometric leaf.

## Canonical chain

```text
186 → 183 → 179 → 181 → 177 → 174 → 167 → 162 → 160 → 154 → 147 → witnessSplit → coassoc_gen
```

## Residual (the honest floor now)

* **deep forest recovery** — `forestRecovered_subset_promoted` (light) and `promoted_subset_forestRecovered` (heavy),
  both resting on the prerequisite: concrete `componentToForest` / `forestTag` / `promote` compatibility;
* **forest membership** — `forestComponentMem` (body-185);
* **classifier** — `represented_cases` (body-180);
* **backward-outer** — the three sector bridges (bodies 170/171/172), proved up to `choice_tag_trichotomy` (body-173);
* **`HEq` transports** — `backward_choice_heq` (body-164), `forward_quotient_heq` (body-165);
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract `vertices_eq`, measure,
  star/global-gap kernel, survivor/remnant Inj/Gen, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

## Note

The forward-outer geometry is now one leaf in two inclusions, gated on making `componentToForest` / `promote`
concrete.  The next front is the `componentToForest` concretization scout — how far it can be made concrete from
`ForestPrimitiveIndex.toOccurrence` / `forest_surj` / `Classical.choose` — before the inclusion proofs are
attempted.  No declarations beyond this docstring anchor; the imports keep the map honest against the source.  No
facade, no flat term, no `forgetHopf`.
-/
