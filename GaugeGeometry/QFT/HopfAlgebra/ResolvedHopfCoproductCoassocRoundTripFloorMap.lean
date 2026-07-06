import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForwardQuotientAssembly
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestParentRecoveryScout

/-!
# R-6c-body-209 — round-trip floor map: all four round-trips reduced to local bridges (docs anchor)

Two-hundred-and-ninth genuine-body step, a documentation anchor (no new geometry) — a late-stage milestone.  After
bodies 202–208 all four round-trip obligations of the resolved coassociativity backward map are reduced to local
sector / compatibility bridges.  This module records that state and the residual leaves, importing the
forward-quotient assembly and the forest-parent-recovery modules so the map stays type-checked.  Reader-facing
narrative: `CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies 202–208"; proof-dependency map:
`CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c bodies 202–208".

## The four round-trips, at their floor (all axiom-clean `[propext, Classical.choice, Quot.sound]`)

```text
backward outer    170/171/172 + 173     three sector bridges + choice_tag_trichotomy (proved)
forward outer     190                    compatibility leaves (188/185/180) + region constructions
backward choice   202 → 200 → 199        parent_recovered = rfl from the forest bridge (171)
forward quotient  206/207 → 208          survivor_mem + remnant_mem (the duals of 170/171)
```

## Canonical chains

```text
backward choice   202 → 200 → 198 → 196 → 194 → 193 → 164 → 160 → 154 → 147 → witnessSplit → coassoc_gen
forward quotient  208 → 206/207 → 204 → 203 → 165 → 160 → 154 → 147 → witnessSplit → coassoc_gen
```

## Main statement

```text
The witnessSplit round-trip proof-shape is complete.
All four round-trip obligations now consume only local sector / compatibility bridges.
No global HEq or Sigma proof-shape remains.
```

## Residual (the honest floor now)

* **sector bridge internals** — the left / right / forest bridges (bodies 170/171/172) and the recovered-side
  `survivor_mem` / `remnant_mem` (bodies 206/207) — the `componentToRight` / `componentToForest` round-trips;
* **forward compatibility** — `forestTag` / `recoverChoice_forest_eq` / `promote_collapse` (body-188),
  `forestComponentMem` (body-185), `represented_cases` (body-180);
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract geometry `vertices_eq`, measure,
  survivor/remnant `Inj`/`Gen`, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

## Note

The round-trip proof-shape is entirely closed to local bridges; the next front is the sector bridge internals,
starting with the lighter survivor / right side (`survivor_mem` / `rightRecovered_forward_membership`), leaving the
heavier remnant / forest side for later.  No declarations beyond this docstring anchor; the imports keep the map
honest against the source.  No facade, no flat term, no `forgetHopf`.
-/
