import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSurvivorMemTagReduction
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightRecoveredSectorScout
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestSectorBridgeScout
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantMemTagReduction

/-!
# R-6c-body-217 — sector correspondence floor map: all sector leaves reduced to image correspondences (docs anchor)

Two-hundred-and-seventeenth genuine-body step, a documentation anchor (no new geometry) — a milestone.  After bodies
211/213/215/216 all four sector bridge leaves are reduced to image correspondences.  This module records that state
and the residual leaves, importing the four reduction modules so the map stays type-checked.  Reader-facing
narrative: `CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies 211–216"; proof-dependency map:
`CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c bodies 211–216".

## The four sector correspondences (all axiom-clean `[propext, Classical.choice, Quot.sound]`)

```text
survivor quotient side  body-211  survivor_image_correspondence   rightComponents image ↔ star-avoiding
right    G-side         body-213  right_image_correspondence      componentToRight image ↔ inl false
forest   G-side         body-215  forest_image_correspondence     componentToForest image ↔ inr (forestChoiceSelected)
remnant  quotient side  body-216  remnant_image_correspondence    remnantComponent image ↔ star-touching
```

## The one heavy correspondence

```text
The first three are pure tag / image correspondences:
  the G-side maps are abstract componentToRight / componentToForest fields, and survivorReembed preserves
  vertices at rfl, leaving only the inl-false / inr ⟷ star-avoiding / star-touching tag content.
The remnant correspondence is the genuine de-contraction leaf:
  remnantComponent lands in the contracted graph with a nontrivial remnantClass_eq,
  so its HEq bridges genuinely different vertex sets (bodies 126/183).
```

## Canonical connection

```text
survivor → 206 → 208 → forward_quotient_heq
right    → 170 → backward-outer / backward-choice floors
forest   → 171 → backward-outer / backward-choice floors
remnant  → 207 → 208 → forward_quotient_heq
```

## Residual (the honest floor now)

* **image correspondences** — `survivor_image_correspondence` (211), `right_image_correspondence` (213),
  `forest_image_correspondence` (215) [three tag correspondences], and `remnant_image_correspondence` (216) [the one
  de-contraction correspondence];
* **forward compatibility** — `forestTag` / `recoverChoice_forest_eq` / `promote_collapse` (body-188),
  `forestComponentMem` (body-185), `represented_cases` (body-180);
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract geometry, measure, survivor/remnant
  `Inj`/`Gen`, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

## Note

The sector bridges are all four image correspondences; the next front is to bundle the three light tag
correspondences, leaving the single heavy `remnant_image_correspondence` (the de-contraction) for a focused attack.
No declarations beyond this docstring anchor; the imports keep the map honest against the source.  No facade, no flat
term, no `forgetHopf`.
-/
