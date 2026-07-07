import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightImageCorrespondenceScout
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestImageCorrespondenceReduction
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSurvivorImageCorrespondenceReduction
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantImageCorrespondenceReduction

/-!
# R-6c-body-223 — sector sound/complete map: all sector correspondences reduced to directions (docs anchor)

Two-hundred-and-twenty-third genuine-body step, a documentation anchor (no new geometry).  After bodies 219–222 all
four sector image correspondences are reduced to two `sound` / `complete` directions each — a uniform proof-shape.
This module records that state and the residual leaves, importing the four reduction modules so the map stays
type-checked.  Reader-facing narrative: `CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies 219–222"; proof-dependency map:
`CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c bodies 219–222".

## The four sector correspondences, reduced (all axiom-clean `[propext, Classical.choice, Quot.sound]`)

```text
right     body-219  right_sound    / right_complete      componentToRight  round-trip ↔ inl false     (G-side, no HEq)
forest    body-220  forest_sound   / forest_complete     componentToForest round-trip ↔ inr B         (G-side, no HEq)
survivor  body-221  survivor_sound / survivor_complete   survivorComponent round-trip ↔ star-avoiding (quotient, HEq)
remnant   body-222  remnant_sound  / remnant_complete    remnantComponent  round-trip ↔ star-touching (quotient, HEq, de-contraction)
```

## Main statement

```text
All four sector image correspondences now have the same proof-shape:
  image correspondence = sound + complete.
Proved by term-mode Finset.mem_image.mp / .mpr, the quotient-side pair closing the cross-graph HEq via eq_of_heq.
The only heavy pair is remnant, which carries de-contraction geometry (remnantClass_eq).
```

## Canonical links

```text
right / forest    → backward-outer and backward-choice floors (bodies 170/171)
survivor / remnant → forward-quotient floor (bodies 206/207 → 208)
```

## Residual (the honest floor now)

* **eight sector `sound` / `complete` directions** — `right_sound` / `right_complete` (219), `forest_sound` /
  `forest_complete` (220), `survivor_sound` / `survivor_complete` (221), `remnant_sound` / `remnant_complete` (222);
* **forward compatibility** — `forestTag` / `recoverChoice_forest_eq` / `promote_collapse` (body-188),
  `forestComponentMem` (body-185), `represented_cases` (body-180);
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract geometry, measure, survivor/remnant
  `Inj`/`Gen`, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

## Note

The sector bridge layer's proof-shape is uniform (eight `sound` / `complete` directions); the next front is the deeper
sector-inverse wiring, starting with the lightest G-side `right_sound` / `right_complete`, where the already-proved
`right_surj` / `right_left_inv` / `right_right_inv` may apply.  No declarations beyond this docstring anchor; the
imports keep the map honest against the source.  No facade, no flat term, no `forgetHopf`.
-/
