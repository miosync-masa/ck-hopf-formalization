import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSurvivorMemTagReduction
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightRecoveredSectorScout

/-!
# R-6c-body-214 — right sector correspondence map: both right leaves reduced to image correspondences (docs anchor)

Two-hundred-and-fourteenth genuine-body step, a documentation anchor (no new geometry).  After bodies 210–213 both
right-sector leaves are reduced to image correspondences.  This module records that state and the residual leaves,
importing the two reduction modules so the map stays type-checked.  Reader-facing narrative:
`CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies 210–213"; proof-dependency map:
`CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c bodies 210–213".

## The right sector, reduced (all axiom-clean `[propext, Classical.choice, Quot.sound]`)

```text
210  scout — rightRecovered_forward_membership (170) and survivor_mem (206) are DUAL but not identical
211  survivor side — survivor_mem → survivor_image_correspondence
       x₁ ∈ rightComponents(recovered).attach.image survivorComponent ↔ x₂ ∈ rightDomain z   (survivorReembed rfl)
213  G-side — rightRecovered_forward_membership → right_image_correspondence
       γ ∈ (rightDomain (fwdMap q)).attach.image componentToRight ↔ rightPrimSelected q γ    (over a wiring bridge)
```

## The `rightEquiv` negative finding (body-213)

```text
rightEquiv does not directly discharge these leaves:
it lives at the sector-index / quotient-graph level (forward survivorComponent),
while the region maps use abstract componentToRight fields disconnected from it.
The remaining right content is the correspondence between
  B's star-avoiding quotient components  and  q's inl-false source choices.
```

## Residual (the honest floor now)

* **right sector** — `survivor_image_correspondence` (body-211) and `right_image_correspondence` (body-213);
* **remnant / forest sector** — `remnant_mem` (body-207) and `forestRecovered_forward_membership` (body-171), the
  heavier de-contraction bridges;
* **forward compatibility** — `forestTag` / `recoverChoice_forest_eq` / `promote_collapse` (body-188),
  `forestComponentMem` (body-185), `represented_cases` (body-180);
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract geometry, measure, survivor/remnant
  `Inj`/`Gen`, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

## Note

The right sector is closed to two image correspondences (star-avoiding ⟷ `inl false`); the next front is the heavier
remnant / forest sector (`remnant_mem` / `forestRecovered_forward_membership`), where the de-contraction may share the
promotion compatibility (bodies 188/189).  No declarations beyond this docstring anchor; the imports keep the map
honest against the source.  No facade, no flat term, no `forgetHopf`.
-/
