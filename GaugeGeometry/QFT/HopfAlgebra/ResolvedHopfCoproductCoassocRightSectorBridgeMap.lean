import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSurvivorMemTagReduction
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightSectorBridgeScout

/-!
# R-6c-body-212 — right sector bridge map: the right / survivor sector floor (docs anchor)

Two-hundred-and-twelfth genuine-body step, a documentation anchor (no new geometry).  After bodies 210/211 the
lighter right / survivor sector bridge is opened: the two right leaves are dual but not identical, and the survivor
leaf is reduced to a single image correspondence.  This module records that state and the residual leaves, importing
the survivor reduction and the right sector scout so the map stays type-checked.  Reader-facing narrative:
`CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies 210–211"; proof-dependency map:
`CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c bodies 210–211".

## The right / survivor sector, opened (all axiom-clean `[propext, Classical.choice, Quot.sound]`)

```text
210  right sector scout — rightRecovered_forward_membership (170) and survivor_mem (206) are DUAL, not identical:
       rightRecovered_forward_membership = G-level, backward componentToRight (δ ↦ G-parent)
       survivor_mem                      = quotient-level, forward survivorComponent = survivorReembed
     opposite halves of one right-sector round-trip, over different graphs — no shared provider.
     The abstract sector-index right inverse (right_left_inv / right_right_inv, ResolvedRightSectorEquivSupply) is
     already proved and underlies leaf 170.
211  survivor_mem reduction — rightDomain_mem_iff (Finset.mem_filter) proved; rightSurvivorForest_elements rfl;
     survivor_mem reduced (via body-206's heq_finset_of_mem_iff) to survivor_image_correspondence.
```

## The survivor-side residual (the pure tag correspondence)

```text
survivor_image_correspondence :
  x₁ ∈ rightComponents(recovered).attach.image survivorComponent   -- recoverChoice z γ = inl false, reembedded
    ↔ x₂ ∈ z.2.1.elements ∧ Disjoint x₂.vertices (starOfZ z)        -- star-avoiding components of B
  (survivorReembed_toResolvedFeynmanGraph = rfl — vertices preserved; the inl-false ⟷ star-avoid tag)
```

## Residual (the honest floor now)

* **survivor side** — `survivor_image_correspondence` (body-211);
* **right / G side** — `rightRecovered_forward_membership` (body-170, the G-level `componentToRight` round-trip);
* **remnant / forest side** — `remnant_mem` (body-207) and `forestRecovered_forward_membership` (body-171), the
  heavier de-contraction bridges;
* **forward compatibility** — `forestTag` / `recoverChoice_forest_eq` / `promote_collapse` (body-188),
  `forestComponentMem` (body-185), `represented_cases` (body-180);
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract geometry, measure, survivor/remnant
  `Inj`/`Gen`, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

## Note

The survivor side is down to a tag correspondence and the right / G side to a `componentToRight` round-trip; the next
front is `rightRecovered_forward_membership` (the G-level right side, where the proved `rightEquiv` / sector inverse
may apply), leaving the heavier remnant / forest side for later.  No declarations beyond this docstring anchor; the
imports keep the map honest against the source.  No facade, no flat term, no `forgetHopf`.
-/
