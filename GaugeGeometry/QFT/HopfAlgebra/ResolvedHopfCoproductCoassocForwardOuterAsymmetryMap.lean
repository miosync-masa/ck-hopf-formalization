import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredRegionMembershipAssembly
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedRegionRoundTrip

/-!
# R-6c-body-176 — forward-outer asymmetry map: tag-level `leftOf` vs geometry-level `promotedOf` (docs anchor)

Hundred-and-seventy-sixth genuine-body step, a documentation anchor (no new geometry).  After bodies 173–175 the
two outer round-trip partitions are in their final localised form: the backward outer is proved to the choice-tag
trichotomy on the three sector bridges, and the forward outer is split into a **tag half** (proved) and a
**geometry half** (isolated).  This module records that state and the residual leaves, importing the two assembly
modules so the map stays type-checked.  Reader-facing narrative:
`CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies 169–175"; proof-dependency map:
`CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c bodies 169–175".

## The two outer partitions, in final form (all axiom-clean `[propext, Classical.choice, Quot.sound]`)

```text
backward outer   body-173  recovered_region_membership
   PROVED by:    rw the 3 sector bridges (170/171/172) into the region disjunction, then
                 choice_tag_trichotomy (PROVED): (inl true ∨ inl false ∨ inr) ↔ γ ∈ q.1.1.elements

forward outer    body-174  leftOf_recovered_eq       PROVED from tags
                           (leftOf recovered).elements = leftResidual z .elements   (inl true, filter)
                 body-174  promotedOf_recovered_eq   does NOT follow from tags — fielded
                 body-175  promoted_region_eq        isolated as the de-contraction round-trip leaf
                 (open)    target_outer_partition    (γ ∈ leftResidual ∨ γ ∈ forestRecovered) ↔ γ ∈ A.elements
```

## The asymmetry (the body-174/175 finding — canonical statement)

```text
leftOf is tag-level.
promotedOf is geometry-level.
promotedOf.elements is the promoted / de-contracted components
  (biUnion over forest-tagged γ of (promote γ Bᵧ).elements),
while forestRecovered.elements is the componentToForest PARENT components
  (images of the star-touching remnant components of the quotient B).
Their equality is a sector promotion / de-contraction round-trip — not a tag lemma.
```

`leftOf` is the `filter` of the recovered outer by `leftSelectedConcrete` (`inl true`), so `leftOf = leftResidual`
falls to the region tags + `union_eq` (the `all_inl` / `exists_inr` pattern).  `promotedOf` de-contracts each
forest choice `Bᵧ` back into `G` via `promote`, so its equality with the `componentToForest` parents is genuinely
geometric — the first non-combinatorial leaf forced on the forward side.

## Chain

```text
173 (recovered_region_membership) → RecoveredOuterRegionPartition (168) → 163 → 160 → 154 → 147 → witnessSplit → coassoc_gen
174 (leftOf_recovered_eq PROVED) ┐
175 (promoted_region_eq leaf)    ├→ SelectedOuterRegionPartition (167) → 162 → 160 → 154 → 147 → witnessSplit → coassoc_gen
    (target_outer_partition)     ┘
```

## Residual (the honest floor now)

* **forward-outer, two leaves** — `promoted_region_eq` (body-175, promotion / de-contraction round-trip) and
  `target_outer_partition` (`leftResidual ∪ forestRecovered = A`, the star-touch / remnant coverage); `leftOf` is
  PROVED (body-174);
* **backward-outer** — PROVED to `choice_tag_trichotomy` (body-173) on the three sector bridges (bodies 170/171/172);
* **`HEq` transports** — `backward_choice_heq` (body-164), `forward_quotient_heq` (body-165);
* **sector bridge internals** — the `componentToRight` / `componentToForest` round-trips inside the three bridges,
  `representedInQuotient` (body-157), the `promote` de-contraction behind `promoted_region_eq`;
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract `vertices_eq`, measure,
  star/global-gap kernel, survivor/remnant Inj/Gen, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

## Note

The forward outer is now cleanly split into a tag half (`leftOf`, PROVED) and a geometry half (`promoted_region_eq`)
plus coverage (`target_outer_partition`); the next front is `target_outer_partition`, separating the promotion side
from the coverage side.  No declarations beyond this docstring anchor; the imports keep the map honest against the
source.  No facade, no flat term, no `forgetHopf`.
-/
