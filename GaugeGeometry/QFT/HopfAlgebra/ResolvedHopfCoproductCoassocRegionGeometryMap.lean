import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterUnionRegionsConcrete
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionTagsConcrete
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionStarFacts
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredChoiceMembership
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteRoundTripObligations

/-!
# R-6c-body-155 — region geometry map: the in-source region-layer inventory (docs anchor)

Hundred-and-fifty-fifth genuine-body step, a documentation anchor (no new geometry).  After bodies 149–154 the
backward map's proof-shape is closed and the remaining content is localised onto the three concrete regions of the
recovered outer forest.  This module records the region-geometry chain and the residual region providers in the
source tree, importing the region-layer modules so the map stays type-checked.  The reader-facing narrative is
`CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies 149–154"; the proof-dependency map is `CK_HOPF_DEPENDENCY_GRAPH.md`
§"R-6c bodies 149–154".

## Region geometry chain (all axiom-clean `[propext, Classical.choice, Quot.sound]`)

```text
ResolvedOuterUnionRegionsConcreteSupply   (body-153: unionOuter = (left ∪ right) ∪ forest, union_eq PROVED)
   .toOuterUnionConstructionSupply → ResolvedOuterUnionConstructionSupply (body-145)
ResolvedRegionTagDefinitionSupply         (body-152: recoverChoice = region-priority dite, 3 tags PROVED)
   .toRegionChoiceRoundTripSupply → ResolvedRegionChoiceRoundTripSupply (body-146)
ResolvedConcreteRoundTripObligationSupply (body-154: 4 named round-trips A / B / A' / p)
   .toRegionRoundTripReductionSupply → ResolvedRegionRoundTripReductionSupply (body-147)
      → WitnessSplitBranchCombiner (144) → WitnessSplitConcrete (141) → WitnessSplitCoverSupply (139)
      → BijectionProvider (131) → coassoc_gen
ResolvedRegionStarFactSupply              (body-150: toFun_mem star facts, mixed PROVED)
ResolvedRecoveredChoiceMembershipSupply   (body-151: invFun_mem p-tags, forest PROVED)
```

## Proved / banked (the classifier + assembly layer)

* four membership fields — `toFun_mem` / `invFun_mem` plumbing (bodies 132/133/150/151);
* three region tags (body-152, region-priority `recoverChoice`);
* `union_eq` (body-153, `Finset.ext` + `union_elements`);
* summand-agreement bundle (body-129); survivor/remnant provider (body-148); base providers (bodies 137/140/124).

## Residual region providers (the honest floor)

* **region construction** (body-153) — `leftResidual` ("not represented in `B`"), `rightRecovered`
  (`componentToRight` image), `forestRecovered` (`componentToForest` image), the two cross-disjointnesses, and the
  carrier membership;
* **round-trips** (body-154) — `forward_outer` (A-reconstruction), `forward_quotient` (B-reconstruction),
  `backward_outer` (A'-recovery), `backward_choice` (p-recovery);
* **classifiers** (bodies 150/151/152) — `survivor_avoids` / `mixed_remnant_empty` / `forest_quotient_touch`,
  `mixed_ne_pR` / `mixed_ne_pL`, `forestTag` and the region exclusivities;
* **non-region base** — contract `vertices_eq` (body-140), measure (body-124), the star/global-gap kernel
  (`ResolvedStarGlobalGapSupply`), survivor/remnant Inj/Gen (body-148), and `carrier_isProperForest` (body-137) /
  `rep` / `selectedOuter_mem` (body-128).

## Superseded / off the canonical path

* the σ-cover common-cover route (bodies 36–87) — the *other* formulation, kept separate (body-139 scout);
* the `boundary_tail_eq` well-founded induction (body-89) — superfluous once the nested-forest bijection is direct.

No declarations beyond this docstring anchor; the imports keep the map honest against the source.  No facade, no
flat term, no `forgetHopf`.
-/
