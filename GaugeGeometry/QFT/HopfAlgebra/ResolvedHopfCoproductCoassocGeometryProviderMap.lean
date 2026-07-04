import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionRoundTripReduction
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocContractGeometryProvider
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSurvivorRemnantProviders
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCarrierProperProvider

/-!
# R-6c-body-149 — geometry provider map: the in-source residual inventory (docs anchor)

Hundred-and-forty-ninth genuine-body step, a documentation anchor (no new geometry).  After bodies 137–148 the
proof-shape phase is complete: the whole `Δᵣ`-coassociativity is assembled and axiom-clean, and every remaining
obligation is a named *local* geometry / measure / kernel fact.  This module records the canonical final chain and
the residual provider list in the source tree, importing the top-level provider modules so the map stays
type-checked alongside them.  The reader-facing narrative is `CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies 137–148";
the proof-dependency map is `CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c bodies 137–148".

## Canonical final chain (all axiom-clean `[propext, Classical.choice, Quot.sound]`)

```text
ResolvedRegionRoundTripReductionSupply   (body-147: region tags + 2 Sigma-level round-trips)
   .toBranchSupply → witnessSplit          (body-144/141: two-branch backward map)
      + ResolvedConcreteSummandBundleSupply (body-129: the whole PRODUCT side)
      + ResolvedContractGeometryProvider    (body-140: contract-twice vertices_eq)
      + ResolvedSurvivorRemnantProvider     (body-148: survivor/remnant Inj/Gen)
      + ResolvedMeasureLeafSupply           (body-124: cd_nonempty + contract_preserves_CD)
      + ResolvedCarrierProperProvider       (body-137: carrier_isProperForest)
   → ResolvedForestBlockBijectionSideSupply (body-130) → ResolvedOuterMixingAssemblySupply (body-113)
   → ResolvedForestBlockMapData → forest_block → forest_core → nested_matching → boundary_tail_eq
   → coassoc_gen (x) : D.coassocLeft (X x) = D.coassocRight (X x)
```

## The residual provider list (the honest floor — named local geometry / measure / kernel facts)

* **region geometry** (bodies 145–147) — the outer union (`leftResidual` / `rightRecovered` = `componentToRight` /
  `forestRecovered` = `componentToForest` / `unionOuter` / `union_eq`), the three region tags with `forestRecovered`
  empty (mixed) / nonempty (forest), and the two `Sigma`-level round-trips (`forward_outer` / `forward_quotient` /
  `backward_outer` / `backward_choice`);
* **star facts** (body-132, `mixed_avoids_star` / `forest_touches_star`) and `forestChoiceCarrier` membership (body-133);
* **contract geometry** (body-140 → `vertices_eq`, the three-route star correspondence of bodies 27–32);
* **measure** (body-124, `cd_nonempty` + `contract_preserves_CD`);
* **star / global-gap kernel** (`ResolvedStarGlobalGapSupply`, powering `survivorInj` / `remnantInj` via `occurrence_inj`);
* **survivor / remnant** (body-148, the four Inj/Gen leaves);
* **base** — `carrier_isProperForest` (body-137), the representative lift, and `selectedOuter_mem` (body-128 closure).

## Superseded / off the canonical path

* the σ-cover common-cover route (bodies 36–87) — the *other* formulation; its `cover_on` / `inj_on` are not reused
  for the outer-mixing route (kept separate, body-139 scout);
* the `boundary_tail_eq` well-founded induction (body-89) — superfluous once the nested-forest bijection is direct.

No declarations beyond this docstring anchor; the imports keep the map honest against the source.  No facade, no
flat term, no `forgetHopf`.
-/
