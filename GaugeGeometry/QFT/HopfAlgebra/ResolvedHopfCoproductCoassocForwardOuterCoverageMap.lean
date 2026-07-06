import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTargetOuterCoverageAssembly

/-!
# R-6c-body-182 — forward outer coverage map: the coverage assembled to its floor (docs anchor)

Hundred-and-eighty-second genuine-body step, a documentation anchor (no new geometry).  After bodies 177–181 the
forward-outer partition is assembled down to its floor: the coverage half is a represented-classification, its three
facts are discharged or isolated, and the whole partition runs out to body-162 in one line.  This module records
that state and the residual leaves, importing the assembly module so the map stays type-checked.  Reader-facing
narrative: `CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies 177–181"; proof-dependency map:
`CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c bodies 177–181".

## The coverage assembly (all axiom-clean `[propext, Classical.choice, Quot.sound]`)

```text
leftResidual_mem      body-178  PROVED by filterElements (leftResidual = A.filter (¬ representedInQuotient))
                                over the fielded wiring bridge leftResidual_eq (abstract union ↔ body-157)
forest recovery box   body-179  forestRecovered_mem + promoted_region_eq — two faces of the one
                                componentToForest de-contraction round-trip, shared in one provider
coverage classifier   body-180  coverage PROVED from represented_cases (represented → representedByForest)
                                by excluded middle; the survivor case is vacuous for the target outer
assembly              body-181  178 + 179 + 180 → 177 → 174 → 167 → 162, predicates pinned
```

## Forward outer final floor (the asymmetry, fully descended)

```text
leftOf side       leftOf_recovered_eq   PROVED by tags (body-174)
coverage side     leftResidual_mem      PROVED by filterElements (body-178)
                  forestRecovered_mem   fielded in the forest-recovery box (body-179)
                  coverage              PROVED from represented_cases (body-180)
promotion side    promoted_region_eq    fielded in the forest-recovery box (body-179)
```

So the only genuinely fielded forward-outer content is the **forest-recovery geometry** (`forestRecovered_mem` +
`promoted_region_eq`, body-179), the **star/remnant classifier** (`represented_cases`, body-180), and the **wiring
bridge** (`leftResidual_eq`, body-178).  Everything else on the forward outer is proved.

## Canonical chain

```text
181 → 177 → 174 → 167 → 162 → 160 → 154 → 147 → witnessSplit → coassoc_gen
```

## Residual (the honest floor now)

* **forward-outer, forest-recovery geometry** — `forestRecovered_mem` and `promoted_region_eq` (body-179, the one
  `componentToForest` / `promote` de-contraction round-trip);
* **forward-outer, classifier + bridge** — `represented_cases` (body-180) and `leftResidual_eq` (body-178);
* **backward-outer** — the three sector bridges (bodies 170/171/172), proved up to `choice_tag_trichotomy` (body-173);
* **`HEq` transports** — `backward_choice_heq` (body-164), `forward_quotient_heq` (body-165);
* **pairwise disjointnesses** (body-158) and the **carrier closure** (body-159);
* **region classifiers** (bodies 150/151/152) and the non-region base (contract `vertices_eq`, measure,
  star/global-gap kernel, survivor/remnant Inj/Gen, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).

## Note

Both outer partitions are at their floors: the backward outer on the three sector bridges + a proved trichotomy, the
forward outer on the forest-recovery geometry + the star/remnant classifier.  The next front is the forest-recovery
geometry — the `componentToForest` inverse / promotion de-contraction, the genuinely geometric remaining leaf.  No
declarations beyond this docstring anchor; the imports keep the map honest against the source.  No facade, no flat
term, no `forgetHopf`.
-/
