import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightSectorWiringScout

/-!
# R-6c-body-225 — sector floor limit map: the sector-inverse route stops at the abstract-region floor (docs anchor)

Two-hundred-and-twenty-fifth genuine-body step, a documentation anchor (no new geometry).  Body-224's scout found the
eight sector `sound` / `complete` directions cannot be reduced further through the sector inverse; this module records
that limit and the pivot, importing the wiring scout so the map stays type-checked.  Reader-facing narrative:
`CK_HOPF_FORMALIZATION_MAP.md` §"R-6c body 224"; proof-dependency map: `CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c body 224".

## The negative finding (body-224)

```text
Sector inverse is NOT the next reduction path.
- The region maps componentToRight / componentToForest are ABSTRACT FIELDS
  (only rightComponentCD / rightComponentDisjoint), and ResolvedRegionConstructionFromSectorSupply is NEVER
  instantiated — so right_surj / componentToRight_spec cannot even be named in a proof about them.
- The sector index over fwdMap q gives a parent in (selectedOuterOf q).1 (the recovered / left-factor outer),
  NOT q.1.1 (the original domain outer); no lemma equates them.
- The sector inl-false / inr tag is over fwdMap q's recoverChoice-derived structure, NOT q.2.
Therefore the eight sound/complete leaves are the honest floor for the ABSTRACT region construction;
discharging them (not just fielding) requires concretizing the whole region construction.
```

The **sector-inverse route is retired / saturated**: no further abstract reduction of the sector bridges is available.

## Residual (the honest floor now)

* **sector / round-trip — floor reached** — the eight `sound` / `complete` directions (bodies 219–222); no further
  abstract reduction via the sector inverse;
* **forward compatibility (reducible candidate)** — `forestTag` / `recoverChoice_forest_eq` / `promote_collapse`
  (body-188), `forestComponentMem` (body-185), `represented_cases` (body-180);
* **disjoint / carrier (reducible candidate)** — the pairwise disjointnesses (body-158) and the recovered-outer
  carrier closure (body-159);
* **non-region base** — contract geometry, measure, survivor/remnant `Inj`/`Gen` providers, `carrier_isProperForest`
  / `rep` / `selectedOuter_mem`.

## Note

The round-trip and sector layers are fully mapped to their floors; the next front is the disjoint / carrier candidates
(bodies 158/159), which may still admit a shallow provider reduction — leaving the deeper forward compatibility and the
non-region base for later.  No declarations beyond this docstring anchor; the import keeps the map honest against the
source.  No facade, no flat term, no `forgetHopf`.
-/
