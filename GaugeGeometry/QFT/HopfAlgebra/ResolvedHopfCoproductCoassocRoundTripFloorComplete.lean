import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocGeometryFloorAssembly

/-!
# R-6c-body-300 — the round-trip layer is complete at its final geometric floor (docs anchor)

Three-hundredth genuine-body step, a documentation anchor (no new geometry).  It fixes the fourth and final completion
node of the R-6c campaign: the round-trip layer is closed at its irreducible local-geometry floor.  Imports body-299 so
the map stays type-checked against the source.  Reader-facing narrative: `CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies
293–299"; proof-dependency map: `CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c bodies 293–299".

## The headline

```text
The canonical R-6c round-trip layer is complete at its final geometric floor.

Eight local component-level model facts imply resolved coproduct coassociativity;
no proof-shape, migration, global-HEq, or abstract round-trip obligation remains.
```

## The six-leaf → eight-fact map

```text
survivor_mem_value   → survivor_sound_value + survivor_complete_value   (293, z-local)
remnant_mem_value    → remnant_sound_value  + remnant_complete_value    (294, z-local)
forestComponentMem   → forest_parent_mem_value                          (297, pointwise floor)
represented_cases    → represented_forest_complete_value                (298, pointwise floor)
forestTag_agrees     → forestTag_agrees                                 (295, floor pin)
promote_collapse     → promote_collapse                                 (296, floor pin)
```

`coassoc_gen_of_geometry_floor` (body-299) bundles the eight over ONE `Data` and chains through body-291/286; the old six
leaves are gone from its arguments — only the eight floor facts + the base leaves remain.

## Interface, not backlog

The eight facts are the honest geometry any concrete region / carrier *model* must supply — de-contraction
(`promote_collapse`), parent membership (`forest_parent_mem_value`, `represented_forest_complete_value`), tag occurrence
(`forestTag_agrees`), and the survivor / remnant star sound/complete directions.  They are NOT unfinished proof-shape
obligations.

## Two-layer status

```text
round-trip geometry layer   exactly EIGHT local model facts
complete theorem            those eight + (inside Data) region sound/complete + carrier closure + F/V + base leaves
```

## The four completion nodes

```text
271  parametric theorem            (conditional coassoc from the parametric model)
287  construction migration        (concrete cover off the filtered root)
292  global-identity elimination   (all abstract round-trip / global-HEq obligations gone)
300  final local-geometry floor    (round-trip residual = eight local model facts)
```

The canonical path to `coassoc_gen_of_geometry_floor` is entirely S-free, `Forward`-free, and legacy-adapter-free.
**Full unconditional resolved coassociativity is still not claimed complete** — a concrete phase-1b model instance must
discharge the eight local facts + the region / carrier supplies — but the round-trip layer is now closed at its final,
irreducible geometric floor.

Per the HALT: this is a docstring anchor only; the import keeps the pin honest against body-299.  No declarations beyond
this docstring; no facade, no flat term, no `forgetHopf`.
-/
