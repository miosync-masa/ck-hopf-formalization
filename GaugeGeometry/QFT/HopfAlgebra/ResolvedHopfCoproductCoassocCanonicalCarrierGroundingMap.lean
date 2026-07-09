import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCanonicalCarrierProper

/-!
# R-6c-body-229 — canonical carrier grounding map: bodies 227–228, the first floor leaf grounded (docs anchor)

Two-hundred-and-twenty-ninth genuine-body step, a documentation anchor (no new geometry).  It fixes the turning point
where the canonical-instance phase begins: body-227 (scout) established that the canonical carrier discharges only one
of the four closure floor leaves, and body-228 (proof) grounded that one — `carrier_isProperForest` — into a canonical
model instance.  Imports body-228 so the map stays type-checked.  Reader-facing narrative:
`CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies 226–228"; proof-dependency map: `CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c
bodies 226–228".

## The turning point (bodies 227–228)

```text
227 scout:
  Canonical carrier does NOT discharge all closure leaves.
  mem_properDisjointAdmissibleDivergentSubgraphs re-expresses ∈ carrier as IsProperForest ∧ disjoint ∧ …,
  so for a CONSTRUCTED object the obligation is still its properness/disjointness (abstract componentToRight geometry).
  It only makes carrier_isProperForest free. No canonical D exists yet — it must be constructed.

228 proof:
  ResolvedCanonicalCarrierProperSupply (wrapper)
    index : (G) → ResolvedProperForestFiniteIndex G     -- carrier + mem_proper (ResolvedCoproduct.lean:172)
    carrier G := (index G).carrier
    carrier_isProperForest := fun G A hA => (index G).mem_proper A hA     -- PROVED, not a field
  .toData : ResolvedCoproductProperForestData
  .toCarrierProperProvider : ResolvedCarrierProperProvider W.toData     -- body-137 leaf, constructed
```

## Status table (the four closure floor leaves)

```text
carrier_isProperForest   grounded by 228 (proved from ResolvedProperForestFiniteIndex.mem_proper)
selectedOuter_mem        construction-specific (constructed object must be a canonical member)
region cross-disjoint    construction-specific (3 regions must be pieces of one member / representedInQuotient concrete)
recovered_outer_mem      construction-specific (constructed region union must be a canonical member)
```

## The note that matters

```text
Canonical carrier is not merely repackaging:
it genuinely discharges 137 (carrier_isProperForest).
But selectedOuter / recoveredOuter membership still requires proving
the constructed objects are proper / disjoint / admissible canonical members.
```

## Residual (refreshed)

* **grounded** — `carrier_isProperForest` (body-228, via the proper-forest finite index);
* **still construction-specific** — `selectedOuter_mem` (128), `recovered_outer_mem` (159), the region pairwise
  disjointnesses (158);
* **other floors** — the eight sector `sound` / `complete` directions (bodies 219–222), forward compatibility
  (`forestTag` / `promote_collapse` 188, `forestComponentMem` 185, `represented_cases` 180), and the non-region base
  (contract geometry, measure, survivor/remnant `Inj`/`Gen`, `rep`, and the heavy canonical fields `index` / `starOf`
  / `hCD` / `mapPerm` naturalities left fielded by body-228).

## Note

The next front is a **`mem_rewrite` adapter** (body-230) reshaping `selectedOuter_mem` / `recovered_outer_mem` from
carrier membership into "the constructed forest is proper / disjoint / admissible" — a reshaping (not a proof) that
puts the residual obligations into canonical form for the constructed regions.  No declarations beyond this docstring
anchor; the import keeps the map honest against the source.  No facade, no flat term, no `forgetHopf`.
-/
