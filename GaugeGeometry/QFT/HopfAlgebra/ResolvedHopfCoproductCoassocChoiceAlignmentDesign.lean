import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarGeometryHeadline

/-!
# R-6c-body-336 — choice-alignment design: generic engine REUSES, but the forward leaf needs biUnion widening (judgment)

Three-hundred-and-thirty-sixth genuine-body step — the choice-alignment design scout.  Verdict: the generic
`recoverChoiceValue` priority engine + tag lemmas REUSE verbatim (supply concrete multi-star regions + 3 exclusivities,
no new engine), BUT the generic `forward_outer_value` route is NOT reusable — its `promotedOf` leaf is the singleton
`promote_collapse`/floor-297 shape (FALSE for multi-star); the multi-star assembly must WIDEN it to the biUnion form
(body-334).  The right/survivor `componentToRight` is the (light) Front-2 entry.

## REUSE — the generic engine + tag lemmas plug in (no new choice def)

`recoverChoiceValue` (OuterUnionRegionTagValue.lean:101-110) and `left_tag`/`right_tag`/`forest_tag` (:113-136) are GENERIC
over `T : ResolvedRegionTagValueSupply F V`, reading regions only through `T.Closure.Assembly.Left.leftResidual` /
`.Region.rightRecovered` / `.Region.forestRecovered` / `T.forestTag`.  The tag lemmas consume ONLY the three exclusivities
`right_notMem_left` / `forest_notMem_left` / `forest_notMem_right` (:80-94).  The `leftResidual` / `rightRecovered` /
`forestRecovered` are DERIVED `def`s over sub-supply component-fields, so the multi-star wiring is a `where`-assignment:

```text
Assembly.Left.representedInQuotient := representedByTouched   ⟹ leftResidual = leftResidualTouched   (defeq, filterElements)
Assembly.Region.componentToForest   := M.parent               ⟹ forestRecovered = forestRecoveredMulti (both ofElements ∘ image)
Tags.forestTag                       := M.forestTag F          (body-333 construction)
Assembly.Region.componentToRight     := <survivor reembed>     (Front-2, below)
```

## CRITICAL CAVEAT — the generic `forward_outer_value` leaf is FALSE for multi-star; WIDEN to biUnion

The generic `promotedOf_recovered_eq` (ForwardOuterValue.lean:112-157) proves `promotedOf.elements = forestRecovered z
.elements` VIA `promote_collapse` (`(promote γ (forestTag γ)).elements = {γ}`, :59-62).  For multi-star this is WRONG on
BOTH counts:

* `promote_collapse = {γ}` is FALSE — `promote (parent δ) (innerIdx δ)` has elements `touchedOuterComponents z δ` (a
  COLLECTION, body-334 `promote_parent_innerIdx_elements`), not the singleton `{parent}`.
* `forestRecovered.elements = {parents}` and `parents ∉ z.1.1.elements` (orphans) — so `coverage_value`
  (`leftResidual ∪ promotedOf = z.1.1`, ForwardOuterValue.lean:160-172) would need `forestComponentMem` = floor-297 (FALSE).

The CORRECT multi-star leaf is the biUnion form (all PROVED, bodies 333-334):
```text
promotedOf.elements = ⋃_{γ ∈ forestRecovered} (promote γ (forestTag γ)).elements       (biUnion + forest_tag + promotedComponentElements_inr)
                    = ⋃_{δ} (promote (parent δ) (innerIdx δ)).elements                  (forestTag_of_parent, HEq transport, body-333)
                    = ⋃_{δ} touchedOuterComponents z δ = promotedTouchedUnion z          (promote_parent_innerIdx_elements, body-334)
                    = representedForestTouched z                                          (promotedTouchedUnion_eq_represented, body-334)
selectedOuterRawOf.elements = leftResidualTouched z ∪ representedForestTouched z = z.1.1.elements   (touched_coverage, D5 body-323)
```
So `forward_outer_value_multi` is a NEW proof (biUnion + the `forestTag_of_parent` transport + body-334), NOT the generic
289 route.  This is the real work of the assembly — the generic engine reuses for the CHOICE/tags, but the forward-outer
element equality is re-proved through the touched biUnion, with NO `promote_collapse` and NO floor-297.

## Cross-disjointness split

* **left↔forest** (`forest_notMem_left`, `left_forest_disjoint`) — FULLY MECHANICAL from the touched partition:
  `leftResidualTouched = filter ¬representedByTouched`, `forestRecoveredMulti.elements = represented image`, disjoint by
  `touched_coverage` / `representedForestTouched_eq_biUnion` (body-323).
* **right↔left / right↔forest** (`right_notMem_left`, `forest_notMem_right`, `left_right_disjoint`,
  `right_forest_disjoint`) — need the concrete right map to STATE, but are D4/D5-adjacent: right lives in
  `rightDomain z = z.2.1.elements.filter (Disjoint · starOfZ)` (star-AVOIDING), the exact negation of `forestDomain`
  (star-touching); at the vertex level right and forest do not overlap.

## Front-2 entry — `componentToRight` = the LIGHT survivor reembed (NOT a de-contraction)

The right region needs `componentToRight : {x // x ∈ rightDomain z} → ResolvedFeynmanSubgraph G`
(RegionConstructionValue.lean:50) + `rightComponentCD` + `rightComponentDisjoint`.  A star-AVOIDING quotient survivor
lifts STRAIGHT back to an outer right-primitive with NO promotion/de-contraction — via `survivorReembed` /
`survivorReembedOfDisjoint` (ResolvedSurvivorEmbedSupport.lean:90-96 / ResolvedSurvivorEmbedComplement.lean:68).  Contrast
the forest half's heavy `parent`/`innerIdx` de-contraction.  This is the genuine Front-2 entry and it is LIGHT.

Per the HALT: design judgment pin — the reuse verdict, the biUnion-widening caveat, the cross-disjointness split, and the
Front-2 survivor-reembed entry are recorded; NO wiring/assembly is built; `forestTag_agrees` (inverse-side) is NOT
entered; floor-297/298 and the singleton `promote_collapse` are NOT reused; cross-disjointness is NOT inferred from
carrier membership; no facade, no flat term, no `forgetHopf`.  STATUS: choice alignment + the biUnion forward-outer proof
+ the survivor right map remain — Front-1/Front-2 boundary is now named at `componentToRight`.
-/
