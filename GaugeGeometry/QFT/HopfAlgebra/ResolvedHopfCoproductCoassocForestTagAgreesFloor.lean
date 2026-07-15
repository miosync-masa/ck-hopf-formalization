import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestValueEqValue

/-!
# R-6c-body-295 — `forestTag_agrees` is an honest component-level model leaf (floor pin)

Two-hundred-and-ninety-fifth genuine-body step, a floor-pin scout (no new geometry).  It audits whether body-288's
`forestTag_agrees` can be discharged by defining the opaque `forestTag` (body-282) occurrence-derived, and records the
verdict: **it cannot — `forestTag_agrees` is a genuine floor leaf.**  Imports body-288 so the pin stays honest against
the source.

## The question

`forestTag` (`ResolvedRegionTagValueSupply.forestTag`, OuterUnionRegionTagValue.lean:76) is an ARBITRARY field: it
returns the forest index `Bᵧ` of a forest-recovered component `γ ∈ forestRecovered z` for a GENERIC
`z : ForestBlockCodType D G`.  Body-288's `forestTag_agrees` (ForestValueEqValue.lean) asserts, at the forward image
`z = fwdMapFilteredValue q`, that this `forestTag` equals `forestTag_fwd_value` — the `choiceAt`-recovered `B` from
body-278's forest bridge.  Could `forestTag` be DEFINED as an occurrence's `B` so this becomes `rfl` / provable?

## The three obstructions (why it is a floor)

* **Missing witness.**  The region core `ResolvedRegionConstructionFromSectorValueSupply` (body-277,
  RegionConstructionValue.lean:60) keeps only the parent `componentToForest : {x // x ∈ forestDomain z} →
  ResolvedFeynmanSubgraph G` — no forest index, no occurrence.  A `forestDomain` component `δ` is a bare star-touching
  quotient subgraph (RegionConstructionFromSector.lean:88-90) with NO attached `B`.
* **No `B`-uniqueness.**  There is no `componentToForest` injectivity / `forestDomain`-to-parent injectivity field (only
  `forestComponentDisjoint`).  So even a hypothetical `forestTag z γ := B` is not well-defined for a generic `z`.
* **`B` is `choiceAt`-sourced, forward-image only.**  The only exact `B` lives in `ForestChoiceOccurrence`
  (`⟨γ, B, hchoice : choiceAt γ = inr B⟩`, Remnant.lean:50-56) / `ForestPrimitiveIndex.toOccurrence`
  (SectorIndexBridge.lean:53), which require a split choice's `choiceAt` — available only at forward images
  `fwdMapFilteredValue q`, never for a generic codomain `z`.

## Verdict

Even enriching the core with a region-side `componentToForestOccurrence` + parent coherence + `B`-uniqueness (a genuine
S-free supply, VERDICT 2) would NOT eliminate `forestTag_agrees`: the region-side `B` for a generic `z` has no `choiceAt`
to read, so it is an INDEPENDENT de-contraction datum, not definitionally the `choiceAt`-sourced `forestTag_fwd_value`.
The equality of the two occurrences' `B` is exactly what `forestTag_agrees` names — it relocates, it does not become
`rfl`.

> **`forestTag_agrees` is a genuine component-level model leaf (floor).**  `forestTag` (body-282) is honestly arbitrary
> because the region core retains no `B`/occurrence for a generic `z`, no `componentToForest` injectivity pins `B`, and
> the only exact `B` is the `choiceAt`-sourced one available exclusively at forward images — which is precisely the
> agreement `forestTag_agrees` asserts.

This pins the floor for one of the six component-level leaves.  The remaining reduction work is `promote_collapse`,
`forestComponentMem`, `represented_cases` (body-289 region-core geometry); `survivor_mem_value` / `remnant_mem_value`
are reduced to their two-direction floors (bodies 293/294).

Per the HALT: this is a docstring floor-pin only; the import keeps the pin honest against body-288.  No declarations
beyond this docstring; no facade, no flat term, no `forgetHopf`.
-/
