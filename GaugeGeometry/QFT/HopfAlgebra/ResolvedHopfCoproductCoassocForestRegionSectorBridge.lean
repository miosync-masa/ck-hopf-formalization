import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRoundTripComponentPartition

/-!
# R-6c-body-171 — forest region sector bridge: `forestRecovered (forward q)` ↔ forest-choice components

Hundred-and-seventy-first genuine-body step, the remnant (forest) side of the sector bridge — the twin of body-170.
On the forward image `fwdMap q`, the forest-recovered region's components are exactly `q`'s forest-choice
components (`q.2 γ = inr Bᵧ`), by the sector remnant round-trip.  This compresses the forest side of the
backward-outer partition (body-168's `recovered_region_membership`) to a single named bridge.

## The bridge (fielded)

`forestChoiceSelected q γ = ∃ hγ, ∃ B, q.2 ⟨γ, hγ⟩ = inr B` — "`γ` is a component of `q.1` with a forest choice
`inr B`" (the `inr` mirror of `rightPrimSelected`, body-120).  `ResolvedForestRegionSectorBridgeSupply D S Region`
fields the single membership equivalence

```text
forestRecovered_forward_membership :
  γ ∈ (forestRecovered (fwdMap q)).elements  ↔  forestChoiceSelected q γ
```

## Why it is the remnant round-trip

For `z = fwdMap q = ⟨selectedOuterOf q, quotientForest q⟩`, the quotient `B = quotientForest q` splits by the outer
star into survivors and remnants (`forestDomain z`); `forestRecovered z` is the `componentToForest` image of the
remnants (body-156).  On a *forward* image, the remnants of `B` are exactly the de-contracted images of `q`'s
forest-choice components, and `componentToForest` inverts that (the sector `forest_left_inv` / `forest_right_inv`,
`SectorLeafBundle`) — so `forestRecovered (fwdMap q) = ` the forest-choice components of `q`.  The exact forest
sub-forest `Bᵧ` is recovered up to the de-contraction (a `HEq`, deferred); the membership is only "`γ` has an `inr`
tag".  The full component round-trip is the sector remnant inverse law, fielded here as the single membership
bridge.

## Consequence

With the survivor bridge (body-170, `rightRecovered` ↔ `inl false`), the forest bridge here (`forestRecovered` ↔
`inr`), and the left-residual bridge (next body, `leftResidual` ↔ `inl true`), body-168's
`recovered_region_membership` becomes the choice-tag trichotomy — every component of `q.1` has exactly one tag
(`inl true` / `inl false` / `inr`), so the backward-outer partition is fully in `q.2` vocabulary.

Per the HALT: the `componentToForest` inverse law / remnant de-contraction is not entered; the exact `Bᵧ`
recovery is left to the sector `HEq`; the remnant round-trip is fielded as the single membership bridge, at the
same granularity as body-170's survivor bridge.

Landed:

* `forestChoiceSelected` — the forest-choice component predicate (`inr` mirror of `rightPrimSelected`);
* `ResolvedForestRegionSectorBridgeSupply D S Region` — the remnant membership bridge.

Toolkit body (like body-170).  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **R-6c-body-171 — the forest-choice component predicate.**  `γ` is a component of `q.1` with a forest choice
`inr B` (the `inr` mirror of `rightPrimSelected`, body-120). -/
def forestChoiceSelected (q : ResolvedCoassocSplitChoice D G) (γ : ResolvedFeynmanSubgraph G) : Prop :=
  ∃ hγ : γ ∈ q.1.1.elements,
    ∃ B, ResolvedCoassocSplitChoice.choiceAt q ⟨γ, hγ⟩ = Sum.inr B

/-- **R-6c-body-171 — the forest region sector bridge.**  On a forward image, the forest-recovered region's
components are exactly `q`'s forest-choice components (`q.2 γ = inr Bᵧ`) — the remnant sector round-trip, as a
single membership bridge. -/
structure ResolvedForestRegionSectorBridgeSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- The forest-recovered components of the forward image are `q`'s forest-choice (`inr`) components. -/
  forestRecovered_forward_membership : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : ResolvedFeynmanSubgraph G),
    γ ∈ (Region.Union.forestRecovered (fwdMap S q)).elements ↔ forestChoiceSelected q γ

end GaugeGeometry.QFT.Combinatorial
