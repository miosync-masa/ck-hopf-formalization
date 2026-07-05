import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRoundTripComponentPartition
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightPrimitiveFactorComplete

/-!
# R-6c-body-170 — right region sector bridge: `rightRecovered (forward q)` ↔ right-primitive components

Hundred-and-seventieth genuine-body step, the survivor (right) side of the sector bridge.  On the forward image
`fwdMap q`, the right-recovered region's components are exactly `q`'s right-primitive components (`q.2 γ = inl
false`), by the sector survivor round-trip.  This compresses the survivor side of the backward-outer partition
(body-168's `recovered_region_membership`) to a single named bridge.

## The bridge (fielded)

`ResolvedRightRegionSectorBridgeSupply D S Region` fields the single membership equivalence

```text
rightRecovered_forward_membership :
  γ ∈ (rightRecovered (fwdMap q)).elements  ↔  rightPrimSelected q γ
```

where `rightPrimSelected q γ = ∃ hγ, q.2 ⟨γ, hγ⟩ = inl false` (body-120) — "`γ` is a component of `q.1` with choice
`inl false`".

## Why it is the survivor round-trip

For `z = fwdMap q = ⟨selectedOuterOf q, quotientForest q⟩`, the quotient `B = quotientForest q` splits by the outer
star into survivors (`rightDomain z`) and remnants; `rightRecovered z` is the `componentToRight` image of the
survivors (body-156).  On a *forward* image, the survivors of `B` are exactly the images of `q`'s right-primitive
components under the forward survivor map, and `componentToRight` inverts that (the sector `right_left_inv` /
`right_right_inv`, `SectorLeafBundle`) — so `rightRecovered (fwdMap q) = ` the right-primitive components of `q`.
The full component round-trip is the sector survivor inverse law, fielded here as the single membership bridge.

## Consequence

The survivor side of body-168's `recovered_region_membership` — the `γ ∈ rightRecovered` branch — is now exactly
`rightPrimSelected q γ` (`q.2 γ = inl false`).  With the forest analogue (`forestRecovered` ↔ `inr`, next body) and
the left residual, `recovered_region_membership` becomes the tautology "every component of `q.1` has some tag", and
the backward-outer partition is fully in choice-tag vocabulary.

Per the HALT: the `componentToRight` inverse law is not proved; the survivor round-trip is fielded as the single
membership bridge `rightRecovered_forward_membership`; the forest / `inr` side is untouched.

Landed:

* `ResolvedRightRegionSectorBridgeSupply D S Region` — the survivor membership bridge.

Toolkit body (like body-164/165).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-170 — the right region sector bridge.**  On a forward image, the right-recovered region's
components are exactly `q`'s right-primitive components (`q.2 γ = inl false`) — the survivor sector round-trip, as
a single membership bridge. -/
structure ResolvedRightRegionSectorBridgeSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- The right-recovered components of the forward image are `q`'s right-primitive (`inl false`) components. -/
  rightRecovered_forward_membership : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : ResolvedFeynmanSubgraph G),
    γ ∈ (Region.Union.rightRecovered (fwdMap S q)).elements ↔ rightPrimSelected q γ

end GaugeGeometry.QFT.Combinatorial
