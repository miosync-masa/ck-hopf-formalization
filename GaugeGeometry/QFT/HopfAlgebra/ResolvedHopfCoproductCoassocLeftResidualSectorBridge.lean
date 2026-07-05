import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRoundTripComponentPartition
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftSelectConcrete

/-!
# R-6c-body-172 — left residual sector bridge: `leftResidual (forward q)` ↔ left-primitive components

Hundred-and-seventy-second genuine-body step, the third and last region bridge (the left-primitive side).  On the
forward image `fwdMap q`, the left-residual region's components are exactly `q`'s left-primitive components (`q.2 γ
= inl true`).  With the survivor (body-170) and forest (body-171) bridges, this completes the region bridge: every
recovered region corresponds to a choice tag, so the backward-outer partition (body-168's
`recovered_region_membership`) is the choice-tag trichotomy.

## The bridge (fielded)

`leftSelectedConcrete q γ = ∃ hγ, q.2 ⟨γ, hγ⟩ = inl true` (the `inl true` predicate, body-117/`LeftSelectConcrete`).
`ResolvedLeftResidualSectorBridgeSupply D S Region` fields the single membership equivalence

```text
leftResidual_forward_membership :
  γ ∈ (leftResidual (fwdMap q)).elements  ↔  q.leftSelectedConcrete γ
```

## Why it is the left-residual identity

`leftResidual z = z.1.filterElements (¬ representedInQuotient z)` (body-157), and on the forward image `z = fwdMap
q` the represented components are exactly the survivor (`rightRecovered` ↔ `inl false`, body-170) and remnant
(`forestRecovered` ↔ `inr`, body-171) components; so the *not* represented components are exactly the
left-primitive (`inl true`) ones.  The left-residual region is the identity on `q`'s left-primitive components (no
sector round-trip — they are untouched by the quotient), so the bridge is the "left residual = the untouched
left-primitives" fact, fielded here at the same granularity as the survivor / forest bridges.

## Consequence — the three region bridges

| region | body | bridge |
|---|---|---|
| left  | 172 | `leftResidual (fwdMap q)` ↔ `leftSelectedConcrete q` (`inl true`) |
| right | 170 | `rightRecovered (fwdMap q)` ↔ `rightPrimSelected q` (`inl false`) |
| forest| 171 | `forestRecovered (fwdMap q)` ↔ `forestChoiceSelected q` (`inr`) |

Every component of `q.1` has exactly one tag (`inl true` / `inl false` / `inr`), so the three region memberships
partition `q.1.1.elements` — the assembly proving body-168's `recovered_region_membership` (next body).

Per the HALT: `representedInQuotient`'s equality with survivor ⊔ remnant is not proved here; the sector inverse
laws are not entered; the left-residual identity is fielded as the single membership bridge, matching bodies
170/171.

Landed:

* `ResolvedLeftResidualSectorBridgeSupply D S Region` — the left-primitive membership bridge.

Toolkit body (like body-170/171).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-172 — the left residual sector bridge.**  On a forward image, the left-residual region's
components are exactly `q`'s left-primitive components (`q.2 γ = inl true`) — the untouched left-primitives, as a
single membership bridge. -/
structure ResolvedLeftResidualSectorBridgeSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- The left-residual components of the forward image are `q`'s left-primitive (`inl true`) components. -/
  leftResidual_forward_membership : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : ResolvedFeynmanSubgraph G),
    γ ∈ (Region.Union.leftResidual (fwdMap S q)).elements
      ↔ ResolvedCoassocSplitChoice.leftSelectedConcrete q γ

end GaugeGeometry.QFT.Combinatorial
