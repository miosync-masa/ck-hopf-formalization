import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestRegionSectorBridge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionConstructionFromSector

/-!
# R-6c-body-215 — forest sector bridge scout: G-side `forestRecovered_forward_membership` reduced (clone of body-213)

Two-hundred-and-fifteenth genuine-body step, a scout that turned into a reduction of the lighter forest-sector leaf,
body-171's `forestRecovered_forward_membership` — the `inr` mirror of body-213's `rightRecovered_forward_membership`.

## The scout finding — the two forest leaves, and their relation to bodies 188/189

* `forestRecovered_forward_membership` (body-171, G-side, over `fwdMap q`) and `remnant_mem` (body-207,
  quotient-side, over recovered `z`) are the forest duals of the right-sector leaves (bodies 213/211).
* **They do NOT share the forward-outer de-contraction compatibility (bodies 188/189).**  Body-188/189/183 are the
  *forward-outer* side (`promoted_eq_forestRecovered`, `promote_collapse`, over the recovered choice at the G-region
  level, via `promote`); the two sector leaves are the *round-trip* side (over `fwdMap q` / the quotient graph, via
  `componentToForest` / `remnantComponent`).  They share the de-contraction *kernel* (the `componentToForest` ↔
  `promote` inverse pair) only as **inverse directions on different objects** — the dual-not-same pattern of
  body-197/198.  So the forest sector is fielded fresh, not routed through 188/189.
* **The G-side reduces exactly like body-213** (same weight): `forestRecovered_elements_eq` is `rfl`, the wiring
  bridge is a homogeneous `G`-level equality (already `rfl` at the concrete instantiation, body-184), and
  `componentToForest` is an abstract field.  **The quotient-side `remnant_mem` clones body-211's scaffolding** but
  its residual correspondence is heavier: `remnantComponent` lands in the contracted graph with a nontrivial
  `remnantClass_eq` (no `rfl` vertex preservation, unlike `survivorReembed`).  So do the G-side first.

## The G-side reduction (PROVED)

`ResolvedForestRecoveredSectorDecompositionSupply D S Region` fields body-156's construction, the wiring bridge
`forestRecovered_eq`, and the single fresh **forest image correspondence**

```text
forest_image_correspondence : ∀ q γ,
  γ ∈ (forestDomain (fwdMap q)).attach.image (componentToForest (fwdMap q))   -- the G-parents of B's star-touchers
    ↔ forestChoiceSelected q γ                                                 -- ∃ B, q.2 γ = inr B
```

`.forestRecovered_forward_membership` is **proved** (`rw` the bridge, `simp` the `rfl` image shape, apply the
correspondence), and `.toForestRegionSectorBridgeSupply` produces body-171's supply.

## Consequence

The forest G-side is now the single fresh `forest_image_correspondence` (the `componentToForest` round-trip:
star-touching components of `B` pulled back to `q`'s forest-choice parents) plus the wiring bridge.  The heavier
quotient-side `remnant_mem` (body-207) remains — the next body clones body-211's scaffolding for it, leaving its
de-contraction correspondence as the genuine content.

Per the HALT: the `componentToForest` round-trip body is not entered; bodies 188/189 are not routed through; the
quotient-side `remnant_mem` is untouched; only the `ofElements` image reduction over the wiring bridge is proved.

Landed:

* `ResolvedForestRecoveredSectorDecompositionSupply D S Region` — body-156's construction + the wiring bridge + the
  fresh forest image correspondence;
* `.forestRecovered_forward_membership` — body-171's leaf (PROVED from the correspondence);
* `.toForestRegionSectorBridgeSupply` — body-171's supply.

Scout / toolkit body (like body-213).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-215 — the forest recovered sector decomposition supply.**  Body-156's sector region construction, the
wiring bridge to the abstract union region, and the fresh forest image correspondence (the `componentToForest`
round-trip). -/
structure ResolvedForestRecoveredSectorDecompositionSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- Body-156's sector region construction (the `componentToForest` image). -/
  Construction : ResolvedRegionConstructionFromSectorSupply D S
  /-- Wiring bridge: the abstract union forest region agrees with body-156's construction (element level). -/
  forestRecovered_eq : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    (Region.Union.forestRecovered (fwdMap S q)).elements
      = (Construction.forestRecovered (fwdMap S q)).elements
  /-- The fresh image correspondence: the `componentToForest` G-parents of `B`'s star-touching components are exactly
  `q`'s forest-choice (`inr`) components. -/
  forest_image_correspondence : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : ResolvedFeynmanSubgraph G),
    γ ∈ (forestDomain (fwdMap S q)).attach.image (Construction.componentToForest (fwdMap S q))
      ↔ forestChoiceSelected q γ

namespace ResolvedForestRecoveredSectorDecompositionSupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-215 — body-171's `forestRecovered_forward_membership` from the image correspondence.** -/
theorem forestRecovered_forward_membership
    (F : ResolvedForestRecoveredSectorDecompositionSupply D S Region)
    {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G) (γ : ResolvedFeynmanSubgraph G) :
    γ ∈ (Region.Union.forestRecovered (fwdMap S q)).elements ↔ forestChoiceSelected q γ := by
  rw [F.forestRecovered_eq q]
  simp only [ResolvedRegionConstructionFromSectorSupply.forestRecovered_elements_eq]
  exact F.forest_image_correspondence q γ

/-- **R-6c-body-215 — body-171's forest region sector bridge supply.** -/
def toForestRegionSectorBridgeSupply
    (F : ResolvedForestRecoveredSectorDecompositionSupply D S Region) :
    ResolvedForestRegionSectorBridgeSupply D S Region where
  forestRecovered_forward_membership := fun {G} q γ => F.forestRecovered_forward_membership q γ

end ResolvedForestRecoveredSectorDecompositionSupply

end GaugeGeometry.QFT.Combinatorial
