import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightRegionSectorBridge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionConstructionFromSector

/-!
# R-6c-body-213 — right recovered sector scout: `rightRecovered_forward_membership` reduced to an image correspondence

Two-hundred-and-thirteenth genuine-body step, a scout that turned into a reduction of body-170's
`rightRecovered_forward_membership` — the G-level / backward twin of the survivor leaf (body-211).

## The scout finding — the abstract `rightEquiv` does NOT discharge it

The proved abstract right-sector inverse (`ResolvedRightSectorEquivSupply.rightEquiv : RightPrimitiveIndex D G s ≃
(rightForest s).elements`, `right_left_inv` / `right_right_inv`) operates on the **sector-index** level over the
**quotient graph** via the *forward* `survivorComponent`.  The leaf's `rightRecovered (fwdMap q)` is built from the
**region** `componentToRight` (body-156, `δ ↦ G-parent`), an *abstract field* with **no** definitional link to the
sector maps (confirmed: nowhere is the region `componentToRight` wired to `RightPrimitiveIndex.toComponent`).  So
`rightEquiv` cannot discharge this G-level backward leaf — a fresh `componentToRight` round-trip bridge is required.
This is heavier than the survivor side (body-211): there `survivorReembed` preserved vertices at `rfl`; here the
backward `componentToRight` has no such collapse.

## The reduction (PROVED)

Since `rightRecovered z = ofElements ((rightDomain z).attach.image (componentToRight z))` with `rightRecovered_elements_eq`
`rfl` (body-156), the leaf reduces — over a wiring bridge `rightRecovered_eq` identifying the abstract union region
with body-156's construction — to a single fresh **image correspondence**:

```text
right_image_correspondence : ∀ q γ,
  γ ∈ (rightDomain (fwdMap q)).attach.image (componentToRight (fwdMap q))   -- the G-parents of B's star-avoiders
    ↔ rightPrimSelected q γ                                                  -- q.2 γ = inl false
```

`ResolvedRightRecoveredSectorDecompositionSupply D S Region` fields body-156's construction, the wiring bridge, and
the image correspondence; `.rightRecovered_forward_membership` is **proved** (`rw` the bridge, `simp` the `rfl` image
shape, apply the correspondence), and `.toRightRegionSectorBridgeSupply` produces body-170's supply.

## Consequence

The right / G side is now the single fresh `right_image_correspondence` (the `componentToRight` round-trip:
star-avoiding components of `B` pulled back to `q`'s right-primitive parents) plus the wiring bridge.  With the
survivor side (body-211) this closes the right-sector floor to two image correspondences; the heavier remnant /
forest side (bodies 207/171) remains.

Per the HALT: the `componentToRight` round-trip body is not entered; `rightEquiv` / sector inverse is not routed
through; the remnant side is untouched; only the `ofElements` image reduction over the wiring bridge is proved.

Landed:

* `ResolvedRightRecoveredSectorDecompositionSupply D S Region` — body-156's construction + the wiring bridge + the
  fresh image correspondence;
* `.rightRecovered_forward_membership` — body-170's leaf (PROVED from the correspondence);
* `.toRightRegionSectorBridgeSupply` — body-170's supply.

Scout / toolkit body (like body-211).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-213 — the right recovered sector decomposition supply.**  Body-156's sector region construction, the
wiring bridge to the abstract union region, and the fresh image correspondence (the `componentToRight` round-trip). -/
structure ResolvedRightRecoveredSectorDecompositionSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- Body-156's sector region construction (the `componentToRight` image). -/
  Construction : ResolvedRegionConstructionFromSectorSupply D S
  /-- Wiring bridge: the abstract union right region agrees with body-156's construction (element level). -/
  rightRecovered_eq : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    (Region.Union.rightRecovered (fwdMap S q)).elements
      = (Construction.rightRecovered (fwdMap S q)).elements
  /-- The fresh image correspondence: the `componentToRight` G-parents of `B`'s star-avoiding components are exactly
  `q`'s right-primitive (`inl false`) components. -/
  right_image_correspondence : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : ResolvedFeynmanSubgraph G),
    γ ∈ (rightDomain (fwdMap S q)).attach.image (Construction.componentToRight (fwdMap S q))
      ↔ rightPrimSelected q γ

namespace ResolvedRightRecoveredSectorDecompositionSupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-213 — body-170's `rightRecovered_forward_membership` from the image correspondence.** -/
theorem rightRecovered_forward_membership
    (F : ResolvedRightRecoveredSectorDecompositionSupply D S Region)
    {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G) (γ : ResolvedFeynmanSubgraph G) :
    γ ∈ (Region.Union.rightRecovered (fwdMap S q)).elements ↔ rightPrimSelected q γ := by
  rw [F.rightRecovered_eq q]
  simp only [ResolvedRegionConstructionFromSectorSupply.rightRecovered_elements_eq]
  exact F.right_image_correspondence q γ

/-- **R-6c-body-213 — body-170's right region sector bridge supply.** -/
def toRightRegionSectorBridgeSupply
    (F : ResolvedRightRecoveredSectorDecompositionSupply D S Region) :
    ResolvedRightRegionSectorBridgeSupply D S Region where
  rightRecovered_forward_membership := fun {G} q γ => F.rightRecovered_forward_membership q γ

end ResolvedRightRecoveredSectorDecompositionSupply

end GaugeGeometry.QFT.Combinatorial
