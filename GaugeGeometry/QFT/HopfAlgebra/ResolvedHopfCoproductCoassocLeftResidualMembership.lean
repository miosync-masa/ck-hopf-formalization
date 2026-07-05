import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTargetOuterCoverage
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftResidualConstruction

/-!
# R-6c-body-178 — left residual membership: the first coverage fact PROVED from body-157's filter

Hundred-and-seventy-eighth genuine-body step, discharging the first of body-177's three coverage facts.
`leftResidual` was defined in body-157 as the `filterElements` of the target outer `A` by "not represented in the
quotient `B`":

```text
leftResidual z = z.1.1.filterElements (fun γ => ¬ representedInQuotient z γ)      (body-157)
```

so its membership is a pure `Finset.mem_filter` fact.  This body proves body-177's `leftResidual_mem` — the
"represented" predicate is instantiated to body-157's `representedInQuotient` — leaving only `forestRecovered_mem`
and `coverage` fielded.

## The wiring bridge (fielded) and the membership (PROVED)

Body-177's coverage supply is stated on the abstract `Region.Union.leftResidual` (a field of
`ResolvedOuterUnionConstructionSupply`, which carries no element-shape lemma), whereas the `filter` shape lives on
body-157's concrete `leftResidual`.  `ResolvedLeftResidualMembershipSupply D S Region` therefore fields the single
element-level wiring bridge

```text
leftResidual_eq : (Region.Union.leftResidual z).elements = (L.leftResidual z).elements
```

(the abstract union region agrees with body-157's construction — definitional at the concrete instantiation, a
field here).  With it, `leftResidual_membership` is **PROVED**:

```text
γ ∈ (Region.Union.leftResidual z).elements
  ↔ γ ∈ (L.leftResidual z).elements                                   -- leftResidual_eq
  ↔ γ ∈ z.1.1.elements.filter (¬ representedInQuotient z)             -- leftResidual_elements_eq (rfl)
  ↔ γ ∈ z.1.1.elements ∧ ¬ representedInQuotient z γ                  -- Finset.mem_filter
```

So body-177's `leftResidual_mem` (with `represented := representedInQuotient`) is no longer fielded; it is the
`filterElements` unfolding.

## Consequence

Of body-177's three coverage facts, the first is now PROVED.  The residual coverage content is:

* `forestRecovered_mem` — `γ ∈ forestRecovered ↔ γ ∈ A ∧ representedByForest` (the remnant-parent side, which — like
  `promoted_region_eq` — is `componentToForest` de-contraction geometry, not a filter);
* `coverage` — `γ ∈ A → ¬ represented ∨ representedByForest` (every `A`-component is untouched or a remnant parent).

Per the HALT: `representedInQuotient`'s body (the right / forest sector image) is not entered; `forestRecovered_mem`
/ `coverage` are untouched; only the `leftResidual` `filterElements` unfolding is done, over the fielded wiring
bridge.

Landed:

* `ResolvedLeftResidualMembershipSupply D S Region` — body-157's construction `L` + the element-level wiring bridge;
* `.leftResidual_membership` — body-177's `leftResidual_mem` (PROVED, `represented := representedInQuotient`).

Toolkit body (like body-174).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-178 — the left-residual membership supply.**  Body-157's left-residual construction `L` (carrying
`representedInQuotient` and the `filterElements` shape) together with the element-level bridge identifying the
abstract union region with it. -/
structure ResolvedLeftResidualMembershipSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- Body-157's left-residual construction (the `representedInQuotient` filter). -/
  L : ResolvedLeftResidualConstructionSupply D S
  /-- The abstract union left-residual region agrees with body-157's construction (element level). -/
  leftResidual_eq : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    (Region.Union.leftResidual z).elements = (L.leftResidual z).elements

namespace ResolvedLeftResidualMembershipSupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-178 — body-177's `leftResidual_mem` from body-157's filter.**  The left-residual region is the
"not represented in `B`" filter of the target outer `A` — a pure `Finset.mem_filter` fact over the wiring bridge. -/
theorem leftResidual_membership (M : ResolvedLeftResidualMembershipSupply D S Region)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) (γ : ResolvedFeynmanSubgraph G) :
    γ ∈ (Region.Union.leftResidual z).elements
      ↔ γ ∈ z.1.1.elements ∧ ¬ M.L.representedInQuotient z γ := by
  rw [M.leftResidual_eq z, M.L.leftResidual_elements_eq z, Finset.mem_filter]

end ResolvedLeftResidualMembershipSupply

end GaugeGeometry.QFT.Combinatorial
