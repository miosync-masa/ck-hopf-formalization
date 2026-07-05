import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteSummandBundle

/-!
# R-6c-body-157 — leftResidual construction: the left region as a filter of the target outer

Hundred-and-fifty-seventh genuine-body step, the last of body-153's three regions.  `leftResidual` is made
concrete as a **filter of the target outer** `A = z.1`: the components of `A` not represented by the quotient `B`
(neither a survivor nor a remnant image).  So with body-156 (`rightRecovered` / `forestRecovered` as sector
images), all three regions of the recovered outer forest now have an explicit element shape.

## The left region (filter of `A`)

`ResolvedLeftResidualConstructionSupply D S` fields the representation predicate `representedInQuotient z γ` — "the
component `γ` of `A` is represented by `B`" (i.e. `γ` is a `componentToRight` image of a star-avoiding component of
`B`, or a `componentToForest` image of a star-touching one).  Then

```text
leftResidual z = z.1.1.filterElements (fun γ => ¬ representedInQuotient z γ)
```

and `leftResidual_elements_eq` holds by `rfl` (`filterElements_elements`): its elements are exactly
`A.elements.filter (¬ representedInQuotient z)`.  The `CD` and pairwise-disjointness of `leftResidual` are inherited
from `A` (`filterElements` keeps them), so no extra well-formedness is fielded.

## Consequence

All three regions now have an explicit element shape:

* `leftResidual z` = `A.elements.filter (¬ representedInQuotient z)` (this body);
* `rightRecovered z` = the `componentToRight` image of the survivors of `B` (body-156);
* `forestRecovered z` = the `componentToForest` image of the remnants of `B` (body-156).

so `union_eq` / the cross-disjointnesses (body-153) and `forward_outer` (body-154, `A`-reconstruction) become
component-set partition facts — `A = leftResidual ∪ (represented components)` — the next region obligations.

Per the HALT: `leftResidual` is defined as the filter of `A` (element shape `rfl`); `representedInQuotient` is
fielded (its equality with the sector-map images is the residual partition fact, not proved here); no round-trip is
entered.

Landed:

* `ResolvedLeftResidualConstructionSupply D S` — the representation predicate;
* `.leftResidual` — the concrete filter of `A`;
* `.leftResidual_elements_eq` — the element shape (`rfl`).

Toolkit body (like body-156).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-157 — the left-residual construction supply.**  The representation predicate
`representedInQuotient z γ` — a component `γ` of the target outer `A` is represented by the quotient `B` (a survivor
or remnant image). -/
structure ResolvedLeftResidualConstructionSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) where
  /-- A component of the target outer `A` is represented by the quotient `B`. -/
  representedInQuotient : ∀ {G : ResolvedFeynmanGraph},
    ForestBlockCodType D G → ResolvedFeynmanSubgraph G → Prop

namespace ResolvedLeftResidualConstructionSupply

variable {S : ResolvedConcreteSummandBundleSupply D}

/-- **R-6c-body-157 — the recovered left region** (the components of `A` not represented by `B`). -/
noncomputable def leftResidual (L : ResolvedLeftResidualConstructionSupply D S)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) : ResolvedAdmissibleSubgraph G :=
  z.1.1.filterElements (fun γ => ¬ L.representedInQuotient z γ)

/-- **R-6c-body-157 — the left region's element shape** (`rfl`).  `leftResidual` is the filter of `A`'s components
by "not represented in `B`". -/
@[simp] theorem leftResidual_elements_eq (L : ResolvedLeftResidualConstructionSupply D S)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    (L.leftResidual z).elements = z.1.1.elements.filter (fun γ => ¬ L.representedInQuotient z γ) :=
  rfl

end ResolvedLeftResidualConstructionSupply

end GaugeGeometry.QFT.Combinatorial
