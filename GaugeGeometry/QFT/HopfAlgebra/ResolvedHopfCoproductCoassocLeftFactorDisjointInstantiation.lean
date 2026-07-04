import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterMixingAssembly
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocElementNonempty

/-!
# R-6c-body-116 — left-factor disjoint instantiation: `left_hdisj` is the existing `hLP` (from nonemptiness)

Hundred-and-sixteenth genuine-body step, recovering the assembly's LEFT-factor disjoint field `left_hdisj`
(`Disjoint (leftOf q).elements (promotedOf q).elements`) from the existing promote machinery.  For the concrete
left-selection / promoted-forest construction, this Finset-disjointness IS the already-proved leaf-10/11 `hLP`
(`ResolvedInputOuterElementNonemptySupply.hLP`), derived from component nonemptiness (the same body-1
`cd_nonempty` fact behind `outer_nonempty`).  So `left_hdisj` is not new — it reduces to the one nonemptiness
supply.

## The reduction (PROVED)

`resolved_left_hdisj_of_nonempty`: for the concrete left-selection / promoted-of supplies,

```text
Disjoint ((resolvedConcreteLeftSelectionSupply D G).leftOf q).elements
         ((resolvedPromotedOfSupply D G).promotedOf q).elements
```

is exactly `N.hLP` for a `ResolvedInputOuterElementNonemptySupply N` (component nonemptiness →
`product_hLP_of_elements_nonempty`, leaf-10).  When the assembly's `imageSupply` is instantiated with
`leftSelection = resolvedConcreteLeftSelectionSupply` and `promotedOf = resolvedPromotedOfSupply.promotedOf`,
this IS the assembly's `left_hdisj`.

## Consequence

Both union/disjoint blocks are now closed: RIGHT (`right_union_eq` / `right_hdisj` / `right_hcross`, body-115,
from the star filter) and LEFT (`left_hdisj`, body-116, from nonemptiness).  The disjointness geometry is fully
recovered from existing σ-cover machinery; only the four factor products, the backward map, the contract
geometry, and the base carrier / nonemptiness leaves remain.

Per the HALT: only `left_hdisj` is instantiated (as the existing `hLP`); the promoted factor product is NOT
proved; the dependency on component nonemptiness (body-1) is recorded; no other field touched.

Landed:

* `resolved_left_hdisj_of_nonempty` — the assembly's `left_hdisj` from a `ResolvedInputOuterElementNonemptySupply`
  (PROVED, `:= N.hLP`).

Partial-instantiation body (no `coassoc_gen`; feeds the LEFT `left_hdisj` of body-113's assembly).  No facade,
no flat term, no `forgetHopf`.
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

/-- **R-6c-body-116 — `left_hdisj` from component nonemptiness.**  For the concrete left-selection / promoted-of
construction, the assembly's LEFT-factor Finset-disjointness is the existing leaf-10/11 `hLP`, derived from the
one component-nonemptiness fact (body-1). -/
theorem resolved_left_hdisj_of_nonempty (N : ResolvedInputOuterElementNonemptySupply D G) :
    ∀ q : ForestBlockDomType D G,
      Disjoint ((resolvedConcreteLeftSelectionSupply D G).leftOf q).elements
        ((resolvedPromotedOfSupply D G).promotedOf q).elements :=
  N.hLP

end GaugeGeometry.QFT.Combinatorial
