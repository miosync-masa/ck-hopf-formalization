import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCross
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterBridge

/-!
# R-6c-heart-4 P5 — selectedOuter carrier membership (the closure obligation)

The selected outer forest `selectedOuterRawOf s = leftOf s ∪ promotedOf s` is a fully concrete admissible
forest (P4c).  The image side, however, needs it as a *carrier* forest `{A // A ∈ D.carrier G}` (the
image-side sum runs over carrier forests).

**Scout decision (Case A — supply field, not a theorem):** `ResolvedCoproductProperForestData.carrier`
is an ARBITRARY supplied finite carrier per graph (its only constraints are `hCD`/`carrier_mapPerm`/
`star_mapPerm` — no sub-forest-closure).  So `selectedOuterRawOf s ∈ D.carrier G` cannot be proved
generically: the selected outer is a *sub-forest* of an input carrier forest, and an arbitrary carrier is
not sub-forest-closed.  (The flat analogue `forestComponentForestChoiceOuterSubgraph_mem_properDisjoint`
proves it only because the flat carrier is the canonical COMPLETE
`properDisjointAdmissibleDivergentSubgraphs`.)  This mirrors R-6b-5: the proper-forest data is parametric,
so the selected-outer closure is part of that supplied data, not derivable.  Per the HALT, it is kept as a
**supply hypothesis**; a "complete carrier" instance of `D` could later discharge it.

So with the closure supplied, the selected-outer map is fully assembled and the entire image side becomes
concrete.

Landed:

* `resolvedConcreteSelectedOuterImageSupply` — the `ResolvedCoassocSelectedOuterImageSupply` with concrete
  `leftSelection` / `promotedOf` / `cross` (P4c) and the supplied carrier-membership; its `selectedOuterOf`
  is the concrete selected-outer map, ready for the heart-3 image side.

No facade, no flat term, no `forgetHopf`, no rep/perm.  The carrier-membership is the single supplied
obligation; `term_eq` (heart-2 product_eq/right_eq) and the finite cover/regroup/∀x remain.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-4 P5 — the concrete selected-outer image supply.**  Bundles the concrete left selection
(P4c-pre), promoted forest (P1–P4b), and cross-disjointness (P4c) with the supplied carrier-membership
`selectedOuter_mem` (the closure obligation on the parametric `D.carrier`).  Its `selectedOuterOf` is the
concrete `ResolvedCoassocSplitChoice D G → {A // A ∈ D.carrier G}` for the image side. -/
noncomputable def resolvedConcreteSelectedOuterImageSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (selectedOuter_mem :
      ∀ s, (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s ∈ D.carrier G) :
    ResolvedCoassocSelectedOuterImageSupply D G where
  leftSelection := resolvedConcreteLeftSelectionSupply D G
  promotedOf := (resolvedPromotedOfSupply D G).promotedOf
  cross := cross_disjoint_leftOf_promotedOf
  selectedOuter_mem := selectedOuter_mem

end GaugeGeometry.QFT.Combinatorial
