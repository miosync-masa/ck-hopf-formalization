import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuter
import GaugeGeometry.QFT.HopfAlgebra.ResolvedAdmissibleSubgraphOfElements

/-!
# R-6c-support-2 — resolved forest-promote supply + selectedOuter assembly

Scout result (flat `Coassoc.lean:6465`): `feynmanSubgraphRepForestPromoteAdmissibleSubgraph γ hγ B`
transports a representative-component forest `B` back to the intrinsic component graph
(`feynmanSubgraphRepToComponentAdmissibleSubgraph`, a `mapPerm` preimage along the rep perm) and then
promotes it into the ambient graph (`feynmanSubgraphPromoteAdmissibleSubgraph`).  This is a heavy
rep/perm/promote chain; the resolved analogue is a substantial de-contraction build.

Per the HALT, the promote (and the left-selected forest) are **isolated as a supply**: for each split
choice, the left-selected admissible forest `leftOf` and the promoted admissible forest `promotedOf`,
with the cross-disjointness `cross`.  The selected outer forest is then `selectedOuterRawOf s :=
(leftOf s).union (promotedOf s) (cross s)` — assembled mechanically via the support-1 `union`.

So `selectedOuterRaw` is reduced to supplying `leftOf`/`promotedOf` (the de-contraction forests) +
`cross`; the carrier membership `selectedOuter_mem` (R-6c-4f part 3c-1) is still separate.

Landed:

* `ResolvedForestPromoteSupply D G` — `leftOf`, `promotedOf`, `cross` (the de-contraction forests as
  supply fields);
* `ResolvedForestPromoteSupply.selectedOuterRawOf` — `(leftOf s).union (promotedOf s) (cross s)`, the
  selected outer forest, ready to feed `ResolvedCoassocSelectedOuterSupply.selectedOuterRaw`.

No facade, no flat promote theorem, no `forgetHopf`; the concrete `leftOf`/`promotedOf` (the rep/perm
promote) are the deferred build.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-support-2 — the resolved forest-promote supply.**  For each split choice, the left-selected
admissible forest and the promoted admissible forest (the resolved
`feynmanSubgraphRepForestPromote` output), with their cross-disjointness — the de-contraction forests
isolated as supply fields. -/
structure ResolvedForestPromoteSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) where
  /-- The left-selected admissible forest of a split choice (the primitive-left components). -/
  leftOf : ResolvedCoassocSplitChoice D G → ResolvedAdmissibleSubgraph G
  /-- The promoted admissible forest of a split choice (the promoted forest-choice components). -/
  promotedOf : ResolvedCoassocSplitChoice D G → ResolvedAdmissibleSubgraph G
  /-- The left-selected and promoted components are cross-disjoint. -/
  cross : ∀ s, ∀ γ ∈ (leftOf s).elements, ∀ δ ∈ (promotedOf s).elements, γ ≠ δ → γ.Disjoint δ

/-- **R-6c-support-2 — the selected outer forest from the promote supply.**  The union of the
left-selected and promoted forests (via the support-1 `union`).  This is the resolved
`forestComponentForestChoiceOuterSubgraph`, ready to feed
`ResolvedCoassocSelectedOuterSupply.selectedOuterRaw`. -/
noncomputable def ResolvedForestPromoteSupply.selectedOuterRawOf (P : ResolvedForestPromoteSupply D G)
    (s : ResolvedCoassocSplitChoice D G) : ResolvedAdmissibleSubgraph G :=
  (P.leftOf s).union (P.promotedOf s) (P.cross s)

end GaugeGeometry.QFT.Combinatorial
