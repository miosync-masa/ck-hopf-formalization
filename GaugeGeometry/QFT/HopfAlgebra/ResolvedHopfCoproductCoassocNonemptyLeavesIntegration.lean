import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMeasureLeaves
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedDisjointLeaf
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedCD
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftFactorDisjointInstantiation

/-!
# R-6c-body-124 — nonemptiness leaves integration: `hPD` / `hLP` / `component_nonempty` from one measure leaf

Hundred-and-twenty-fourth genuine-body step, unifying the nonemptiness-dependent leaves scattered across the
factor-product / choice-partition machinery.  All of them — `component_nonempty` (body-1/leaf-11), `hLP` /
`left_hdisj` (body-116), and the promoted `hPD` (body-122) — flow from the single measure-level fact
`cd_nonempty` (a `ResolvedMeasureLeafSupply` field).  So one `Measure` bundle feeds the whole nonemptiness
dependency graph.

## The integration (PROVED)

From a `ResolvedMeasureLeafSupply D M`:

* `M.componentNonempty (G)` — the input-outer element nonemptiness supply
  (`M.toInputOuterElementNonemptySupply`);
* `M.leftHDisj (q)` — the `leftOf` / `promotedOf` `Finset`-disjointness `hLP`
  (`resolved_left_hdisj_of_nonempty M.toInputOuterElementNonemptySupply`, body-116);
* `M.promotedHPD (s)` — the pairwise-disjointness `hPD` of the promoted component sets
  (`product_hPD_of_promoted_nonempty` with `hne := fun s γ δ hδ => M.cd_nonempty δ
  (s.promotedComponentElements_CD hδ)`, body-13/122) — the promoted components are CD
  (`promotedComponentElements_CD`), so `cd_nonempty` gives their vertex-nonemptiness.

All three are the SAME `cd_nonempty` fact instantiated: `hLP` needs each input-outer component nonempty, `hPD`
needs each promoted (forest-choice) component nonempty, and both are CD, hence nonempty by the measure leaf.

## Consequence

The `promoted_factor` (body-122, needs `hPD`), `right_primitive`/`left_primitive` `choice_partition` /
`left_hdisj` (bodies 95/116, need nonemptiness), and `outer_nonempty` (body-96, `carrier_isProperForest.1`) all
draw from one `ResolvedMeasureLeafSupply`.  The residual coassoc content is now cleanly the non-nonemptiness
leaves: the two quotient transports (survival / de-contraction), the backward map, and the contract-twice
geometry.

Per the HALT: the nonemptiness leaves are unified under one measure supply; `hPD`'s promoted-nonemptiness is
routed through `promotedComponentElements_CD` + `cd_nonempty`; no transport / inverse / contract content is
entered.

Landed:

* `ResolvedMeasureLeafSupply.componentNonempty` / `.leftHDisj` / `.promotedHPD` — the three nonemptiness leaves
  from one measure leaf (PROVED).

Toolkit body (like body-116/122), no new supply.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **R-6c-body-124 — `component_nonempty` from the measure leaf.** -/
def ResolvedMeasureLeafSupply.componentNonempty (M : ResolvedMeasureLeafSupply D)
    (G : ResolvedFeynmanGraph) : ResolvedInputOuterElementNonemptySupply D G :=
  M.toInputOuterElementNonemptySupply

/-- **R-6c-body-124 — `hLP` / `left_hdisj` from the measure leaf** (body-116). -/
theorem ResolvedMeasureLeafSupply.leftHDisj (M : ResolvedMeasureLeafSupply D)
    (q : ResolvedCoassocSplitChoice D G) :
    Disjoint ((resolvedConcreteLeftSelectionSupply D G).leftOf q).elements
      ((resolvedPromotedOfSupply D G).promotedOf q).elements :=
  resolved_left_hdisj_of_nonempty M.toInputOuterElementNonemptySupply q

/-- **R-6c-body-124 — the promoted `hPD` from the measure leaf** (body-13/122).  The promoted components are CD
(`promotedComponentElements_CD`), so `cd_nonempty` gives their nonemptiness, and
`product_hPD_of_promoted_nonempty` gives the pairwise-disjointness. -/
theorem ResolvedMeasureLeafSupply.promotedHPD (M : ResolvedMeasureLeafSupply D)
    (s : ResolvedCoassocSplitChoice D G) :
    (↑(s.1.1.elements.attach) : Set {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}).PairwiseDisjoint
      s.promotedComponentElements :=
  product_hPD_of_promoted_nonempty
    (fun s γ δ hδ => M.cd_nonempty δ (s.promotedComponentElements_CD hδ)) s

end GaugeGeometry.QFT.Combinatorial
