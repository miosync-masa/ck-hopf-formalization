import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterUnionConstruction

/-!
# R-6c-body-158 — region partition and disjoint: the cross-disjointnesses from pairwise region disjointness

Hundred-and-fifty-eighth genuine-body step, reducing body-153's union cross-disjointnesses to the three pairwise
region disjointnesses, and fielding the representation partition.  With the three regions now having explicit
element shapes (bodies 156/157), the union assembly's `hcross_lr` / `hcross_lrf` follow from "the regions are
pairwise disjoint", and the recovered outer is a clean three-region partition of the reconstructed forest.

## The cross-disjointnesses (PROVED)

`ResolvedRegionPartitionSupply D S` fields the three regions and their **pairwise disjointnesses**
(`left_right_disjoint`, `left_forest_disjoint`, `right_forest_disjoint` — each pair of distinct components is
graph-disjoint).  Then body-153's two union cross-disjointnesses follow:

* `hcross_lr` = `left_right_disjoint` (verbatim);
* `hcross_lrf` — for `γ ∈ (leftResidual ∪ rightRecovered).elements`, case-split (`union_elements` +
  `Finset.mem_union`) into the left / right region and apply `left_forest_disjoint` / `right_forest_disjoint`.

So the union assembly's disjointness data (body-153's `hcross_lr` / `hcross_lrf`) reduces exactly to the three
pairwise region disjointnesses.  The representation partition proper (`A = leftResidual ∪ (represented
components)`, i.e. an `A`-component is `representedInQuotient` iff it lies in `rightRecovered` / `forestRecovered`)
is the fact that `forward_outer` / `backward_outer` (body-154) consumes; it is left to the round-trip body.

Per the HALT: the cross-disjointnesses are reduced to the three pairwise region disjointnesses; no
`componentToRight` / `componentToForest` injectivity and no round-trip are entered.

Landed:

* `ResolvedRegionPartitionSupply D S` — the three regions + the three pairwise disjointnesses;
* `.hcross_lr` / `.hcross_lrf` — body-153's union cross-disjointnesses (PROVED from the pairwise disjointnesses).

Toolkit body (like body-156/157).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-158 — the region partition supply.**  The three regions, their pairwise disjointnesses, and the
representation partition (a component of `A` is represented iff it is a survivor or remnant image). -/
structure ResolvedRegionPartitionSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) where
  /-- The left-primitive region. -/
  leftResidual : ∀ {G : ResolvedFeynmanGraph}, ForestBlockCodType D G → ResolvedAdmissibleSubgraph G
  /-- The right-primitive region. -/
  rightRecovered : ∀ {G : ResolvedFeynmanGraph}, ForestBlockCodType D G → ResolvedAdmissibleSubgraph G
  /-- The forest-choice region. -/
  forestRecovered : ∀ {G : ResolvedFeynmanGraph}, ForestBlockCodType D G → ResolvedAdmissibleSubgraph G
  /-- Left / right pairwise disjointness. -/
  left_right_disjoint : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ∀ γ ∈ (leftResidual z).elements, ∀ δ ∈ (rightRecovered z).elements, γ ≠ δ → γ.Disjoint δ
  /-- Left / forest pairwise disjointness. -/
  left_forest_disjoint : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ∀ γ ∈ (leftResidual z).elements, ∀ δ ∈ (forestRecovered z).elements, γ ≠ δ → γ.Disjoint δ
  /-- Right / forest pairwise disjointness. -/
  right_forest_disjoint : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ∀ γ ∈ (rightRecovered z).elements, ∀ δ ∈ (forestRecovered z).elements, γ ≠ δ → γ.Disjoint δ

namespace ResolvedRegionPartitionSupply

variable {S : ResolvedConcreteSummandBundleSupply D}

/-- **R-6c-body-158 — body-153's `hcross_lr`** (verbatim from `left_right_disjoint`). -/
theorem hcross_lr (P : ResolvedRegionPartitionSupply D S) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) :
    ∀ γ ∈ (P.leftResidual z).elements, ∀ δ ∈ (P.rightRecovered z).elements, γ ≠ δ → γ.Disjoint δ :=
  P.left_right_disjoint z

/-- **R-6c-body-158 — body-153's `hcross_lrf`** from `left_forest_disjoint` + `right_forest_disjoint`. -/
theorem hcross_lrf (P : ResolvedRegionPartitionSupply D S) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) :
    ∀ γ ∈ ((P.leftResidual z).union (P.rightRecovered z) (P.hcross_lr z)).elements,
    ∀ δ ∈ (P.forestRecovered z).elements, γ ≠ δ → γ.Disjoint δ := by
  intro γ hγ δ hδ hne
  simp only [ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union] at hγ
  rcases hγ with hl | hr
  · exact P.left_forest_disjoint z γ hl δ hδ hne
  · exact P.right_forest_disjoint z γ hr δ hδ hne

end ResolvedRegionPartitionSupply

end GaugeGeometry.QFT.Combinatorial
