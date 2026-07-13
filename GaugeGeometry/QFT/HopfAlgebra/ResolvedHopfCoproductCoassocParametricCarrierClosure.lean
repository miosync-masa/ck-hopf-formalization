import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterFilteredMem
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionPartitionDisjoint
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredOuterMembership

/-!
# R-6c-body-269 — parametric carrier-closure supply: the model obligations consolidated on raw roots (PROVED)

Two-hundred-and-sixty-ninth genuine-body step — the single honest interface for the parametric model's carrier-closure
assumptions.  It bundles the **filtered** selected-outer closure (body-245), the three region pairwise disjointnesses
(body-158), and the **raw** recovered-outer carrier membership (stated on the bare region union, not the carrier-tagged
`unionOuter`), with converters to the existing supplies.  No carrier-tagged `unionOuter`, no total `selectedOuter_mem`,
no certificate / `recovered_eq` is used.

## The raw recovered union (no carrier tag)

`recoveredRawUnion` is the bare triple region union built from the three region maps + their three pairwise
disjointnesses via `ResolvedAdmissibleSubgraph.union` alone (the `left ∪ right` vs `forest` cross is *derived* from the
three pairwise facts).  This is exactly body-159's union expression — body-159's `recovered_outer_mem` is already stated
on this bare union, never on `unionOuter`.

## The consolidated supply

```lean
structure ResolvedParametricCarrierClosureSupply (D) (S) where
  selected : ResolvedSelectedOuterFilteredMemSupply D            -- filtered selected-outer closure (body-245)
  leftResidual / rightRecovered / forestRecovered               -- the three region maps
  left_right_disjoint / left_forest_disjoint / right_forest_disjoint  -- the three pairwise (body-158)
  recovered_raw_mem : ∀ z, recoveredRawUnion … ∈ D.carrier G     -- raw recovered-outer closure (body-159, bare union)
```

Every field is either a proved-geometry input (the region maps) or a **model closure assumption** (`selected`, the
three disjointnesses, `recovered_raw_mem`) — the two are not mixed.  The ordering is enforced: raw regions → pairwise
disjoint → `recoveredRawUnion` → supplied carrier membership; the carrier-tagged `unionOuter` is built *downstream* from
`recovered_raw_mem`, never assumed.

## Converters

* `.toSelectedOuterFilteredMemSupply` — the filtered selected-outer closure verbatim (body-245);
* `.toRegionPartitionSupply` — body-158 from the region maps + the three pairwise;
* `.toRecoveredOuterCarrierSupply` — body-159 from the region maps + the derived cross forms + `recovered_raw_mem`
  (defeq: `recoveredRawUnion` is body-159's union).

## Audit — consumer wiring (the last routing check)

* `.toSelectedOuterFilteredMemSupply` feeds the **filtered-migrated** chain directly (bodies 245/252/253) — no legacy.
* `.toRegionPartitionSupply` / `.toRecoveredOuterCarrierSupply` feed body-158/153/159, which the region construction
  (bodies 156/157/184) consumes.  These reach the live sum through `Region.Union` (body-153's
  `ResolvedOuterUnionConstructionSupply`, whose `unionOuter` this supply's `recovered_raw_mem` *inhabits*, not assumes).
* The remaining legacy-typed consumer is the **total** `ResolvedForwardMapCoherenceSupply.selectedOuter_mem`
  (`ForwardMapCoherence.lean:72`), reached only through the `.ofLegacy` comparison lemmas (bodies 249–254); the
  canonical chain uses `.toSelectedOuterFilteredMemSupply` instead.

`IsProperForest` (5/5, bodies 264/266) is kept separately as the discharge material for a *concrete* canonical instance
(the payload-carrier construction, phase 1b); it is not a field of this parametric closure interface.

Per the HALT: the parametric carrier-closure interface + its converters are defined/proved; no total `selectedOuter_mem`,
no `unionOuter.2` assumption, no `recovered_eq`.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-269 — the raw recovered union** (no carrier tag).  The bare triple region union; the `left ∪ right` vs
`forest` cross is derived from the three pairwise disjointnesses.  Exactly body-159's union expression. -/
noncomputable def recoveredRawUnion (leftResidual rightRecovered forestRecovered : ResolvedAdmissibleSubgraph G)
    (h_lr : ∀ γ ∈ leftResidual.elements, ∀ δ ∈ rightRecovered.elements, γ ≠ δ → γ.Disjoint δ)
    (h_lf : ∀ γ ∈ leftResidual.elements, ∀ δ ∈ forestRecovered.elements, γ ≠ δ → γ.Disjoint δ)
    (h_rf : ∀ γ ∈ rightRecovered.elements, ∀ δ ∈ forestRecovered.elements, γ ≠ δ → γ.Disjoint δ) :
    ResolvedAdmissibleSubgraph G :=
  (leftResidual.union rightRecovered h_lr).union forestRecovered (by
    intro γ hγ δ hδ hne
    simp only [ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union] at hγ
    rcases hγ with hl | hr
    · exact h_lf γ hl δ hδ hne
    · exact h_rf γ hr δ hδ hne)

/-- **R-6c-body-269 — the parametric carrier-closure supply.**  One honest interface for the model's closure
assumptions on raw roots: filtered selected outer (245), region pairwise disjointnesses (158), and the raw recovered
outer's carrier membership (159, bare union). -/
structure ResolvedParametricCarrierClosureSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) where
  /-- The filtered selected-outer carrier closure (body-245). -/
  selected : ResolvedSelectedOuterFilteredMemSupply D
  /-- The left-primitive region. -/
  leftResidual : ∀ {G : ResolvedFeynmanGraph}, ForestBlockCodType D G → ResolvedAdmissibleSubgraph G
  /-- The right-primitive region. -/
  rightRecovered : ∀ {G : ResolvedFeynmanGraph}, ForestBlockCodType D G → ResolvedAdmissibleSubgraph G
  /-- The forest-choice region. -/
  forestRecovered : ∀ {G : ResolvedFeynmanGraph}, ForestBlockCodType D G → ResolvedAdmissibleSubgraph G
  /-- Left / right pairwise disjointness (model closure assumption). -/
  left_right_disjoint : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ∀ γ ∈ (leftResidual z).elements, ∀ δ ∈ (rightRecovered z).elements, γ ≠ δ → γ.Disjoint δ
  /-- Left / forest pairwise disjointness (model closure assumption). -/
  left_forest_disjoint : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ∀ γ ∈ (leftResidual z).elements, ∀ δ ∈ (forestRecovered z).elements, γ ≠ δ → γ.Disjoint δ
  /-- Right / forest pairwise disjointness (model closure assumption). -/
  right_forest_disjoint : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ∀ γ ∈ (rightRecovered z).elements, ∀ δ ∈ (forestRecovered z).elements, γ ≠ δ → γ.Disjoint δ
  /-- The raw recovered outer lies in the carrier — bare union, no `unionOuter` (model closure assumption). -/
  recovered_raw_mem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    recoveredRawUnion (leftResidual z) (rightRecovered z) (forestRecovered z)
      (left_right_disjoint z) (left_forest_disjoint z) (right_forest_disjoint z) ∈ D.carrier G

namespace ResolvedParametricCarrierClosureSupply

variable {S : ResolvedConcreteSummandBundleSupply D}

/-- **R-6c-body-269 — the filtered selected-outer closure** (body-245), verbatim. -/
def toSelectedOuterFilteredMemSupply (C : ResolvedParametricCarrierClosureSupply D S) :
    ResolvedSelectedOuterFilteredMemSupply D :=
  C.selected

/-- **R-6c-body-269 — body-158's region partition** from the region maps + the three pairwise disjointnesses. -/
def toRegionPartitionSupply (C : ResolvedParametricCarrierClosureSupply D S) :
    ResolvedRegionPartitionSupply D S where
  leftResidual := C.leftResidual
  rightRecovered := C.rightRecovered
  forestRecovered := C.forestRecovered
  left_right_disjoint := C.left_right_disjoint
  left_forest_disjoint := C.left_forest_disjoint
  right_forest_disjoint := C.right_forest_disjoint

/-- **R-6c-body-269 — body-159's recovered-outer carrier supply** from the raw membership + derived cross forms. -/
def toRecoveredOuterCarrierSupply (C : ResolvedParametricCarrierClosureSupply D S) :
    ResolvedRecoveredOuterCarrierSupply D S C.leftResidual C.rightRecovered C.forestRecovered
      C.toRegionPartitionSupply.hcross_lr C.toRegionPartitionSupply.hcross_lrf where
  recovered_outer_mem := fun {G} z => C.recovered_raw_mem z

end ResolvedParametricCarrierClosureSupply

end GaugeGeometry.QFT.Combinatorial
