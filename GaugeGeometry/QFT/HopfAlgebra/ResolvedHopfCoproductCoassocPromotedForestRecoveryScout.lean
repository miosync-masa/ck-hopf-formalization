import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestParentCarrier

/-!
# R-6c-body-186 — promoted/forest-recovery scout: the deep leaf split into two directions

Hundred-and-eighty-sixth genuine-body step, a deep structure audit + directional split of the one remaining
forward-outer leaf, `promoted_eq_forestRecovered`.  After bodies 184/185 discharged the shallow forest-box leaves,
this is the sole geometric obstruction: the de-contraction round-trip

```text
(promotedOf recovered).elements = (Construction.forestRecovered z).elements
```

## The two sides (scout)

```text
LHS  (promotedOf recovered).elements = recovered.promotedElements
     = unionOuter.elements.attach.biUnion promotedComponentElements
     = ⋃_{γ ∈ forestRecovered z}  (promote γ (forestTag z γ)).elements       -- inr-tagged components only
       (recoverChoice tags γ `inr Bᵧ` exactly on forestRecovered — body-152 forest_tag;
        promotedComponentElements_inr then gives (promote γ Bᵧ).elements; promote_elements =
        Bᵧ.elements.image (γ.promote ·) — the de-contracted subforest of γ, living in G)

RHS  (forestRecovered z).elements = (forestDomain z).attach.image (componentToForest z)
     = the forest-choice PARENTS, one per star-touching remnant δ of B (componentToForest δ)
```

So the two sides index over *different* base sets: LHS biUnions a whole promoted subforest per parent; RHS is the
set of parents themselves.  The equality asserts that the promoted subforests collapse to exactly the parent set.

## The negative finding (why this is the core leaf)

The sector inverse laws (`forest_left_inv` / `forest_right_inv`, `ResolvedSectorLeafBundle`) bind `componentToForest`
**only** to `forestToComponent` (= the quotient-side `remnantComponent` into `selectedOuterContractGraph`) — never to
`promote`.  The product-level de-contraction facts (`remnant_region_eq`, `product_remnantGen_of_decontraction`) live
on the quotient side at the polynomial/class level, not as element-level `Finset` equalities.  **No existing lemma
relates `promote` (de-contraction into `G`) to `componentToForest`.**  So this leaf is genuinely fresh; it cannot be
proved against the *abstract* `componentToForest` / `forestTag` supplies — those must be made concrete first (or the
identity fielded).

## The directional split (this body)

`ResolvedPromotedForestRecoveryDecompositionSupply D S Region` fields body-156's construction and the two membership
directions:

* `forestRecovered_subset_promoted` — **the lighter direction**: a parent `γ ∈ forestRecovered z` is `inr`-tagged, so
  `promotedComponentElements ⟨γ,_⟩ = (promote γ Bᵧ).elements`, and `γ` appears there as one de-contracted component;
  reuses `forestRecovered_elements_eq` + `forest_tag` + `promotedComponentElements_inr` + `promote_elements`;
* `promoted_subset_forestRecovered` — **the heavier direction**: every de-contracted component `γ.promote δ₀ ∈ promote
  γ Bᵧ` is itself a `componentToForest` parent — the identity that `promote` fully undoes the contraction into the
  parent set.

Then `promoted_eq_forestRecovered` is **PROVED** by `Finset.Subset.antisymm` of the two directions, discharging
body-183/185's leaf.

Per the HALT: neither direction's body is entered (both fielded); only the antisymm assembly is proved; the crux and
the reuse path (`forest_tag`, `promotedComponentElements_inr`, `promote_elements`, `forestRecovered_elements_eq`) are
recorded for the next attack.

Landed:

* `ResolvedPromotedForestRecoveryDecompositionSupply D S Region` — the two membership directions;
* `.promoted_eq_forestRecovered` — body-183/185's leaf (PROVED from the two directions by `antisymm`).

Scout / toolkit body (like body-183).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-186 — the promoted/forest-recovery decomposition supply.**  Body-156's construction and the two
membership directions of the de-contraction round-trip `promotedOf recovered = forestRecovered`. -/
structure ResolvedPromotedForestRecoveryDecompositionSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- Body-156's sector region construction. -/
  Construction : ResolvedRegionConstructionFromSectorSupply D S
  /-- Lighter direction: a forest parent is a de-contracted component of its own promoted subforest. -/
  forestRecovered_subset_promoted : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : ResolvedFeynmanSubgraph G),
    γ ∈ (Construction.forestRecovered z).elements →
    γ ∈ ((S.Forward.imageSupply G).promotedOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
  /-- Heavier direction: every de-contracted component is a forest parent. -/
  promoted_subset_forestRecovered : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : ResolvedFeynmanSubgraph G),
    γ ∈ ((S.Forward.imageSupply G).promotedOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements →
    γ ∈ (Construction.forestRecovered z).elements

namespace ResolvedPromotedForestRecoveryDecompositionSupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-186 — body-183/185's `promoted_eq_forestRecovered` from the two directions.** -/
theorem promoted_eq_forestRecovered (F : ResolvedPromotedForestRecoveryDecompositionSupply D S Region)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    ((S.Forward.imageSupply G).promotedOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
      = (F.Construction.forestRecovered z).elements :=
  Finset.Subset.antisymm
    (fun γ h => F.promoted_subset_forestRecovered z γ h)
    (fun γ h => F.forestRecovered_subset_promoted z γ h)

end ResolvedPromotedForestRecoveryDecompositionSupply

end GaugeGeometry.QFT.Combinatorial
