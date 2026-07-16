import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionConstructionValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftResidualValueBridge

/-!
# R-6c-body-303 — the `representedInQuotient` keystone: the forest-image predicate (PROVED)

Three-hundred-and-third genuine-body step — the first phase-1b keystone.  It concretizes the opaque `representedInQuotient`
(body-279) as the **forest-image predicate over the S-free Region core**, and proves the DEFINITIONAL downstream unlocks
(`represented_forest_complete_value`, `represented_cases`).  Per the audit, this is a dependency-alignment key — it does
NOT auto-prove carrier closure; the reclassification of each downstream leaf is recorded below.

## The concrete predicate (forest-only)

```lean
representedInQuotient z γ  :=  ∃ δ : {x // x ∈ forestDomain z}, Region.componentToForest z δ = γ
```
i.e. `γ` is a `componentToForest` image of a `forestDomain` (remnant/forest-choice) parent — equivalently
`γ ∈ forestRecovered z`.  It is **forest-only, not right ∨ forest**: `represented_cases` proves
`representedInQuotient z γ → γ ∈ forestRecovered z`, which with the three regions pairwise disjoint forces
`represented ⊆ forestRecovered` (a `rightRecovered` disjunct is impossible); and the recovered outer decomposes as
`leftResidual ∪ forestRecovered` only — right-primitive components live in the quotient `B`, not among `z.1.1`'s
components.

## Non-circular

The predicate reads ONLY the Region core (`componentToForest`, `forestDomain`); it references NONE of `Left.leftResidual`,
recovered coverage, forward round-trip, or carrier membership.  `leftResidual` (body-279) becomes
`filterElements (fun γ => ¬ ∃ δ, componentToForest z δ = γ)` — downstream of the Region core, no recursion into `Left`.

## Downstream reclassification (dependency alignment, NOT closure)

```text
DEFINITIONAL (free now):
  represented_forest_complete_value (298)   the predicate IS the ∃ — `fun _ h => h`
  represented_cases (298/289)               forestRecovered_elements_eq + Finset.mem_image
  left_forest_disjoint (281)                left ∈ z.1.1 (filter) + forest ∈ z.1.1 (forest_parent_mem) + z.1.1 pairwise
NEEDS ADDITIONAL GEOMETRY:
  left_right_disjoint / right_forest_disjoint (281)   distinct image-map disjointness (componentToRight vs Forest)
  left_sound_value / left_complete_value (280/279)    NEW: ¬(forest image) ⇔ choiceAt = inl true (image ↔ tag)
CARRIER-MODEL OBLIGATION (unchanged, Group-3):
  recovered_raw_mem (159)   selectedOuter_mem (128)   raw-union / selected-outer carrier closure — untouched
```

Per the HALT: only the concrete predicate + the two definitional unlocks are proved; the image↔tag and image-map
disjointness facts are named for later bodies; `recovered_raw_mem` / `selectedOuter_mem` stay carrier-model; no closure is
claimed proved; generic `z`; no `Forward` / round-trip / carrier membership.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-303 — the concrete left-residual construction from a Region.**  `representedInQuotient` is the
forest-image predicate over the Region core (S-free, non-circular). -/
def leftResidualConstructionOfRegion (Region : ResolvedRegionConstructionFromSectorValueSupply D) :
    ResolvedLeftResidualConstructionValueSupply D where
  representedInQuotient := fun {G} z γ =>
    ∃ δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z},
      Region.componentToForest z δ = γ

/-- **R-6c-body-303 — `represented_forest_complete_value` is DEFINITIONAL** (the predicate IS the `∃`). -/
theorem represented_forest_complete_of_region
    (Region : ResolvedRegionConstructionFromSectorValueSupply D)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) (γ : ResolvedFeynmanSubgraph G)
    (_hmem : γ ∈ z.1.1.elements)
    (hrep : (leftResidualConstructionOfRegion Region).representedInQuotient z γ) :
    ∃ δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z},
      Region.componentToForest z δ = γ :=
  hrep

/-- **R-6c-body-303 — `represented_cases` is DEFINITIONAL** (forest image ⟹ `∈ forestRecovered`, via the image shape). -/
theorem represented_cases_of_region
    (Region : ResolvedRegionConstructionFromSectorValueSupply D)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) (γ : ResolvedFeynmanSubgraph G)
    (_hmem : γ ∈ z.1.1.elements)
    (hrep : (leftResidualConstructionOfRegion Region).representedInQuotient z γ) :
    γ ∈ (Region.forestRecovered z).elements := by
  rw [ResolvedRegionConstructionFromSectorValueSupply.forestRecovered_elements_eq]
  obtain ⟨δ, hδ⟩ := hrep
  exact Finset.mem_image.mpr ⟨δ, Finset.mem_attach _ _, hδ⟩

end GaugeGeometry.QFT.Combinatorial
