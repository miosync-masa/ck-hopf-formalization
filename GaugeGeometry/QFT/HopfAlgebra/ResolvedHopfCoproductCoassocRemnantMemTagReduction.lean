import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantElementsRecovery
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionConstructionFromSector

/-!
# R-6c-body-216 — remnant mem tag reduction: `remnant_mem` unfolded to a remnantComponent-image correspondence

Two-hundred-and-sixteenth genuine-body step, the mirror of body-211 for the quotient-side remnant leaf — the last of
the four sector leaves.  Body-207's `remnant_mem` bridge is unfolded — its `rfl`/`filter`-level sides (the
`remnantForest` image, the `forestDomain` star filter) are exposed — leaving one fresh correspondence: the recovered
`remnantComponent` image is exactly `B`'s star-touching components.

## The shallow unfoldings (PROVED)

* `forestDomain_mem_iff` — `x ∈ forestDomain z ↔ x ∈ z.2.1.elements ∧ ¬ Disjoint x.vertices (starOfZ z)`
  (`Finset.mem_filter` on body-156's `forestDomain` filter; the `¬ Disjoint` mirror of body-211's `rightDomain_mem_iff`);
* `(remnantForest recovered).elements = forestComponents(recovered).attach.image (fun γ => remnantComponent
  (forestComponentOccurrence γ))` (body-126 `remnantForest_elements`, `rfl`), where `forestComponents = filter
  (∃ B, recoverChoice z γ = inr B)`.

## The reduction

`ResolvedRemnantMemTagReductionSupply D S Region` fields the reused `selectedOuter_partition` and the single fresh
**remnant image correspondence**

```text
remnant_image_correspondence : ∀ x₁ x₂, HEq x₁ x₂ →
  (x₁ ∈ forestComponents(recovered).attach.image (fun γ => remnantComponent (forestComponentOccurrence γ))
    ↔ x₂ ∈ z.2.1.elements ∧ ¬ Disjoint x₂.vertices (starOfZ z))
```

Unlike body-211's survivor correspondence — where `survivorReembed` preserves vertices at `rfl`, so the `HEq` was
near-definitional and only the pure tag correspondence remained — here `remnantComponent` lands in the contracted
graph with a nontrivial `remnantClass_eq` (de-contraction geometry, bodies 126/183); so the `HEq x₁ x₂` genuinely
bridges different vertex sets.  This is the heaviest of the four sector correspondences.  Then `.remnant_mem` is
**proved** by unfolding the image / filter and applying the correspondence, and `.toRemnantElementsRecoverySupply`
produces body-207's supply.

## Consequence — all four sector leaves reduced

```text
survivor (211)  survivor_image_correspondence     rightComponents image ↔ star-avoiding (survivorReembed rfl)
right    (213)  right_image_correspondence        componentToRight image ↔ inl false
forest   (215)  forest_image_correspondence       componentToForest image ↔ inr (forestChoiceSelected)
remnant  (216)  remnant_image_correspondence      remnantComponent image ↔ star-touching (de-contraction, heaviest)
```

The four sector bridges are now four image correspondences.  The remnant one carries genuine de-contraction geometry;
the other three are tag correspondences.

Per the HALT: the `remnantComponent` / de-contraction (`remnantGen` / `remnantClass_eq`) body is not entered; the
survivor / right / forest sides are untouched; only the image / filter unfolding is proved.

Landed:

* `forestDomain_mem_iff` — the star-touching filter membership (PROVED, reusable);
* `ResolvedRemnantMemTagReductionSupply D S Region` — the ambient transport + the remnant image correspondence;
* `.remnant_mem` — body-207's remnant bridge (PROVED from the correspondence);
* `.toRemnantElementsRecoverySupply` — body-207's supply.

Toolkit body (like body-211).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-216 — the star-touching filter membership** (`Finset.mem_filter` on `forestDomain`). -/
theorem forestDomain_mem_iff {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))) :
    x ∈ forestDomain z ↔ x ∈ z.2.1.elements ∧ ¬ Disjoint x.vertices (starOfZ z) := by
  rw [forestDomain, Finset.mem_filter]

/-- **R-6c-body-216 — the remnant mem tag reduction supply.**  The reused ambient transport and the single fresh
remnant image correspondence (`remnantComponent` image ↔ star-touching, carrying the de-contraction). -/
structure ResolvedRemnantMemTagReductionSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- Body-162/190: the recovered selected outer has exactly `A`'s components (the ambient transport). -/
  selectedOuter_partition : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ((S.Forward.imageSupply G).selectedOuterOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1.elements
      = z.1.1.elements
  /-- The fresh remnant image correspondence: the recovered `remnantComponent` image is exactly `B`'s star-touching
  components (carrying the de-contraction geometry). -/
  remnant_image_correspondence : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₁ : ResolvedFeynmanSubgraph (((S.Forward.imageSupply G).selectedOuterOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1.contractWithStars
        (D.starOf G ((S.Forward.imageSupply G).selectedOuterOf
          (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
    HEq x₁ x₂ →
    (x₁ ∈ (ResolvedCoassocSplitChoice.forestComponents
          (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).attach.image
          (fun γ => S.Remnant.remnant.remnantComponent
            (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)
            (ResolvedCoassocSplitChoice.forestComponentOccurrence
              (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G) γ))
      ↔ x₂ ∈ z.2.1.elements ∧ ¬ Disjoint x₂.vertices (starOfZ z))

namespace ResolvedRemnantMemTagReductionSupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-216 — body-207's `remnant_mem` from the remnant image correspondence.** -/
theorem remnant_mem (F : ResolvedRemnantMemTagReductionSupply D S Region)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₁ : ResolvedFeynmanSubgraph (((S.Forward.imageSupply G).selectedOuterOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1.contractWithStars
        (D.starOf G ((S.Forward.imageSupply G).selectedOuterOf
          (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (h : HEq x₁ x₂) :
    x₁ ∈ (S.Remnant.remnant.remnantForest
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
      ↔ x₂ ∈ forestDomain z := by
  simp only [ResolvedRemnantComponentSupply.remnantForest_elements, forestDomain, Finset.mem_filter]
  exact F.remnant_image_correspondence z x₁ x₂ h

/-- **R-6c-body-216 — body-207's remnant elements recovery supply.** -/
def toRemnantElementsRecoverySupply (F : ResolvedRemnantMemTagReductionSupply D S Region) :
    ResolvedRemnantElementsRecoverySupply D S Region where
  selectedOuter_partition := fun {G} z => F.selectedOuter_partition z
  remnant_mem := fun {G} z x₁ x₂ h => F.remnant_mem z x₁ x₂ h

end ResolvedRemnantMemTagReductionSupply

end GaugeGeometry.QFT.Combinatorial
