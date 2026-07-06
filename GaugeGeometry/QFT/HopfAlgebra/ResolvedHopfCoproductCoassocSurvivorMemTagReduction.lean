import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSurvivorElementsRecovery
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionConstructionFromSector

/-!
# R-6c-body-211 — survivor mem tag reduction: `survivor_mem` unfolded to a survivorComponent-image correspondence

Two-hundred-and-eleventh genuine-body step, thinning the survivor half's floor one more level.  Body-206's
`survivor_mem` bridge is unfolded — its two `rfl`/`filter`-level sides (the `rightSurvivorForest` image, the
`rightDomain` star filter) are exposed — leaving one fresh correspondence: the recovered `survivorComponent` image
is exactly `B`'s star-avoiding components.

## The shallow unfoldings (PROVED)

* `rightDomain_mem_iff` — `x ∈ rightDomain z ↔ x ∈ z.2.1.elements ∧ Disjoint x.vertices (starOfZ z)` (`Finset.mem_filter`
  on body-156's `rightDomain` filter);
* `(rightSurvivorForest recovered).elements = rightComponents(recovered).attach.image survivorComponent`
  (body-125 `rightSurvivorForest_elements`, `rfl`), where `rightComponents = filter (recoverChoice z γ = inl false)`.

## The reduction

`ResolvedSurvivorMemTagReductionSupply D S Region` fields the reused `selectedOuter_partition` and the single fresh
**survivor image correspondence**

```text
survivor_image_correspondence : ∀ x₁ x₂, HEq x₁ x₂ →
  (x₁ ∈ rightComponents(recovered).attach.image survivorComponent
    ↔ x₂ ∈ z.2.1.elements ∧ Disjoint x₂.vertices (starOfZ z))
```

Its meaning (body-210's finding): since `survivorComponent = survivorReembed` preserves vertices at `rfl`, this is
the pure tag correspondence — the `recoverChoice z γ = inl false` (right-primitive) components of `unionOuter z`,
reembedded, are exactly the star-avoiding (`Disjoint · (starOfZ z)`) components of `B = z.2`.  Then
`.survivor_mem` is **proved** by unfolding the image / filter and applying the correspondence, and
`.toSurvivorElementsRecoverySupply` produces body-206's supply.

## Consequence

The survivor half of the forward-quotient `HEq` is now the single fresh survivor image correspondence (the pure
`inl false` ⟷ star-avoiding tag correspondence, with `survivorReembed` `rfl`), plus the reused ambient transport.
The remnant half (body-207) is untouched.

Per the HALT: the `survivorComponent` / `survivorReembed` / tag-correspondence body is not entered; the sector
right-inverse is not entered; the remnant side is untouched; only the image / filter unfolding is proved.

Landed:

* `rightDomain_mem_iff` — the star-avoiding filter membership (PROVED, reusable);
* `ResolvedSurvivorMemTagReductionSupply D S Region` — the ambient transport + the survivor image correspondence;
* `.survivor_mem` — body-206's survivor bridge (PROVED from the correspondence);
* `.toSurvivorElementsRecoverySupply` — body-206's supply.

Toolkit body (like body-196).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-211 — the star-avoiding filter membership** (`Finset.mem_filter` on `rightDomain`). -/
theorem rightDomain_mem_iff {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))) :
    x ∈ rightDomain z ↔ x ∈ z.2.1.elements ∧ Disjoint x.vertices (starOfZ z) := by
  rw [rightDomain, Finset.mem_filter]

/-- **R-6c-body-211 — the survivor mem tag reduction supply.**  The reused ambient transport and the single fresh
survivor image correspondence (the `inl false` ⟷ star-avoiding tag correspondence, with `survivorReembed` `rfl`). -/
structure ResolvedSurvivorMemTagReductionSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- Body-162/190: the recovered selected outer has exactly `A`'s components (the ambient transport). -/
  selectedOuter_partition : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ((S.Forward.imageSupply G).selectedOuterOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1.elements
      = z.1.1.elements
  /-- The fresh survivor image correspondence: the recovered `survivorComponent` image is exactly `B`'s
  star-avoiding components (the pure `inl false` ⟷ star-avoiding tag correspondence). -/
  survivor_image_correspondence : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₁ : ResolvedFeynmanSubgraph (((S.Forward.imageSupply G).selectedOuterOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1.contractWithStars
        (D.starOf G ((S.Forward.imageSupply G).selectedOuterOf
          (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
    HEq x₁ x₂ →
    (x₁ ∈ (ResolvedCoassocSplitChoice.rightComponents
          (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).attach.image
          (S.Survivor.survivor.survivorComponent
            (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G))
      ↔ x₂ ∈ z.2.1.elements ∧ Disjoint x₂.vertices (starOfZ z))

namespace ResolvedSurvivorMemTagReductionSupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-211 — body-206's `survivor_mem` from the survivor image correspondence.** -/
theorem survivor_mem (F : ResolvedSurvivorMemTagReductionSupply D S Region)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₁ : ResolvedFeynmanSubgraph (((S.Forward.imageSupply G).selectedOuterOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1.contractWithStars
        (D.starOf G ((S.Forward.imageSupply G).selectedOuterOf
          (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (h : HEq x₁ x₂) :
    x₁ ∈ (S.Survivor.survivor.rightSurvivorForest
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
      ↔ x₂ ∈ rightDomain z := by
  simp only [ResolvedRightSurvivorSupply.rightSurvivorForest_elements, rightDomain, Finset.mem_filter]
  exact F.survivor_image_correspondence z x₁ x₂ h

/-- **R-6c-body-211 — body-206's survivor elements recovery supply.** -/
def toSurvivorElementsRecoverySupply (F : ResolvedSurvivorMemTagReductionSupply D S Region) :
    ResolvedSurvivorElementsRecoverySupply D S Region where
  selectedOuter_partition := fun {G} z => F.selectedOuter_partition z
  survivor_mem := fun {G} z x₁ x₂ h => F.survivor_mem z x₁ x₂ h

end ResolvedSurvivorMemTagReductionSupply

end GaugeGeometry.QFT.Combinatorial
