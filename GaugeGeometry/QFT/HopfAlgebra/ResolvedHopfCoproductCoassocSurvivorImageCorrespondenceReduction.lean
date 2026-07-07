import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSurvivorMemTagReduction

/-!
# R-6c-body-221 — survivor image correspondence reduction: reduced to `survivorComponent` sound + complete

Two-hundred-and-twenty-first genuine-body step, the quotient-side mirror of bodies 219/220: body-211's
`survivor_image_correspondence` is reduced to the two `survivorComponent` round-trip directions, so **all three
tag-side sector correspondences** now sit at the same `sound` / `complete` granularity.  The survivor split carries
the cross-graph `HEq` (unlike the G-side), handled by `eq_of_heq`.

## The reduction

`survivor_image_correspondence` is `x₁ ∈ rightComponents(recovered).attach.image survivorComponent ↔ x₂ ∈
z.2.1.elements ∧ Disjoint x₂.vertices (starOfZ z)` (`HEq x₁ x₂` given).  Via `Finset.mem_image` it splits into:

* **sound** — for a right-primitive component `γ` and an `HEq`-linked `x₂`, `survivorComponent γ` being `HEq x₂`
  forces `x₂` star-avoiding;
* **complete** — every star-avoiding `x₂` has a right-primitive component `γ` with `survivorComponent γ` `HEq x₂`.

`ResolvedSurvivorImageCorrespondenceDecompositionSupply D S Region` fields the two fresh directions `survivor_sound`
/ `survivor_complete`.  Then `.survivor_image_correspondence` is **proved**: the forward direction reads off
`survivorComponent γ = x₁` (`Finset.mem_image.mp`, term-mode) and applies `survivor_sound` with the given `HEq`; the
backward direction gets `γ` from `survivor_complete`, uses `eq_of_heq (hγ.trans hxx.symm)` to identify
`survivorComponent γ = x₁` (both over the recovered contract graph), then `Finset.mem_image.mpr`.
`.toSurvivorMemTagReductionSupply` (given the reused `selectedOuter_partition`) produces body-211's supply.

## Consequence — all three tag correspondences at one granularity

```text
right    (219)  right_sound    / right_complete      componentToRight  ↔ inl false      (G-side, no HEq)
forest   (220)  forest_sound   / forest_complete     componentToForest ↔ inr B          (G-side, no HEq)
survivor (221)  survivor_sound / survivor_complete   survivorComponent ↔ star-avoiding  (quotient-side, HEq)
```

The three tag sector correspondences are now six `sound` / `complete` directions.  The remnant correspondence
(body-216, the one de-contraction leaf) remains; the deeper win (wiring to the sector inverse) is deferred.

Per the HALT: the `survivorComponent` round-trip body (soundness / completeness) is not entered; `survivorReembed` /
`right_surj` are not entered; only the `mem_image` + `HEq` assembly is proved.

Landed:

* `ResolvedSurvivorImageCorrespondenceDecompositionSupply D S Region` — the two fresh directions `sound` / `complete`;
* `.survivor_image_correspondence` — body-211's leaf (PROVED from the two directions);
* `.toSurvivorMemTagReductionSupply` — body-211's supply.

Toolkit body (like body-219).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-221 — the survivor image correspondence decomposition supply.**  The reused ambient transport and
the two fresh `survivorComponent` round-trip directions (soundness / completeness, `HEq`-linked across the two
contract graphs). -/
structure ResolvedSurvivorImageCorrespondenceDecompositionSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- Body-162/190: the recovered selected outer has exactly `A`'s components (the ambient transport). -/
  selectedOuter_partition : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ((S.Forward.imageSupply G).selectedOuterOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1.elements
      = z.1.1.elements
  /-- Sound: a `survivorComponent` image (`HEq`-linked to `x₂`) forces `x₂` star-avoiding. -/
  survivor_sound : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {y // y ∈ ResolvedCoassocSplitChoice.rightComponents
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)})
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
    HEq (S.Survivor.survivor.survivorComponent
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G) γ) x₂ →
    (x₂ ∈ z.2.1.elements ∧ Disjoint x₂.vertices (starOfZ z))
  /-- Complete: every star-avoiding `x₂` has a `survivorComponent` preimage (`HEq`-linked). -/
  survivor_complete : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
    (x₂ ∈ z.2.1.elements ∧ Disjoint x₂.vertices (starOfZ z)) →
    ∃ γ : {y // y ∈ ResolvedCoassocSplitChoice.rightComponents
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)},
      HEq (S.Survivor.survivor.survivorComponent
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G) γ) x₂

namespace ResolvedSurvivorImageCorrespondenceDecompositionSupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-221 — body-211's `survivor_image_correspondence` from `sound` + `complete`.** -/
theorem survivor_image_correspondence
    (F : ResolvedSurvivorImageCorrespondenceDecompositionSupply D S Region)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₁ : ResolvedFeynmanSubgraph (((S.Forward.imageSupply G).selectedOuterOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1.contractWithStars
        (D.starOf G ((S.Forward.imageSupply G).selectedOuterOf
          (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (hxx : HEq x₁ x₂) :
    x₁ ∈ (ResolvedCoassocSplitChoice.rightComponents
          (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).attach.image
          (S.Survivor.survivor.survivorComponent
            (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G))
      ↔ x₂ ∈ z.2.1.elements ∧ Disjoint x₂.vertices (starOfZ z) := by
  constructor
  · intro h
    obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp h
    exact F.survivor_sound z γ x₂ hxx
  · intro hand
    obtain ⟨γ, hγlink⟩ := F.survivor_complete z x₂ hand
    have heq : S.Survivor.survivor.survivorComponent
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G) γ = x₁ :=
      eq_of_heq (hγlink.trans hxx.symm)
    exact heq ▸ Finset.mem_image.mpr ⟨γ, Finset.mem_attach _ _, rfl⟩

/-- **R-6c-body-221 — body-211's survivor mem tag reduction supply.** -/
def toSurvivorMemTagReductionSupply
    (F : ResolvedSurvivorImageCorrespondenceDecompositionSupply D S Region) :
    ResolvedSurvivorMemTagReductionSupply D S Region where
  selectedOuter_partition := fun {G} z => F.selectedOuter_partition z
  survivor_image_correspondence := fun {G} z x₁ x₂ h => F.survivor_image_correspondence z x₁ x₂ h

end ResolvedSurvivorImageCorrespondenceDecompositionSupply

end GaugeGeometry.QFT.Combinatorial
