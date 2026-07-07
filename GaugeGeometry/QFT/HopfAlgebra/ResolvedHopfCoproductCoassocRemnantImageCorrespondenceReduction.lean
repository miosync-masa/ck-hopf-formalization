import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantMemTagReduction

/-!
# R-6c-body-222 — remnant image correspondence reduction: reduced to `remnantComponent` sound + complete

Two-hundred-and-twenty-second genuine-body step, the last of the four sector reductions: body-216's
`remnant_image_correspondence` — the one de-contraction leaf — is reduced to the two `remnantComponent` round-trip
directions by the same `HEq`-linked pattern as body-221's survivor.  So **all four sector correspondences** now sit
at the uniform `sound` / `complete` granularity.

## The reduction

`remnant_image_correspondence` is `x₁ ∈ forestComponents(recovered).attach.image (fun γ => remnantComponent
(forestComponentOccurrence γ)) ↔ x₂ ∈ z.2.1.elements ∧ ¬ Disjoint x₂.vertices (starOfZ z)` (`HEq x₁ x₂` given).  Via
`Finset.mem_image` it splits into:

* **sound** — for a forest-choice component `γ` and an `HEq`-linked `x₂`, `remnantComponent (forestComponentOccurrence
  γ)` being `HEq x₂` forces `x₂` star-touching;
* **complete** — every star-touching `x₂` has a forest-choice `γ` with `remnantComponent (forestComponentOccurrence
  γ)` `HEq x₂`.

Unlike the survivor / right / forest tag correspondences, these two carry the genuine **de-contraction** geometry
(`remnantComponent` lands in the contracted graph with a nontrivial `remnantClass_eq`, bodies 126/183); at this
assembly layer they are fielded uniformly.

`ResolvedRemnantImageCorrespondenceDecompositionSupply D S Region` fields the two fresh directions `remnant_sound` /
`remnant_complete`.  Then `.remnant_image_correspondence` is **proved** exactly as body-221: the forward direction
reads off the image element (`Finset.mem_image.mp`, term-mode) and applies `remnant_sound` with the given `HEq`; the
backward direction gets `γ` from `remnant_complete`, uses `eq_of_heq (hγ.trans hxx.symm)` to identify the image
element with `x₁`, then `Finset.mem_image.mpr`.  `.toRemnantMemTagReductionSupply` (given the reused
`selectedOuter_partition`) produces body-216's supply.

## Consequence — all four sector correspondences at one granularity

```text
right    (219)  right_sound    / right_complete      componentToRight  ↔ inl false        (G-side, no HEq)
forest   (220)  forest_sound   / forest_complete     componentToForest ↔ inr B            (G-side, no HEq)
survivor (221)  survivor_sound / survivor_complete   survivorComponent ↔ star-avoiding    (quotient, HEq)
remnant  (222)  remnant_sound  / remnant_complete    remnantComponent  ↔ star-touching    (quotient, HEq, de-contraction)
```

The four sector correspondences are now eight `sound` / `complete` directions — the uniform sector-bridge floor.
Three are tag round-trips; the remnant pair carries the de-contraction.  The deeper win (wiring the region maps to
the sector inverse, collapsing all eight) is deferred.

Per the HALT: the `remnantComponent` round-trip body (soundness / completeness) is not entered; `remnantGen` /
`remnantClass_eq` / de-contraction are not entered; only the `mem_image` + `HEq` assembly is proved.

Landed:

* `ResolvedRemnantImageCorrespondenceDecompositionSupply D S Region` — the two fresh directions `sound` / `complete`;
* `.remnant_image_correspondence` — body-216's leaf (PROVED from the two directions);
* `.toRemnantMemTagReductionSupply` — body-216's supply.

Toolkit body (like body-221).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-222 — the remnant image correspondence decomposition supply.**  The reused ambient transport and the
two fresh `remnantComponent` round-trip directions (soundness / completeness, `HEq`-linked, carrying the
de-contraction). -/
structure ResolvedRemnantImageCorrespondenceDecompositionSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- Body-162/190: the recovered selected outer has exactly `A`'s components (the ambient transport). -/
  selectedOuter_partition : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ((S.Forward.imageSupply G).selectedOuterOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1.elements
      = z.1.1.elements
  /-- Sound: a `remnantComponent` image (`HEq`-linked to `x₂`) forces `x₂` star-touching. -/
  remnant_sound : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {y // y ∈ ResolvedCoassocSplitChoice.forestComponents
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)})
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
    HEq (S.Remnant.remnant.remnantComponent
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)
        (ResolvedCoassocSplitChoice.forestComponentOccurrence
          (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G) γ)) x₂ →
    (x₂ ∈ z.2.1.elements ∧ ¬ Disjoint x₂.vertices (starOfZ z))
  /-- Complete: every star-touching `x₂` has a `remnantComponent` preimage (`HEq`-linked). -/
  remnant_complete : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
    (x₂ ∈ z.2.1.elements ∧ ¬ Disjoint x₂.vertices (starOfZ z)) →
    ∃ γ : {y // y ∈ ResolvedCoassocSplitChoice.forestComponents
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)},
      HEq (S.Remnant.remnant.remnantComponent
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)
        (ResolvedCoassocSplitChoice.forestComponentOccurrence
          (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G) γ)) x₂

namespace ResolvedRemnantImageCorrespondenceDecompositionSupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-222 — body-216's `remnant_image_correspondence` from `sound` + `complete`.** -/
theorem remnant_image_correspondence
    (F : ResolvedRemnantImageCorrespondenceDecompositionSupply D S Region)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₁ : ResolvedFeynmanSubgraph (((S.Forward.imageSupply G).selectedOuterOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1.contractWithStars
        (D.starOf G ((S.Forward.imageSupply G).selectedOuterOf
          (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (hxx : HEq x₁ x₂) :
    x₁ ∈ (ResolvedCoassocSplitChoice.forestComponents
          (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).attach.image
          (fun γ => S.Remnant.remnant.remnantComponent
            (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)
            (ResolvedCoassocSplitChoice.forestComponentOccurrence
              (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G) γ))
      ↔ x₂ ∈ z.2.1.elements ∧ ¬ Disjoint x₂.vertices (starOfZ z) := by
  constructor
  · intro h
    obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp h
    exact F.remnant_sound z γ x₂ hxx
  · intro hand
    obtain ⟨γ, hγlink⟩ := F.remnant_complete z x₂ hand
    have heq : S.Remnant.remnant.remnantComponent
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)
        (ResolvedCoassocSplitChoice.forestComponentOccurrence
          (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G) γ) = x₁ :=
      eq_of_heq (hγlink.trans hxx.symm)
    exact heq ▸ Finset.mem_image.mpr ⟨γ, Finset.mem_attach _ _, rfl⟩

/-- **R-6c-body-222 — body-216's remnant mem tag reduction supply.** -/
def toRemnantMemTagReductionSupply
    (F : ResolvedRemnantImageCorrespondenceDecompositionSupply D S Region) :
    ResolvedRemnantMemTagReductionSupply D S Region where
  selectedOuter_partition := fun {G} z => F.selectedOuter_partition z
  remnant_image_correspondence := fun {G} z x₁ x₂ h => F.remnant_image_correspondence z x₁ x₂ h

end ResolvedRemnantImageCorrespondenceDecompositionSupply

end GaugeGeometry.QFT.Combinatorial
