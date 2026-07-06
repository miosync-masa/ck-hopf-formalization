import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSurvivorElementsScout

/-!
# R-6c-body-206 — survivor elements recovery: `survivor_elements_heq` from a fresh survivor membership bridge

Two-hundred-and-sixth genuine-body step, discharging body-204's survivor half `survivor_elements_heq` from one fresh
membership bridge.  This closes the survivor half of the forward-quotient `HEq` to a single quotient-side survivor
bridge — the dual of bodies 170/171.

## The membership-link transport helper (PROVED)

`heq_finset_of_mem_iff` is the caller-friendly single-Finset transport: an outer subgraph equality plus a
membership equivalence *linked across the two graphs by `HEq` of the elements* gives the `HEq` of the two Finsets.
`cases` the outer equality (abstract bound variables) collapses the two graphs; `Finset.ext` + `HEq.rfl` closes it.
Unlike body-205's `heq_finset_of_transport` (which needs a `▸` transport in the statement), this states the
membership over both graphs directly — clean to field.

## The reduction

`ResolvedSurvivorElementsRecoverySupply D S Region` fields the reused ambient transport `selectedOuter_partition`
(body-162/190) and the single fresh **survivor membership bridge**

```text
survivor_mem : ∀ x₁ x₂, HEq x₁ x₂ →
  (x₁ ∈ (rightSurvivorForest recovered).elements ↔ x₂ ∈ rightDomain z)
```

Its meaning: a recovered right-survivor component `x₁` and its `z`-graph image `x₂` (`HEq x₁ x₂`) correspond — the
`recoverChoice z γ = inl false`, `survivorReembed`-ed components of `unionOuter z` are exactly the star-avoiding
components of the original quotient `B = z.2`.

Then `.survivor_elements_heq` is **proved** by `heq_finset_of_mem_iff`.

## Consequence

The survivor half of the forward-quotient `HEq` is now the single fresh `survivor_mem` (the quotient-side survivor
bridge).  The remnant half (`remnant_elements_heq`, body-204) is untouched — the next body (body-207) fields its
analogous remnant bridge.  So the forward-quotient `HEq` residual splits into two membership bridges, both the dual
of the backward sector bridges.

Per the HALT: the survivor bridge body (the `recoverChoice` / `survivorReembed` correspondence) is not entered; the
`survivorComponent` / `componentToRight` inverse is not entered; the remnant side is untouched; this body is the
transport assembly only.

Landed:

* `heq_finset_of_mem_iff` — the membership-linked single-Finset `HEq` transport (PROVED, reusable);
* `ResolvedSurvivorElementsRecoverySupply D S Region` — the ambient transport + the fresh survivor bridge;
* `.survivor_elements_heq` — body-204's survivor half (PROVED from the bridge).

Toolkit body (like body-193).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-206 — the membership-linked single-Finset `HEq` transport.**  An outer subgraph equality plus a
membership equivalence linked across the two graphs by `HEq` of the elements gives the `HEq` of the two Finsets.
`cases` the outer equality, then `Finset.ext` + `HEq.rfl`.  Reusable for the survivor and remnant halves. -/
theorem heq_finset_of_mem_iff {G : ResolvedFeynmanGraph} {A₁ A₂ : ResolvedAdmissibleSubgraph G}
    (houter : A₁ = A₂)
    {s₁ : Finset (ResolvedFeynmanSubgraph (A₁.contractWithStars (D.starOf G A₁)))}
    {s₂ : Finset (ResolvedFeynmanSubgraph (A₂.contractWithStars (D.starOf G A₂)))}
    (hmem : ∀ (x₁ : ResolvedFeynmanSubgraph (A₁.contractWithStars (D.starOf G A₁)))
      (x₂ : ResolvedFeynmanSubgraph (A₂.contractWithStars (D.starOf G A₂))),
      HEq x₁ x₂ → (x₁ ∈ s₁ ↔ x₂ ∈ s₂)) :
    HEq s₁ s₂ := by
  cases houter
  apply heq_of_eq
  ext x
  exact hmem x x HEq.rfl

/-- **R-6c-body-206 — the survivor elements recovery supply.**  The reused ambient transport
`selectedOuter_partition` and the fresh survivor membership bridge. -/
structure ResolvedSurvivorElementsRecoverySupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- Body-162/190: the recovered selected outer has exactly `A`'s components (the ambient transport). -/
  selectedOuter_partition : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ((S.Forward.imageSupply G).selectedOuterOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1.elements
      = z.1.1.elements
  /-- The fresh survivor membership bridge: a recovered right-survivor component and its `z`-graph image (`HEq`)
  correspond exactly to `B`'s star-avoiding survivors. -/
  survivor_mem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₁ : ResolvedFeynmanSubgraph (((S.Forward.imageSupply G).selectedOuterOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1.contractWithStars
        (D.starOf G ((S.Forward.imageSupply G).selectedOuterOf
          (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
    HEq x₁ x₂ →
    (x₁ ∈ (S.Survivor.survivor.rightSurvivorForest
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
      ↔ x₂ ∈ rightDomain z)

namespace ResolvedSurvivorElementsRecoverySupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-206 — body-204's `survivor_elements_heq` from the survivor bridge.** -/
theorem survivor_elements_heq (F : ResolvedSurvivorElementsRecoverySupply D S Region)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    HEq (S.Survivor.survivor.rightSurvivorForest
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
      (rightDomain z) :=
  heq_finset_of_mem_iff (ResolvedAdmissibleSubgraph.ext_elements (F.selectedOuter_partition z))
    (F.survivor_mem z)

end ResolvedSurvivorElementsRecoverySupply

end GaugeGeometry.QFT.Combinatorial
