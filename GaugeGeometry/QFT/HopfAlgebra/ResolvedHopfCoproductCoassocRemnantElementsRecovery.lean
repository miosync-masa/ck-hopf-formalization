import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSurvivorElementsRecovery

/-!
# R-6c-body-207 — remnant elements recovery: `remnant_elements_heq` from a fresh remnant membership bridge

Two-hundred-and-seventh genuine-body step, discharging body-204's remnant half `remnant_elements_heq` from one
fresh membership bridge — the same shape as the survivor half (body-206), via body-206's `heq_finset_of_mem_iff`.
This closes the remnant half of the forward-quotient `HEq` to a single quotient-side remnant bridge, the dual of
body-171.

## The reduction

`ResolvedRemnantElementsRecoverySupply D S Region` fields the reused ambient transport `selectedOuter_partition`
(body-162/190) and the single fresh **remnant membership bridge**

```text
remnant_mem : ∀ x₁ x₂, HEq x₁ x₂ →
  (x₁ ∈ (remnantForest recovered).elements ↔ x₂ ∈ forestDomain z)
```

Its meaning: a recovered remnant component `x₁` and its `z`-graph image `x₂` (`HEq x₁ x₂`) correspond — the
`recoverChoice z γ = inr B`, de-contracted `remnantComponent` components of `unionOuter z` are exactly the
star-touching components of the original quotient `B = z.2`.  Unlike the survivor half — where `survivorReembed`
preserves vertices (`rfl`-level) — this bridge carries the genuine de-contraction geometry (bodies 126/183); but at
this assembly layer it is fielded uniformly.

Then `.remnant_elements_heq` is **proved** by `heq_finset_of_mem_iff` (body-206).

## Consequence

Both halves of the forward-quotient `HEq` are now single fresh membership bridges: `survivor_mem` (body-206) and
`remnant_mem` (here), the duals of the backward sector bridges.  The next body (body-208) assembles
206 + 207 → body-204 → 203 → 165, so `forward_quotient_heq` reduces to exactly these two bridges (plus the reused
ambient transport).

Per the HALT: the remnant bridge body (the `recoverChoice` / `remnantComponent` de-contraction correspondence) is
not entered; `remnantGen` / `componentToForest` inverse is not entered; the survivor side is untouched; this body is
the transport assembly only.

Landed:

* `ResolvedRemnantElementsRecoverySupply D S Region` — the ambient transport + the fresh remnant bridge;
* `.remnant_elements_heq` — body-204's remnant half (PROVED from the bridge via body-206's helper).

Toolkit body (like body-206).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-207 — the remnant elements recovery supply.**  The reused ambient transport
`selectedOuter_partition` and the fresh remnant membership bridge (the recovered remnant forest's components,
transported to `z`'s contract graph, are `B`'s star-touching remnants). -/
structure ResolvedRemnantElementsRecoverySupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- Body-162/190: the recovered selected outer has exactly `A`'s components (the ambient transport). -/
  selectedOuter_partition : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ((S.Forward.imageSupply G).selectedOuterOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1.elements
      = z.1.1.elements
  /-- The fresh remnant membership bridge: a recovered remnant component and its `z`-graph image (`HEq`) correspond
  exactly to `B`'s star-touching remnants. -/
  remnant_mem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₁ : ResolvedFeynmanSubgraph (((S.Forward.imageSupply G).selectedOuterOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1.contractWithStars
        (D.starOf G ((S.Forward.imageSupply G).selectedOuterOf
          (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
    HEq x₁ x₂ →
    (x₁ ∈ (S.Remnant.remnant.remnantForest
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
      ↔ x₂ ∈ forestDomain z)

namespace ResolvedRemnantElementsRecoverySupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-207 — body-204's `remnant_elements_heq` from the remnant bridge.** -/
theorem remnant_elements_heq (F : ResolvedRemnantElementsRecoverySupply D S Region)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    HEq (S.Remnant.remnant.remnantForest
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
      (forestDomain z) :=
  heq_finset_of_mem_iff (ResolvedAdmissibleSubgraph.ext_elements (F.selectedOuter_partition z))
    (F.remnant_mem z)

end ResolvedRemnantElementsRecoverySupply

end GaugeGeometry.QFT.Combinatorial
