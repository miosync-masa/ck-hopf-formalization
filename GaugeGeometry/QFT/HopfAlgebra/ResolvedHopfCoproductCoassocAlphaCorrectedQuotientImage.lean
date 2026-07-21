import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaContractGlobalPerm
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientImage

/-!
# R-6c-body-514 — the canonical corrected quotient image at a filtered `q` (PROVED)

Five-hundred-and-fourteenth genuine-body step — the membership-derived image owner feeding the three-route correspondence,
built at the FILTERED `q` only (no raw `∀ s` lift — the body-468 over-quantification and the `p_R`-false total
`selectedOuter_mem` are avoided; the membership is body-496's filtered `mem_of_mem_forestBlockDomFinset`).

## The image owner

`canonicalCorrectedQuotientImage Measure E q : ResolvedCoassocQuotientImage W'.toData G` — the pair
`⟨⟨selectedOuterRawOf q.1, filtered mem⟩, canonicalCorrectedQuotientRaw … q.1⟩`.  Its projections are `rfl`:

* `resolvedCoassocQuotientGraph (canonicalCorrectedQuotientImage …) = selectedOuterContractGraph q.1`;
* `(canonicalCorrectedQuotientImage …).quotientForest = canonicalCorrectedQuotientRaw … q.1`;
* `(canonicalCorrectedQuotientImage …).selectedOuter.1 = selectedOuterRawOf q.1`.

So the image's inner-right graph is exactly body-512/513's `G₂` (the corrected quotient's contract-with-stars), and the
image is the `imageOf`-value the three-route star machinery (`quotientStarEquivOf`, `ResolvedQuotientStarCodomainSplit
Supply`) consumes.

## The named residual — the q-local three-route correspondence

Building body-513's `correspondence` field is the SOLE remaining combinatorial heart, reducing (via `quotientStarEquivOf`)
to three q-local sector inputs at this image:

```text
ResolvedQuotientStarCodomainSplitSupply.codomainEquiv   TwoStageStarIndex ≃ RightSurvivorIndex ⊕ RemnantIndex
rightEquiv   : RightPrimitiveIndex ≃ RightSurvivorIndex   (survivorInj_of_measure — right-survivor sector)
forestEquiv  : ForestPrimitiveIndex ≃ RemnantIndex        (correctedRemnantComponent_forestOccurrence_injective
                                                            + body-467 cross + body-464 disjointness — remnant sector)
```

plus the original-survivor / left-star routes (`survivingOriginal` / `leftStar_toSurvivor`) re-keyed to `q.1`.  These are
NOT built here (the assets — `survivorInj_of_measure` (498), `correctedRemnantComponent_forestOccurrence_injective` (466),
body-467 cross, body-464 disjointness, the union geometry `union_eq` (469) — all exist; the work is bundling them into the
three sector `Equiv`s at the filtered `q`, staying q-local).  Named as the residual; NOT claimed derived.

Per the HALT/guards: NOT lifted to a raw `∀ s` supply (the `imageOf` value is at `q.1` only); no `p_L`-branch stand-in
quotient; local correcting permutations are NOT composed; no `corrected = uncorrected` equality; correspondence and field
equalities are NOT co-resident; `quot_eq` / `ValueGeometry` are NOT entered; the un-built sector `Equiv`s are the named
residual; strict `StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc claim.  No facade, no flat term, no
`forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
  (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)

/-- **R-6c-body-514 ∎ — the canonical corrected quotient image at a filtered `q`.**  Membership from body-496's filtered
`mem_of_mem_forestBlockDomFinset` (NO raw `∀ s`). -/
noncomputable def canonicalCorrectedQuotientImage {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) :
    ResolvedCoassocQuotientImage canonicalUniqueSupportedCarrierProperSupply.toData G :=
  ⟨⟨(resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf q.1,
      (canonicalUniqueSelectedOuterFilteredMemSupply_of_measure Measure E).mem_of_mem_forestBlockDomFinset q.1 q.2⟩,
    canonicalCorrectedQuotientRaw Measure
      canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
      canonicalUniqueStarFactsOfW' q.1⟩

/-- **R-6c-body-514 — projection: the image's selected outer is the raw selected outer** (`rfl`). -/
theorem canonicalCorrectedQuotientImage_selectedOuter {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) :
    (canonicalCorrectedQuotientImage Measure E q).selectedOuter.1
      = (resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf q.1 :=
  rfl

/-- **R-6c-body-514 — projection: the image's quotient forest is the corrected quotient** (`rfl`). -/
theorem canonicalCorrectedQuotientImage_quotientForest {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) :
    (canonicalCorrectedQuotientImage Measure E q).quotientForest
      = canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1 :=
  rfl

/-- **R-6c-body-514 — projection: the image's quotient graph is the selected-outer contract graph** (`rfl`). -/
theorem canonicalCorrectedQuotientImage_quotientGraph {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) :
    resolvedCoassocQuotientGraph (canonicalCorrectedQuotientImage Measure E q)
      = ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1 :=
  rfl

end GaugeGeometry.QFT.Combinatorial
