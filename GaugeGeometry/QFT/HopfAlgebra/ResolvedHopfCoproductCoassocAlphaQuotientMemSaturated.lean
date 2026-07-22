import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaCorrectedQuotientSaturation
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaQuotientMemComplete
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaQuotientMemDischarge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaInnerRawSaturation
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRecoveredSaturationComplete
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarCoreClosureAssembly

/-!
# R-6c-body-540 — the `W″` corrected-quotient six-condition membership + carrier-closure bundle (PROVED)

Five-hundred-and-fortieth genuine-body step — the `W″` ownership-completion checkpoint.  Body-539 landed the LAST
combinatorial fourth-axis fact (`canonicalCorrectedQuotientRaw_forestExternalLegSaturated`: both regions of the corrected
/ two-stage quotient are `ResolvedForestExternalLegSaturated`).  This body lifts it to a FORMAL `W″` six-condition
membership, and assembles the single-owner `W″` carrier-closure bundle.

## The two deliverables

* **Step 1 — `W″` complement positivity.**  A verbatim replay of body-501's
  `canonicalCorrectedQuotientRaw_complementEdges_card_pos`, with the carrier-supply accessors swapped
  (`canonicalUniqueSupportedCarrierProperSupply` → `canonicalLegSaturatedCarrierProperSupply`,
  `canonicalUniqueStarFactsOfW'` → `canonicalLegSaturatedStarFacts`) and the two `W′`-specific projections on `q.1.1.2`
  routed through `canonicalLegSaturatedCarrier_mem_W'` / `mem_canonicalLegSaturatedCarrier_full_iff`.  The count geometry
  (`selectedOuter_internalEdges_le_inputOuter`, `count_map_eq_count_of_injOn_mem`, `retargetEdge_injOn_internalEdges`,
  `count_complementEdges_eq_count_contractWithStars`, `canonicalCorrectedQuotientRaw_internalEdges_le_inputResidual`,
  `complementEdges_card_pos_of_count_lt`) is generic over the carrier supply and transports unchanged.

* **Step 2 — `W″` six-condition quotient membership.**  A replay of body-499's
  `canonicalCorrectedQuotient_mem_of_complement`, now over `W″`, with the SIXTH conjunct — external-leg saturation —
  discharged from body-539.  `IsProperForest` (conjunct 5) is fed Step 1; the fourth-axis saturation (conjunct 6) is
  `canonicalCorrectedQuotientRaw_forestExternalLegSaturated` (body-539) fed the SOURCE outer saturation
  `canonicalLegSaturatedCarrier_saturated q.1.1.2`.  The leg-attachment side-condition `hL` is NOT an input: it is
  `hAmbG.2` (`AmbientLegsSupported G`, the second component of `ResolvedAmbientSupported G`), read off the block's own
  ambient support — one fewer hypothesis than the task recipe.

* **Step 3 — the single-owner `W″` carrier-closure bundle.**  Mirrors body-443's
  `canonicalUniqueMultiStarCarrierClosureBundleSupply` over `W″`: `Closure := canonicalLegSaturatedInnerRawCarrierClosureSupply
  Core` (body-538) and `recovered_raw_mem := canonicalLegSaturated_regionRawUnion_mem` (body-537), with the same
  `Core.toDecontractionSupply (canonicalLegSaturatedInnerRawCarrierClosureSupply Core)` owner in both the field and the
  body.  `Nne` is sourced from `Measure.toConnectedDivergentNonemptySupply`, `Ppos` from the explicit `E`.

## Running scoreboard (`W″` migration)

```text
selectedOuter        DERIVED W″ membership  (body-534)
recoveredRawUnion    DERIVED W″ membership  (body-537)
innerRaw             DERIVED W″ closure      (body-538)
corrected-quotient   DERIVED W″ membership  (body-540, this file)   ← the last combinatorial checkpoint, now FORMAL
W″ carrier-closure bundle   CONSTRUCTED      (body-540, this file)
```

Independent `LegModel` input at the carrier-closure level = **ZERO**: every saturation obligation is DISCHARGED as a
consequence of membership.  `LegModel` is ABSORBED BY MEMBERSHIP.

## Post-540 status

`W″` combinatorial carrier ownership is COMPLETE.  What remains is the `quot_eq` / alpha-wrapper RE-SPECIALIZATION to the
`W″` owner — a migration campaign re-issuing body-529's canonical alpha chain over `W″` (bodies 496–531 re-keyed from
`W′` to `W″`).  Once that lands, the only remaining GENUINE model law is `Parent` (the inverse-decontraction /
divergence-closure physics law).  Final signature target after that campaign: `Measure / E / Parent / rep*`.

Per the HALT/guards: body-501's `W′` `canonicalCorrectedQuotient_mem` is NOT reused / cast; NO quot_eq / coassoc wrapper
migration and NO `Parent` CD derivation; no target membership is read to reverse-engineer properness/saturation (both
CONSTRUCTED); no corrected-permutation comparison, no strict socket, no unconditional-coassoc claim; the `Closure` owner
is written ONCE (`canonicalLegSaturatedInnerRawCarrierClosureSupply Core`) so both projections read the SAME closure.  No
facade, no flat term, no `forgetHopf`, no rep/perm, and NO new datum field / socket.
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

variable {G : ResolvedFeynmanGraph}

/-! ## Step 1 — the `W″` quotient complement is nonempty (body-501 replay, accessors swapped). -/

/-- **R-6c-body-540 ∎ — the `W″` corrected quotient complement is nonempty.**  A verbatim replay of body-501's
strict-count witness, with the carrier-supply accessors routed to `W″` (`canonicalLegSaturatedCarrier_mem_W'` for
edge-id uniqueness, `mem_canonicalLegSaturatedCarrier_full_iff` for input-outer properness).  The count geometry is
generic over the carrier supply and transports unchanged. -/
theorem canonicalLegSaturatedCorrectedQuotientRaw_complementEdges_card_pos
    (Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData)
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G) :
    0 < (canonicalCorrectedQuotientRaw Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
        canonicalLegSaturatedStarFacts q.1).complementEdges.card := by
  set S := (resolvedConcreteForestPromoteSupply canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf
    q.1 with hSdef
  set f := S.retargetEdge (canonicalLegSaturatedCarrierProperSupply.toData.starOf G S) with hfdef
  -- Step 1 — the input-outer residual witness
  have hId : G.EdgeIdsUnique := edgeIdsUnique_of_carrier_mem (canonicalLegSaturatedCarrier_mem_W' q.1.1.2)
  have hApf : q.1.1.1.IsProperForest :=
    ((mem_canonicalLegSaturatedCarrier_full_iff _).mp q.1.1.2).2.2.2.2.1
  obtain ⟨e, heA⟩ := Multiset.card_pos_iff_exists_mem.mp
    (ResolvedAdmissibleSubgraph.complementEdges_card_pos_of_isProperForest hApf)
  have hAG : Multiset.count e q.1.1.1.internalEdges < Multiset.count e G.internalEdges :=
    ResolvedAdmissibleSubgraph.count_lt_of_mem_complementEdges heA
  -- Step 2 — subtraction survives the strict gap
  have hSA : S.internalEdges ≤ q.1.1.1.internalEdges := selectedOuter_internalEdges_le_inputOuter q.1
  have hcSA : Multiset.count e S.internalEdges ≤ Multiset.count e q.1.1.1.internalEdges :=
    Multiset.count_le_of_le e hSA
  have heG : e ∈ G.internalEdges := Multiset.mem_of_le (Multiset.sub_le_self _ _) heA
  have heS : e ∈ S.complementEdges := by
    show e ∈ G.internalEdges - S.internalEdges
    rw [← Multiset.count_pos, Multiset.count_sub]; omega
  have hRstrict : Multiset.count e (q.1.1.1.internalEdges - S.internalEdges)
      < Multiset.count e S.complementEdges := by
    show Multiset.count e (q.1.1.1.internalEdges - S.internalEdges)
      < Multiset.count e (G.internalEdges - S.internalEdges)
    rw [Multiset.count_sub, Multiset.count_sub]; omega
  -- Step 3 — residual map-side transport
  have hRmap : Multiset.count (f e)
        ((q.1.1.1.internalEdges - S.internalEdges).map f)
      = Multiset.count e (q.1.1.1.internalEdges - S.internalEdges) :=
    count_map_eq_count_of_injOn_mem
      (ResolvedAdmissibleSubgraph.retargetEdge_injOn_internalEdges hId S _)
      (fun a ha => Multiset.mem_of_le q.1.1.1.internalEdges_le
        (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha)) heG
  -- Step 4 — contract-ambient transport
  have hH : Multiset.count e S.complementEdges
      = Multiset.count (f e) (S.contractWithStars
          (canonicalLegSaturatedCarrierProperSupply.toData.starOf G S)).internalEdges :=
    ResolvedAdmissibleSubgraph.count_complementEdges_eq_count_contractWithStars hId S _ heS
  -- Step 5 — the quotient's strict count
  have hQcount : Multiset.count (f e)
        (canonicalCorrectedQuotientRaw Measure
          canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
          canonicalLegSaturatedStarFacts q.1).internalEdges
      ≤ Multiset.count (f e) ((q.1.1.1.internalEdges - S.internalEdges).map f) :=
    Multiset.count_le_of_le _
      (canonicalCorrectedQuotientRaw_internalEdges_le_inputResidual Measure _ _ q.1)
  refine ResolvedAdmissibleSubgraph.complementEdges_card_pos_of_count_lt (e := f e) ?_
  show Multiset.count (f e)
      (canonicalCorrectedQuotientRaw Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
        canonicalLegSaturatedStarFacts q.1).internalEdges
    < Multiset.count (f e) (S.contractWithStars
        (canonicalLegSaturatedCarrierProperSupply.toData.starOf G S)).internalEdges
  omega

/-! ## Step 2 — the `W″` six-condition corrected-quotient membership (body-499 replay + saturation). -/

/-- **R-6c-body-540 ∎ — the canonical `W″` filtered corrected-quotient membership, DISCHARGED.**  All six `W″` carrier
conditions of the contract graph `H := q.1.selectedOuterContractGraph` hold: the four ambient facts transfer through the
contraction (body-499's engines), properness is body-428 fed Step 1's complement positivity, and — the new sixth
condition — external-leg saturation is body-539's `canonicalCorrectedQuotientRaw_forestExternalLegSaturated` fed the
SOURCE outer saturation `canonicalLegSaturatedCarrier_saturated q.1.1.2`.  The leg-attachment side-condition is `hAmbG.2`
(`AmbientLegsSupported G`), so NO `hL` premise is needed.  body-501's `W′` membership is NOT reused. -/
theorem canonicalLegSaturatedCorrectedQuotient_mem
    (Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    (q : FilteredForestBlockDom canonicalLegSaturatedCarrierProperSupply.toData G) :
    canonicalCorrectedQuotientRaw Measure
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
        canonicalLegSaturatedStarFacts q.1
      ∈ canonicalLegSaturatedCarrierProperSupply.toData.carrier
          (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) := by
  set A := (resolvedConcreteForestPromoteSupply
    canonicalLegSaturatedCarrierProperSupply.toData G).selectedOuterRawOf q.1 with hA
  have hAmbG : ResolvedAmbientSupported G :=
    canonicalUniqueSupportedCarrier_ambientSupported (canonicalLegSaturatedCarrier_mem_W' q.1.1.2)
  have hCDG : G.forget.IsConnectedDivergent :=
    canonicalUniqueSupportedCarrier_ambientCD (canonicalLegSaturatedCarrier_mem_W' q.1.1.2)
  refine (mem_canonicalLegSaturatedCarrier_full_iff _).mpr ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · -- ResolvedAmbientSupported H (edges)
    exact A.contractWithStars_internalEdges_supported _ hAmbG.1
  · -- ResolvedAmbientSupported H (legs)
    exact A.contractWithStars_externalLegs_supported _ hAmbG.2
  · -- H.forget.IsConnectedDivergent
    exact Measure.contract_preserves_CD G A hCDG
  · -- H.EdgeIdsUnique
    exact edgeIdsUnique_contractWithStars A _
      (edgeIdsUnique_of_carrier_mem (canonicalLegSaturatedCarrier_mem_W' q.1.1.2))
  · -- H.LegIdsUnique
    exact legIdsUnique_contractWithStars A _
      (legIdsUnique_of_carrier_mem (canonicalLegSaturatedCarrier_mem_W' q.1.1.2))
  · -- IsProperForest, reduced to conjunct 1 + conjunct 5
    exact isProperForest_of_isNonempty_complement
      (Measure.toConnectedDivergentNonemptySupply _) (E _) _
      (canonicalCorrectedQuotientRaw_isNonempty Measure _ _ q)
      (canonicalLegSaturatedCorrectedQuotientRaw_complementEdges_card_pos Measure q)
  · -- ResolvedForestExternalLegSaturated H — body-539, source outer saturation from live membership
    exact canonicalCorrectedQuotientRaw_forestExternalLegSaturated Measure
      canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider
      canonicalLegSaturatedStarFacts q.1 hAmbG.2
      (canonicalLegSaturatedCarrier_saturated q.1.1.2)

/-! ## Step 3 — the single-owner `W″` carrier-closure bundle (body-443 mirror). -/

/-- **R-6c-body-540 ∎ — the `W″` carrier-closure bundle.**  Mirrors body-443's
`canonicalUniqueMultiStarCarrierClosureBundleSupply` over `W″`: `Closure` is body-538's `W″` inner-raw carrier closure and
`recovered_raw_mem` is body-537's `W″` recovered-union membership.  The `Closure` owner is written ONCE
(`canonicalLegSaturatedInnerRawCarrierClosureSupply Core`), so the field value and the `Core.toDecontractionSupply …` in
the body read the SAME closure.  `Nne` is sourced from `Measure.toConnectedDivergentNonemptySupply`, `Ppos` from `E`. -/
noncomputable def canonicalLegSaturatedMultiStarCarrierClosureBundleSupply
    (Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData)
    (E : ∀ G : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply G)
    (Core : ResolvedMultiStarDecontractionValueCoreSupply
      canonicalLegSaturatedCarrierProperSupply.toData) :
    ResolvedMultiStarCarrierClosureBundleSupply Core canonicalLegSaturatedStarFacts where
  Closure := canonicalLegSaturatedInnerRawCarrierClosureSupply Core
  recovered_raw_mem := fun {G} z =>
    canonicalLegSaturated_regionRawUnion_mem
      (fun H => Measure.toConnectedDivergentNonemptySupply H) E
      (Core.toDecontractionSupply (canonicalLegSaturatedInnerRawCarrierClosureSupply Core))
      canonicalLegSaturatedStarFacts z

end GaugeGeometry.QFT.Combinatorial
