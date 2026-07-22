import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaParentSaturation
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRecoveredSaturationAudit
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSaturationAlgebra
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarRegionCross
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTouchedLocalizationLeg
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTOFPreimageAlignment
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSaturatedCarrier
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionRawNonempty
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocComplementCountBackbone
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredRawClosureAssembly

/-!
# R-6c-body-537 — the `W″` `recoveredRawUnion` external-leg-saturation closure (PROVED)

Five-hundred-and-thirty-seventh genuine-body step — the concrete three-region assembly that body-536 recorded as "recipe,
NOT forced".  Body-536 landed the three per-region closures individually (left FREE via body-535, right DERIVED via
body-535, forest via the boundary-ID cancellation) but left the forest closure gated on an EXTERNAL hypothesis
`hInner`/`hInnerAll` — the per-component source saturation of the localized quotient component
`touchedLocalComponent z δ` inside its touched-forest-contracted ambient.  This body:

* **Step 1** discharges that gate — `touchedLocalComponent_externalLegSaturated_of_whole` derives the touched-local
  source saturation from the WHOLE-contracted quotient saturation `hWhole` (the live `z.2` membership datum), so `hInner`
  is no longer an input.  The mechanism is a multiplicity-safe FILTER EQUALITY: the `δ`-attach filters of the
  touched-forest-contracted and whole-contracted external legs coincide, because the two retargets agree on every
  `δ`-attached (touched-or-outside) leg (`whole_touched_retargetLeg_eq`, body-320) and the two attach predicates are
  equivalent on `G.externalLegs` (`touched_vertex_ok_of_local` / `touched_vertex_ok`, bodies 437/319).  No membership-only
  shortcut, no new socket.
* **Step 2** assembles the concrete three-region union `regionRawUnion` — `resolvedForestExternalLegSaturated_union`
  (body-534) applied twice over the left/right/forest regions (body-338), with left = body-535 FREE, right = body-535
  DERIVED, forest = body-536 Step 5 fed by Step 1.  The saturation hypotheses `hOuter`/`hQuotient`/`hLegId` are EXPLICIT.
* **Step 3** specializes to `W″`, discharging `hOuter`/`hQuotient` from the live block memberships `z.1.2`/`z.2.2`
  (`canonicalLegSaturatedCarrier_saturated`) and `hLegId` from the `W′` accessor
  (`legIdsUnique_of_carrier_mem`).  `z.2.2` IS a `W″` carrier membership (the inner forest lives over the same canonical
  `W″` carrier of the contracted graph), so it yields the quotient saturation DIRECTLY.
* **Step 4** — the payoff: `regionRawUnion M Fstar z ∈ W″.carrier`, via
  `mem_canonicalLegSaturatedCarrier_full_iff` with the five `W′`/geometry conditions (support/CD/edge/leg from the `W′`
  accessors on `z.1.2`; properness from the body-444 complement backbone) plus the Step-3 saturation as the sixth.

## Running scoreboard (do NOT count "only the three constructions" as done)

`W″` migration has MORE saturation obligations than the recovered union:

```text
selectedOuter        PASSED W″  (body-534)
recoveredRawUnion    PASSED W″  (body-537, this file)
innerRaw             AUDIT OPEN  ← ResolvedMultiStarDecontractionSupply.innerRaw_mem carries a saturation conjunct on a
                                   DIFFERENT owner (the DE-CONTRACTED PARENT's graph, not G), NOT covered here
corrected-quotient   AUDIT OPEN
```

The `innerRaw_mem` field (`canonicalUniqueInnerRawCarrierClosureSupply.innerRaw_mem`, body-443) inserts the parent
`Core.parent z δ` into `W′.carrier (Core.parent z δ).toResolvedFeynmanGraph`; migrated to `W″` it acquires a
`ResolvedForestExternalLegSaturated (Core.parent z δ)` conjunct on the parent's OWN ambient graph — a distinct owner from
the recovered union's `G`, so this closure does NOT discharge it.  Likewise the corrected-quotient two-stage survivor
carrier (bodies 520–529) is untouched.

Per the HALT/guards: `hInner` is DISCHARGED (Step 1), never socketed; no target recovered-union membership is read for
saturation (Step 4's target membership is CONSTRUCTED from the five `W′`/geometry conditions + Step 3, not read); the `W″`
`LegModel` supply is NOT used; `parentCD` is NOT touched in any saturation proof; no `houter` / forward reconstruction /
round-trip; the corrected quotient is NOT entered; the coassoc theorem is NOT re-issued; strict `StarProm` /
`InnerStarRaw` stay ZERO; NO unconditional-coassoc claim.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
`promote_collapse` / singleton / floor-297.
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

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-! ## Step 1 — whole→touched localization: discharge body-536's `hInner` gate. -/

/-- **R-6c-body-537 ∎ — the localized quotient component is externally-leg-saturated from the WHOLE saturation.**
Removes body-536's `hInner` external hypothesis: the touched-forest-contracted saturation of `touchedLocalComponent z δ`
is derived from the whole-contracted saturation `hWhole` of `δ` (the live `z.2` membership datum).  Both targets share the
RHS `δ.externalLegs` (`touchedLocalComponent`'s vertices/legs are `δ`'s, `rfl`), so it suffices to prove the
multiplicity-safe FILTER EQUALITY: the `δ`-attach filters of the two contracted external-leg multisets coincide.  The
retargets agree on every `δ`-attached (touched-or-outside) leg (`whole_touched_retargetLeg_eq`), and the two attach
predicates are equivalent on `G.externalLegs` (`touched_vertex_ok_of_local` forward / `touched_vertex_ok` reverse). -/
theorem touchedLocalComponent_externalLegSaturated_of_whole (Fstar : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (hWhole : ResolvedExternalLegSaturated (z.1.1.contractWithStars (D.starOf G z.1.1)) δ) :
    ResolvedExternalLegSaturated ((touchedOuterForest z δ).contractWithStars (D.starOf G z.1.1))
      (touchedLocalComponent z δ) := by
  -- Attachment of a retargeted leg is the retargeted attachment vertex.
  have hTattach : ∀ ℓ : ResolvedExternalLeg,
      ((touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1) ℓ).attachedTo
        = (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) ℓ.attachedTo := by
    intro ℓ
    unfold ResolvedAdmissibleSubgraph.retargetExternalLeg
    rw [ResolvedExternalLeg.retarget_attachedTo]
  have hWattach : ∀ ℓ : ResolvedExternalLeg,
      (z.1.1.retargetExternalLeg (D.starOf G z.1.1) ℓ).attachedTo
        = z.1.1.retargetVertex (D.starOf G z.1.1) ℓ.attachedTo := by
    intro ℓ
    unfold ResolvedAdmissibleSubgraph.retargetExternalLeg
    rw [ResolvedExternalLeg.retarget_attachedTo]
  -- On `G.externalLegs`, the two attach predicates coincide.
  have hiff : ∀ ℓ ∈ G.externalLegs,
      (((touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1) ℓ).attachedTo ∈ δ.vertices
        ↔ (z.1.1.retargetExternalLeg (D.starOf G z.1.1) ℓ).attachedTo ∈ δ.vertices) := by
    intro ℓ _
    rw [hTattach ℓ, hWattach ℓ]
    have hvle : (ℓ.attachedTo ∈ (touchedOuterForest z δ).vertices ∨ ℓ.attachedTo ∉ z.1.1.vertices) →
        z.1.1.retargetVertex (D.starOf G z.1.1) ℓ.attachedTo
          = (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) ℓ.attachedTo := by
      intro hok
      rw [← hWattach ℓ, ← hTattach ℓ, whole_touched_retargetLeg_eq z δ ℓ hok]
    constructor
    · intro hT
      rw [hvle (touched_vertex_ok_of_local Fstar z δ hT)]; exact hT
    · intro hW
      rw [← hvle (touched_vertex_ok z δ hW)]; exact hW
  -- On the touched-attached submultiset, the two retargets agree.
  have hmapc : ∀ ℓ ∈ G.externalLegs.filter (fun ℓ =>
        ((touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1) ℓ).attachedTo ∈ δ.vertices),
      (touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1) ℓ
        = z.1.1.retargetExternalLeg (D.starOf G z.1.1) ℓ := by
    intro ℓ hℓ
    have hTP : ((touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1) ℓ).attachedTo ∈ δ.vertices :=
      (Multiset.mem_filter.mp hℓ).2
    rw [hTattach ℓ] at hTP
    exact (whole_touched_retargetLeg_eq z δ ℓ (touched_vertex_ok_of_local Fstar z δ hTP)).symm
  -- The filter equality: the `δ`-attach filters of the two contracted external legs coincide.
  have hkey : ((touchedOuterForest z δ).contractWithStars (D.starOf G z.1.1)).externalLegs.filter
        (fun ℓ => ℓ.attachedTo ∈ δ.vertices)
      = (z.1.1.contractWithStars (D.starOf G z.1.1)).externalLegs.filter
        (fun ℓ => ℓ.attachedTo ∈ δ.vertices) := by
    rw [ResolvedAdmissibleSubgraph.contractWithStars_externalLegs,
        ResolvedAdmissibleSubgraph.contractWithStars_externalLegs,
        Multiset.filter_map, Multiset.filter_map]
    exact (Multiset.map_congr rfl hmapc).trans
      (congrArg (Multiset.map (z.1.1.retargetExternalLeg (D.starOf G z.1.1)))
        (Multiset.filter_congr hiff))
  -- Transport `hWhole` across the equality.
  show ((touchedOuterForest z δ).contractWithStars (D.starOf G z.1.1)).externalLegs.filter
      (fun ℓ => ℓ.attachedTo ∈ δ.vertices) ≤ δ.externalLegs
  rw [hkey]
  exact hWhole

/-! ## Step 2 — the generic concrete three-region closure (explicit hypotheses). -/

/-- **R-6c-body-537 ∎ — the raw three-region union is forest external-leg-saturated.**  Assembles the concrete
`regionRawUnion` (body-338) via `resolvedForestExternalLegSaturated_union` (body-534) applied twice: left = body-535 FREE
(`leftResidualTouched_forestExternalLegSaturated`), right = body-535 DERIVED (`rightReembed_externalLegSaturated`), forest
= body-536 Step 5 (`multiStarForestRecovered_forestExternalLegSaturated`) fed by Step 1 (so the forest closure needs no
external `hInner`).  The saturation hypotheses `hOuter`/`hQuotient`/`hLegId` are EXPLICIT (discharged from the live block
membership only at the `W″` call site, Step 3). -/
theorem regionRawUnion_forestExternalLegSaturated (M : ResolvedMultiStarDecontractionSupply D)
    (Fstar : ResolvedCanonicalStarFacts D) (z : ForestBlockCodType D G)
    (hOuter : ResolvedForestExternalLegSaturated z.1.1)
    (hQuotient : ResolvedForestExternalLegSaturated z.2.1)
    (hLegId : G.LegIdsUnique) :
    ResolvedForestExternalLegSaturated (regionRawUnion M Fstar z) := by
  intro δ hδ
  simp only [regionRawUnion, recoveredRawUnion, ResolvedAdmissibleSubgraph.union_elements,
    Finset.mem_union] at hδ
  rcases hδ with (hl | hr) | hf
  · -- left residual (FREE)
    rw [leftRegion_elements] at hl
    exact leftResidualTouched_forestExternalLegSaturated z hOuter δ hl
  · -- right recovered (DERIVED)
    rw [rightRegion_elements] at hr
    obtain ⟨δr, -, rfl⟩ := Finset.mem_image.mp hr
    exact rightReembed_externalLegSaturated z δr (hQuotient δr.1 (Finset.mem_filter.mp δr.2).1)
  · -- forest recovered (Step 1 discharges `hInner`)
    rw [forestRegion_elements] at hf
    obtain ⟨δf, -, rfl⟩ := Finset.mem_image.mp hf
    exact localizedParent_externalLegSaturated_of_source M z δf hLegId
      (touchedLocalComponent_externalLegSaturated_of_whole Fstar z δf.1
        (hQuotient δf.1 (Finset.mem_filter.mp δf.2).1))

/-! ## Step 3 — the canonical `W″` specialization (hypotheses discharged from live membership). -/

/-- **R-6c-body-537 ∎ — the `W″` recovered-union forest saturation, hypotheses DISCHARGED.**  `hOuter`/`hQuotient` come
from the live block memberships `z.1.2`/`z.2.2` (`canonicalLegSaturatedCarrier_saturated` — `z.2.2` IS the inner forest's
`W″` carrier membership over the contracted graph), and `hLegId` from the `W′` accessor
(`legIdsUnique_of_carrier_mem`).  No socket, no target membership read. -/
theorem canonicalLegSaturated_regionRawUnion_forestExternalLegSaturated
    (M : ResolvedMultiStarDecontractionSupply canonicalLegSaturatedCarrierProperSupply.toData)
    (Fstar : ResolvedCanonicalStarFacts canonicalLegSaturatedCarrierProperSupply.toData)
    {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G) :
    ResolvedForestExternalLegSaturated (regionRawUnion M Fstar z) :=
  regionRawUnion_forestExternalLegSaturated M Fstar z
    (canonicalLegSaturatedCarrier_saturated z.1.2)
    (canonicalLegSaturatedCarrier_saturated z.2.2)
    (legIdsUnique_of_carrier_mem (canonicalLegSaturatedCarrier_mem_W' z.1.2))

/-! ## Step 4 — the recovered-union `W″` membership (body-444 mirror + Step 3 saturation). -/

/-- **R-6c-body-537 ∎ — the raw recovered-outer union lies in the `W″` carrier.**  Mirrors body-444's `recovered_raw_mem`
over `W′`, extended by the sixth (saturation) condition: support/CD/edge/leg are read off the block's own `W′` membership
`z.1.2` (via `canonicalLegSaturatedCarrier_mem_W'`), properness is the body-429/431/439 complement backbone, and the
external-leg saturation is Step 3.  The target membership is CONSTRUCTED from the six `mem_canonicalLegSaturatedCarrier_full_iff`
conjuncts, never read. -/
theorem canonicalLegSaturated_regionRawUnion_mem
    (Nne : ∀ G : ResolvedFeynmanGraph, ResolvedConnectedDivergentNonemptySupply G)
    (Ppos : ∀ G : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply G)
    (M : ResolvedMultiStarDecontractionSupply canonicalLegSaturatedCarrierProperSupply.toData)
    (Fstar : ResolvedCanonicalStarFacts canonicalLegSaturatedCarrierProperSupply.toData)
    {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G) :
    regionRawUnion M Fstar z ∈ (canonicalLegSaturatedCarrierProperSupply.index G).carrier := by
  have hW' := canonicalLegSaturatedCarrier_mem_W' z.1.2
  have hEdgeG := edgeIdsUnique_of_carrier_mem hW'
  refine (mem_canonicalLegSaturatedCarrier_full_iff _).mpr
    ⟨canonicalUniqueSupportedCarrier_ambientSupported hW',
     canonicalUniqueSupportedCarrier_ambientCD hW',
     hEdgeG, legIdsUnique_of_carrier_mem hW', ?_,
     canonicalLegSaturated_regionRawUnion_forestExternalLegSaturated M Fstar z⟩
  exact regionRawUnion_isProperForest_of_complement (Nne G) (Ppos G)
    canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider M Fstar z
    (regionRawUnion_complementEdges_card_pos_of_count_lt
      canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider M Fstar z
      (regionRawUnion_count_lt Fstar hEdgeG
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider M z))

end GaugeGeometry.QFT.Combinatorial
