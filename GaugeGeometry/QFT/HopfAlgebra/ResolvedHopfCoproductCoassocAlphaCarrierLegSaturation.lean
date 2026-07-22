import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaValueGeometryDecompose
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaQuotEqDischarged
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTouchedLegCompletenessAudit

/-!
# R-6c-body-531 — primitive model-law audit: carrier full-boundary saturation (PROVED)

Five-hundred-and-thirty-first genuine-body step — the primitive model-law audit.  Body-530 exposed the `ValueGeometry`
residual as two laws (`touchedLegSaturated` / `parentCD`); this body DERIVES the leg law from a MORE PRIMITIVE
carrier-level property — every carrier component is external-leg full-boundary saturated — and pins `parentCD`'s honest
direction.  The aim is NOT to eliminate the laws, but to fix, AS TYPES, exactly what the CK model must guarantee.

## The primitive carrier law + its derivation

* `ResolvedCarrierExternalLegSaturationSupply` — for every carrier member `B ∈ D.carrier H` and component `δ ∈ B.elements`,
  the ambient legs attached to `δ` saturate into `δ` (multiplicity-preserving `filter ≤`).  This is the multiplicity-safe
  full-boundary law, NOT a membership-only one.
* `touchedOuter_externalLegs_map_le_componentFilter` — the CONSTRUCTION side: the touched forest's retargeted legs land in
  the `δ`-filter of the contracted ambient (touched legs `≤ G`, whole↔touched retarget agreement, each retargets to a star
  vertex in `δ.vertices`; `Multiset.le_filter`).  Per the body-330-era `TouchedLegCompletenessAudit`, the direct
  `≤ δ.externalLegs` is NOT recoverable from the construction — that gap is exactly the carrier law.
* `canonicalTouchedLegSaturationSupply` — the two composed (`le_trans`): the carrier full-boundary law INHABITS body-530's
  `ResolvedCanonicalUniqueTouchedLegSaturationSupply`, so `touchedLegSaturated` is DERIVED.

## Reduced final wrapper

* `coassoc_gen_of_canonicalMultiStar_alpha_model_laws` — native `W'` `Δᵣ`-coassociativity whose explicit roots are
  `Measure` / `E` / a `ResolvedCarrierExternalLegSaturationSupply` / a `ResolvedCanonicalUniqueDecontractionCDSupply` /
  `rep*`.  The `ValueGeometry` aggregate record is GONE; the residual is exactly the two CK-model laws.

## Verdicts (audit)

* **W' five conditions ≠ leg saturation.**  `mem_canonicalUniqueSupportedCarrier_iff` gives ambient support / CD / EdgeIds /
  LegIds / proper-forest — NONE is component external-leg full-boundary saturation.  So the leg law is NOT fabricated from
  the current `W'`; it is a genuine CK-model property supplied to `ResolvedCarrierExternalLegSaturationSupply`.
* **`parentCD` direction.**  `Measure.contract_preserves_CD : parent → contraction`; `parentCD` is the INVERSE
  (contracted component + inserted forest → de-contracted parent).  It stays an HONEST model law
  (`ResolvedCanonicalUniqueDecontractionCDSupply`, body-530), NOT derived from the forward preservation nor back-computed
  from the round-trip while a generic `z` remains.

Attainment: `touchedLegSaturated ← carrier full-boundary saturation` DERIVED; `parentCD` the divergent
insertion/decontraction law (honest).  The last residual is two axiomatic CK-model properties, not an implementation
record.

Per the HALT/guards: leg saturation is NOT back-computed from `W'` properness; no membership-only proof discards multiset
multiplicity; `parentCD` is NOT built from forward contraction preservation; no typeclass instance is globally registered;
strict `StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc claim.  No facade, no flat term, no `forgetHopf`, no
rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-! ## Step 1 — the primitive carrier full-boundary saturation law -/

/-- **R-6c-body-531 — the carrier external-leg full-boundary saturation law.**  Every carrier component absorbs the ambient
legs attached to it, with multiplicity. -/
structure ResolvedCarrierExternalLegSaturationSupply (D : ResolvedCoproductProperForestData) where
  /-- Ambient legs attached to a carrier component saturate into it (multiplicity-preserving). -/
  externalLegs_saturated_of_mem :
    ∀ {H : ResolvedFeynmanGraph} {B : ResolvedAdmissibleSubgraph H}, B ∈ D.carrier H →
      ∀ {δ : ResolvedFeynmanSubgraph H}, δ ∈ B.elements →
        H.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ δ.vertices) ≤ δ.externalLegs

/-! ## Step 2 — touched legs → ambient filter (the construction side) -/

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-body-531 ∎ — the touched forest's retargeted legs land in the `δ`-filter of the contracted ambient.** -/
theorem touchedOuter_externalLegs_map_le_componentFilter
    (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))) :
    (touchedOuterForest z δ).externalLegs.map ((touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1))
      ≤ (z.1.1.contractWithStars (D.starOf G z.1.1)).externalLegs.filter
          (fun ℓ => ℓ.attachedTo ∈ δ.vertices) := by
  rw [Multiset.le_filter]
  refine ⟨?_, ?_⟩
  · have hmapeq : (touchedOuterForest z δ).externalLegs.map
          ((touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1))
        = (touchedOuterForest z δ).externalLegs.map (z.1.1.retargetExternalLeg (D.starOf G z.1.1)) := by
      refine Multiset.map_congr rfl (fun ℓ hℓ => ?_)
      obtain ⟨A, hA, hℓA⟩ := Multiset.mem_sum.mp hℓ
      exact (whole_touched_retargetLeg_eq z δ ℓ
        (Or.inl (ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨A, hA, A.legs_supported ℓ hℓA⟩))).symm
    rw [hmapeq, ResolvedAdmissibleSubgraph.contractWithStars_externalLegs]
    exact Multiset.map_le_map
      (resolvedAdmissibleSubgraph_externalLegs_le_of_pairwise _ (touchedOuterForest z δ).isPairwiseDisjoint)
  · intro a ha
    obtain ⟨ℓ, hℓ, rfl⟩ := Multiset.mem_map.mp ha
    obtain ⟨A, hA, hℓA⟩ := Multiset.mem_sum.mp hℓ
    show ((touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1) ℓ).attachedTo ∈ δ.vertices
    unfold ResolvedAdmissibleSubgraph.retargetExternalLeg
    rw [ResolvedExternalLeg.retarget_attachedTo,
      retargetVertex_eq_star_of_mem_element (touchedOuterForest z δ) (D.starOf G z.1.1) hA
        (A.legs_supported ℓ hℓA)]
    exact touchedOuterForest_starTouch z hA

/-! ## Step 3 — the canonical saturation adapter (`touchedLegSaturated` DERIVED) -/

/-- **R-6c-body-531 ∎ — the carrier law inhabits body-530's leg-saturation supply.** -/
def canonicalTouchedLegSaturationSupply
    (LegModel : ResolvedCarrierExternalLegSaturationSupply canonicalUniqueSupportedCarrierProperSupply.toData) :
    ResolvedCanonicalUniqueTouchedLegSaturationSupply where
  saturated := fun z δ =>
    le_trans (touchedOuter_externalLegs_map_le_componentFilter z δ.1)
      (LegModel.externalLegs_saturated_of_mem z.2.2 (Finset.mem_of_mem_filter _ δ.2))

/-! ## Step 6 — the reduced final wrapper (`ValueGeometry` GONE) -/

/-- **R-6c-body-531 ∎ — native `W'` `Δᵣ`-coassociativity from the two CK-model laws.**  The `ValueGeometry` aggregate is
gone; the explicit roots are `Measure` / `E` / the carrier leg-saturation law / the decontraction-CD law / `rep*`. -/
theorem coassoc_gen_of_canonicalMultiStar_alpha_model_laws
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    (LegModel : ResolvedCarrierExternalLegSaturationSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (Parent : ResolvedCanonicalUniqueDecontractionCDSupply (canonicalTouchedLegSaturationSupply LegModel))
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x))
    (x : ResolvedHopfGen) :
    canonicalUniqueSupportedCarrierProperSupply.toData.coassocLeft (MvPolynomial.X x)
      = canonicalUniqueSupportedCarrierProperSupply.toData.coassocRight (MvPolynomial.X x) :=
  coassoc_gen_of_canonicalMultiStar_alpha_construction_discharged Measure E
    Parent.toValueGeometry rep repCD rep_gen x

end GaugeGeometry.QFT.Combinatorial
