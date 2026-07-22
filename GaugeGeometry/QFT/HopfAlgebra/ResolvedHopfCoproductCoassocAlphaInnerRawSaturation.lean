import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRecoveredSaturationComplete
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocToInner
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerRawM3
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerRawProper
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerRawCarrierClosure
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocUniqueClosureMigration
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTouchedOuterComponents

/-!
# R-6c-body-538 — the `W″` `innerRaw` external-leg-saturation carrier closure (PROVED)

Five-hundred-and-thirty-eighth genuine-body step — migrating the `innerRaw` carrier closure (body-443's
`canonicalUniqueInnerRawCarrierClosureSupply`) from `W′` to `W″`.  Under `W″` the parent's carrier membership acquires a
sixth conjunct — `ResolvedForestExternalLegSaturated (Core.innerRaw z δ)` — on the DE-CONTRACTED PARENT's own ambient
graph `(Core.parent z δ).toResolvedFeynmanGraph`, a DIFFERENT owner from the recovered union's `G` (body-537's
scoreboard flagged exactly this owner as `AUDIT OPEN`).  This body discharges it.

## The `innerRaw` closure is the SHALLOWEST of the three `W″` migrations

The saturation proof is *pure filter monotonicity*, shallower even than body-536's boundary-ID cancellation:

* the de-contracted parent's boundary multiset is `(localizedParentWithTouchedLegs …).externalLegs = datum.legs`, and
  `datum.legs ≤ G.externalLegs` (`datum.legs_le`) — the parent ambient's boundary multiset SHRINKS to the leg preimage;
* each inner component `toInner z δ datum hE hL A` re-types a touched outer component `A`, keeping its vertices/legs
  (`= A.1`'s, `rfl`), so its `δ`-attach filter is against `A.1.vertices` with RHS `A.1.externalLegs`;
* so the parent-boundary `A.1.vertex`-attach filter is a SUBFILTER of the `G`-boundary `A.1.vertex`-attach filter
  (`Multiset.filter_le_filter datum.legs_le`), and the latter is `≤ A.1.externalLegs` by the SOURCE outer saturation
  `hOuter A.1` — **source outer saturation descends contravariantly through the shrinking boundary**.

No ID cancellation, no `LegModel` supply, no `parentCD` in the saturation derivation (bodies 536/537 each needed a
retarget-agreement filter equality; here it is a bare `≤`).

* **Step 1** `multiset_filter_le_filter_of_le` — the generic filter-monotonicity wrapper (`Multiset.filter_le_filter`).
* **Step 2** `toInner_externalLegSaturated_of_outer` — the per-component descent (`le_trans` of Step 1 through
  `hOuter A.1`, the SOURCE outer saturation on the touched component `A.1 ∈ z.1.1.elements`).
* **Step 3** `innerRaw_forestExternalLegSaturated` — `∀` over the inner forest's `toInner`-image components.
* **Step 4** `canonicalLegSaturatedInnerRawCarrierClosureSupply` — the `W″` `innerRaw_mem` closure: body-443's five
  `W′`/geometry conjuncts on `(Core.parent z δ).toResolvedFeynmanGraph` (support/CD/edge/leg from `z.1.2`'s `W′`
  accessors, properness from body-378) plus the Step-3 saturation as the sixth, discharged from the outer block's own
  `W″` membership `z.1.2` (`canonicalLegSaturatedCarrier_saturated`).

## Running scoreboard (`W″` migration)

```text
selectedOuter        PASSED W″  (body-534)
recoveredRawUnion    PASSED W″  (body-537)
innerRaw             PASSED W″  (body-538, this file)  ← SHALLOWEST: pure filter monotonicity (datum.legs_le)
corrected-quotient   AUDIT OPEN  ← bodies 520–529 two-stage survivor, the LAST combinatorial fourth-axis checkpoint
```

## Optional `W″` bundle — recorded as a recipe, NOT forced (Step 5 STOPPED)

A `ResolvedMultiStarCarrierClosureBundleSupply Core canonicalLegSaturatedStarFacts` would mirror body-443's
`canonicalUniqueMultiStarCarrierClosureBundleSupply` with `Closure := canonicalLegSaturatedInnerRawCarrierClosureSupply
Core` and `recovered_raw_mem := <canonicalLegSaturated_regionRawUnion_mem (body-537), instantiated with
M := Core.toDecontractionSupply Closure and Fstar := canonicalLegSaturatedStarFacts>`.  It is NOT built here: per the
guards, the `M`/`Fstar` owner alignment between body-537's generic `regionRawUnion M Fstar z` and the bundle field's
fixed `M := Core.toDecontractionSupply Closure` / `Fstar := canonicalLegSaturatedStarFacts` is type friction that must not
be forced.  The bundle is a follow-up body; this file lands the `innerRaw` closure alone.

Per the HALT/guards: no datum field / socket is added; the `W″` `LegModel` supply is NOT used; the target `innerRaw`
membership is CONSTRUCTED from the six `mem_canonicalLegSaturatedCarrier_full_iff` conjuncts (never read); `parentCD` is
used ONLY for the CD conjunct of the carrier membership, NEVER in the saturation derivation; `hOuter` is an explicit
hypothesis in Steps 2/3, discharged from `z.1.2`'s `W″` membership only at Step 4; no `houter` / forward reconstruction /
round-trip; no ID cancellation; the corrected quotient is NOT entered; the coassoc theorem is NOT re-issued; strict
`StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc claim.  No facade, no flat term, no `forgetHopf`, no
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

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-! ## Step 1 — generic filter monotonicity. -/

/-- **R-6c-body-538 — filter monotonicity.**  A submultiset's `p`-filter is a submultiset of the ambient's `p`-filter
(a thin wrapper over `Multiset.filter_le_filter`). -/
theorem multiset_filter_le_filter_of_le {α : Type*} [DecidableEq α] {p : α → Prop} [DecidablePred p]
    {M N : Multiset α} (h : M ≤ N) : M.filter p ≤ N.filter p :=
  Multiset.filter_le_filter p h

/-! ## Step 2 — component saturation (source outer saturation descends contravariantly). -/

/-- **R-6c-body-538 ∎ — an inner component is externally-leg-saturated from the SOURCE outer saturation.**  The parent
boundary is `datum.legs` and `datum.legs ≤ G.externalLegs`, and `toInner … A` keeps `A.1`'s vertices/legs, so the
parent-boundary `A.1.vertex`-attach filter is a subfilter of the `G`-boundary filter, itself `≤ A.1.externalLegs` by
`hOuter A.1` (the touched component `A.1 ∈ z.1.1.elements`).  Pure `le_trans` — no ID cancellation, no `parentCD`. -/
theorem toInner_externalLegSaturated_of_outer (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    (hOuter : ResolvedForestExternalLegSaturated z.1.1)
    (A : {x : ResolvedFeynmanSubgraph G // x ∈ touchedOuterComponents z δ}) :
    ResolvedExternalLegSaturated (localizedParentWithTouchedLegs z δ datum hE hL).toResolvedFeynmanGraph
      (toInner z δ datum hE hL A) := by
  show datum.legs.filter (fun ℓ => ℓ.attachedTo ∈ A.1.vertices) ≤ A.1.externalLegs
  exact le_trans (multiset_filter_le_filter_of_le datum.legs_le)
    (hOuter A.1 (mem_touchedOuterComponents.mp A.2).1)

/-! ## Step 3 — forest saturation over the inner forest's components. -/

/-- **R-6c-body-538 ∎ — the inner raw forest is external-leg-saturated from the SOURCE outer saturation.**  Every
component is a `toInner`-retype of a touched outer component (`innerRaw_elements`), handled by Step 2. -/
theorem innerRaw_forestExternalLegSaturated (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    (hOuter : ResolvedForestExternalLegSaturated z.1.1) :
    ResolvedForestExternalLegSaturated (innerRaw z δ datum hE hL) := by
  intro B hB
  rw [innerRaw_elements] at hB
  obtain ⟨A, -, rfl⟩ := Finset.mem_image.mp hB
  exact toInner_externalLegSaturated_of_outer z δ datum hE hL hOuter A

/-! ## Step 4 — the `W″` `innerRaw` carrier closure (body-443 mirror + saturation conjunct). -/

/-- **R-6c-body-538 ∎ — `innerRaw_mem` over `W″`.**  Body-443's five `W′`/geometry conjuncts on the parent's ambient
graph (support/CD/edge/leg from `z.1.2`'s `W′` accessors, properness from body-378) plus the sixth external-leg
saturation, discharged from the outer block's own `W″` membership `z.1.2`
(`canonicalLegSaturatedCarrier_saturated`).  The target membership is CONSTRUCTED from the six
`mem_canonicalLegSaturatedCarrier_full_iff` conjuncts, never read. -/
noncomputable def canonicalLegSaturatedInnerRawCarrierClosureSupply
    (Core : ResolvedMultiStarDecontractionValueCoreSupply
      canonicalLegSaturatedCarrierProperSupply.toData) :
    ResolvedMultiStarInnerRawCarrierClosureSupply Core where
  innerRaw_mem := fun z δ => by
    have hEdgeG := edgeIdsUnique_of_carrier_mem (canonicalLegSaturatedCarrier_mem_W' z.1.2)
    have hLegG := legIdsUnique_of_carrier_mem (canonicalLegSaturatedCarrier_mem_W' z.1.2)
    refine (mem_canonicalLegSaturatedCarrier_full_iff _).mpr
      ⟨resolvedAmbientSupported_of_subgraphGraph (Core.parent z δ), ?_,
       edgeIdsUnique_of_subgraphGraph hEdgeG (Core.parent z δ),
       legIdsUnique_of_subgraphGraph hLegG (Core.parent z δ), ?_, ?_⟩
    · rw [← ResolvedFeynmanSubgraph.forget_toFeynmanGraph (Core.parent z δ)]
      exact (Core.parent z δ).forget.toFeynmanGraph_isConnectedDivergent (Core.parentCD z δ)
    · exact innerRaw_isProperForest
        canonicalLegSaturatedCarrierProperSupply.toCarrierProperProvider Core z δ
    · exact innerRaw_forestExternalLegSaturated z δ.1 (Core.legLift z δ) (Core.hE z) (Core.hL z)
        (canonicalLegSaturatedCarrier_saturated z.1.2)

end GaugeGeometry.QFT.Combinatorial
