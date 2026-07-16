import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTouchedLocalizationEdge

/-!
# R-6c-body-320 — M1 external-leg localization: whole↔touched retarget-leg-eq + `externalLegs_le` (PROVED)

Three-hundred-and-twentieth genuine-body step — M1 (Front 1): the EXTERNAL-LEG obligation of localizing a quotient
component `δ` into `(touchedOuterForest z δ).contractWithStars f`, the last of the three support inclusions.  It reuses
the shared vertex core (body-319 `whole_touched_retargetVertex_eq` / `touched_vertex_ok`); legs are SIMPLER than edges —
they map over the whole `G.externalLegs`, so `quotientLegPreimage_le` lands directly in `G.externalLegs` with NO
`complementEdges` subtraction.

## Banked here

* `whole_touched_retargetLeg_eq` — the retarget-leg version of the vertex agreement (on `attachedTo`).
* `touched_leg_att_ok` — attachment of a `quotientLegPreimage` leg is touched-or-outside.
* `touchedContractedExternalLegs_le` — `δ.externalLegs ≤ ((touchedOuterForest z δ).contractWithStars f).externalLegs`
  — the M1 external-leg field: `contractWithStars_externalLegs` + `← quotientLegPreimage_map` + `Multiset.map_congr`
  (retarget-leg-eq) + `Multiset.map_le_map (quotientLegPreimage_le)`.  No complement subtraction — the inclusion is
  directly `quotientLegPreimage ≤ G.externalLegs`.

## M1 is now complete — body-321 is pure assembly

With the three support inclusions proved (vertices body-318, internalEdges body-319, externalLegs body-320) and the data
`vertices := δ.vertices, internalEdges := δ.internalEdges, externalLegs := δ.externalLegs` (so `edges_supported` /
`legs_supported` are δ's, free), `TouchedLocalizationData.localComponent : ResolvedFeynmanSubgraph
((touchedOuterForest z δ).contractWithStars f)` is a pure record assembly (body-321).  The remaining Front-1 obligations
are then exactly M2 (the localized-parent CD certificate) and M3 (the collection-level `promote`/`contractWithStars`
inverse, i.e. `(promote parent innerRaw).elements = touchedOuterComponents z δ`).

Per the HALT: only the leg core + external-leg inclusion are proved; the `localComponent` assembly (body-321), CD, carrier,
and D2 are NOT entered; no `complementEdges` argument for legs; only the needed `Multiset` inclusion (not a full
external-leg equality); the divergence typeclasses stay ambient assumptions, not new geometry fields; no facade, no flat
term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-320 — whole↔touched retarget-leg agreement.** -/
theorem whole_touched_retargetLeg_eq {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (ℓ : ResolvedExternalLeg)
    (hatt : ℓ.attachedTo ∈ (touchedOuterForest z δ).vertices ∨ ℓ.attachedTo ∉ z.1.1.vertices) :
    z.1.1.retargetExternalLeg (D.starOf G z.1.1) ℓ
      = (touchedOuterForest z δ).retargetExternalLeg (D.starOf G z.1.1) ℓ := by
  have h1 := whole_touched_retargetVertex_eq z δ hatt
  unfold ResolvedAdmissibleSubgraph.retargetExternalLeg ResolvedExternalLeg.retarget
  rw [h1]

/-- **R-6c-body-320 — attachment of a `δ`-preimage leg is touched-or-outside.** -/
theorem touched_leg_att_ok {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    {ℓ : ResolvedExternalLeg} (hℓ : ℓ ∈ quotientLegPreimage z.1.1 (D.starOf G z.1.1) δ) :
    ℓ.attachedTo ∈ (touchedOuterForest z δ).vertices ∨ ℓ.attachedTo ∉ z.1.1.vertices := by
  apply touched_vertex_ok z δ
  have hmem : z.1.1.retargetExternalLeg (D.starOf G z.1.1) ℓ ∈ δ.externalLegs := by
    rw [← quotientLegPreimage_map z.1.1 (D.starOf G z.1.1) δ]; exact Multiset.mem_map_of_mem _ hℓ
  simpa [ResolvedAdmissibleSubgraph.retargetExternalLeg] using δ.legs_supported _ hmem

/-- **R-6c-body-320 — the M1 external-leg field.** -/
theorem touchedContractedExternalLegs_le {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))) :
    δ.externalLegs
      ≤ ((touchedOuterForest z δ).contractWithStars (D.starOf G z.1.1)).externalLegs := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_externalLegs,
    ← quotientLegPreimage_map z.1.1 (D.starOf G z.1.1) δ,
    Multiset.map_congr rfl (fun ℓ hℓ =>
      whole_touched_retargetLeg_eq z δ ℓ (touched_leg_att_ok z δ hℓ))]
  exact Multiset.map_le_map (quotientLegPreimage_le z.1.1 (D.starOf G z.1.1) δ)

end GaugeGeometry.QFT.Combinatorial
