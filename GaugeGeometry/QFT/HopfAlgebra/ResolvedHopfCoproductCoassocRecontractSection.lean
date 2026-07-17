import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerRawRetarget

/-!
# R-6c-body-353 — the explicit-star re-contract data section: internal edges + external legs (PROVED)

Three-hundred-and-fifty-third genuine-body step — the section assembly, first two data equalities.  With the
retarget trunk (body-352) the re-contract data section is a rewrite job: re-contracting `innerRaw` under the
explicit star `touchedInnerStarTotal` returns `δ`'s internal edges and external legs.

* **internalEdges** — `innerRaw.complementEdges = quotientEdgePreimage(…)` (body-351 aggregate +
  `add_tsub_cancel_left`), then `map_congr` (body-352 edge) + `quotientEdgePreimage_map`.
* **externalLegs** — `parentGraph.externalLegs = datum.legs`, then `map_congr` (body-352 leg) + `legLift.map_eq`.

Landed axiom-clean: `recontract_innerRaw_internalEdges`, `recontract_innerRaw_externalLegs`.

Per the HALT: only the edge and leg data equalities are proved; the vertex equality (independent, membership
level) and the remnant round-trip are next; `innerStar_agrees`, the hardcoded `D.starOf parent innerRaw`,
occurrence, and the remnant provider are NOT used; no forward quotient / global forward round-trip.  No facade,
no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  (z : ForestBlockCodType D G)
  (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
  (datum : ResolvedTouchedLegLiftDatum z δ)
  (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
  (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)

set_option linter.unusedSectionVars false

/-- **R-6c-body-353 — `innerRaw`'s complement edges are the quotient edge preimage.** -/
theorem innerRaw_complementEdges_eq :
    (innerRaw z δ datum hE hL).complementEdges
      = quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ) := by
  unfold ResolvedAdmissibleSubgraph.complementEdges
  rw [innerRaw_internalEdges_eq_touchedOuterForest]
  show (localizedParentWithTouchedLegs z δ datum hE hL).internalEdges - (touchedOuterForest z δ).internalEdges
    = quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ)
  show (touchedOuterForest z δ).internalEdges
      + quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ)
      - (touchedOuterForest z δ).internalEdges
    = quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ)
  rw [add_tsub_cancel_left]

/-- **R-6c-body-353 — the re-contract's internal edges are `δ`'s.** -/
theorem recontract_innerRaw_internalEdges :
    ((innerRaw z δ datum hE hL).contractWithStars (touchedInnerStarTotal z δ datum hE hL)).internalEdges
      = δ.internalEdges := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_internalEdges, innerRaw_complementEdges_eq,
    Multiset.map_congr rfl (fun e _ => innerRaw_retargetEdge_eq_touched z δ datum hE hL e),
    quotientEdgePreimage_map, touchedLocalComponent_internalEdges]

/-- **R-6c-body-353 — the re-contract's external legs are `δ`'s.** -/
theorem recontract_innerRaw_externalLegs :
    ((innerRaw z δ datum hE hL).contractWithStars (touchedInnerStarTotal z δ datum hE hL)).externalLegs
      = δ.externalLegs := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_externalLegs]
  show (localizedParentWithTouchedLegs z δ datum hE hL).externalLegs.map
      ((innerRaw z δ datum hE hL).retargetExternalLeg (touchedInnerStarTotal z δ datum hE hL))
    = δ.externalLegs
  show datum.legs.map
      ((innerRaw z δ datum hE hL).retargetExternalLeg (touchedInnerStarTotal z δ datum hE hL))
    = δ.externalLegs
  rw [Multiset.map_congr rfl (fun ℓ _ => innerRaw_retargetExternalLeg_eq_touched z δ datum hE hL ℓ),
    datum.map_eq, touchedLocalComponent_externalLegs]

end GaugeGeometry.QFT.Combinatorial
