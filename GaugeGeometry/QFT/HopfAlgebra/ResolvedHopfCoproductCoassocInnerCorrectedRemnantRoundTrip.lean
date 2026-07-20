import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerCorrectedOccurrenceTransport
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteRemnant

/-!
# R-6c-body-454 — the inner-corrected remnant component round-trip (closes the inner side) (PROVED)

Four-hundred-and-fifty-fourth genuine-body step — the reembed + `HEq` assembly that closes the inner side.  The
occurrence's contracted source graph, relabeled by the inner correcting permutation `ρ` (body-450), is re-embedded into
the quotient graph `selectedOuterContractGraph` and shown to `HEq`-round-trip to `δ` — WITHOUT strict
`innerStar_agrees_raw`.

* `innerCorrectedOccurrenceSourceGraph o` — `o.contractedSourceGraph.mapPerm ρ` (the corrected data owner, no proofs);
* `innerCorrectedSource_vertices_subset` / `_internalEdges_le` / `_externalLegs_le` — the three quotient containments,
  via body-453 (`corrected data = δ data`) + `δ`'s own subset fields + `houter`'s ambient equality;
* `innerCorrectedSource_edges_supported` / `_legs_supported` — endpoint well-formedness, transported from `δ.1`'s;
* `innerCorrectedRemnantComponent` — the reembed (projections `rfl`);
* `innerCorrectedRemnantComponent_roundtrip` — `HEq (innerCorrectedRemnantComponent …) δ.1` via body-346
  `subgraph_heq_of_data` (ambient equality `congrArg contractWithStars houter`, data by the body-453 helpers).

This body's exact deliverable: **the recovered-side corrected remnant component round-trips to `δ` without
`innerStar_agrees_raw`.**  It is still the RECOVERED-side comparator (`ρ = innerStarCorrectingPerm z δ`), NOT the forward
provider's component, so this is NOT the full corrected `hround` — the forward `promotedStarCorrectingPerm q o` and the
two-corrected-components graph equality are the next bodies.

Per the HALT/guards: no carrier membership, no `ForestIdx` `mapPerm` transport, no promoted correction, no permutation
equality; strict `InnerStarRaw` / `innerStar_agrees_raw` NOT used; `Concrete` / `VBuild` NOT wired; `hConn` / `hPos` are
the existing quotient-CD / quotient-properness obligations; body-445 stays a valid conditional.  NOT the unconditional
theorem.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  (Fstar : ResolvedCanonicalStarFacts D) (M : ResolvedMultiStarDecontractionSupply D)
  (z : ForestBlockCodType D G)
  (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
  {s : ResolvedCoassocSplitChoice D G}

/-- The quotient-graph ambient equality induced by `houter`. -/
private theorem selectedOuter_eq_z (o : s.ForestChoiceOccurrence)
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s = z.1.1) :
    s.selectedOuterContractGraph = z.1.1.contractWithStars (D.starOf G z.1.1) :=
  congrArg (fun A => A.contractWithStars (D.starOf G A)) houter

include Fstar

/-- **R-6c-body-454 — the corrected occurrence source graph.**  The occurrence's contracted source graph relabeled by the
inner correcting permutation; the data owner for the corrected remnant. -/
noncomputable def innerCorrectedOccurrenceSourceGraph (o : s.ForestChoiceOccurrence) :
    ResolvedFeynmanGraph :=
  o.contractedSourceGraph.mapPerm (innerStarCorrectingPerm Fstar M z δ)

/-- **R-6c-body-454 — the corrected source graph's vertices are `δ`'s** (under alignment + connectivity/positivity). -/
theorem innerCorrectedOccurrenceSource_vertices (o : s.ForestChoiceOccurrence)
    (hparent : o.γ.1 = M.parent z δ) (hidx : HEq o.B (M.innerIdx z δ))
    (hConn : (touchedLocalComponent z δ.1).forget.IsConnected)
    (hPos : 0 < (touchedLocalComponent z δ.1).internalEdges.card) :
    (innerCorrectedOccurrenceSourceGraph Fstar M z δ o).vertices = δ.1.vertices :=
  innerCorrectedSource_vertices_helper Fstar M z δ o.B
    (congrArg ResolvedFeynmanSubgraph.toResolvedFeynmanGraph hparent) hidx hConn hPos

/-- **R-6c-body-454 — the corrected source graph's internal edges are `δ`'s** (unconditional). -/
theorem innerCorrectedOccurrenceSource_internalEdges (o : s.ForestChoiceOccurrence)
    (hparent : o.γ.1 = M.parent z δ) (hidx : HEq o.B (M.innerIdx z δ)) :
    (innerCorrectedOccurrenceSourceGraph Fstar M z δ o).internalEdges = δ.1.internalEdges :=
  innerCorrectedSource_internalEdges_helper Fstar M z δ o.B
    (congrArg ResolvedFeynmanSubgraph.toResolvedFeynmanGraph hparent) hidx

/-- **R-6c-body-454 — the corrected source graph's external legs are `δ`'s** (unconditional). -/
theorem innerCorrectedOccurrenceSource_externalLegs (o : s.ForestChoiceOccurrence)
    (hparent : o.γ.1 = M.parent z δ) (hidx : HEq o.B (M.innerIdx z δ)) :
    (innerCorrectedOccurrenceSourceGraph Fstar M z δ o).externalLegs = δ.1.externalLegs :=
  innerCorrectedSource_externalLegs_helper Fstar M z δ o.B
    (congrArg ResolvedFeynmanSubgraph.toResolvedFeynmanGraph hparent) hidx

/-- **R-6c-body-454 — the corrected source graph's vertices sit in the quotient graph.** -/
theorem innerCorrectedSource_vertices_subset (o : s.ForestChoiceOccurrence)
    (hparent : o.γ.1 = M.parent z δ) (hidx : HEq o.B (M.innerIdx z δ))
    (hConn : (touchedLocalComponent z δ.1).forget.IsConnected)
    (hPos : 0 < (touchedLocalComponent z δ.1).internalEdges.card)
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s = z.1.1) :
    (innerCorrectedOccurrenceSourceGraph Fstar M z δ o).vertices
      ⊆ s.selectedOuterContractGraph.vertices := by
  rw [innerCorrectedOccurrenceSource_vertices Fstar M z δ o hparent hidx hConn hPos,
    selectedOuter_eq_z z o houter]
  exact δ.1.vertices_subset

/-- **R-6c-body-454 — the corrected source graph's internal edges sit in the quotient graph.** -/
theorem innerCorrectedSource_internalEdges_le (o : s.ForestChoiceOccurrence)
    (hparent : o.γ.1 = M.parent z δ) (hidx : HEq o.B (M.innerIdx z δ))
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s = z.1.1) :
    (innerCorrectedOccurrenceSourceGraph Fstar M z δ o).internalEdges
      ≤ s.selectedOuterContractGraph.internalEdges := by
  rw [innerCorrectedOccurrenceSource_internalEdges Fstar M z δ o hparent hidx,
    selectedOuter_eq_z z o houter]
  exact δ.1.internalEdges_le

/-- **R-6c-body-454 — the corrected source graph's external legs sit in the quotient graph.** -/
theorem innerCorrectedSource_externalLegs_le (o : s.ForestChoiceOccurrence)
    (hparent : o.γ.1 = M.parent z δ) (hidx : HEq o.B (M.innerIdx z δ))
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s = z.1.1) :
    (innerCorrectedOccurrenceSourceGraph Fstar M z δ o).externalLegs
      ≤ s.selectedOuterContractGraph.externalLegs := by
  rw [innerCorrectedOccurrenceSource_externalLegs Fstar M z δ o hparent hidx,
    selectedOuter_eq_z z o houter]
  exact δ.1.externalLegs_le

/-- **R-6c-body-454 — the corrected source graph is endpoint-supported** (transported from `δ.1`). -/
theorem innerCorrectedSource_edges_supported (o : s.ForestChoiceOccurrence)
    (hparent : o.γ.1 = M.parent z δ) (hidx : HEq o.B (M.innerIdx z δ))
    (hConn : (touchedLocalComponent z δ.1).forget.IsConnected)
    (hPos : 0 < (touchedLocalComponent z δ.1).internalEdges.card) :
    ∀ e ∈ (innerCorrectedOccurrenceSourceGraph Fstar M z δ o).internalEdges,
      e.source ∈ (innerCorrectedOccurrenceSourceGraph Fstar M z δ o).vertices
        ∧ e.target ∈ (innerCorrectedOccurrenceSourceGraph Fstar M z δ o).vertices := by
  intro e he
  rw [innerCorrectedOccurrenceSource_internalEdges Fstar M z δ o hparent hidx] at he
  rw [innerCorrectedOccurrenceSource_vertices Fstar M z δ o hparent hidx hConn hPos]
  exact δ.1.edges_supported e he

/-- **R-6c-body-454 — the corrected source graph's legs are endpoint-supported** (transported from `δ.1`). -/
theorem innerCorrectedSource_legs_supported (o : s.ForestChoiceOccurrence)
    (hparent : o.γ.1 = M.parent z δ) (hidx : HEq o.B (M.innerIdx z δ))
    (hConn : (touchedLocalComponent z δ.1).forget.IsConnected)
    (hPos : 0 < (touchedLocalComponent z δ.1).internalEdges.card) :
    ∀ ℓ ∈ (innerCorrectedOccurrenceSourceGraph Fstar M z δ o).externalLegs,
      ℓ.attachedTo ∈ (innerCorrectedOccurrenceSourceGraph Fstar M z δ o).vertices := by
  intro ℓ hℓ
  rw [innerCorrectedOccurrenceSource_externalLegs Fstar M z δ o hparent hidx] at hℓ
  rw [innerCorrectedOccurrenceSource_vertices Fstar M z δ o hparent hidx hConn hPos]
  exact δ.1.legs_supported ℓ hℓ

/-- **R-6c-body-454 — the local corrected remnant component.**  The corrected source graph re-embedded into the quotient
graph; projections to the three data fields are `rfl`. -/
noncomputable def innerCorrectedRemnantComponent (o : s.ForestChoiceOccurrence)
    (hparent : o.γ.1 = M.parent z δ) (hidx : HEq o.B (M.innerIdx z δ))
    (hConn : (touchedLocalComponent z δ.1).forget.IsConnected)
    (hPos : 0 < (touchedLocalComponent z δ.1).internalEdges.card)
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s = z.1.1) :
    ResolvedFeynmanSubgraph s.selectedOuterContractGraph :=
  (innerCorrectedOccurrenceSourceGraph Fstar M z δ o).reembedAsSubgraph s.selectedOuterContractGraph
    (innerCorrectedSource_vertices_subset Fstar M z δ o hparent hidx hConn hPos houter)
    (innerCorrectedSource_internalEdges_le Fstar M z δ o hparent hidx houter)
    (innerCorrectedSource_externalLegs_le Fstar M z δ o hparent hidx houter)
    (innerCorrectedSource_edges_supported Fstar M z δ o hparent hidx hConn hPos)
    (innerCorrectedSource_legs_supported Fstar M z δ o hparent hidx hConn hPos)

/-- **R-6c-body-454 ∎ — the recovered-side corrected remnant component round-trips to `δ`.**  Without strict
`innerStar_agrees_raw`: `subgraph_heq_of_data` with the `houter` ambient equality and the body-453 data transports. -/
theorem innerCorrectedRemnantComponent_roundtrip (o : s.ForestChoiceOccurrence)
    (hparent : o.γ.1 = M.parent z δ) (hidx : HEq o.B (M.innerIdx z δ))
    (hConn : (touchedLocalComponent z δ.1).forget.IsConnected)
    (hPos : 0 < (touchedLocalComponent z δ.1).internalEdges.card)
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s = z.1.1) :
    HEq (innerCorrectedRemnantComponent Fstar M z δ o hparent hidx hConn hPos houter) δ.1 :=
  subgraph_heq_of_data (selectedOuter_eq_z z o houter)
    (innerCorrectedRemnantComponent Fstar M z δ o hparent hidx hConn hPos houter) δ.1
    (innerCorrectedOccurrenceSource_vertices Fstar M z δ o hparent hidx hConn hPos)
    (innerCorrectedOccurrenceSource_internalEdges Fstar M z δ o hparent hidx)
    (innerCorrectedOccurrenceSource_externalLegs Fstar M z δ o hparent hidx)

end GaugeGeometry.QFT.Combinatorial
