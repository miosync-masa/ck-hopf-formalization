import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedCorrectedInternalSupport
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedInnerCorrectedEq
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestIdxTransportAudit
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantSupport

/-!
# R-6c-body-461 — the corrected remnant provider + alpha round-trip (PROVED)

Four-hundred-and-sixty-first genuine-body step — the forward-owned corrected remnant provider (inhabiting the body-448
`ResolvedCorrectedRemnantReembedSupply` prototype from the three supports 458/459/460), and the alpha round-trip that
replaces the strict `innerStar_agrees_raw` `hround` consumer.

* `ResolvedCorrectedRemnantReembedSupply.correctedRemnantComponent` — the generic reembed (projections `rfl`);
* `canonicalCorrectedRemnantReembedSupply` — the canonical provider over a RAW split choice `s` (body-463 retype):
  `starPerm := promotedStarCorrectingPerm Fstar s`, supports from bodies 458/460/459, endpoint support from
  `contractWithStars_{internalEdges,externalLegs}_supported` on `o.γ.1`'s subgraph invariant;
* `correctedRemnantComponent_eq_inner` — the forward component equals the recovered-side component (same quotient
  ambient, three data fields by body-457 `promotedCorrectedSource_*_eq_inner`, proof fields by proof irrelevance);
* `canonicalCorrectedRemnantComponent_roundtrip` — `HEq (correctedRemnantComponent …) δ.1` (the component equality
  composed with the body-454 inner round-trip).

Per the HALT/guards: **`VBuild` migration is NOT done here** — even though the provider is now over a RAW `s`, the existing
`VBuild.Concrete` additionally owns `remnantCD/disjoint/Inj/Gen/cross/quotient`; family disjointness (per-occurrence
correcting permutations) is NOT free from `mapPerm` invariance, so it is the V-ownership work of a later body.  Strict
`StarProm` also keeps a parent-reconstruction consumer, so the two strict sockets are NOT yet recorded as removed from the
final signature.  NO permutation equality; strict `innerStar_agrees_raw` NOT used in the round-trip; body-445 stays a valid
conditional.  NOT the unconditional theorem.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
`promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-461 — the generic corrected remnant component.**  The corrected source graph re-embedded into the
quotient graph; projections to the three data fields are `rfl`. -/
noncomputable def ResolvedCorrectedRemnantReembedSupply.correctedRemnantComponent
    {s : ResolvedCoassocSplitChoice D G} (R : ResolvedCorrectedRemnantReembedSupply D G s)
    (o : s.ForestChoiceOccurrence) : ResolvedFeynmanSubgraph s.selectedOuterContractGraph :=
  (o.contractedSourceGraph.mapPerm (R.starPerm o)).reembedAsSubgraph s.selectedOuterContractGraph
    (R.corrected_vertices o) (R.corrected_edges o) (R.corrected_legs o)
    (R.corrected_edges_supported o) (R.corrected_legs_supported o)

variable (s : ResolvedCoassocSplitChoice D G)
  (o : s.ForestChoiceOccurrence)
  (Fstar : ResolvedCanonicalStarFacts D)

/-- **R-6c-body-461 — the forward corrected source is endpoint-supported** (edges). -/
theorem promotedCorrectedSource_edges_supported :
    ∀ e ∈ (promotedCorrectedOccurrenceSourceGraph Fstar s o).internalEdges,
      e.source ∈ (promotedCorrectedOccurrenceSourceGraph Fstar s o).vertices
        ∧ e.target ∈ (promotedCorrectedOccurrenceSourceGraph Fstar s o).vertices := by
  rw [← promotedCorrectedSource_eq Fstar s o]
  exact ResolvedAdmissibleSubgraph.contractWithStars_internalEdges_supported o.B.1
    (promotedOccurrenceStar s o) o.γ.1.edges_supported

/-- **R-6c-body-461 — the forward corrected source is endpoint-supported** (legs). -/
theorem promotedCorrectedSource_legs_supported :
    ∀ ℓ ∈ (promotedCorrectedOccurrenceSourceGraph Fstar s o).externalLegs,
      ℓ.attachedTo ∈ (promotedCorrectedOccurrenceSourceGraph Fstar s o).vertices := by
  rw [← promotedCorrectedSource_eq Fstar s o]
  exact ResolvedAdmissibleSubgraph.contractWithStars_externalLegs_supported o.B.1
    (promotedOccurrenceStar s o) o.γ.1.legs_supported

/-- **R-6c-body-461 — the canonical forward corrected remnant provider** (over a RAW split choice `s`). -/
noncomputable def canonicalCorrectedRemnantReembedSupply :
    ResolvedCorrectedRemnantReembedSupply D G s where
  starPerm := fun o => promotedStarCorrectingPerm Fstar s o
  corrected_vertices := fun o => promotedCorrectedSource_vertices_subset s o Fstar
  corrected_edges := fun o => promotedCorrectedSource_internalEdges_le s o Fstar
  corrected_legs := fun o => promotedCorrectedSource_externalLegs_le s o Fstar
  corrected_edges_supported := fun o => promotedCorrectedSource_edges_supported s o Fstar
  corrected_legs_supported := fun o => promotedCorrectedSource_legs_supported s o Fstar

/-- **R-6c-body-461 — the forward corrected remnant component equals the recovered-side component.**  Filtered bridge to
the recovered side (uses the body-457 filtered projections); passes `q.1` to the raw-`s` provider. -/
theorem correctedRemnantComponent_eq_inner (q : FilteredForestBlockDom D G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1) (Fstar : ResolvedCanonicalStarFacts D)
    (M : ResolvedMultiStarDecontractionSupply D) (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
    (hparent : o.γ.1 = M.parent z δ) (hidx : HEq o.B (M.innerIdx z δ))
    (hConn : (touchedLocalComponent z δ.1).forget.IsConnected)
    (hPos : 0 < (touchedLocalComponent z δ.1).internalEdges.card)
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1 = z.1.1) :
    (canonicalCorrectedRemnantReembedSupply q.1 Fstar).correctedRemnantComponent o
      = innerCorrectedRemnantComponent Fstar M z δ o hparent hidx hConn hPos houter :=
  ResolvedFeynmanSubgraph.ext
    (promotedCorrectedSource_vertices_eq_inner M z δ q o Fstar hparent hidx houter)
    (promotedCorrectedSource_internalEdges_eq_inner M z δ q o Fstar hparent hidx houter)
    (promotedCorrectedSource_externalLegs_eq_inner M z δ q o Fstar hparent hidx houter)

/-- **R-6c-body-461 ∎ — the alpha round-trip.**  The forward corrected remnant component round-trips to `δ` — the
`innerStar_agrees_raw`-free replacement of the strict `hround` consumer. -/
theorem canonicalCorrectedRemnantComponent_roundtrip (q : FilteredForestBlockDom D G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1) (Fstar : ResolvedCanonicalStarFacts D)
    (M : ResolvedMultiStarDecontractionSupply D) (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
    (hparent : o.γ.1 = M.parent z δ) (hidx : HEq o.B (M.innerIdx z δ))
    (hConn : (touchedLocalComponent z δ.1).forget.IsConnected)
    (hPos : 0 < (touchedLocalComponent z δ.1).internalEdges.card)
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1 = z.1.1) :
    HEq ((canonicalCorrectedRemnantReembedSupply q.1 Fstar).correctedRemnantComponent o) δ.1 :=
  (heq_of_eq (correctedRemnantComponent_eq_inner q o Fstar M z δ hparent hidx hConn hPos houter)).trans
    (innerCorrectedRemnantComponent_roundtrip Fstar M z δ o hparent hidx hConn hPos houter)

/-- **R-6c-body-463 ∎ — the total corrected remnant provider family, CONSTRUCTED.**  The filtered corrected provider is
generalized to every raw split choice (totality via `promote_mem_selectedOuterRawOf_raw`, no new geometry). -/
noncomputable def canonicalCorrectedRemnantReembedFamily (Fstar : ResolvedCanonicalStarFacts D) :
    ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G),
      ResolvedCorrectedRemnantReembedSupply D G s :=
  fun s => canonicalCorrectedRemnantReembedSupply s Fstar

end GaugeGeometry.QFT.Combinatorial
