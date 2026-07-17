import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantRoundTrip
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestOccurrenceInversion
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLocalizedParentCD

/-!
# R-6c-body-367 — Front-3 bank-2: the multi-star remnant round-trip gate (PROVED)

Three-hundred-and-sixty-seventh genuine-body step — the first derived-geometry socket.  Body-358's
`remnantComponent_roundtrip` needs `hparent + hidx + innerStar_agrees + houter + hConn + hPos`.  This body banks the
multi-star specialization: `innerStar_agrees` is `StarCoh`, `hConn` is DERIVED from `δ ∈ forestDomain` (body-322's
`touchedLocalComponent_isConnectedDivergent` on the forest's own connected-divergence), and `houter` is the caller's
body-341 identity — leaving exactly `hparent` / `hidx` (+ the `hPos` edge-positivity leaf) at the interface.

Crucially `hround` (this) does NOT consume `OccInv`: occurrence inversion enters only in the composed
`_of_occurrence` form (body-359's `hidx` source), so the two never double-count.

* `multiStar_remnant_roundtrip` — body-358 with `StarCoh` wired and `hConn` derived;
* `multiStar_remnant_roundtrip_of_occurrence` — the same, with `hidx` produced from `OccInv` (body-343).

Per the HALT: this is a DERIVED adapter of body-358, NOT a new `hround` model field; `T` still carries the six bridges,
so the `T` construction is not yet unconditionalised; the six sound/complete bridges, `hSurvivor`, carrier membership,
and the survivor sector are UNTOUCHED.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
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

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

namespace ResolvedMultiStarDecontractionSupply

variable (M : ResolvedMultiStarDecontractionSupply D) {G : ResolvedFeynmanGraph}

/-- **R-6c-body-367 — the multi-star remnant round-trip gate.**  Body-358 with the inner-star coherence supply wired
and the touched-component connectivity derived from `δ ∈ forestDomain`. -/
theorem multiStar_remnant_roundtrip (Fstar : ResolvedCanonicalStarFacts D)
    (StarCoh : ResolvedInnerStarCoherenceSupply M) (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
    {s : ResolvedCoassocSplitChoice D G} (Remnant : ResolvedConcreteRemnantReembedSupply D G s)
    (o : s.ForestChoiceOccurrence)
    (hparent : o.γ.1 = M.parent z δ) (hidx : HEq o.B (M.innerIdx z δ))
    (hPos : 0 < (touchedLocalComponent z δ.1).internalEdges.card)
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s = z.1.1) :
    HEq (Remnant.remnantComponent o) δ.1 :=
  M.remnantComponent_roundtrip Fstar StarCoh z δ Remnant o hparent hidx
    (touchedLocalComponent_isConnectedDivergent z δ.1
      (z.2.1.isConnectedDivergent δ.1 (Finset.mem_filter.mp δ.2).1)).1
    hPos houter

/-- **R-6c-body-367 — composed form**: `hidx` produced from occurrence inversion (body-343). -/
theorem multiStar_remnant_roundtrip_of_occurrence (Fstar : ResolvedCanonicalStarFacts D)
    (StarCoh : ResolvedInnerStarCoherenceSupply M) (OccInv : ResolvedForestOccurrenceInversionSupply M)
    (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
    {s : ResolvedCoassocSplitChoice D G} (Remnant : ResolvedConcreteRemnantReembedSupply D G s)
    (o : s.ForestChoiceOccurrence)
    (hparent : o.γ.1 = M.parent z δ)
    (hPos : 0 < (touchedLocalComponent z δ.1).internalEdges.card)
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s = z.1.1) :
    HEq (Remnant.remnantComponent o) δ.1 :=
  M.multiStar_remnant_roundtrip Fstar StarCoh z δ Remnant o hparent
    (M.innerIdx_occurrence OccInv z δ s o hparent.symm).symm hPos houter

end ResolvedMultiStarDecontractionSupply

end GaugeGeometry.QFT.Combinatorial
