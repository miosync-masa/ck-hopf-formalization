import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCorrectedRemnantProvider
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedInnerCorrectedEq

/-!
# R-6c-body-489 — the raw (membership-free) corrected remnant round-trip (cycle repair) (PROVED)

Four-hundred-and-eighty-ninth genuine-body step — the CYCLE REPAIR.  The roadmap's "filtered `hquotient` first" is
impossible as stated: `V.quotientForestRaw qz` needs `qz : FilteredForestBlockDom`, whose membership needs `mixed_ne_pL`,
which classically consumed the forward quotient identity.  Body-469's escape is that `canonicalCorrectedQuotientRaw s` is
defined over a RAW `s` with NO membership.  This body supplies the other half: the corrected remnant round-trip
generalized to a raw split choice `s`, so the forward quotient identity can be assembled BEFORE the filtered witness
exists.

The body-461 round-trip and its body-457 support chain read only `q.1` (never the membership `q.2`), so they generalize
verbatim from a filtered `q` to a raw `s : ResolvedCoassocSplitChoice D G` (the body-463 raw-domain migration pattern), on
the total corrected provider `canonicalCorrectedRemnantReembedSupply s Fstar` (body-461/463) + the raw promote membership
(body-462).  No fabricated membership is introduced; `houter` is a HYPOTHESIS (proved for the recovered `s` in a later
body from the alpha tags, membership-free).

* `occurrenceContract_transport_raw` / `promotedCorrectedSource_eq_innerCorrectedSource_raw` +
  `promotedCorrectedSource_{vertices,internalEdges,externalLegs}_eq_inner_raw` — the body-457 central cross-ambient
  equality over a raw `s`;
* `correctedRemnantComponent_eq_inner_raw` — the body-461 forward↔recovered component equality over a raw `s`;
* `canonicalCorrectedRemnantComponent_roundtrip_raw` — the body-461 round-trip `HEq (correctedRemnantComponent …) δ.1`,
  MEMBERSHIP-FREE, the `innerStar_agrees_raw`-free `hround` on a raw `s`.

Per the HALT/guards: `ResolvedRecoveredPreimageAlphaValueMemSupply` is NOT built; no `qz` filtered subtype is issued; no
upgrade to `V.quotientForestRaw qz`; NO fabricated membership / Classical choice; the filtered body-461 is NOT reused for
`s` (this is its raw generalization); strict `StarProm` / `InnerStarRaw` NOT restored; body-445 stays a valid conditional.
NOT the unconditional theorem.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` /
singleton / floor-297.
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
  (M : ResolvedMultiStarDecontractionSupply D) (z : ForestBlockCodType D G)
  (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
  (s : ResolvedCoassocSplitChoice D G)

/-- **R-6c-body-489 — the occurrence's promoted-star contraction transported to the touched-star contraction, over a raw
`s`** (body-457 mirror; the `q.2` membership is never read). -/
theorem occurrenceContract_transport_raw (γ' : ResolvedFeynmanSubgraph G)
    (B' : (D.supply γ'.toResolvedFeynmanGraph).ForestIdx)
    (hγ : γ' = M.parent z δ) (hB : HEq B' (M.innerIdx z δ))
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s = z.1.1) :
    B'.1.contractWithStars (fun b => D.starOf G
        ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s) (γ'.promote b))
      = (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)).contractWithStars
          (touchedInnerStarTotal z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)) := by
  subst hγ
  obtain rfl := eq_of_heq hB
  simp only [houter]
  exact innerRaw_contract_intrinsic_eq_touched M z δ

variable (o : s.ForestChoiceOccurrence) (Fstar : ResolvedCanonicalStarFacts D)

/-- **R-6c-body-489 — the central cross-ambient equality over a raw `s`** (body-457 mirror). -/
theorem promotedCorrectedSource_eq_innerCorrectedSource_raw
    (hparent : o.γ.1 = M.parent z δ) (hidx : HEq o.B (M.innerIdx z δ))
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s = z.1.1) :
    promotedCorrectedOccurrenceSourceGraph Fstar s o
      = innerCorrectedOccurrenceSourceGraph Fstar M z δ o := by
  have h1 : o.B.1.contractWithStars (promotedOccurrenceStar s o)
      = (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)).contractWithStars
          (touchedInnerStarTotal z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)) :=
    occurrenceContract_transport_raw M z δ s o.γ.1 o.B hparent hidx houter
  have h2 : o.contractedSourceGraph
      = (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)).contractWithStars
          (D.starOf (M.parent z δ).toResolvedFeynmanGraph
            (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z))) :=
    occurrenceSource_eq M z δ o.γ.1 o.B hparent hidx
  rw [← promotedCorrectedSource_eq Fstar s o, h1, innerStarCorrected_contract_eq Fstar M z δ,
    innerCorrectedOccurrenceSourceGraph, h2]

/-- **R-6c-body-489 — the central equality on vertices, over a raw `s`.** -/
theorem promotedCorrectedSource_vertices_eq_inner_raw
    (hparent : o.γ.1 = M.parent z δ) (hidx : HEq o.B (M.innerIdx z δ))
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s = z.1.1) :
    (promotedCorrectedOccurrenceSourceGraph Fstar s o).vertices
      = (innerCorrectedOccurrenceSourceGraph Fstar M z δ o).vertices :=
  congrArg ResolvedFeynmanGraph.vertices
    (promotedCorrectedSource_eq_innerCorrectedSource_raw M z δ s o Fstar hparent hidx houter)

/-- **R-6c-body-489 — the central equality on internal edges, over a raw `s`.** -/
theorem promotedCorrectedSource_internalEdges_eq_inner_raw
    (hparent : o.γ.1 = M.parent z δ) (hidx : HEq o.B (M.innerIdx z δ))
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s = z.1.1) :
    (promotedCorrectedOccurrenceSourceGraph Fstar s o).internalEdges
      = (innerCorrectedOccurrenceSourceGraph Fstar M z δ o).internalEdges :=
  congrArg ResolvedFeynmanGraph.internalEdges
    (promotedCorrectedSource_eq_innerCorrectedSource_raw M z δ s o Fstar hparent hidx houter)

/-- **R-6c-body-489 — the central equality on external legs, over a raw `s`.** -/
theorem promotedCorrectedSource_externalLegs_eq_inner_raw
    (hparent : o.γ.1 = M.parent z δ) (hidx : HEq o.B (M.innerIdx z δ))
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s = z.1.1) :
    (promotedCorrectedOccurrenceSourceGraph Fstar s o).externalLegs
      = (innerCorrectedOccurrenceSourceGraph Fstar M z δ o).externalLegs :=
  congrArg ResolvedFeynmanGraph.externalLegs
    (promotedCorrectedSource_eq_innerCorrectedSource_raw M z δ s o Fstar hparent hidx houter)

/-- **R-6c-body-489 — the forward corrected remnant component equals the recovered-side component, over a raw `s`** (body-461
mirror; passes `s` to the total corrected provider). -/
theorem correctedRemnantComponent_eq_inner_raw
    (hparent : o.γ.1 = M.parent z δ) (hidx : HEq o.B (M.innerIdx z δ))
    (hConn : (touchedLocalComponent z δ.1).forget.IsConnected)
    (hPos : 0 < (touchedLocalComponent z δ.1).internalEdges.card)
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s = z.1.1) :
    (canonicalCorrectedRemnantReembedSupply s Fstar).correctedRemnantComponent o
      = innerCorrectedRemnantComponent Fstar M z δ o hparent hidx hConn hPos houter :=
  ResolvedFeynmanSubgraph.ext
    (promotedCorrectedSource_vertices_eq_inner_raw M z δ s o Fstar hparent hidx houter)
    (promotedCorrectedSource_internalEdges_eq_inner_raw M z δ s o Fstar hparent hidx houter)
    (promotedCorrectedSource_externalLegs_eq_inner_raw M z δ s o Fstar hparent hidx houter)

/-- **R-6c-body-489 ∎ — the RAW corrected remnant round-trip, MEMBERSHIP-FREE.**  The forward corrected remnant component
of a raw split choice `s` round-trips to `δ` — the `innerStar_agrees_raw`-free `hround`, now free of any filtered witness.
This is the second half of the cycle repair (`canonicalCorrectedQuotientRaw s` being the first, body-469). -/
theorem canonicalCorrectedRemnantComponent_roundtrip_raw
    (hparent : o.γ.1 = M.parent z δ) (hidx : HEq o.B (M.innerIdx z δ))
    (hConn : (touchedLocalComponent z δ.1).forget.IsConnected)
    (hPos : 0 < (touchedLocalComponent z δ.1).internalEdges.card)
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s = z.1.1) :
    HEq ((canonicalCorrectedRemnantReembedSupply s Fstar).correctedRemnantComponent o) δ.1 :=
  (heq_of_eq (correctedRemnantComponent_eq_inner_raw M z δ s o Fstar hparent hidx hConn hPos houter)).trans
    (innerCorrectedRemnantComponent_roundtrip Fstar M z δ o hparent hidx hConn hPos houter)

end GaugeGeometry.QFT.Combinatorial
