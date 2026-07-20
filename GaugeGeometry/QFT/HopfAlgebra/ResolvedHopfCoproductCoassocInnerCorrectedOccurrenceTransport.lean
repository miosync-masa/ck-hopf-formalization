import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerCorrectedRoundTripSeed
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSurvivorRoundTrip

/-!
# R-6c-body-453 — the inner-corrected occurrence transport (free-`H` / `HEq`) (PROVED)

Four-hundred-and-fifty-third genuine-body step — the occurrence-side wrappers of body-452's seed, mirroring body-358's
free-`H` / `HEq` helpers but with the alpha (`mapPerm ρ`) contraction instead of the strict star.  Given a forest-block
`B'` over an ambient `H` that aligns with the recovered inner index (`hH : H = (M.parent z δ).tRFG`,
`hB : HEq B' (M.innerIdx z δ)`), the corrected contraction of `B'` has the same three-field data as `δ`.

* `innerCorrectedSource_internalEdges_helper` / `_externalLegs_helper` — unconditional;
* `innerCorrectedSource_vertices_helper` — under the touched component's connectivity + positivity.

Proof shape (mirror of body-358): `subst hH`, `obtain rfl := eq_of_heq hB`, then the body-452 field theorem (the
recovered index is definitionally `innerRaw`).  These are exactly the data hypotheses `subgraph_heq_of_data` (body-346)
consumes; combined with body-341's `houter` ambient alignment, they give the corrected remnant round-trip — the alpha
replacement of strict `innerStar_agrees_raw` — WITHOUT that datum.  The local corrected remnant component and the
assembled `HEq` round-trip are the immediate next step (they only wrap these three helpers with `subgraph_heq_of_data`).

Per the HALT/guards: no promoted correction is mixed in (`innerStarCorrectingPerm` is the recovered-side comparator only);
no full `Concrete` provider, no `VBuild` wiring; strict `innerStar_agrees_raw` is NOT used; `hConn` / `hPos` are the
existing quotient-CD / quotient-properness obligations, NOT new measure leaves; body-445 stays a valid conditional.  NOT
the unconditional theorem.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton /
floor-297.
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

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  (Fstar : ResolvedCanonicalStarFacts D) (M : ResolvedMultiStarDecontractionSupply D)
  (z : ForestBlockCodType D G)
  (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})

include Fstar

/-- **R-6c-body-453 — free-`H` internal-edges transport.** -/
theorem innerCorrectedSource_internalEdges_helper {H : ResolvedFeynmanGraph}
    (B' : (D.supply H).ForestIdx) (hH : H = (M.parent z δ).toResolvedFeynmanGraph)
    (hB : HEq B' (M.innerIdx z δ)) :
    ((B'.1.contractWithStars (D.starOf H B'.1)).mapPerm
        (innerStarCorrectingPerm Fstar M z δ)).internalEdges = δ.1.internalEdges := by
  subst hH
  obtain rfl := eq_of_heq hB
  exact innerCorrected_contract_internalEdges Fstar M z δ

/-- **R-6c-body-453 — free-`H` external-legs transport.** -/
theorem innerCorrectedSource_externalLegs_helper {H : ResolvedFeynmanGraph}
    (B' : (D.supply H).ForestIdx) (hH : H = (M.parent z δ).toResolvedFeynmanGraph)
    (hB : HEq B' (M.innerIdx z δ)) :
    ((B'.1.contractWithStars (D.starOf H B'.1)).mapPerm
        (innerStarCorrectingPerm Fstar M z δ)).externalLegs = δ.1.externalLegs := by
  subst hH
  obtain rfl := eq_of_heq hB
  exact innerCorrected_contract_externalLegs Fstar M z δ

/-- **R-6c-body-453 ∎ — free-`H` vertices transport** (under the touched component's connectivity / positivity). -/
theorem innerCorrectedSource_vertices_helper {H : ResolvedFeynmanGraph}
    (B' : (D.supply H).ForestIdx) (hH : H = (M.parent z δ).toResolvedFeynmanGraph)
    (hB : HEq B' (M.innerIdx z δ))
    (hConn : (touchedLocalComponent z δ.1).forget.IsConnected)
    (hPos : 0 < (touchedLocalComponent z δ.1).internalEdges.card) :
    ((B'.1.contractWithStars (D.starOf H B'.1)).mapPerm
        (innerStarCorrectingPerm Fstar M z δ)).vertices = δ.1.vertices := by
  subst hH
  obtain rfl := eq_of_heq hB
  exact innerCorrected_contract_vertices Fstar M z δ hConn hPos

end GaugeGeometry.QFT.Combinatorial
