import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocStarRenameContract
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecontractSection
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecontractVertexEq

/-!
# R-6c-body-452 — the inner-corrected local alpha round-trip SEED (corrected contraction data = `δ` data) (PROVED)

Four-hundred-and-fifty-second genuine-body step — the local alpha round-trip seed that will replace strict
`innerStar_agrees_raw`.  Ownership discipline (per the plan): `innerStarCorrectingPerm z δ` depends on the RECOVERED
`z, δ`, so it is the round-trip-SIDE comparator, NOT a forward-input `starPerm`.  This body banks the three-field data
equality on the RECOVERED index only — no forward provider, no `VBuild`, no promoted correction.

The corrected contraction graph is the hardcoded-star contraction relabeled by `ρ` (body-451); its data equals `δ`'s
because body-451 rewrites it to the TOUCHED-star contraction, whose data is `δ`'s by the body-353/356 recontract section:

```text
((innerRaw.contractWithStars hardcodedStar).mapPerm ρ).data
  = (innerRaw.contractWithStars touchedInnerStarTotal).data   (body-451, reversed)
  = δ.data                                                    (body-353/356 recontract)
```

* `innerCorrected_contract_internalEdges` / `_externalLegs` — unconditional;
* `innerCorrected_contract_vertices` — under the touched component's own connectivity + positivity (`hConn` / `hPos`),
  exactly the body-353/358 vertex obligation.

The free-`H` / `HEq` occurrence transport (matching an occurrence `o.B` against `M.innerIdx z δ`), the local corrected
remnant component, and the `HEq`-round-trip are the next body; the corrected forward provider and its `VBuild` migration
come after the promoted correction.

Per the HALT/guards: `innerStarCorrectingPerm` is used only on the recovered index (round-trip comparator); no full
`Concrete` provider, no `VBuild` wiring, no promoted correction; strict `innerStar_agrees_raw` is NOT used; body-445 stays
a valid conditional.  NOT the unconditional theorem.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
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

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  (Fstar : ResolvedCanonicalStarFacts D) (M : ResolvedMultiStarDecontractionSupply D)
  (z : ForestBlockCodType D G)
  (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})

include Fstar

/-- **R-6c-body-452 — the corrected contraction's internal edges are `δ`'s.** -/
theorem innerCorrected_contract_internalEdges :
    (((innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)).contractWithStars
        (D.starOf (M.parent z δ).toResolvedFeynmanGraph
          (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)))).mapPerm
        (innerStarCorrectingPerm Fstar M z δ)).internalEdges = δ.1.internalEdges := by
  rw [← innerStarCorrected_contract_eq Fstar M z δ]
  exact recontract_innerRaw_internalEdges z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)

/-- **R-6c-body-452 — the corrected contraction's external legs are `δ`'s.** -/
theorem innerCorrected_contract_externalLegs :
    (((innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)).contractWithStars
        (D.starOf (M.parent z δ).toResolvedFeynmanGraph
          (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)))).mapPerm
        (innerStarCorrectingPerm Fstar M z δ)).externalLegs = δ.1.externalLegs := by
  rw [← innerStarCorrected_contract_eq Fstar M z δ]
  exact recontract_innerRaw_externalLegs z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)

/-- **R-6c-body-452 ∎ — the corrected contraction's vertices are `δ`'s** (under the touched component's connectivity /
positivity). -/
theorem innerCorrected_contract_vertices
    (hConn : (touchedLocalComponent z δ.1).forget.IsConnected)
    (hPos : 0 < (touchedLocalComponent z δ.1).internalEdges.card) :
    (((innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)).contractWithStars
        (D.starOf (M.parent z δ).toResolvedFeynmanGraph
          (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)))).mapPerm
        (innerStarCorrectingPerm Fstar M z δ)).vertices = δ.1.vertices := by
  rw [← innerStarCorrected_contract_eq Fstar M z δ]
  exact recontract_innerRaw_vertices z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) Fstar hConn hPos

end GaugeGeometry.QFT.Combinatorial
