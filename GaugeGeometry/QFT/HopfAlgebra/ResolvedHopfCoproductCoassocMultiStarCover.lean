import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestTagIdentityAdapter
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredPreimageValueCover
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCarrierProperProvider

/-!
# R-6c-body-363 — the multi-star concrete cover (PROVED)

Three-hundred-and-sixty-third genuine-body step — the descent to the cover.  The recovered-identity root (body-361)
plus the forest-tag identity adapter (body-362) assemble, over ONE shared `Data`, the three leaves body-285's
`ResolvedRecoveredPreimageValueRoundTripLeafSupply` needs, and `toCover` (body-286's `toConcreteData.toCover`)
descends to a concrete `ResolvedWitnessSplitFilteredValueCoverSupply` — the value-root cover the S-free raid-boss
(body-286) consumes.

The `let`-shared `Data` (built once from `I.toRawForwardValueSupply` + the carrier provider `P`) flows into
`ForestEq`, `R`, and back, so NO `Tags`/`Data`-equality transport ever re-appears: the forward-outer / forward-quotient
leaves are `I`'s own, and the forest leaf is body-288's `forest_value_eq` fed by body-362.

Landed axiom-clean: `toMultiStarCover`.

Per the HALT (per the plan): the cover is completed here; the top-level conditional `coassoc_gen` — which body-286
delivers from `R` PLUS the base leaves (`carrier_isProperForest`, `rep` / `repCD` / `rep_gen`) — is deferred to
body-364, keeping THIS body strictly free of `rep` / perm.  The Front-3 gates (`hForest`, `hFT`, `P`, and `I`'s own
`houter` / `hRight` / `hForest` / `hround` / `hSurvivor` / `S`) stay explicit; the full `V.Remnant` provider is NOT
claimed complete.  No forward hidden round-trip, no facade, no flat term, no `forgetHopf`, no rep/perm, and NO
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

variable (M : ResolvedMultiStarDecontractionSupply D)
  {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-363 — the multi-star concrete cover.**  Assembles body-285's round-trip leaf supply over one shared
`Data` (from the recovered-identity root, body-361, and the carrier provider `P`), the forest leaf via body-288 fed by
body-362, and descends to the value-root cover. -/
noncomputable def toMultiStarCover (Fstar : ResolvedCanonicalStarFacts D)
    (S : ResolvedForestOccurrenceInversionSupply M) (Measure : ResolvedMeasureLeafSupply D)
    (I : ResolvedMultiStarRecoveredIdentitySupply M Fstar Fmem V)
    (P : ResolvedCarrierProperProvider D)
    (hForest : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      (I.Tags.Closure.Assembly.Region.forestRecovered z).elements
        = (M.forestRecoveredMulti Fstar z).elements)
    (hFT : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
      (γ' : {x : ResolvedFeynmanSubgraph G // x ∈ (I.Tags.Closure.unionOuterValue z).1.elements})
      (h : γ'.1 ∈ (I.Tags.Closure.Assembly.Region.forestRecovered z).elements)
      (h' : γ'.1 ∈ (M.forestRecoveredMulti Fstar z).elements),
      I.Tags.forestTag z γ' h = M.forestTag Fstar z ⟨γ'.1, h'⟩) :
    ResolvedWitnessSplitFilteredValueCoverSupply Fmem V :=
  let Data := I.toRawForwardValueSupply.toRecoveredPreimageValueMemSupply P
  let ForestEq : ResolvedForestValueEqValueSupply Fmem V :=
    { Data := Data
      forestTag_agrees := fun {_G} q γ hu hmem =>
        M.forestTag_agrees_for_identity_tags Fstar S Measure Data hForest hFT q γ hu hmem }
  let R : ResolvedRecoveredPreimageValueRoundTripLeafSupply Fmem V :=
    { Data := Data
      forward_outer_value := I.forward_outer_value
      forward_quotient_value := I.forward_quotient_value
      forest_value_eq := fun {_G} q γ hu B hmem hqB => ForestEq.forest_value_eq q γ hu B hmem hqB }
  R.toCover

end ResolvedMultiStarDecontractionSupply

end GaugeGeometry.QFT.Combinatorial
