import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredIdentityGeometry
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarCoassocGen

/-!
# R-6c-body-394 — the all-sockets-wired conditional native `Δᵣ`-coassociativity (PROVED)

Three-hundred-and-ninety-fourth genuine-body step — the final conditional theorem.  Body-393's fully wired recovered
identity is connected straight through body-364's raid-boss adapter to native `Δᵣ`-coassociativity on `X x`, with the
six sound/complete bridges, the parent gate, `hround`, `hForest`/`hFT`, and the round-trip identity all DERIVED — they no
longer appear in the caller's signature.

The `hForest` / `hFT` leaves are NOT returned to the caller: they are built in place from body-366's `rfl`/proof-
irrelevance wirings (exposed with `change` past the `let`-projections), so the only hypotheses that survive are the
honest concrete-model inhabitants.

## The final residual (this signature's hypotheses)

* value core `Core`; carrier closure `Closure`, `rrm`, implicit `Fmem`;
* cross-ambient geometry `StarProm`, `StarRaw`, `OccRaw`;
* `V` ownership `Wiring`, `hSurvivorComponent`, implicit `V`;
* base ownership `Ids`, `CarrierProper`, `Fstar`, `Measure`, `Split`;
* representation `rep`, `repCD`, `rep_gen`.

Per the HALT: this is the ALL-SOCKETS-WIRED conditional coassoc theorem, NOT unconditional — every surviving hypothesis
is an honest concrete-model inhabitant (surfaced, not hidden); the six bridges, the parent gate, `hround`,
`hForest`/`hFT`, and the round-trip identity are eliminated.  No facade, no flat term, no `forgetHopf`, no rep/perm
facade, and NO `promote_collapse` / singleton / floor-297.
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

variable {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
  {Concrete : ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G),
    ResolvedConcreteRemnantReembedSupply D G s}

/-- **R-6c-body-394 — all-sockets-wired conditional native `Δᵣ`-coassociativity.**  Every hypothesis is an honest
concrete-model inhabitant; the six bridges + parent gate + `hround` + `hForest`/`hFT` + round-trip identity are all
derived through body-393. -/
theorem coassoc_gen_of_multiStar_value_geometry
    (Core : ResolvedMultiStarDecontractionValueCoreSupply D)
    (Closure : ResolvedMultiStarInnerRawCarrierClosureSupply Core)
    (CarrierProper : ResolvedCarrierProperProvider D)
    (Ids : ResolvedFilteredForestBlockUniqueIdSupply D)
    (Fstar : ResolvedCanonicalStarFacts D)
    (StarProm : ResolvedPromotedStarCoherenceValueSupply Fmem V)
    (StarRaw : ResolvedInnerStarCoherenceValueSupply Core)
    (Wiring : ResolvedRemnantComponentValueWiringSupply V Concrete)
    (OccRaw : ResolvedForestOccurrenceInversionValueSupply Core)
    (Measure : ResolvedMeasureLeafSupply D)
    (Split : ResolvedValueQuotientRegionSplitSupply Fmem V)
    (hSurvivorComponent : ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G)
      (γ : {y : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements} //
        y ∈ ResolvedCoassocSplitChoice.rightComponents s}),
      V.Survivor.survivor.survivorComponent s γ = (survivorSupply_of_measure Measure G).survivorComponent s γ)
    (rrm : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      regionRawUnion (Core.toDecontractionSupply Closure) Fstar z ∈ D.carrier G)
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x))
    (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) := by
  let M := Core.toDecontractionSupply Closure
  let OccInv := Core.toForestOccurrenceInversionSupply Closure OccRaw
  let I := recoveredIdentitySupplyOfValueGeometry Core Closure CarrierProper Ids Fstar StarProm StarRaw
    Wiring OccRaw Measure Split hSurvivorComponent rrm
  have hForest : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      (I.Tags.Closure.Assembly.Region.forestRecovered z).elements
        = (M.forestRecoveredMulti Fstar z).elements :=
    fun z => M.multiStar_forestRecovered_wiring Fstar z
  have hFT : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
      (γ' : {y : ResolvedFeynmanSubgraph G // y ∈ (I.Tags.Closure.unionOuterValue z).1.elements})
      (h : γ'.1 ∈ (I.Tags.Closure.Assembly.Region.forestRecovered z).elements)
      (h' : γ'.1 ∈ (M.forestRecoveredMulti Fstar z).elements),
      I.Tags.forestTag z γ' h = M.forestTag Fstar z ⟨γ'.1, h'⟩ := by
    intro G z γ' h h'
    change M.forestTag Fstar z ⟨γ'.1, h⟩ = M.forestTag Fstar z ⟨γ'.1, h'⟩
    exact M.multiStar_forestTag_wiring Fstar z γ'.1 h h'
  exact coassoc_gen_of_multiStar_model M Fstar OccInv Measure I CarrierProper hForest hFT
    CarrierProper.carrier_isProperForest rep repCD rep_gen x

end GaugeGeometry.QFT.Combinatorial
