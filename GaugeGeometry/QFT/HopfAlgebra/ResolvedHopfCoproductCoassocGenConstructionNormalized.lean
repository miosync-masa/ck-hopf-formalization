import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocGenValueGeometry
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteSummandValueConstruction
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarCoreClosureAssembly

/-!
# R-6c-body-400 — construction-normalized conditional native `Δᵣ`-coassociativity (PROVED)

Four-hundredth genuine-body step — the completion node.  Body-394's all-sockets-wired theorem is fed by the three
coherent construction roots (body-396's faithful `VBuild`, body-399's `CoreBuild` / `CarrierBundle`), so every
proof-architecture and ownership-wiring obligation is now a PROJECTION: `V` / `Measure` / `Wiring` / `hSurvivorComponent`
collapse into `VBuild`, and `Core` / `Closure` / `rrm` into `CoreBuild` / `Carrier`.

This is NOT the unconditional theorem — honest fields survive INSIDE `VBuild` / `CoreBuild` / `CarrierBundle`
(`legComplete`, `parentCD`, `Ambient`, `remnantDisjoint`, `survivorInj`, `quotient_mem`, …) together with the
cross-ambient model data (`StarProm` / `StarRaw` / `OccRaw`) and the base inputs (`CarrierProper` / `Ids` / `Fstar` /
`Split` / `Fmem` / `rep` / `repCD` / `rep_gen`).  It is the **construction-normalized conditional** coassoc theorem: no
equality bridge, no `change`, no honest residual re-expanded into an argument — the hypotheses are exactly the concrete
construction roots + the cross-ambient data + the base representation inputs.

> Every proof-architecture and ownership-wiring obligation has disappeared; native resolved coassociativity now follows
> from three coherent concrete construction roots, the cross-ambient model data, and the base representation inputs.

Per the HALT: this is a completion node, still CONDITIONAL; the surviving hypotheses are honest concrete-model
inhabitants (surfaced, not hidden); their canonical discharge (401+) is the concrete σ-cover model.  No facade, no flat
term, no `forgetHopf`, no rep/perm facade, and NO `promote_collapse` / singleton / floor-297.
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

variable {Fmem : ResolvedSelectedOuterFilteredMemSupply D}
  {Concrete : ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G),
    ResolvedConcreteRemnantReembedSupply D G s}

/-- **R-6c-body-400 — construction-normalized conditional native `Δᵣ`-coassociativity.**  Native resolved
coassociativity from the three coherent construction roots (`VBuild` / `CoreBuild` / `Carrier`), the cross-ambient model
data, and the base representation inputs — every proof-architecture / ownership obligation is a projection. -/
theorem coassoc_gen_of_multiStar_constructions
    (VBuild : ResolvedConcreteSummandValueConstructionSupply D Concrete)
    (CoreBuild : ResolvedMultiStarValueCoreConstructionSupply D)
    (Fstar : ResolvedCanonicalStarFacts D)
    (Carrier : ResolvedMultiStarCarrierClosureBundleSupply CoreBuild.toValueCore Fstar)
    (CarrierProper : ResolvedCarrierProperProvider D)
    (Ids : ResolvedFilteredForestBlockUniqueIdSupply D)
    (StarProm : ResolvedPromotedStarCoherenceValueSupply Fmem VBuild.toConcreteSummandValueSupply)
    (StarRaw : ResolvedInnerStarCoherenceValueSupply CoreBuild.toValueCore)
    (OccRaw : ResolvedForestOccurrenceInversionValueSupply CoreBuild.toValueCore)
    (Split : ResolvedValueQuotientRegionSplitSupply Fmem VBuild.toConcreteSummandValueSupply)
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x))
    (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  coassoc_gen_of_multiStar_value_geometry
    CoreBuild.toValueCore
    Carrier.Closure
    CarrierProper
    Ids
    Fstar
    StarProm
    StarRaw
    VBuild.remnantComponentValueWiring_of_construction
    OccRaw
    VBuild.Measure
    Split
    VBuild.hSurvivorComponent_of_construction
    Carrier.recovered_raw_mem
    rep repCD rep_gen x

end GaugeGeometry.QFT.Combinatorial
