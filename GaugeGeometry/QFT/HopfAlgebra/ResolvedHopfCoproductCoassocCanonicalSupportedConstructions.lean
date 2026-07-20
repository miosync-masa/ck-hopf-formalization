import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocGenConstructionNormalized
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredRawClosureAssembly

/-!
# R-6c-body-441 — canonical-supported construction-normalized conditional coassociativity (PROVED)

Four-hundred-and-forty-first genuine-body step — re-normalizing body-400's `coassoc_gen_of_multiStar_constructions` with
the canonical supported carrier `W` and the body-439 **derived** carrier-closure bundle.  Everything the carrier root
supplies is now discharged from `W`; the surviving hypotheses are exactly value geometry, cross-ambient model data, the
measure / id leaves, and the base representatives.

Discharged from `W` (no longer in the signature):
`D` (`:= W.toData`), `Fstar` (`:= canonicalStarFactsOfW`), `CarrierProper` (`:= W.toCarrierProperProvider`), the ambient
support (`:= ambientSupportOfW`, folded into the value-geometry `CoreBuild`), and — crucially — the whole `Carrier`
bundle: `Closure` (body-427) and `recovered_raw_mem` (body-439) are BOTH derived by
`canonicalMultiStarCarrierClosureBundleSupply`.

Single-owned / surfaced:
* the CD-nonempty measure leaf is single-owned by `VBuild.Measure`
  (`ResolvedMeasureLeafSupply.toConnectedDivergentNonemptySupply`) — NOT duplicated;
* deriving `recovered_raw_mem` (which quantifies over ALL ambient `G`) SURFACES two leaves that the opaque carrier field
  had hidden: the CD-positive-internal-edges measure leaf (`Ppos`) and unconditional id-uniqueness
  (`hIdAll` / `hLegAll` — strictly stronger than the block-local `Ids`, from which `Ids` is here re-derived).  These are
  reported, not concealed.

Guards honoured: canonical `ResolvedCanonicalStarFacts` (`Fstar`) and the cross-ambient `StarRaw`
(`ResolvedInnerStarCoherenceValueSupply`) are kept distinct; `parentCD` reads the CANONICAL leg-lift built from the SAME
`legComplete` (the value-geometry root couples them); the carrier bundle is DERIVED (body-439), not re-input; body-400's
proof is reused by a projection adapter only (no re-proof).  This is NOT the unconditional theorem.

## The remaining sockets (this theorem's hypotheses ARE the final ledger)

```text
VBuild                         concrete summand value construction (owns Measure / Wiring / hSurvivorComponent)
ValueGeometry                  legComplete + parentCD (parentCD couples the canonical leg-lift from legComplete)
Ppos                           cd_positiveInternalEdges measure leaf (surfaced by the recovered-outer properness)
hIdAll / hLegAll               ∀ G edge/leg id-uniqueness (surfaced; re-derives the block-local Ids)
StarProm                       promoted-star coherence (cross-ambient)
StarRaw                        inner-star coherence (cross-ambient) — distinct from Fstar
OccRaw                         forest-occurrence inversion
Split                          value quotient-region split
rep / repCD / rep_gen          base-model representatives
```

Per the HALT: no facade, no flat term, no `forgetHopf`, no rep/perm facade, and NO `promote_collapse` / singleton /
floor-297.  `Fmem` and `Concrete` remain implicit model parameters (audited below, NOT hidden).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false

/-- **R-6c-body-441 — the canonical value-geometry root.**  Just the CK value geometry (`legComplete` + `parentCD`), with
the ambient support pinned to `ambientSupportOfW`; `parentCD` reads the canonical leg-lift built from the SAME
`legComplete`. -/
structure ResolvedCanonicalMultiStarValueGeometrySupply where
  /-- The CK leg-completeness condition per touched quotient component (body-376). -/
  legComplete : ∀ {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalSupportedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalSupportedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z}),
    touchedLegComplete z δ.1
  /-- The de-contracted parent is connected-divergent — reading the canonical leg-lift from `legComplete` and the
  `W`-derived ambient support. -/
  parentCD : ∀ {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalSupportedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalSupportedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z}),
    (localizedParentWithTouchedLegs z δ.1
      (touchedLegLiftDatum_of_complete z δ.1 (legComplete z δ))
      (liveAmbient_edges_supported ambientSupportOfW z)
      (liveAmbient_legs_supported ambientSupportOfW z)).forget.IsConnectedDivergent

/-- **R-6c-body-441 — the value-geometry root becomes the coherent `CoreBuild`**, with `Ambient := ambientSupportOfW`. -/
def ResolvedCanonicalMultiStarValueGeometrySupply.toCoreBuild
    (VG : ResolvedCanonicalMultiStarValueGeometrySupply) :
    ResolvedMultiStarValueCoreConstructionSupply canonicalSupportedCarrierProperSupply.toData where
  Ambient := ambientSupportOfW
  legComplete := VG.legComplete
  parentCD := VG.parentCD

variable {Fmem : ResolvedSelectedOuterFilteredMemSupply canonicalSupportedCarrierProperSupply.toData}
  {Concrete : ∀ {G : ResolvedFeynmanGraph}
    (s : ResolvedCoassocSplitChoice canonicalSupportedCarrierProperSupply.toData G),
    ResolvedConcreteRemnantReembedSupply canonicalSupportedCarrierProperSupply.toData G s}

/-- **R-6c-body-441 ∎ — canonical-supported construction-normalized conditional native `Δᵣ`-coassociativity.**  Body-400
with the carrier root discharged from `W`: `D` / `Fstar` / `CarrierProper` / ambient support and the entire
`Carrier` bundle (`Closure` body-427 + `recovered_raw_mem` body-439) are gone; the hypotheses are exactly value geometry
(`VBuild` / `ValueGeometry`), the surfaced measure & id leaves (`Ppos` / `hIdAll` / `hLegAll`), the cross-ambient data
(`StarProm` / `StarRaw` / `OccRaw` / `Split`), and the base representatives.  A pure projection onto body-400. -/
theorem coassoc_gen_of_canonical_supported_constructions
    (VBuild : ResolvedConcreteSummandValueConstructionSupply
      canonicalSupportedCarrierProperSupply.toData Concrete)
    (ValueGeometry : ResolvedCanonicalMultiStarValueGeometrySupply)
    (Ppos : ∀ G : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply G)
    (hIdAll : ∀ G : ResolvedFeynmanGraph, G.EdgeIdsUnique)
    (hLegAll : ∀ G : ResolvedFeynmanGraph, G.LegIdsUnique)
    (StarProm : ResolvedPromotedStarCoherenceValueSupply Fmem VBuild.toConcreteSummandValueSupply)
    (StarRaw : ResolvedInnerStarCoherenceValueSupply ValueGeometry.toCoreBuild.toValueCore)
    (OccRaw : ResolvedForestOccurrenceInversionValueSupply ValueGeometry.toCoreBuild.toValueCore)
    (Split : ResolvedValueQuotientRegionSplitSupply Fmem VBuild.toConcreteSummandValueSupply)
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x))
    (x : ResolvedHopfGen) :
    canonicalSupportedCarrierProperSupply.toData.coassocLeft (MvPolynomial.X x)
      = canonicalSupportedCarrierProperSupply.toData.coassocRight (MvPolynomial.X x) :=
  coassoc_gen_of_multiStar_constructions
    VBuild
    ValueGeometry.toCoreBuild
    canonicalStarFactsOfW
    (canonicalMultiStarCarrierClosureBundleSupply
      (fun G => VBuild.Measure.toConnectedDivergentNonemptySupply G)
      Ppos hIdAll ValueGeometry.toCoreBuild.toValueCore)
    canonicalSupportedCarrierProperSupply.toCarrierProperProvider
    ⟨fun _ => hIdAll _, fun _ => hLegAll _⟩
    StarProm StarRaw OccRaw Split
    rep repCD rep_gen x

end GaugeGeometry.QFT.Combinatorial
