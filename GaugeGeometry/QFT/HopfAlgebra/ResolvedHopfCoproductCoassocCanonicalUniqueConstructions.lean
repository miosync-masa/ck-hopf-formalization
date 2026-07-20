import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocGenConstructionNormalized
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionPropernessDispatch

/-!
# R-6c-body-445 — canonical-unique construction-normalized conditional coassociativity (PROVED)

Four-hundred-and-forty-fifth genuine-body step — the canonical superseding adapter for body-441.  With the unique-ID
carrier `W'` (body-442) and its pure carrier-closure bundle (body-443/444), body-400's carrier root, the id-uniqueness
root, and the carrier-side measure leaves ALL become `W'`-derived.  Body-441 stays a valid conditional theorem; this body
is its canonical replacement.

Discharged from `W'` (no longer in the signature):
`D` (`:= W'.toData`), `Fstar` (`:= canonicalUniqueStarFactsOfW'`), `CarrierProper` (`:= W'.toCarrierProperProvider`), the
ambient support (`:= ambientSupportOfW'`, folded into the value-geometry `CoreBuild`), the `Ids` root
(`:= canonicalUniqueFilteredForestBlockIds`, each block's live carrier membership), the whole `Carrier` bundle (`Closure`
body-443 + `recovered_raw_mem` body-444), and — the point — BOTH carrier-side measure leaves (`Nne` / `Ppos`) and the
`∀ G` id-uniqueness (`hIdAll` / `hLegAll`): the pure bundle takes only the value core.

`VBuild.Measure` REMAINS an honest field inside `V` ownership — the value-side measure is not carrier-closure data, so
this is "the carrier-closure measure leaves are gone", NOT "measure is gone".

## The remaining sockets (this theorem's hypotheses ARE the further-purified ledger)

```text
VBuild                         concrete summand value construction (owns the V-side Measure / Wiring / hSurvivorComponent)
ValueGeometry                  legComplete + parentCD (parentCD couples the canonical leg-lift from legComplete)
StarProm                       promoted-star coherence (cross-ambient)
InnerStarRaw                   inner-star coherence (cross-ambient) — distinct from the canonical Fstar
OccRaw                         forest-occurrence inversion
Split                          value quotient-region split
rep / repCD / rep_gen          base-model representatives
{Fmem} {Concrete}              implicit model parameters (audited, NOT hidden)
```

Per the HALT/guards: body-441 is preserved as a valid conditional theorem; no re-proof of body-400 (projection adapter
only); canonical `Fstar` and cross-ambient `InnerStarRaw` are kept distinct; `Fmem` / `Concrete` remain implicit
(audited).  This is NOT the unconditional theorem.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
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

set_option linter.unusedSectionVars false

/-- **R-6c-body-445 — the block-local id supply, derived from `W'` membership.**  Each filtered forest-block domain
element carries its outer's carrier membership `q.1.1.2`, off which `W'` reads edge/leg id-uniqueness. -/
def canonicalUniqueFilteredForestBlockIds :
    ResolvedFilteredForestBlockUniqueIdSupply canonicalUniqueSupportedCarrierProperSupply.toData where
  edgeIdsUnique := fun {_G} q => edgeIdsUnique_of_carrier_mem q.1.1.2
  legIdsUnique := fun {_G} q => legIdsUnique_of_carrier_mem q.1.1.2

/-- **R-6c-body-445 — `W'` supplies the carrier-ambient support gate.** -/
def ambientSupportOfW' :
    ResolvedCarrierAmbientSupportSupply canonicalUniqueSupportedCarrierProperSupply.toData where
  edges_supported_of_mem := fun hA => (canonicalUniqueSupportedCarrier_ambientSupported hA).1
  legs_supported_of_mem := fun hA => (canonicalUniqueSupportedCarrier_ambientSupported hA).2

/-- **R-6c-body-445 — the canonical-unique value-geometry root.**  The CK value geometry (`legComplete` + `parentCD`),
with ambient support pinned to `ambientSupportOfW'`; `parentCD` reads the canonical leg-lift from the SAME `legComplete`. -/
structure ResolvedCanonicalUniqueMultiStarValueGeometrySupply where
  /-- The CK leg-completeness condition per touched quotient component. -/
  legComplete : ∀ {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z}),
    touchedLegComplete z δ.1
  /-- The de-contracted parent is connected-divergent, via the canonical leg-lift and the `W'`-derived ambient support. -/
  parentCD : ∀ {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z}),
    (localizedParentWithTouchedLegs z δ.1
      (touchedLegLiftDatum_of_complete z δ.1 (legComplete z δ))
      (liveAmbient_edges_supported ambientSupportOfW' z)
      (liveAmbient_legs_supported ambientSupportOfW' z)).forget.IsConnectedDivergent

/-- **R-6c-body-445 — the value-geometry root becomes the coherent `CoreBuild`**, `Ambient := ambientSupportOfW'`. -/
def ResolvedCanonicalUniqueMultiStarValueGeometrySupply.toCoreBuild
    (VG : ResolvedCanonicalUniqueMultiStarValueGeometrySupply) :
    ResolvedMultiStarValueCoreConstructionSupply canonicalUniqueSupportedCarrierProperSupply.toData where
  Ambient := ambientSupportOfW'
  legComplete := VG.legComplete
  parentCD := VG.parentCD

variable {Fmem : ResolvedSelectedOuterFilteredMemSupply canonicalUniqueSupportedCarrierProperSupply.toData}
  {Concrete : ∀ {G : ResolvedFeynmanGraph}
    (s : ResolvedCoassocSplitChoice canonicalUniqueSupportedCarrierProperSupply.toData G),
    ResolvedConcreteRemnantReembedSupply canonicalUniqueSupportedCarrierProperSupply.toData G s}

/-- **R-6c-body-445 ∎ — canonical-unique construction-normalized conditional native `Δᵣ`-coassociativity.**  Body-400
with the carrier root, the id-uniqueness root, and the carrier-side measure leaves all discharged from `W'`; a pure
projection onto body-400. -/
theorem coassoc_gen_of_canonical_unique_supported_constructions
    (VBuild : ResolvedConcreteSummandValueConstructionSupply
      canonicalUniqueSupportedCarrierProperSupply.toData Concrete)
    (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
    (StarProm : ResolvedPromotedStarCoherenceValueSupply Fmem VBuild.toConcreteSummandValueSupply)
    (InnerStarRaw : ResolvedInnerStarCoherenceValueSupply ValueGeometry.toCoreBuild.toValueCore)
    (OccRaw : ResolvedForestOccurrenceInversionValueSupply ValueGeometry.toCoreBuild.toValueCore)
    (Split : ResolvedValueQuotientRegionSplitSupply Fmem VBuild.toConcreteSummandValueSupply)
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x))
    (x : ResolvedHopfGen) :
    canonicalUniqueSupportedCarrierProperSupply.toData.coassocLeft (MvPolynomial.X x)
      = canonicalUniqueSupportedCarrierProperSupply.toData.coassocRight (MvPolynomial.X x) :=
  coassoc_gen_of_multiStar_constructions
    VBuild
    ValueGeometry.toCoreBuild
    canonicalUniqueStarFactsOfW'
    (canonicalUniquePureMultiStarCarrierClosureBundleSupply ValueGeometry.toCoreBuild.toValueCore)
    canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
    canonicalUniqueFilteredForestBlockIds
    StarProm InnerStarRaw OccRaw Split
    rep repCD rep_gen x

end GaugeGeometry.QFT.Combinatorial
