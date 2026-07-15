import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredPreimageValueRoundTrip
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForwardQuotientMemValue

/-!
# R-6c-body-286 — the concrete value cover + coassociativity from the recovered preimage (PROVED)

Two-hundred-and-eighty-sixth genuine-body step — the final mechanical assembly.  The two whole value round-trips
(body-285) fill body-253's `ResolvedWitnessSplitFilteredValueConcreteData`; `.toCover` gives the concrete `cover`; and
`coassoc_gen_of_recovered_preimage_value` feeds it (with the free `forwardMem`, body-272) into body-270's raid-boss
bijection side — **S-free, no `.ofLegacy`, no phantom `S`, no old closure converter**.  This CLOSES the construction
boundary named in body-273: the `cover` hypothesis of the top-level coassociativity theorem is now discharged by a
concrete value-root construction, leaving exactly the three geometry leaves (body-285) + the base leaves.

## The four branch fields are two whole laws

The preimage VALUE is `recoveredPreimageValue` on BOTH branches, so the four `ConcreteData` fields are copies of the two
whole round-trips (body-285): `mixed_forward` / `forest_forward` = `forward_roundtrip_value`; `mixed_backward` /
`forest_backward` = `backward_roundtrip_value`; the classifier hypotheses `h` never touch the value.

## The S-free top-level theorem

`coassoc_gen_of_recovered_preimage_value` builds body-270's `ResolvedFilteredBijectionSideSupply` directly from `F` /
`V` / `R.toCover` / `forwardQuotientMemValueOfValue F V` (free) + the base leaves, and returns `.coassoc_gen`.  It never
mentions `ResolvedParametricCarrierClosureSupply D S` — the phantom `S` and the legacy bundle are gone from the
canonical path.

Per the HALT: the four branch fields are copies of the two whole laws; the classifier proof does not affect the value;
no `.ofLegacy`, no phantom `S`, no old closure converter; the residual is exactly the three geometry leaves (body-285) +
the base leaves.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

namespace ResolvedRecoveredPreimageValueRoundTripLeafSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-286 — the concrete value branch data** (body-253).  Both preimages are `recoveredPreimageValue`; the
four round-trip fields are copies of the two whole laws (body-285). -/
noncomputable def toConcreteData (R : ResolvedRecoveredPreimageValueRoundTripLeafSupply F V) :
    ResolvedWitnessSplitFilteredValueConcreteData F V where
  mixedPreimage := fun z _ => R.Data.Tags.recoveredPreimageValue z
  forestPreimage := fun z _ => R.Data.Tags.recoveredPreimageValue z
  mixedPreimage_mem := fun z h _ => R.Data.mixedPreimage_mem z h
  forestPreimage_mem := fun z h _ => R.Data.forestPreimage_mem z h
  mixed_forward := fun z _ h => R.forward_roundtrip_value z (R.Data.mixedPreimage_mem z h)
  forest_forward := fun z _ h => R.forward_roundtrip_value z (R.Data.forestPreimage_mem z h)
  mixed_backward := fun q _ => R.backward_roundtrip_value q
  forest_backward := fun q _ => R.backward_roundtrip_value q

/-- **R-6c-body-286 — the concrete value cover** (body-253). -/
noncomputable def toCover (R : ResolvedRecoveredPreimageValueRoundTripLeafSupply F V) :
    ResolvedWitnessSplitFilteredValueCoverSupply F V :=
  R.toConcreteData.toCover

end ResolvedRecoveredPreimageValueRoundTripLeafSupply

/-- **R-6c-body-286 — native `Δᵣ`-coassociativity from the recovered-preimage construction** (S-free top-level).  The
concrete value cover (this body) + the free forward membership (body-272) feed body-270's raid-boss bijection side; the
residual is exactly the three geometry leaves (body-285) + the base leaves.  No `.ofLegacy`, no parametric closure, no
phantom `S`. -/
theorem coassoc_gen_of_recovered_preimage_value
    {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
    (R : ResolvedRecoveredPreimageValueRoundTripLeafSupply F V)
    (carrier_isProperForest : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G),
      A ∈ D.carrier G → A.IsProperForest)
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x))
    (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  (ResolvedFilteredBijectionSideSupply.mk F V R.toCover
    (forwardQuotientMemValueOfValue F V) carrier_isProperForest rep repCD rep_gen).coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
