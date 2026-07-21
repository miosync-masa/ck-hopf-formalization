import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSplitDischarge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSurvivorInjection
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocProductGenLeaves

/-!
# R-6c-body-498 — `survivorInj` / `survivorGen` discharge (VBuild survivor ownership ELIMINATED) (PROVED)

Four-hundred-and-ninety-eighth genuine-body step — the third stop of the residual-purification campaign.  Body-497
removed `Fmem` and `Split` from the closed-theorem signature; this body removes the two survivor leaves of `VBuild`
(`survivorInj`, `survivorGen`), reducing the alpha-native filtered-value construction root to `Measure + filtered
Quotient` only.

## The two survivor leaves, DERIVED from `Measure`

Both leaves live over `survivorSupply_of_measure Measure G`, which is *by definition* the concrete right-survivor supply
`resolvedConcreteRightSurvivorSupply D G (fun s γ => rightComponentNonempty_of_measure Measure s γ)`.  So the existing
concrete survivor theorems apply verbatim (defeq bridge, no `change` needed):

* **`survivorInj_of_measure`** — `product_survivorInj_of_concreteSurvivor` at `hne := rightComponentNonempty_of_measure
  Measure` (the survivor reembed preserves the intrinsic graph, so equal images force equal sources — NO ID-uniqueness /
  global-gap re-proof);
* **`survivorGen_of_measure`** — `product_survivorGen_of_concreteSurvivor` at the same `hne` (the survivor is
  connected-divergent, so `resolvedComponentGenTerm` reads only the class — NO new graph/class equality).

The per-component nonemptiness `rightComponentNonempty_of_measure` reads only `Measure.cd_nonempty` (a right-primitive
component is connected-divergent).

## Reduced VBuild root

`ResolvedAlphaNativeFilteredQuotientConstructionSupply` keeps only `Measure` and the body-469 filtered `Quotient`; its
`toAlphaNativeFilteredValueConstructionSupply` projection fills the old survivor leaves from the two theorems above.  The
canonical `W'` wrapper `coassoc_gen_of_canonicalMultiStar_alpha_quotient_root` feeds the reduced root into body-497's
thin theorem — `survivorInj` and `survivorGen` are GONE from the signature.

## Status

```text
survivorInj / survivorGen   CANONICAL DERIVED FROM Measure   (this body)
VBuild survivor ownership    ELIMINATED
reduced V root               Measure + filtered Quotient
remaining explicit roots     Measure + Quotient / E / ValueGeometry / OccRaw / rep
next root                    filtered Quotient.quotient_mem
```

Per the HALT/guards: survivor injectivity is NOT re-proved from ID-uniqueness / global-gap; the corrected remnant is NOT
read; `Quotient.quotient_mem` / `quot_eq` / `OccRaw` / `ValueGeometry` are NOT entered; NO new leaf beyond
`Measure.cd_nonempty`; the old `VBuild` struct is NOT destructively changed (a leaner root is ADDED beside it); strict
`StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc claim; body-445 stays a valid conditional.  No facade, no
flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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
set_option maxHeartbeats 1600000

variable {D : ResolvedCoproductProperForestData}

/-! ## The two survivor leaves, from the measure -/

/-- **R-6c-body-498 ∎ — the survivor `Finset` injectivity leaf, from the measure.**  `product_survivorInj_of_concrete
Survivor` at `hne := rightComponentNonempty_of_measure Measure`; defeq-bridged to `survivorSupply_of_measure`. -/
theorem survivorInj_of_measure (Measure : ResolvedMeasureLeafSupply D)
    {G : ResolvedFeynmanGraph} (q : ResolvedCoassocSplitChoice D G) :
    ∀ γ₁ ∈ q.rightComponents.attach, ∀ γ₂ ∈ q.rightComponents.attach,
      (survivorSupply_of_measure Measure G).survivorComponent q γ₁
        = (survivorSupply_of_measure Measure G).survivorComponent q γ₂ → γ₁ = γ₂ :=
  product_survivorInj_of_concreteSurvivor
    (fun s γ => rightComponentNonempty_of_measure Measure s γ) q

/-- **R-6c-body-498 ∎ — the survivor reembed generator leaf, from the measure.**  `product_survivorGen_of_concrete
Survivor` at the same `hne`; defeq-bridged to `survivorSupply_of_measure`. -/
theorem survivorGen_of_measure (Measure : ResolvedMeasureLeafSupply D)
    {G : ResolvedFeynmanGraph} (q : ResolvedCoassocSplitChoice D G)
    (γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ q.1.1.elements} // x ∈ q.rightComponents}) :
    resolvedComponentGenTerm ((survivorSupply_of_measure Measure G).survivorComponent q γ)
      = resolvedComponentGenTerm γ.1.1 :=
  product_survivorGen_of_concreteSurvivor
    (fun s γ => rightComponentNonempty_of_measure Measure s γ) q γ

/-! ## The reduced VBuild root -/

/-- **R-6c-body-498 — the reduced alpha-native filtered construction root.**  Only `Measure` and the body-469 filtered
`Quotient`; the survivor leaves are DERIVED. -/
structure ResolvedAlphaNativeFilteredQuotientConstructionSupply
    (D : ResolvedCoproductProperForestData) (CarrierProper : ResolvedCarrierProperProvider D)
    (Fstar : ResolvedCanonicalStarFacts D) where
  /-- The measure-leaf supply. -/
  Measure : ResolvedMeasureLeafSupply D
  /-- The filtered quotient ownership (reads `Measure`). -/
  Quotient : ResolvedFilteredQuotientOwnershipSupply D Measure CarrierProper Fstar

variable (CarrierProper : ResolvedCarrierProperProvider D) (Fstar : ResolvedCanonicalStarFacts D)

/-- **R-6c-body-498 ∎ — the projection into the body-471 filtered-value construction root.**  The two survivor leaves
come from the measure theorems above; `Measure` and `Quotient` pass through. -/
noncomputable def ResolvedAlphaNativeFilteredQuotientConstructionSupply.toAlphaNativeFilteredValueConstructionSupply
    (C : ResolvedAlphaNativeFilteredQuotientConstructionSupply D CarrierProper Fstar) :
    ResolvedAlphaNativeFilteredValueConstructionSupply D CarrierProper Fstar where
  Measure := C.Measure
  survivorInj := survivorInj_of_measure C.Measure
  survivorGen := survivorGen_of_measure C.Measure
  Quotient := C.Quotient

/-! ## The canonical `W'` specialization + signature adapter -/

/-- **R-6c-body-498 — the canonical-`W'` reduced alpha filtered-quotient construction root.** -/
abbrev ResolvedCanonicalUniqueAlphaFilteredQuotientConstructionSupply :=
  ResolvedAlphaNativeFilteredQuotientConstructionSupply
    canonicalUniqueSupportedCarrierProperSupply.toData
    canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
    canonicalUniqueStarFactsOfW'

/-- **R-6c-body-498 ∎ — canonical-`W'` native `Δᵣ`-coassociativity with the survivor ownership DISCHARGED.**  A thin
wrapper over body-497's `coassoc_gen_of_canonicalMultiStar_alpha_split_discharged`: the reduced root supplies the full
`VBuild` internally, so `survivorInj` and `survivorGen` are GONE from the signature.  The remaining explicit roots are
`Measure + filtered Quotient` (as `Creduced`) / `E` / `ValueGeometry` / `OccRaw` / `rep`. -/
theorem coassoc_gen_of_canonicalMultiStar_alpha_quotient_root
    (Creduced : ResolvedCanonicalUniqueAlphaFilteredQuotientConstructionSupply)
    (E : ∀ G : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply G)
    (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
    (OccRaw : ResolvedForestOccurrenceInversionValueSupply ValueGeometry.toCoreBuild.toValueCore)
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x))
    (x : ResolvedHopfGen) :
    canonicalUniqueSupportedCarrierProperSupply.toData.coassocLeft (MvPolynomial.X x)
      = canonicalUniqueSupportedCarrierProperSupply.toData.coassocRight (MvPolynomial.X x) :=
  coassoc_gen_of_canonicalMultiStar_alpha_split_discharged
    Creduced.toAlphaNativeFilteredValueConstructionSupply E ValueGeometry OccRaw rep repCD rep_gen x

end GaugeGeometry.QFT.Combinatorial
