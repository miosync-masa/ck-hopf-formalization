import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFilteredBijectionSide

/-!
# R-6c-body-272 — the forward quotient membership is FREE; the last new leaf discharged (PROVED)

Two-hundred-and-seventy-second genuine-body step — it discharges the sole leaf discovered in body-270
(`ResolvedForwardQuotientMemValueSupply.quotient_mem`) from the value bundle's `ForestIdx` typing alone, and sharpens
`coassoc_gen_of_parametric_model` by dropping the `forwardMem` hypothesis.  After this, the raid-boss's twelve
`sum_bij'` fields are all filled from existing canonical data (`F` / `V` / `cover` + base leaves) — no new obligation
survives.

## Why it is free

`ResolvedCoproductProperForestData.supply` (ResolvedHopfCoproductSupply.lean:151-152) fixes the fiber **definitionally**,
for *any* `D`:

```lean
ForestIdx      := {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}
forestCarrier  := (D.carrier G).attach
```

So `(fwdMapFilteredValue F V q).2 = V.quotientForestRaw q.1` already IS an element of the subtype
`{B // B ∈ D.carrier (…)}`, and the codomain fiber `(D.supply …).forestCarrier` is defeq to `(D.carrier …).attach`.
Membership is therefore exactly `Finset.mem_attach` — no `selectedOuter_mem`, no `Forward`, no star classifier, no
carrier-closure assumption.  The "new leaf" of body-270 was a free projection, not a genuine model obligation.

## The sharpened theorem

`coassoc_gen_of_parametric_model_value` supplies `forwardQuotientMemValueOfValue V` internally, so its hypotheses are
just the parametric closure, the value bundle, the filtered cover, and the base leaves.  The `forwardMem` argument is
gone.

Per the HALT: `quotient_mem` is derived from `V`'s `ForestIdx` subtype alone via `Finset.mem_attach`; no selected
membership, no `Forward`, no star classifier; the top-level conditional theorem loses its `forwardMem` hypothesis.  No
facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-272 — the forward quotient membership, FREE.**  The codomain fiber `(D.supply …).forestCarrier` is
`(D.carrier …).attach` (ResolvedHopfCoproductSupply.lean:151-152), and `V.quotientForestRaw q` is a subtype element, so
membership is `Finset.mem_attach`.  No `Forward`, no selected membership, no star classifier. -/
noncomputable def forwardQuotientMemValueOfValue (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) :
    ResolvedForwardQuotientMemValueSupply F V where
  quotient_mem := fun {_G} q => Finset.mem_attach _ (fwdMapFilteredValue F V q).2

/-- **R-6c-body-272 — coassociativity from the parametric model, sharpened.**  The `forwardMem` hypothesis of
`coassoc_gen_of_parametric_model` is discharged internally by `forwardQuotientMemValueOfValue`; the top-level statement
now depends only on the parametric closure, the value bundle, the filtered cover, and the base leaves. -/
theorem coassoc_gen_of_parametric_model_value {S : ResolvedConcreteSummandBundleSupply D}
    (Closure : ResolvedParametricCarrierClosureSupply D S)
    (V : ResolvedConcreteSummandValueSupply D)
    (cover : ResolvedWitnessSplitFilteredValueCoverSupply Closure.toSelectedOuterFilteredMemSupply V)
    (carrier_isProperForest : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G),
      A ∈ D.carrier G → A.IsProperForest)
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x))
    (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  coassoc_gen_of_parametric_model Closure V cover
    (forwardQuotientMemValueOfValue Closure.toSelectedOuterFilteredMemSupply V)
    carrier_isProperForest rep repCD rep_gen x

end GaugeGeometry.QFT.Combinatorial
