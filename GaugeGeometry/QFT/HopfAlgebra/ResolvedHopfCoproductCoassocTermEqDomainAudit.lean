import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientImage

/-!
# R-6c-body-87 — term_eq domain audit: `term_eq` is total (`∀ s`), and image_agreement is Case-A-unsatisfiable

Eighty-seventh genuine-body step, auditing WHERE `term_eq` is required.  Verdict: the `SplitPhiData.term_eq`
field is TOTAL (`∀ s`), hence over-strong (unsatisfiable at the all-right-primitives, body-86); and the
downstream GlobalCover `image_agreement` is likewise Case-A-unsatisfiable.  So the σ-cover common-cover route
cannot prove `coassoc_gen` for the canonical carrier — A2-direct is required.

## `term_eq` is total (`∀ s`)

`ResolvedCoassocSplitPhiData.term_eq : ∀ s, D.resolvedSplitChoiceTerm s = imageWeight (imageOf s)`
(`…CoassocQuotientImage`) is quantified over ALL split choices (`resolved_term_eq_total` below).  The
`ResolvedTermEqGrandSupply.term_eqs` bundle fills exactly this `∀ s` field
(`…TermEqToFullSupply`).  So supplying `term_eq` is a TOTAL obligation — it includes the all-right-primitive
`⟨A, p₀⟩`, where it is UNSATISFIABLE (body-86): `resolvedSplitChoiceTerm ⟨A, p₀⟩ = 1 ⊗ (·)` (slot `1`) cannot
equal `imageWeight (imageOf ⟨A, p₀⟩) = leftTerm(selectedOuter) ⊗ (·)` with `selectedOuter ∈ carrier` nonempty
(slot `leftTerm ≠ 1`).  So the total `term_eq` heart is over-strong AND unsatisfiable for the canonical
(proper-forest) carrier.

## The downstream only needs the cover — but that too is Case-A-unsatisfiable

The GlobalCover (`…CoassocGlobalCover`) uses only the COVER-restricted agreements:

* `resolvedSplitPhi_forest_term_eq : ∀ q, forestWeight q = imageWeight (forestImage q)` (cover elements);
* `image_agreement : regroupImageSum x = ∑ z ∈ imageCarrier, imageWeight z`;
* `branch_agreement : (∑ forestWeight) + (∑ mixedWeight) = regroupBranchSum x`.

So weakening `term_eq` to the cover would remove the `∀ s` all-right-primitive obligation.  BUT `image_agreement`
is itself unsatisfiable under Case A: every `imageWeight z = leftTerm(z.selectedOuter) ⊗ (·)` with
`z.selectedOuter ∈ carrier` nonempty lies in the `leftTerm(nonempty) ⊗ (·)` subspace, so `∑ imageCarrier
imageWeight` has NO `1 ⊗ (·)` component — but `regroupImageSum = 1 ⊗ forestSum + coassocRightTail(forestSum)`
HAS the `1 ⊗ forestSum` boundary (slot `1`).  So `regroupImageSum ≠ ∑ imageCarrier imageWeight`, i.e.
`image_agreement` is UNSATISFIABLE for the canonical carrier.

## Verdict: A2-direct

Neither the total `term_eq` nor the cover-restricted `image_agreement` is satisfiable under Case A (`∅ ∉
carrier`).  The σ-cover common-cover route (regroupImage `= ∑ cover =` regroupBranch, body-38/54/GlobalCover)
CANNOT prove `coassoc_gen` for the canonical carrier: the IMAGE boundary `1 ⊗ forestSum` is not a cover
image-weight.  So `coassoc_gen` must be proven A2-DIRECT — `regroupImageSum = regroupBranchSum` as the algebraic
identity `1 ⊗ forestSum + coassocRightTail(forestSum) = assoc(forestSum ⊗ 1) + coassocLeftTail(forestSum)` (the
`Δᵣ`-coassociativity on the outer forest), with the σ-cover contributing at most the TAIL correspondence
`coassocLeftTail(forestSum) = coassocRightTail(forestSum)`-adjacent relation, NOT a common cover value.

So the whole GrandFull/GlobalCover `image_agreement`/`branch_agreement`-via-common-cover formulation
(bodies 36–86 output work, and the support-9 image side) is OVER-STRONG for the canonical carrier; the OUTPUT
must be re-based on the A2-direct algebraic identity.

Per the HALT: `term_eq` totality is confirmed (proved); the `image_agreement` unsatisfiability is documented (a
slot argument, not re-proved here); no coassoc proof is repaired; the domain verdict is fixed.

Landed:

* `resolved_term_eq_total` — `term_eq` holds for ALL split choices (the total-domain fact).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-87 — `term_eq` is total.**  The `SplitPhiData.term_eq` field is quantified over ALL split
choices, including the all-right-primitive `⟨A, p₀⟩` at which it is unsatisfiable (body-86).  So the heart
`term_eq` obligation is over-strong for the canonical (proper-forest) carrier. -/
theorem resolved_term_eq_total (P : ResolvedCoassocSplitPhiData D G) :
    ∀ s : ResolvedCoassocSplitChoice D G,
      D.resolvedSplitChoiceTerm s = P.imageWeight (P.imageOf s) :=
  P.term_eq

end GaugeGeometry.QFT.Combinatorial
