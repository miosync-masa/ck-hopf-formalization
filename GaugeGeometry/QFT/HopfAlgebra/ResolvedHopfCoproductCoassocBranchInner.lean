import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocBranchSide

/-!
# R-6c-2d-4b-3b — branch inner expansion via the component-choice vessel

The branch side is a sum over outer forests `A` of `branchSummand A` (R-6c-2d-4b-3a).  Each
`branchSummand A` carries an inner left tail `coassocLeftTail D (leftTerm A ⊗ rightTerm A)`, whose
expansion is a *product-of-sums* over component choices.  Rather than implement that combinatorial
explosion inline, we **thicken the interface**: given the `ResolvedComponentChoiceExpansion` vessel
(R-6c-2d-2b) for `A` — which splits the inner tail as `primitiveLeak + choiceSum` — the branch summand
splits as `(outer leak + inner primitive leak) + choiceSum`.

So the branch side closes once a component-choice expansion is supplied per outer forest; constructing
that expansion (the product-of-sums) is the remaining combinatorial work, now isolated behind the
vessel.

Landed:

* `ResolvedCoproductProperForestData.branchLeakTerm` / `branchSummand` — the outer leak and the branch
  summand for one outer forest;
* `ResolvedCoproductProperForestData.regroupBranchSum_eq_branchSummandSum` — `regroupBranchSum` at a
  representative as `∑ A, branchSummand A`;
* `ResolvedCoproductProperForestData.branchSummand_eq_of_componentChoiceExpansion` — given the vessel
  `E`, `branchSummand A = (branchLeakTerm A + E.primitiveLeak) + E.choiceSum`.

No facade, no flat term, no `forgetHopf`; the product-of-sums itself is deferred to the vessel.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable (D : ResolvedCoproductProperForestData)

/-- The outer (left) leak of one branch summand: `assoc((leftTerm A ⊗ rightTerm A) ⊗ 1)`. -/
noncomputable def ResolvedCoproductProperForestData.branchLeakTerm {G : ResolvedFeynmanGraph}
    (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}) : ResolvedHopfH3 :=
  (Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
    (((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A) ⊗ₜ[ℚ] (1 : ResolvedHopfH))

/-- The branch summand for one outer forest `A`: the outer leak plus the inner left tail. -/
noncomputable def ResolvedCoproductProperForestData.branchSummand {G : ResolvedFeynmanGraph}
    (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}) : ResolvedHopfH3 :=
  D.branchLeakTerm A + D.coassocLeftTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)

/-- `regroupBranchSum` at a representative as the outer sum of `branchSummand` (R-6c-2d-4b-3a,
repackaged with the `branchSummand` definition). -/
theorem ResolvedCoproductProperForestData.regroupBranchSum_eq_branchSummandSum
    (G : ResolvedFeynmanGraph) (hCD : G.forget.toClass.IsConnectedDivergent) :
    D.regroupBranchSum (G.toResolvedHopfGen hCD)
      = ∑ A ∈ (D.supply G).forestCarrier, D.branchSummand A := by
  rw [D.regroupBranchSum_eq_outerSum G hCD]
  rfl

/-- **R-6c-2d-4b-3b — branch summand via the component-choice vessel.**  Given the
`ResolvedComponentChoiceExpansion` for `A` (which splits the inner left tail as `primitiveLeak +
choiceSum`), the branch summand splits as `(outer leak + inner primitive leak) + choiceSum`.  So the
branch side closes once the product-of-sums (the vessel) is supplied. -/
theorem ResolvedCoproductProperForestData.branchSummand_eq_of_componentChoiceExpansion
    {G : ResolvedFeynmanGraph} {A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}}
    (E : ResolvedComponentChoiceExpansion D A) :
    D.branchSummand A = (D.branchLeakTerm A + E.primitiveLeak) + E.choiceSum := by
  unfold ResolvedCoproductProperForestData.branchSummand
  rw [E.expansion]
  abel

end GaugeGeometry.QFT.Combinatorial
