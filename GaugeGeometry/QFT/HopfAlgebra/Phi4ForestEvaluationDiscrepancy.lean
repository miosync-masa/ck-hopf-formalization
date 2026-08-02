import GaugeGeometry.QFT.HopfAlgebra.Phi4ForestSupportDiscrepancy

/-!
# QFT-R1-body-655 — scheme-parametric evaluated forest discrepancy (the honest numerical bridge)

**Reviewer Q & A (three tiers).**
*653: the two subtraction prescriptions select set-theoretically DIFFERENT admissible forests
(`W‴ ⊊ W″`, witnessed by the marginal Figure-1 forest `phi4CarrierGapOuterForest`).*
*654: the formal forest-support indicator vectors DIFFER — the marginal forest's coefficient is
`1` in `vec(W″)` and `0` in `vec(W‴)`.*
**655: for ANY linear evaluation scheme `amp` on forests, the evaluated difference equals the total
evaluation of the DROPPED sector `∑ A ∈ W″ ∖ W‴, amp A`; hence whenever that dropped-sector total is
nonzero the two numerical results differ.  A concrete coordinate probe on the marginal forest gives the
witness `1 ≠ 0`.**

## Scope note (what this body DOES and does NOT claim)

The evaluator `amp : (admissible forest) → R` is a **pure abstract SOCKET argument** — an arbitrary
`ℚ`-linear-friendly map into a module `R`.  **NOTHING in this file constructs a genuine BPHZ-subtracted
integral, a Feynman-rule amplitude, a coproduct, a character, an antipode, a Rota–Baxter map, or any
body-556 / BPHZ recursion.**  The genuine φ⁴ evaluator campaign is **body-656+**, NOT here.

Consequently the non-cancellation is ALWAYS a **HYPOTHESIS**, never a theorem: the dropped-sector total
being nonzero (`h`), or the marginal weight being nonzero with the rest of the dropped sector vanishing
(`houter` + `hvanish`), is *assumed*.  We do NOT prove `amp phi4CarrierGapOuterForest ≠ 0` from any φ⁴
integral, and we do NOT assert cancellation is absent unconditionally.  What is proved unconditionally is
the exact identity *difference = evaluated dropped sector* and the concrete rational probe `1 ≠ 0`; the
physical conclusion "the number changes" is exactly `difference ≠ 0`, gated on the stated hypothesis.

## Steps (this file = 655)

1. `phi4ForestSupportEvaluate` — the linear evaluator `v ↦ ∑ q • amp A` (definitionally
   `Finsupp.linearCombination ℚ amp`); `phi4ForestSupportEvaluate_indexVector` — evaluating an indicator
   vector is the plain finite sum `∑ A ∈ I, amp A`.  *(AddCommMonoid R.)*
2. `phi4CarrierGap_evaluated_difference_eq_sdiff` — the exact discrepancy identity: the evaluated
   difference `eval(W″) − eval(W‴)` equals the evaluation of the dropped sector `∑ A ∈ W″ ∖ W‴, amp A`.
   *(AddCommGroup R — subtraction.)*
3. `phi4CarrierGapProbeWeight` + `phi4CarrierGap_probe_wDoublePrime`/`_wTriplePrime` — the Figure-1
   coordinate probe over `R := ℚ` reads off `1` on the W″ side and `0` on the W‴ side.
4. **HEADLINE 1** `phi4CarrierGap_concrete_numerical_probe_differs` — a concrete scalar evaluation gives
   `1 ≠ 0`.
5. `phi4CarrierGap_evaluated_difference_of_nonzero_defect_sum` /
   `phi4CarrierGap_evaluated_difference_of_isolated_marginal` — the precise non-cancellation criteria
   under which ANY evaluation scheme's number must differ.  *(AddCommGroup R; the non-cancellation is a
   HYPOTHESIS.)*

## HALT compliance

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`; NO `Lean.ofReduceBool` — NO `native_decide`).
`phi4ForestSupportEvaluate` / `phi4CarrierGapProbeWeight` are `def`s; the `AddCommMonoid` / `AddCommGroup`
/ `Module ℚ R` typeclasses are ASSUMPTIONS on an argument, NOT new instances.  ZERO new
`structure` / `class` / `instance`.  ZERO forbidden divergence classes in ANY declaration type.  No
CONSTRUCTED BPHZ / character / antipode / coproduct / body-556 / amplitude (the disclaiming words appear
only in this scope-note prose).  No `HEq` / `cast` / graph-data `▸`.  No `sorry` / `admit`.  Bodies ≤654
UNEDITED.

**HALT** — the genuine BPHZ / Feynman-rule evaluator is body-656+; `amp` is a socket, and no numerical
non-cancellation is asserted unconditionally here.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical
open scoped BigOperators

set_option linter.unusedVariables false

variable {G : ResolvedFeynmanGraph}

/-! ## Step 1 — the support-vector evaluator + index-vector evaluation rule (AddCommMonoid) -/

/-- **body-655 (Step 1) — the linear forest evaluator.**  Given any per-forest weight
`amp : (admissible forest) → R` valued in a `ℚ`-module `R`, evaluate a forest-support vector by summing
its coefficients against `amp`.  This is definitionally `Finsupp.linearCombination ℚ amp`.  No subtraction
is used, so an `AddCommMonoid` module suffices. -/
noncomputable def phi4ForestSupportEvaluate
    {R : Type*} [AddCommMonoid R] [Module ℚ R]
    (amp : ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily G → R)
    (v : Phi4ForestSupportVector G) : R :=
  v.sum fun A q => q • amp A

/-- **body-655 (Step 1) — evaluating an indicator vector is the plain finite sum.**  The evaluator applied
to the indicator vector of a forest index `I` is `∑ A ∈ I, amp A`.  Route: `phi4ForestSupportEvaluate amp`
is definitionally `Finsupp.linearCombination ℚ amp`; unfold the indicator vector to `∑ A ∈ I, single A 1`,
push the linear map through the sum (`map_sum`), and collapse each term with
`Finsupp.linearCombination_single` + `one_smul`. -/
theorem phi4ForestSupportEvaluate_indexVector
    {R : Type*} [AddCommMonoid R] [Module ℚ R]
    (amp : ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily G → R)
    (I : Finset (ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily G)) :
    phi4ForestSupportEvaluate amp (phi4ForestIndexVector I) = ∑ A ∈ I, amp A := by
  show Finsupp.linearCombination ℚ amp (phi4ForestIndexVector I) = ∑ A ∈ I, amp A
  unfold phi4ForestIndexVector
  rw [map_sum]
  simp only [Finsupp.linearCombination_single, one_smul]

/-! ## Step 2 — exact discrepancy-sector formula (AddCommGroup — subtraction) -/

/-- **body-655 (Step 2) — the exact discrepancy identity.**  For ANY evaluation scheme `amp`, the
evaluated difference between the W″ and W‴ prescriptions equals the total evaluation of the DROPPED
sector `W″ ∖ W‴` (the forests selected by W″ but discarded by the stricter W‴).  Subtraction requires an
`AddCommGroup` module.  Route: rewrite both evaluations with Step 1 and apply
`Finset.sum_sdiff_eq_sub` (whose RHS is `∑ t − ∑ s`) in `.symm` orientation, using the 653a inclusion
`phi4WTriplePrimeIndex ⊆ phi4WDoublePrimeIndex` at the concrete ambient. -/
theorem phi4CarrierGap_evaluated_difference_eq_sdiff
    {R : Type*} [AddCommGroup R] [Module ℚ R]
    (amp : ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily phi4CarrierGapAmbient → R) :
    phi4ForestSupportEvaluate amp (phi4ForestIndexVector (phi4WDoublePrimeIndex phi4CarrierGapAmbient))
        - phi4ForestSupportEvaluate amp
            (phi4ForestIndexVector (phi4WTriplePrimeIndex phi4CarrierGapAmbient))
      = ∑ A ∈ phi4WDoublePrimeIndex phi4CarrierGapAmbient \ phi4WTriplePrimeIndex phi4CarrierGapAmbient,
          amp A := by
  rw [phi4ForestSupportEvaluate_indexVector, phi4ForestSupportEvaluate_indexVector,
    Finset.sum_sdiff_eq_sub (phi4WTriplePrimeIndex_subset_wDoublePrime phi4CarrierGapAmbient)]

/-! ## Step 3 — Figure-1 coordinate probe (R := ℚ) -/

/-- **body-655 (Step 3) — the Figure-1 coordinate probe.**  The rational weight reading off exactly the
marginal Figure-1 forest coordinate: `1` on `phi4CarrierGapOuterForest`, `0` elsewhere.  A pure
coordinate functional — NOT a Feynman-rule amplitude. -/
noncomputable def phi4CarrierGapProbeWeight
    (A : ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily phi4CarrierGapAmbient) : ℚ :=
  if A = phi4CarrierGapOuterForest then 1 else 0

/-- **body-655 (Step 3) — probe on the W″ side reads `1`.**  Via Step 1, `Finset.sum_ite_eq'`, and the
653b-2b W″ membership. -/
theorem phi4CarrierGap_probe_wDoublePrime :
    phi4ForestSupportEvaluate phi4CarrierGapProbeWeight
      (phi4ForestIndexVector (phi4WDoublePrimeIndex phi4CarrierGapAmbient)) = 1 := by
  rw [phi4ForestSupportEvaluate_indexVector]
  simp only [phi4CarrierGapProbeWeight]
  rw [Finset.sum_ite_eq', if_pos phi4CarrierGapOuterForest_mem_wDoublePrime]

/-- **body-655 (Step 3) — probe on the W‴ side reads `0`.**  Via Step 1, `Finset.sum_ite_eq'`, and the
653b-2b W‴ non-membership. -/
theorem phi4CarrierGap_probe_wTriplePrime :
    phi4ForestSupportEvaluate phi4CarrierGapProbeWeight
      (phi4ForestIndexVector (phi4WTriplePrimeIndex phi4CarrierGapAmbient)) = 0 := by
  rw [phi4ForestSupportEvaluate_indexVector]
  simp only [phi4CarrierGapProbeWeight]
  rw [Finset.sum_ite_eq', if_neg phi4CarrierGapOuterForest_not_mem_wTriplePrime]

/-! ## HEADLINE 1 — a concrete scalar evaluation differs (`1 ≠ 0`) -/

/-- **body-655 (HEADLINE 1) — a concrete scalar evaluation of the two prescriptions differs.**  Under the
Figure-1 coordinate probe (`R := ℚ`), the W″ prescription evaluates to `1` and the W‴ prescription to
`0`, so the two numbers are genuinely distinct.  This is the concrete rational witness `1 ≠ 0` behind the
scheme-parametric criterion; it does NOT use, and does NOT construct, any genuine BPHZ amplitude. -/
theorem phi4CarrierGap_concrete_numerical_probe_differs :
    phi4ForestSupportEvaluate phi4CarrierGapProbeWeight
        (phi4ForestIndexVector (phi4WDoublePrimeIndex phi4CarrierGapAmbient))
      ≠ phi4ForestSupportEvaluate phi4CarrierGapProbeWeight
          (phi4ForestIndexVector (phi4WTriplePrimeIndex phi4CarrierGapAmbient)) := by
  rw [phi4CarrierGap_probe_wDoublePrime, phi4CarrierGap_probe_wTriplePrime]
  norm_num

/-! ## Step 4 — physical non-cancellation criteria (AddCommGroup; hypothesised) -/

/-- **body-655 (Step 4) — non-cancellation from a nonzero dropped-sector total.**  For ANY evaluation
scheme `amp`, IF the total evaluation of the dropped sector `W″ ∖ W‴` is nonzero, THEN the two
prescriptions' numerical results differ.  The nonzero-total condition is a HYPOTHESIS on `amp`; no φ⁴
amplitude is constructed here.  Route: reduce the goal to the Step 2 identity and `sub_self`. -/
theorem phi4CarrierGap_evaluated_difference_of_nonzero_defect_sum
    {R : Type*} [AddCommGroup R] [Module ℚ R]
    (amp : ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily phi4CarrierGapAmbient → R)
    (h : (∑ A ∈ phi4WDoublePrimeIndex phi4CarrierGapAmbient
            \ phi4WTriplePrimeIndex phi4CarrierGapAmbient, amp A) ≠ 0) :
    phi4ForestSupportEvaluate amp (phi4ForestIndexVector (phi4WDoublePrimeIndex phi4CarrierGapAmbient))
      ≠ phi4ForestSupportEvaluate amp
          (phi4ForestIndexVector (phi4WTriplePrimeIndex phi4CarrierGapAmbient)) := by
  intro heq
  apply h
  rw [← phi4CarrierGap_evaluated_difference_eq_sdiff, heq, sub_self]

/-- **body-655 (Step 4) — non-cancellation from an isolated marginal weight.**  A physically transparent
sufficient condition: IF the marginal Figure-1 forest carries nonzero weight (`houter`) and every OTHER
forest in the dropped sector evaluates to zero (`hvanish`), THEN the numerical results differ.  Both
`houter` and `hvanish` are HYPOTHESES on the socket `amp` — nothing forces a genuine φ⁴ amplitude to
satisfy them, and no such amplitude is constructed.  Route: `Finset.sum_eq_single_of_mem` collapses the
dropped-sector total to `amp phi4CarrierGapOuterForest` (the marginal forest lies in the dropped sector by
`Finset.mem_sdiff` from the two 653b-2b memberships), then defer to
`phi4CarrierGap_evaluated_difference_of_nonzero_defect_sum`. -/
theorem phi4CarrierGap_evaluated_difference_of_isolated_marginal
    {R : Type*} [AddCommGroup R] [Module ℚ R]
    (amp : ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily phi4CarrierGapAmbient → R)
    (houter : amp phi4CarrierGapOuterForest ≠ 0)
    (hvanish : ∀ A ∈ phi4WDoublePrimeIndex phi4CarrierGapAmbient
        \ phi4WTriplePrimeIndex phi4CarrierGapAmbient,
        A ≠ phi4CarrierGapOuterForest → amp A = 0) :
    phi4ForestSupportEvaluate amp (phi4ForestIndexVector (phi4WDoublePrimeIndex phi4CarrierGapAmbient))
      ≠ phi4ForestSupportEvaluate amp
          (phi4ForestIndexVector (phi4WTriplePrimeIndex phi4CarrierGapAmbient)) := by
  have hmem : phi4CarrierGapOuterForest ∈ phi4WDoublePrimeIndex phi4CarrierGapAmbient
      \ phi4WTriplePrimeIndex phi4CarrierGapAmbient :=
    Finset.mem_sdiff.mpr
      ⟨phi4CarrierGapOuterForest_mem_wDoublePrime, phi4CarrierGapOuterForest_not_mem_wTriplePrime⟩
  have hsum : (∑ A ∈ phi4WDoublePrimeIndex phi4CarrierGapAmbient
          \ phi4WTriplePrimeIndex phi4CarrierGapAmbient, amp A)
      = amp phi4CarrierGapOuterForest :=
    Finset.sum_eq_single_of_mem _ hmem hvanish
  exact phi4CarrierGap_evaluated_difference_of_nonzero_defect_sum amp (by rw [hsum]; exact houter)

end GaugeGeometry.QFT.Combinatorial
