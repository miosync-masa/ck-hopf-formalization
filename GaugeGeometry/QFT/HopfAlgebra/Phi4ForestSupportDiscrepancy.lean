import GaugeGeometry.QFT.HopfAlgebra.Phi4WDoubleTriplePrimeStrictness
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# QFT-R1-body-654 — "Does the computation change?" a formal forest-support discrepancy

**Reviewer Q & A.**  *Q: The two subtraction prescriptions W″ and W‴ are set-theoretically distinct
(body-653b-2b: `W‴ ⊊ W″`, witnessed by the marginal Figure-1 forest `phi4CarrierGapOuterForest`).  But
does the actual computation change — do the two prescriptions produce different formal forest sums?*

**A: Yes — the two prescriptions produce distinct formal forest sums.**  Representing each finite forest
index as its indicator vector in the free ℚ-vector space over the forest-index type (an `A ↦ 1` per
selected forest, packaged as a `Finsupp`), the marginal forest of Figure 1 has coefficient **one** in the
W″ vector and **zero** in the W‴ vector.  Hence the two indicator vectors differ, and the
subtraction-channel defect `v(W″) − v(W‴)` carries coefficient `1` exactly on that marginal forest.

## Scope note (what this body DOES and does NOT claim)

This is a **FORMAL** coefficient statement about the forest-index indicator vector / subtraction-channel
support.  It says the formal forest-sum coefficient of `phi4CarrierGapOuterForest` genuinely changes
between the two prescriptions.  It is **NOT** a claim that the numerically-evaluated amplitude, the
BPHZ-subtracted integral, or any Feynman-rule evaluation differs — there is NO evaluation map, NO
Feynman-rule evaluator, NO coproduct, NO body-556, NO BPHZ integral in this file.  Lifting this formal
coefficient difference to a numerical-amplitude statement is body-655.  This is the first step of a
carrier-geometry → renormalization-calculation chain.

## Steps (this file = 654)

1. `phi4ForestIndexVector_apply` — the general indicator rule: the coefficient of a forest `A` in the
   indicator vector of an index `I` is `if A ∈ I then 1 else 0` (a standard `Finsupp.finset_sum_apply` /
   `Finsupp.single_apply` / `Finset.sum_ite_eq'` collapse).
2. The two concrete coefficients: `1` in W″ (via `if_pos` on the 653b-2b membership), `0` in W‴ (via
   `if_neg` on the 653b-2b non-membership).
3. **HEADLINE** — the two indicator vectors differ (`DFunLike.congr_fun` at the marginal forest +
   `1 ≠ 0`); and the subtraction-channel defect coefficient at the marginal forest is exactly `1`
   (`Finsupp.sub_apply` + `1 − 0 = 1`).

## HALT compliance

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`; NO `Lean.ofReduceBool` — NO `native_decide`).
`Phi4ForestSupportVector` is an `abbrev`, `phi4ForestIndexVector` a `def`; ZERO new `structure` / `class` /
`instance` (`DecidableEq` for the forest-index type and the `if _ ∈ _` decidability come from
`open scoped Classical`).  ZERO forbidden divergence classes in ANY declaration type.  No evaluation map /
Feynman-rule evaluator / coproduct / body-556 / BPHZ / amplitude claim.  No `HEq` / `cast` / graph-data
`▸` (the only rewrites are on `Prop`-level membership and `Finsupp`-apply equalities).  No
`native_decide` / `Lean.ofReduceBool`; no `sorry` / `admit`.  Bodies ≤653b-2b UNEDITED.

**HALT** — the numerical-amplitude lift is body-655; it is NOT attempted here.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical
open scoped BigOperators

set_option linter.unusedVariables false

variable {G : ResolvedFeynmanGraph}

/-- **body-654 — the free ℚ-vector space over the φ⁴ forest-index type.**  The support carrier of the
formal forest sum / subtraction channel: functions with finite support from the forest-index type of `G`
to ℚ.  (An `abbrev`, not a new structure.) -/
abbrev Phi4ForestSupportVector (G : ResolvedFeynmanGraph) :=
  ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily G →₀ ℚ

/-- **body-654 — the indicator vector of a finite forest index.**  Each selected forest `A` contributes
`Finsupp.single A 1`; the sum is the formal forest sum with unit coefficients. -/
noncomputable def phi4ForestIndexVector
    (I : Finset (ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily G)) :
    Phi4ForestSupportVector G :=
  ∑ A ∈ I, Finsupp.single A 1

/-! ## Step 1 — the general coefficient rule -/

/-- **body-654 (Step 1) — the indicator-vector coefficient rule.**  The coefficient of a forest `A` in the
indicator vector of an index `I` is `1` if `A ∈ I` and `0` otherwise.  Pure `Finsupp` indicator algebra:
push evaluation through the finite sum (`Finsupp.finset_sum_apply`), expand each `single`
(`Finsupp.single_apply`), and collapse the resulting equality-test sum (`Finset.sum_ite_eq'`). -/
theorem phi4ForestIndexVector_apply
    (I : Finset (ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily G))
    (A : ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily G) :
    phi4ForestIndexVector I A = if A ∈ I then 1 else 0 := by
  classical
  unfold phi4ForestIndexVector
  rw [Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq']

/-! ## Step 2 — the two concrete coefficients -/

/-- **body-654 (Step 2) — the marginal Figure-1 forest has coefficient `1` in the W″ indicator vector.**
Via Step 1 and the 653b-2b W″ membership. -/
theorem phi4CarrierGap_wDoublePrime_coefficient :
    phi4ForestIndexVector (phi4WDoublePrimeIndex phi4CarrierGapAmbient)
      phi4CarrierGapOuterForest = 1 := by
  rw [phi4ForestIndexVector_apply, if_pos phi4CarrierGapOuterForest_mem_wDoublePrime]

/-- **body-654 (Step 2) — the marginal Figure-1 forest has coefficient `0` in the W‴ indicator vector.**
Via Step 1 and the 653b-2b W‴ non-membership (the `h03` fifth-axis failure). -/
theorem phi4CarrierGap_wTriplePrime_coefficient :
    phi4ForestIndexVector (phi4WTriplePrimeIndex phi4CarrierGapAmbient)
      phi4CarrierGapOuterForest = 0 := by
  rw [phi4ForestIndexVector_apply, if_neg phi4CarrierGapOuterForest_not_mem_wTriplePrime]

/-! ## Step 3 — HEADLINE (the vectors differ) + the defect coefficient -/

/-- **body-654 (HEADLINE) — the two prescriptions produce distinct formal forest sums.**  The W″ and W‴
indicator vectors of the concrete φ⁴ ambient are NOT equal: they already disagree at the marginal Figure-1
forest, where the coefficient is `1` in W″ and `0` in W‴.  This is the FORMAL forest-sum / subtraction-
channel coefficient difference — NOT a numerical-amplitude claim (that is body-655). -/
theorem phi4CarrierGap_formal_subtraction_support_differs :
    phi4ForestIndexVector (phi4WDoublePrimeIndex phi4CarrierGapAmbient)
      ≠ phi4ForestIndexVector (phi4WTriplePrimeIndex phi4CarrierGapAmbient) := by
  intro h
  have hc := DFunLike.congr_fun h phi4CarrierGapOuterForest
  rw [phi4CarrierGap_wDoublePrime_coefficient, phi4CarrierGap_wTriplePrime_coefficient] at hc
  exact absurd hc (by norm_num)

/-- **body-654 — the subtraction-channel defect coefficient.**  The difference of the two indicator
vectors carries coefficient exactly `1` at the marginal Figure-1 forest — the precise formal forest that
distinguishes the W″ prescription from the W‴ prescription. -/
theorem phi4CarrierGap_formal_subtraction_defect_coefficient :
    (phi4ForestIndexVector (phi4WDoublePrimeIndex phi4CarrierGapAmbient)
       - phi4ForestIndexVector (phi4WTriplePrimeIndex phi4CarrierGapAmbient))
      phi4CarrierGapOuterForest = 1 := by
  rw [Finsupp.sub_apply, phi4CarrierGap_wDoublePrime_coefficient,
    phi4CarrierGap_wTriplePrime_coefficient, sub_zero]

end GaugeGeometry.QFT.Combinatorial
