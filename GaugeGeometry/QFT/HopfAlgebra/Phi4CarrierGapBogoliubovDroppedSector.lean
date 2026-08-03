import GaugeGeometry.QFT.HopfAlgebra.Phi4CarrierGapBogoliubovDiscrepancy

/-!
# body-664b (QFT-R2) — the settlement: W″-comparison value, dropped-sector identity, marginal term, numerical criteria

664b is the **settlement**: the W″-comparison value (a comparison SCALAR fixing the SAME `φ₋, φ`
over the broader W″ support — **NOT** a W″ character/coproduct, **NO** W″ recursion fabricated), the
PAPER HEADLINE exact dropped-sector identity
`comparisonValue - φ₊(X gap) = ∑_{W″ ∖ W‴} φ₋(L_F)·φ(R_F)` (655 `sdiff`), the Figure-1 marginal
term (654 coefficient `1`), and the honest numerical criteria (outer weight `≠ 0` + other dropped
weights `= 0`, both HYPOTHESES ⇒ comparison `≠` genuine renormalized character).

The reviewer's answer: the forest-support change **propagates** to the CK-renormalization formula;
the exact difference is the sum of genuine counterterm-times-quotient weights over the dropped
sector; numerical inequality follows **precisely** when that sector does not cancel.

**NO** momentum integral / real amplitude; **nothing** here asserts any weight is nonzero (the outer
weight `≠ 0` and other-weights `= 0` are EXPLICIT HYPOTHESES, never proved).  **NO** singleton
dropped-sector claim.  **NO** antipode / convolution inverse / Laurent series (frontier).  664a / 655
/ 654 / 653b-2b / 662 / 656 are consumed as BLACK BOXES.

## Roadmap
653 forests change → 654 formal coefficient `1 → 0` → 655 scheme-parametric `sdiff` bridge →
656–663 CK character factorization → 664a genuine CK forest-weight discrepancy (DONE) → **664b
settlement (THIS FILE)** → HALT (antipode / convolution inverse / full Hopf frontier).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped BigOperators

open scoped Classical

set_option linter.unusedVariables false

/-- File-scoped re-exposure of the φ⁴ divergence-measure family instance (NOT a permanent/global
instance — scoped to this file exactly as in `Phi4CarrierGapBogoliubovDiscrepancy`), so the W″ / W‴
carrier types elaborate. -/
local instance instPhi4DivergenceMeasureFamily664b : ∀ H : FeynmanGraph, DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

variable {B : Type*} [CommRing B] [Algebra ℚ B]

/-! ## Step 4 — the broader-support comparison value (a comparison SCALAR) -/

/-- **body-664b (Step 4) — the W″-support comparison value.**  This is a COMPARISON SCALAR: it fixes
the SAME `φ₋ = phi4BogoliubovCountertermCharacter S φ` and `φ`, and evaluates the GENUINE CK forest
weight `w(F) = φ₋(L_F)·φ(R_F)` over the BROADER W″ support `phi4WDoublePrimeIndex`.  It is **NOT** a
"W″ coproduct/character" and **NO** W″ Bogoliubov recursion is fabricated — only the SUPPORT differs
from 664a's genuine renormalized formula (which evaluates over the stricter W‴ support).  It isolates
the SUPPORT effect only. -/
noncomputable def phi4CarrierGapWDoublePrimeComparisonValue
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B) : B :=
  phi4BogoliubovCountertermCharacter S φ (MvPolynomial.X phi4CarrierGapStableGen)
    + φ (MvPolynomial.X phi4CarrierGapStableGen)
    + phi4ForestSupportEvaluate (phi4CarrierGapBogoliubovForestWeight S φ)
        (phi4ForestIndexVector (phi4WDoublePrimeIndex phi4CarrierGapAmbient))

/-! ## Step 5 — the exact dropped-sector identity (PAPER HEADLINE) -/

/-- **body-664b (Step 5, PAPER HEADLINE) — the exact dropped-sector identity.**  The difference
between the W″-support comparison value and the GENUINE stable renormalized character on Figure-1's
stable generator equals the genuine CK forest-weight sum over the DROPPED sector `W″ ∖ W‴`:
`comparisonValue - φ₊(X gap) = ∑_{W″ ∖ W‴} φ₋(L_F)·φ(R_F)`.

Route: unfold the comparison value and rewrite `φ₊(X gap)` via 664a's renormalized-character forest
formula, so both are `(c + φ + Eval …)` sharing the leading `c + φ`; the algebra collapses the
leading pair (`add_sub_add_left_eq_sub`, i.e. `(a+b+c) - (a+b+d) = c - d`) to
`Eval(vec W″) - Eval(vec W‴)`, which is exactly 655's `sdiff` identity at
`amp := phi4CarrierGapBogoliubovForestWeight S φ` (`B` is an `AddCommGroup` + `Module ℚ B`).  This is
the reviewer's answer: the support change PROPAGATES to the CK renormalization formula, and the exact
difference is the sum of genuine counterterm-times-quotient weights over the dropped sector. -/
theorem phi4CarrierGap_comparison_minus_renormalized_eq_droppedSector
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B) :
    phi4CarrierGapWDoublePrimeComparisonValue S φ
        - phi4BogoliubovRenormalizedCharacter S φ (MvPolynomial.X phi4CarrierGapStableGen)
      = ∑ A ∈ phi4WDoublePrimeIndex phi4CarrierGapAmbient \ phi4WTriplePrimeIndex phi4CarrierGapAmbient,
          phi4CarrierGapBogoliubovForestWeight S φ A := by
  rw [phi4CarrierGapWDoublePrimeComparisonValue,
      phi4CarrierGap_renormalizedCharacter_eq_forestFormula,
      add_sub_add_left_eq_sub]
  exact phi4CarrierGap_evaluated_difference_eq_sdiff (phi4CarrierGapBogoliubovForestWeight S φ)

/-! ## Step 6 — the Figure-1 marginal term -/

/-- **body-664b (Step 6) — the Figure-1 marginal genuine CK weight.**  The genuine CK forest weight on
the marginal Figure-1 forest `phi4CarrierGapOuterForest` (the W″ member dropped by the stricter W‴)
is the counterterm value of its stable left aggregate times `φ` of its stable forest right term.
Direct from 664a's W″-membership anchor at `phi4CarrierGapOuterForest_mem_wDoublePrime`. -/
theorem phi4CarrierGap_marginalBogoliubovWeight
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B) :
    phi4CarrierGapBogoliubovForestWeight S φ phi4CarrierGapOuterForest
      = phi4BogoliubovCountertermCharacter S φ
          (stableLeftAggregate phi4CarrierGapOuterForest phi4CarrierGapAmbient_stableBoundaryIds)
        * φ (stableForestRightTerm phi4CarrierGapOuterForest
              (phi4WDoublePrimeCanonicalSupply.starOf phi4CarrierGapAmbient phi4CarrierGapOuterForest)
              (phi4WDoublePrimeCanonicalSupply.hCD phi4CarrierGapAmbient phi4CarrierGapOuterForest
                phi4CarrierGapOuterForest_mem_wDoublePrime)
              (stableResolvedBoundaryIds_contractWithStars phi4CarrierGapOuterForest
                (phi4WDoublePrimeCanonicalSupply.starOf phi4CarrierGapAmbient phi4CarrierGapOuterForest)
                phi4CarrierGapAmbient_stableBoundaryIds)) :=
  phi4CarrierGapBogoliubovForestWeight_of_mem_wDoublePrime S φ phi4CarrierGapOuterForest
    phi4CarrierGapOuterForest_mem_wDoublePrime

/-- **body-664b (Step 6) — the marginal renormalization contribution.**  The 654 subtraction-channel
defect coefficient of the marginal Figure-1 forest is exactly `1` (`ℚ`-valued Finsupp coordinate of
`vec W″ - vec W‴`), so scaling the genuine marginal weight by that coefficient leaves it unchanged:
`1 • w(Outer) = w(Outer)`.  Via 654's `phi4CarrierGap_formal_subtraction_defect_coefficient` + `one_smul`. -/
theorem phi4CarrierGap_marginalRenormalizationContribution
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B) :
    ((phi4ForestIndexVector (phi4WDoublePrimeIndex phi4CarrierGapAmbient)
        - phi4ForestIndexVector (phi4WTriplePrimeIndex phi4CarrierGapAmbient)) phi4CarrierGapOuterForest)
        • phi4CarrierGapBogoliubovForestWeight S φ phi4CarrierGapOuterForest
      = phi4CarrierGapBogoliubovForestWeight S φ phi4CarrierGapOuterForest := by
  rw [phi4CarrierGap_formal_subtraction_defect_coefficient, one_smul]

/-! ## Step 7 — honest numerical criteria -/

/-- **body-664b (Step 7) — numerical criterion: nonzero dropped sector.**  If the genuine CK
forest-weight sum over the DROPPED sector `W″ ∖ W‴` is nonzero, then the W″-support comparison value
differs from the genuine stable renormalized character.  The nonvanishing hypothesis `h` is EXPLICIT
— never proved.  Via `sub_ne_zero` + the Step-5 PAPER HEADLINE identity. -/
theorem phi4CarrierGap_bogoliubov_difference_of_nonzero_droppedSector
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (h : (∑ A ∈ phi4WDoublePrimeIndex phi4CarrierGapAmbient \ phi4WTriplePrimeIndex phi4CarrierGapAmbient,
            phi4CarrierGapBogoliubovForestWeight S φ A) ≠ 0) :
    phi4CarrierGapWDoublePrimeComparisonValue S φ
      ≠ phi4BogoliubovRenormalizedCharacter S φ (MvPolynomial.X phi4CarrierGapStableGen) := by
  rw [← sub_ne_zero, phi4CarrierGap_comparison_minus_renormalized_eq_droppedSector]
  exact h

/-- **body-664b (Step 7) — numerical criterion: isolated marginal.**  If the genuine marginal Figure-1
weight is nonzero (`houter`) and every OTHER dropped forest has zero weight (`hvanish`), then the
dropped-sector sum collapses to the single marginal weight (which is nonzero), so the W″-support
comparison value differs from the genuine stable renormalized character.  BOTH `houter` (outer weight
`≠ 0`) and `hvanish` (other dropped weights `= 0`) are EXPLICIT HYPOTHESES — never proved; this does
NOT claim the dropped sector `W″ ∖ W‴` is a singleton.  Via `Finset.sum_eq_single_of_mem` +
`Finset.mem_sdiff` (653b-2b Outer mem/not-mem) + the previous criterion. -/
theorem phi4CarrierGap_bogoliubov_difference_of_isolated_marginal
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (houter : phi4CarrierGapBogoliubovForestWeight S φ phi4CarrierGapOuterForest ≠ 0)
    (hvanish : ∀ A ∈ phi4WDoublePrimeIndex phi4CarrierGapAmbient \ phi4WTriplePrimeIndex phi4CarrierGapAmbient,
        A ≠ phi4CarrierGapOuterForest → phi4CarrierGapBogoliubovForestWeight S φ A = 0) :
    phi4CarrierGapWDoublePrimeComparisonValue S φ
      ≠ phi4BogoliubovRenormalizedCharacter S φ (MvPolynomial.X phi4CarrierGapStableGen) := by
  apply phi4CarrierGap_bogoliubov_difference_of_nonzero_droppedSector
  have hmem : phi4CarrierGapOuterForest
      ∈ phi4WDoublePrimeIndex phi4CarrierGapAmbient \ phi4WTriplePrimeIndex phi4CarrierGapAmbient :=
    Finset.mem_sdiff.mpr ⟨phi4CarrierGapOuterForest_mem_wDoublePrime,
      phi4CarrierGapOuterForest_not_mem_wTriplePrime⟩
  rw [Finset.sum_eq_single_of_mem phi4CarrierGapOuterForest hmem hvanish]
  exact houter

end GaugeGeometry.QFT.Combinatorial
