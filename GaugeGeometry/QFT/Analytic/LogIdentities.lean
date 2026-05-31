import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace GaugeGeometry.QFT.Analytic

/--
The logarithm of a reference-scale ratio vanishes.
-/
theorem log_ref_zero {μ₀ : ℝ} (hμ₀ : 0 < μ₀) :
    Real.log (μ₀ / μ₀) = 0 := by
  have hne : μ₀ ≠ 0 := ne_of_gt hμ₀
  simp [div_self hne]

/--
The logarithm of a positive ratio splits into a difference of logarithms.
-/
theorem log_ratio_identity {μ μ₀ : ℝ} (hμ : 0 < μ) (hμ₀ : 0 < μ₀) :
    Real.log (μ / μ₀) = Real.log μ - Real.log μ₀ := by
  have hμne : μ ≠ 0 := ne_of_gt hμ
  have hμ₀ne : μ₀ ≠ 0 := ne_of_gt hμ₀
  simpa using Real.log_div hμne hμ₀ne

/--
The logarithm of the inverse ratio flips sign.
-/
theorem log_ratio_swap_neg {μ μ₀ : ℝ} (hμ : 0 < μ) (hμ₀ : 0 < μ₀) :
    Real.log (μ₀ / μ) = - Real.log (μ / μ₀) := by
  rw [log_ratio_identity hμ₀ hμ, log_ratio_identity hμ hμ₀]
  ring

/--
Scaling the numerator by the reference scale removes the denominator inside the logarithm.
-/
theorem log_scaling_identity {x μ₀ : ℝ} (hx : 0 < x) (hμ₀ : 0 < μ₀) :
    Real.log ((x * μ₀) / μ₀) = Real.log x := by
  have hne : μ₀ ≠ 0 := ne_of_gt hμ₀
  rw [show ((x * μ₀) / μ₀ : ℝ) = x by field_simp [hne]]

/--
A convenient zero test at unit ratio.
-/
@[simp] theorem log_one_ratio :
    Real.log (1 : ℝ) = 0 := by
  exact Real.log_one

/--
The logarithm of a positive ratio is antisymmetric under exchanging the scales.
-/
theorem log_ratio_antisymm {μ μ₀ : ℝ} (hμ : 0 < μ) (hμ₀ : 0 < μ₀) :
    Real.log (μ / μ₀) + Real.log (μ₀ / μ) = 0 := by
  rw [log_ratio_swap_neg hμ hμ₀]
  ring

end GaugeGeometry.QFT.Analytic
