import GaugeGeometry.QFT.Representation.GaugeProduct
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace GaugeGeometry.QFT.Analytic

abbrev GaugeIndex := GaugeGeometry.QFT.Representation.GaugeIndex
abbrev BetaCoefficients := GaugeIndex → ℚ
abbrev AlphaInvAt := GaugeIndex → ℝ

noncomputable def oneLoopSlope (b : BetaCoefficients) (i : GaugeIndex) : ℝ :=
  ((b i : ℝ) / (2 * Real.pi))

noncomputable def oneLoopCorrection (b : BetaCoefficients) (μ μ₀ : ℝ) (i : GaugeIndex) : ℝ :=
  oneLoopSlope b i * Real.log (μ / μ₀)

noncomputable def alphaInvRunning (b : BetaCoefficients) (α0 : AlphaInvAt) (μ μ₀ : ℝ) :
    GaugeIndex → ℝ :=
  fun i => α0 i - oneLoopCorrection b μ μ₀ i

theorem integrated_one_loop_rg_running
    (b : BetaCoefficients) (α0 : AlphaInvAt) (μ μ₀ : ℝ) :
    alphaInvRunning b α0 μ μ₀
      = fun i => α0 i - (((b i : ℝ) / (2 * Real.pi)) * Real.log (μ / μ₀)) := by
  funext i
  rfl

theorem alphaInvRunning_at_reference
    (b : BetaCoefficients) (α0 : AlphaInvAt) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) :
    alphaInvRunning b α0 μ₀ μ₀ = α0 := by
  funext i
  unfold alphaInvRunning oneLoopCorrection oneLoopSlope
  have hne : (μ₀ : ℝ) ≠ 0 := ne_of_gt hμ₀
  rw [show (μ₀ / μ₀ : ℝ) = 1 by field_simp [hne]]
  rw [Real.log_one]
  ring

theorem alphaInvRunning_sub_reference
    (b : BetaCoefficients) (α0 : AlphaInvAt) (μ μ₀ : ℝ) (i : GaugeIndex) :
    alphaInvRunning b α0 μ μ₀ i - α0 i
      = - (((b i : ℝ) / (2 * Real.pi)) * Real.log (μ / μ₀)) := by
  unfold alphaInvRunning oneLoopCorrection oneLoopSlope
  ring

theorem alphaInvRunning_congr_beta
    {b₁ b₂ : BetaCoefficients} (hb : b₁ = b₂)
    (α0 : AlphaInvAt) (μ μ₀ : ℝ) :
    alphaInvRunning b₁ α0 μ μ₀ = alphaInvRunning b₂ α0 μ μ₀ := by
  subst hb
  rfl

end GaugeGeometry.QFT.Analytic
