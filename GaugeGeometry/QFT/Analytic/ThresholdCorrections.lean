/-
  QFT/Analytic/ThresholdCorrections.lean

  Symbolic threshold-style refinement of the integrated one-loop
  picture. The file stays deliberately thin: Task v3 §9.4 keeps
  threshold effects out of the core one-loop theorem, but reserves a
  place for `Applications` to opt in without touching the RGFlow
  formulation.
-/
import GaugeGeometry.QFT.Analytic.RGFlow
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace GaugeGeometry.QFT.Analytic

/-!
### Threshold profile

A `ThresholdProfile` carries a per-sector additive correction `shift i`
applied to the bare integrated one-loop running. The `trivial` profile
has zero shift and collapses threshold-corrected running back to the
bare formula.
-/

/--
Per-sector additive threshold correction profile.
Concrete threshold schemes (e.g. `M_SUSY`-style matching) specialize
`shift` to their matching logarithms.
-/
structure ThresholdProfile where
  shift : GaugeIndex → ℝ

/-- Trivial threshold profile: zero correction in every sector. -/
def ThresholdProfile.trivial : ThresholdProfile where
  shift := fun _ => 0

@[simp] theorem ThresholdProfile.trivial_shift (i : GaugeIndex) :
    ThresholdProfile.trivial.shift i = 0 := rfl

/--
Threshold-corrected inverse-coupling running.
Defined additively so that matching identities reduce to the bare
`alphaInvRunning` when the threshold profile is `trivial`.
-/
noncomputable def alphaInvRunning_with_threshold
    (b : BetaCoefficients) (α0 : AlphaInvAt) (μ μ₀ : ℝ)
    (T : ThresholdProfile) : GaugeIndex → ℝ :=
  fun i => alphaInvRunning b α0 μ μ₀ i + T.shift i

/--
Matching identity: at the trivial profile, the threshold-corrected
running agrees with the bare `alphaInvRunning`.
-/
theorem alphaInvRunning_with_threshold_trivial
    (b : BetaCoefficients) (α0 : AlphaInvAt) (μ μ₀ : ℝ) :
    alphaInvRunning_with_threshold b α0 μ μ₀ ThresholdProfile.trivial
      = alphaInvRunning b α0 μ μ₀ := by
  funext i
  simp [alphaInvRunning_with_threshold]

/--
Sector-level difference between threshold-corrected and bare running
equals the profile shift.
-/
theorem alphaInvRunning_with_threshold_sub_bare
    (b : BetaCoefficients) (α0 : AlphaInvAt) (μ μ₀ : ℝ)
    (T : ThresholdProfile) (i : GaugeIndex) :
    alphaInvRunning_with_threshold b α0 μ μ₀ T i
      - alphaInvRunning b α0 μ μ₀ i = T.shift i := by
  simp [alphaInvRunning_with_threshold]

/--
Matching composition: stacking two threshold profiles corresponds to
adding their per-sector shifts.
-/
theorem alphaInvRunning_with_threshold_add
    (b : BetaCoefficients) (α0 : AlphaInvAt) (μ μ₀ : ℝ)
    (T₁ T₂ : ThresholdProfile) (i : GaugeIndex) :
    alphaInvRunning_with_threshold b α0 μ μ₀
        { shift := fun j => T₁.shift j + T₂.shift j } i
      = alphaInvRunning_with_threshold b α0 μ μ₀ T₁ i + T₂.shift i := by
  simp [alphaInvRunning_with_threshold, add_assoc]

end GaugeGeometry.QFT.Analytic
