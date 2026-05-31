import GaugeGeometry.QFT.Analytic.RGFlow
import GaugeGeometry.QFT.Analytic.LogIdentities
import GaugeGeometry.QFT.Representation.BetaCoefficients
import GaugeGeometry.QFT.Representation.GaugeProduct
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace GaugeGeometry.QFT.Analytic

abbrev u1Index := GaugeGeometry.QFT.Representation.u1Index
abbrev su2Index := GaugeGeometry.QFT.Representation.su2Index
abbrev su3Index := GaugeGeometry.QFT.Representation.su3Index

/--
MSSM-specialized one-loop running of inverse gauge couplings.
-/
noncomputable def mssmAlphaInvRunning
    (α0 : AlphaInvAt) (μ μ₀ : ℝ) : GaugeIndex → ℝ :=
  alphaInvRunning GaugeGeometry.QFT.Representation.betaTriple α0 μ μ₀

/--
Theorem 2, canonically restated for the MSSM beta triple.
-/
theorem integrated_one_loop_running
    (α0 : AlphaInvAt) (μ μ₀ : ℝ) :
    mssmAlphaInvRunning α0 μ μ₀
      = fun i =>
          α0 i -
            (((GaugeGeometry.QFT.Representation.betaTriple i : ℚ) : ℝ)
              / (2 * Real.pi) * Real.log (μ / μ₀)) := by
  simpa [mssmAlphaInvRunning] using
    integrated_one_loop_rg_running
      GaugeGeometry.QFT.Representation.betaTriple α0 μ μ₀

/--
At the reference scale, MSSM one-loop running collapses to the input coupling.
-/
theorem mssmAlphaInvRunning_at_reference
    (α0 : AlphaInvAt) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) :
    mssmAlphaInvRunning α0 μ₀ μ₀ = α0 := by
  simpa [mssmAlphaInvRunning] using
    alphaInvRunning_at_reference
      GaugeGeometry.QFT.Representation.betaTriple α0 hμ₀

/--
Difference form specialized to the MSSM beta triple.
-/
theorem mssmAlphaInvRunning_sub_reference
    (α0 : AlphaInvAt) (μ μ₀ : ℝ) (i : GaugeIndex) :
    mssmAlphaInvRunning α0 μ μ₀ i - α0 i
      = - (oneLoopSlope GaugeGeometry.QFT.Representation.betaTriple i
            * Real.log (μ / μ₀)) := by
  simpa [mssmAlphaInvRunning, oneLoopSlope] using
    alphaInvRunning_sub_reference
      GaugeGeometry.QFT.Representation.betaTriple α0 μ μ₀ i

/--
Sectorwise sign of the MSSM one-loop slope: U(1) is positive.
-/
theorem oneLoopSlope_u1_positive :
    0 < oneLoopSlope GaugeGeometry.QFT.Representation.betaTriple u1Index := by
  rw [oneLoopSlope, GaugeGeometry.QFT.Representation.betaTriple_b1]
  positivity

/--
Sectorwise sign of the MSSM one-loop slope: SU(2) is positive.
-/
theorem oneLoopSlope_su2_positive :
    0 < oneLoopSlope GaugeGeometry.QFT.Representation.betaTriple su2Index := by
  rw [oneLoopSlope, GaugeGeometry.QFT.Representation.betaTriple_b2]
  positivity

/--
Sectorwise sign of the MSSM one-loop slope: SU(3) is negative.
-/
theorem oneLoopSlope_su3_negative :
    oneLoopSlope GaugeGeometry.QFT.Representation.betaTriple su3Index < 0 := by
  rw [oneLoopSlope, GaugeGeometry.QFT.Representation.betaTriple_b3]
  have hp : 0 < (3 : ℝ) / (2 * Real.pi) := by
    positivity
  have hEq : ((((-3 : ℚ) : ℝ) / (2 * Real.pi))) = - ((3 : ℝ) / (2 * Real.pi)) := by
    ring
  rw [hEq]
  linarith

/--
For positive logarithmic scale separation, the U(1) inverse coupling decreases.
-/
theorem u1_running_lt_reference_of_log_pos
    (α0 : AlphaInvAt) {μ μ₀ : ℝ}
    (hlog : 0 < Real.log (μ / μ₀)) :
    mssmAlphaInvRunning α0 μ μ₀ u1Index < α0 u1Index := by
  have hsub :
      mssmAlphaInvRunning α0 μ μ₀ u1Index - α0 u1Index
        = - (oneLoopSlope GaugeGeometry.QFT.Representation.betaTriple u1Index
              * Real.log (μ / μ₀)) := by
    simpa using mssmAlphaInvRunning_sub_reference α0 μ μ₀ u1Index
  have hmul :
      0 < oneLoopSlope GaugeGeometry.QFT.Representation.betaTriple u1Index
            * Real.log (μ / μ₀) := by
    exact mul_pos oneLoopSlope_u1_positive hlog
  have hneg :
      - (oneLoopSlope GaugeGeometry.QFT.Representation.betaTriple u1Index
          * Real.log (μ / μ₀)) < 0 := by
    linarith
  linarith

/--
For positive logarithmic scale separation, the SU(2) inverse coupling decreases.
-/
theorem su2_running_lt_reference_of_log_pos
    (α0 : AlphaInvAt) {μ μ₀ : ℝ}
    (hlog : 0 < Real.log (μ / μ₀)) :
    mssmAlphaInvRunning α0 μ μ₀ su2Index < α0 su2Index := by
  have hsub :
      mssmAlphaInvRunning α0 μ μ₀ su2Index - α0 su2Index
        = - (oneLoopSlope GaugeGeometry.QFT.Representation.betaTriple su2Index
              * Real.log (μ / μ₀)) := by
    simpa using mssmAlphaInvRunning_sub_reference α0 μ μ₀ su2Index
  have hmul :
      0 < oneLoopSlope GaugeGeometry.QFT.Representation.betaTriple su2Index
            * Real.log (μ / μ₀) := by
    exact mul_pos oneLoopSlope_su2_positive hlog
  have hneg :
      - (oneLoopSlope GaugeGeometry.QFT.Representation.betaTriple su2Index
          * Real.log (μ / μ₀)) < 0 := by
    linarith
  linarith

/--
For positive logarithmic scale separation, the SU(3) inverse coupling increases
(asymptotic freedom at one loop in inverse-coupling form).
-/
theorem su3_running_gt_reference_of_log_pos
    (α0 : AlphaInvAt) {μ μ₀ : ℝ}
    (hlog : 0 < Real.log (μ / μ₀)) :
    α0 su3Index < mssmAlphaInvRunning α0 μ μ₀ su3Index := by
  have hsub :
      mssmAlphaInvRunning α0 μ μ₀ su3Index - α0 su3Index
        = - (oneLoopSlope GaugeGeometry.QFT.Representation.betaTriple su3Index
              * Real.log (μ / μ₀)) := by
    simpa using mssmAlphaInvRunning_sub_reference α0 μ μ₀ su3Index
  have hmul :
      oneLoopSlope GaugeGeometry.QFT.Representation.betaTriple su3Index
        * Real.log (μ / μ₀) < 0 := by
    exact mul_neg_of_neg_of_pos oneLoopSlope_su3_negative hlog
  have hpos :
      0 < - (oneLoopSlope GaugeGeometry.QFT.Representation.betaTriple su3Index
              * Real.log (μ / μ₀)) := by
    exact neg_pos.mpr hmul
  linarith

/--
Reference-scale collapse, specialized per sector.
-/
@[simp] theorem mssmAlphaInvRunning_at_reference_u1
    (α0 : AlphaInvAt) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) :
    mssmAlphaInvRunning α0 μ₀ μ₀ u1Index = α0 u1Index := by
  simpa using congrArg (fun f => f u1Index)
    (mssmAlphaInvRunning_at_reference α0 hμ₀)

@[simp] theorem mssmAlphaInvRunning_at_reference_su2
    (α0 : AlphaInvAt) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) :
    mssmAlphaInvRunning α0 μ₀ μ₀ su2Index = α0 su2Index := by
  simpa using congrArg (fun f => f su2Index)
    (mssmAlphaInvRunning_at_reference α0 hμ₀)

@[simp] theorem mssmAlphaInvRunning_at_reference_su3
    (α0 : AlphaInvAt) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) :
    mssmAlphaInvRunning α0 μ₀ μ₀ su3Index = α0 su3Index := by
  simpa using congrArg (fun f => f su3Index)
    (mssmAlphaInvRunning_at_reference α0 hμ₀)

end GaugeGeometry.QFT.Analytic
