import GaugeGeometry.Applications.Common
import GaugeGeometry.QFT.Representation.GaugeProduct
import GaugeGeometry.QFT.Representation.BetaCoefficients
import GaugeGeometry.QFT.Analytic.RGFlow
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace GaugeGeometry.Applications

noncomputable def alpha3InvPrediction
    (α0 : AlphaInvAt) (μ μ₀ : ℝ) : ℝ :=
  GaugeGeometry.QFT.Analytic.alphaInvRunning
    mssmBetaCoefficients α0 μ μ₀ su3Index

noncomputable def alphaSPrediction
    (α0 : AlphaInvAt) (μ μ₀ : ℝ) : ℝ :=
  1 / alpha3InvPrediction α0 μ μ₀

theorem alpha3InvPrediction_def
    (α0 : AlphaInvAt) (μ μ₀ : ℝ) :
    alpha3InvPrediction α0 μ μ₀ =
      GaugeGeometry.QFT.Analytic.alphaInvRunning
        mssmBetaCoefficients α0 μ μ₀ su3Index := by
  rfl

theorem alpha3InvPrediction_eq_mssm_formula
    (α0 : AlphaInvAt) (μ μ₀ : ℝ) :
    alpha3InvPrediction α0 μ μ₀ =
      α0 su3Index -
        ((((-3 : ℚ) : ℝ) / (2 * Real.pi)) * Real.log (μ / μ₀)) := by
  have hb3 : GaugeGeometry.QFT.Representation.betaTriple su3Index = -3 := by
    simpa using GaugeGeometry.QFT.Representation.betaTriple_b3
  unfold alpha3InvPrediction
  unfold GaugeGeometry.QFT.Analytic.alphaInvRunning
  unfold GaugeGeometry.QFT.Analytic.oneLoopCorrection
  unfold GaugeGeometry.QFT.Analytic.oneLoopSlope
  simp [mssmBetaCoefficients, hb3]

theorem alpha3InvPrediction_at_reference
    (α0 : AlphaInvAt) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) :
    alpha3InvPrediction α0 μ₀ μ₀ = α0 su3Index := by
  unfold alpha3InvPrediction
  simpa using
    congrArg (fun f => f su3Index)
      (GaugeGeometry.QFT.Analytic.alphaInvRunning_at_reference
        mssmBetaCoefficients α0 hμ₀)

theorem alpha3InvPrediction_sub_reference
    (α0 : AlphaInvAt) (μ μ₀ : ℝ) :
    alpha3InvPrediction α0 μ μ₀ - α0 su3Index =
      - (((((-3 : ℚ) : ℝ) / (2 * Real.pi)) * Real.log (μ / μ₀))) := by
  have hb3 : GaugeGeometry.QFT.Representation.betaTriple su3Index = -3 := by
    simpa using GaugeGeometry.QFT.Representation.betaTriple_b3
  have h :=
    GaugeGeometry.QFT.Analytic.alphaInvRunning_sub_reference
      mssmBetaCoefficients α0 μ μ₀ su3Index
  simpa [alpha3InvPrediction, mssmBetaCoefficients, hb3] using h

theorem alphaSPrediction_def
    (α0 : AlphaInvAt) (μ μ₀ : ℝ) :
    alphaSPrediction α0 μ μ₀ = 1 / alpha3InvPrediction α0 μ μ₀ := by
  rfl

/-!
### Sector-indexed one-loop prediction (A)

Lift the SU(3)-specialized `alpha3InvPrediction` to the full
sector-indexed running prediction. This is the prerequisite shape that
any later multiplicative-form rewrite (`(α(μ)/α(μ₀))^γ`) will build on.
-/

/--
Sector-indexed one-loop inverse-coupling prediction, specialized to
the MSSM beta triple.
-/
noncomputable def alphaInvPrediction
    (α0 : AlphaInvAt) (μ μ₀ : ℝ) : GaugeIndex → ℝ :=
  GaugeGeometry.QFT.Analytic.alphaInvRunning mssmBetaCoefficients α0 μ μ₀

theorem alphaInvPrediction_su3_eq
    (α0 : AlphaInvAt) (μ μ₀ : ℝ) :
    alphaInvPrediction α0 μ μ₀ su3Index = alpha3InvPrediction α0 μ μ₀ := by
  rfl

theorem alphaInvPrediction_at_reference
    (α0 : AlphaInvAt) {μ₀ : ℝ} (hμ₀ : 0 < μ₀) :
    alphaInvPrediction α0 μ₀ μ₀ = α0 := by
  simpa [alphaInvPrediction] using
    GaugeGeometry.QFT.Analytic.alphaInvRunning_at_reference
      mssmBetaCoefficients α0 hμ₀

theorem alphaInvPrediction_sub_reference
    (α0 : AlphaInvAt) (μ μ₀ : ℝ) (i : GaugeIndex) :
    alphaInvPrediction α0 μ μ₀ i - α0 i =
      - (GaugeGeometry.QFT.Analytic.oneLoopSlope mssmBetaCoefficients i
          * Real.log (μ / μ₀)) := by
  simpa [alphaInvPrediction] using
    GaugeGeometry.QFT.Analytic.alphaInvRunning_sub_reference
      mssmBetaCoefficients α0 μ μ₀ i

/-!
### Floor initial coupling closure (B)

Inject the geometric floor tuple `(α₁⁻¹, α₂⁻¹, α₃⁻¹) = (60, 30, 8)`
from `Geometric/Arithmetic/FloorValues.lean` into the running
framework as an explicit `AlphaInvAt`. This is the bridge required to
state a physical-consistency theorem that feeds the geometric floor
through the one-loop RG machinery.
-/

/--
The geometric floor `(60, 30, 8)` lifted to a sector-indexed initial
inverse-coupling assignment.
-/
noncomputable def floorInitialAlphaInv : AlphaInvAt :=
  fun i =>
    if i = u1Index then (60 : ℝ)
    else if i = su2Index then (30 : ℝ)
    else (8 : ℝ)

@[simp] theorem floorInitialAlphaInv_u1 :
    floorInitialAlphaInv u1Index = (60 : ℝ) := by
  unfold floorInitialAlphaInv
  rfl

@[simp] theorem floorInitialAlphaInv_su2 :
    floorInitialAlphaInv su2Index = (30 : ℝ) := by
  unfold floorInitialAlphaInv
  have h1 : (su2Index = u1Index) = False := by decide
  simp [h1]

@[simp] theorem floorInitialAlphaInv_su3 :
    floorInitialAlphaInv su3Index = (8 : ℝ) := by
  unfold floorInitialAlphaInv
  have h1 : (su3Index = u1Index) = False := by decide
  have h2 : (su3Index = su2Index) = False := by decide
  simp [h1, h2]

/--
One-loop inverse-coupling prediction starting from the geometric floor.
-/
noncomputable def floorAlphaInvPrediction (μ μ₀ : ℝ) : GaugeIndex → ℝ :=
  alphaInvPrediction floorInitialAlphaInv μ μ₀

/--
SU(3) specialization of the floor-initialized prediction.
-/
noncomputable def floorAlpha3InvPrediction (μ μ₀ : ℝ) : ℝ :=
  alpha3InvPrediction floorInitialAlphaInv μ μ₀

/--
`α_s` prediction starting from the geometric floor.
-/
noncomputable def floorAlphaSPrediction (μ μ₀ : ℝ) : ℝ :=
  alphaSPrediction floorInitialAlphaInv μ μ₀

theorem floorAlphaInvPrediction_at_reference
    {μ₀ : ℝ} (hμ₀ : 0 < μ₀) :
    floorAlphaInvPrediction μ₀ μ₀ = floorInitialAlphaInv := by
  simpa [floorAlphaInvPrediction] using
    alphaInvPrediction_at_reference floorInitialAlphaInv hμ₀

@[simp] theorem floorAlpha3InvPrediction_at_reference
    {μ₀ : ℝ} (hμ₀ : 0 < μ₀) :
    floorAlpha3InvPrediction μ₀ μ₀ = (8 : ℝ) := by
  unfold floorAlpha3InvPrediction
  rw [alpha3InvPrediction_at_reference floorInitialAlphaInv hμ₀]
  simp

theorem floorAlpha3InvPrediction_eq_mssm_formula
    (μ μ₀ : ℝ) :
    floorAlpha3InvPrediction μ μ₀ =
      (8 : ℝ) -
        ((((-3 : ℚ) : ℝ) / (2 * Real.pi)) * Real.log (μ / μ₀)) := by
  unfold floorAlpha3InvPrediction
  rw [alpha3InvPrediction_eq_mssm_formula floorInitialAlphaInv μ μ₀]
  simp

#print axioms alphaInvPrediction_at_reference
#print axioms floorAlpha3InvPrediction_at_reference
#print axioms floorAlpha3InvPrediction_eq_mssm_formula

end GaugeGeometry.Applications
