import GaugeGeometry.Applications.Common
import GaugeGeometry.Core.Sector
import GaugeGeometry.Applications.QuarkMassRatios
import GaugeGeometry.QFT.Representation.GaugeProduct
import GaugeGeometry.QFT.Representation.SectorFactorization
import GaugeGeometry.QFT.Representation.BetaCoefficients
import GaugeGeometry.QFT.Analytic.RGFlow
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace GaugeGeometry.Applications

abbrev SectorWeights := GaugeGeometry.Core.SectorWeights

abbrev GenerationSectorWeights := Fin 3 → SectorWeights

def weakFactor (w : SectorWeights) : ℚ :=
  GaugeGeometry.QFT.Representation.electroweakWeight w

def colorFactor (w : SectorWeights) : ℚ :=
  w.color

def massRatioFromSectorWeights (w : SectorWeights) : ℚ :=
  weakFactor w * colorFactor w

/--
Lift the weak × color decomposition from a single sector-weight record
to a generation-indexed mass-ratio factor.
-/
def generationFactorFromSectorWeights (W : GenerationSectorWeights) : GenerationFactor :=
  fun g => massRatioFromSectorWeights (W g)

/--
Minimal generation-level pattern used to recover the channel-factorized
shape `f₁ = 1`, `f₂ = k`, `f₃ = k · N_c`.

Interpretation:
- generation 0 is normalized to `1 = 1 × 1`
- generations 1 and 2 share the same electroweak baseline `k`
- the color channel is trivial for generation 1 and contributes `N_c`
  for generation 2
-/
def WeakUniformColorScaled
    (W : GenerationSectorWeights) (k N_c : ℚ) : Prop :=
  weakFactor (W 0) = 1 ∧
    colorFactor (W 0) = 1 ∧
    weakFactor (W 1) = k ∧
    weakFactor (W 2) = k ∧
    colorFactor (W 1) = 1 ∧
    colorFactor (W 2) = N_c

theorem mass_ratio_decomposition_from_sector_weights
    (w : SectorWeights) :
    massRatioFromSectorWeights w = weakFactor w * colorFactor w := by
  rfl

theorem massRatioFromSectorWeights_eq_fullWeight
    (w : SectorWeights) :
    massRatioFromSectorWeights w =
      GaugeGeometry.QFT.Representation.fullWeight w := by
  rfl

theorem massRatioFromSectorWeights_eq_factorized
    (w : SectorWeights) :
    massRatioFromSectorWeights w =
      GaugeGeometry.QFT.Representation.electroweakWeight w * w.color := by
  exact GaugeGeometry.QFT.Representation.direct_product_sector_factorization w

/--
Under the uniform-weak/color-scaled generation pattern, the induced
generation factor has the channel-factorized shape needed downstream.
-/
theorem generationFactorFromSectorWeights_shape
    (W : GenerationSectorWeights) (k N_c : ℚ)
    (hPattern : WeakUniformColorScaled W k N_c) :
    generationFactorFromSectorWeights W 0 = 1 ∧
      generationFactorFromSectorWeights W 1 = k ∧
      generationFactorFromSectorWeights W 2 = k * N_c := by
  rcases hPattern with ⟨hWeak0, hColor0, hWeak1, hWeak2, hColor1, hColor2⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold generationFactorFromSectorWeights massRatioFromSectorWeights
    rw [hWeak0, hColor0]
    norm_num
  · unfold generationFactorFromSectorWeights massRatioFromSectorWeights
    rw [hWeak1, hColor1]
    ring
  · unfold generationFactorFromSectorWeights massRatioFromSectorWeights
    rw [hWeak2, hColor2]

/--
The second-generation factor is nonzero as soon as the shared weak
baseline `k` is nonzero.
-/
theorem generationFactorFromSectorWeights_second_nonzero
    (W : GenerationSectorWeights) (k N_c : ℚ)
    (hPattern : WeakUniformColorScaled W k N_c)
    (hk : k ≠ 0) :
    generationFactorFromSectorWeights W 1 ≠ 0 := by
  rcases generationFactorFromSectorWeights_shape W k N_c hPattern with ⟨_h0, h1, _h2⟩
  simpa [h1] using hk

noncomputable def weakRunningFactor
    (w : SectorWeights) (α0 : AlphaInvAt) (μ μ₀ : ℝ) : ℝ :=
  ((w.weak : ℝ) *
      GaugeGeometry.QFT.Analytic.alphaInvRunning mssmBetaCoefficients α0 μ μ₀ su2Index) *
  ((w.hypercharge : ℝ) *
      GaugeGeometry.QFT.Analytic.alphaInvRunning mssmBetaCoefficients α0 μ μ₀ u1Index)

noncomputable def colorRunningFactor
    (w : SectorWeights) (α0 : AlphaInvAt) (μ μ₀ : ℝ) : ℝ :=
  (w.color : ℝ) *
    GaugeGeometry.QFT.Analytic.alphaInvRunning mssmBetaCoefficients α0 μ μ₀ su3Index

noncomputable def runningMassRatioFromSectorWeights
    (w : SectorWeights) (α0 : AlphaInvAt) (μ μ₀ : ℝ) : ℝ :=
  weakRunningFactor w α0 μ μ₀ * colorRunningFactor w α0 μ μ₀

theorem running_mass_ratio_decomposition_from_sector_weights
    (w : SectorWeights) (α0 : AlphaInvAt) (μ μ₀ : ℝ) :
    runningMassRatioFromSectorWeights w α0 μ μ₀ =
      weakRunningFactor w α0 μ μ₀ * colorRunningFactor w α0 μ μ₀ := by
  rfl

/-!
### Canonical witness for `WeakUniformColorScaled`

Internal construction showing that the `WeakUniformColorScaled` pattern
is inhabited for every `k N_c : ℚ`. This discharges the non-emptiness
of the hypothesis without introducing any external input.
-/

/--
Canonical generation-indexed weight assignment satisfying
`WeakUniformColorScaled _ k N_c`.

- generation 0: `(hypercharge, weak, color) = (1, 1, 1)`
- generation 1: `(1, k, 1)`
- generation 2: `(1, k, N_c)`
-/
def canonicalWeakUniformColorScaled (k N_c : ℚ) : GenerationSectorWeights :=
  fun g =>
    if g = 0 then
      { hypercharge := 1, weak := 1, color := 1 }
    else if g = 1 then
      { hypercharge := 1, weak := k, color := 1 }
    else
      { hypercharge := 1, weak := k, color := N_c }

/--
The canonical witness satisfies the `WeakUniformColorScaled` pattern.
-/
theorem canonicalWeakUniformColorScaled_pattern (k N_c : ℚ) :
    WeakUniformColorScaled (canonicalWeakUniformColorScaled k N_c) k N_c := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [weakFactor, colorFactor,
          canonicalWeakUniformColorScaled,
          GaugeGeometry.QFT.Representation.electroweakWeight]

/--
Existence form: for every `k N_c : ℚ`, the `WeakUniformColorScaled`
pattern admits an explicit generation-level witness.
-/
theorem exists_weakUniformColorScaled (k N_c : ℚ) :
    ∃ W : GenerationSectorWeights, WeakUniformColorScaled W k N_c :=
  ⟨canonicalWeakUniformColorScaled k N_c,
    canonicalWeakUniformColorScaled_pattern k N_c⟩

/-!
### Multiplicative-form mass-ratio running (direction Y)

Standard one-loop mass running for a ratio takes the multiplicative form
`m(μ) / m(μ₀) = (α(μ) / α(μ₀)) ^ (γ / b)` per sector, with `γ` the
anomalous dimension and `b` the one-loop β-coefficient.

The linear factors `weakRunningFactor` / `colorRunningFactor` above are
kept as structural placeholders. This section adds the multiplicative
skeleton required by the full one-loop mass-ratio form, built on top of
the already-formalized `alphaInvRunning`. Sector exponents are carried
by the `SectorWeights` record reinterpreted as `γ/b` values.

Positivity of `alphaInvRunning` at `μ` (no Landau pole in the working
range) is taken as an explicit hypothesis where needed.
-/

/--
Reconstructed coupling `α_i(μ)` from the inverse coupling.
Defined as `1 / α⁻¹(μ)`; the sensible regime is
`alphaInvRunning ... > 0`.
-/
noncomputable def alphaRunning
    (α0 : AlphaInvAt) (μ μ₀ : ℝ) (i : GaugeIndex) : ℝ :=
  1 / GaugeGeometry.QFT.Analytic.alphaInvRunning
         mssmBetaCoefficients α0 μ μ₀ i

/--
Multiplicative one-loop factor `(α_i(μ) / α_i(μ₀)) ^ γ` with the
exponent provided as a real parameter.
-/
noncomputable def multiplicativeRunningFactor
    (γ : ℝ) (α0 : AlphaInvAt) (μ μ₀ : ℝ) (i : GaugeIndex) : ℝ :=
  (alphaRunning α0 μ μ₀ i / alphaRunning α0 μ₀ μ₀ i) ^ γ

/--
Multiplicative one-loop mass ratio assembled from sector-wise
exponents `(w.hypercharge, w.weak, w.color)`. Each sector contributes
`(α_i(μ) / α_i(μ₀)) ^ w.sector`; the product is the full mass-ratio
running under the standard direct-product assumption.
-/
noncomputable def multiplicativeRunningMassRatio
    (w : SectorWeights) (α0 : AlphaInvAt) (μ μ₀ : ℝ) : ℝ :=
  multiplicativeRunningFactor (w.hypercharge : ℝ) α0 μ μ₀ u1Index *
    multiplicativeRunningFactor (w.weak : ℝ) α0 μ μ₀ su2Index *
    multiplicativeRunningFactor (w.color : ℝ) α0 μ μ₀ su3Index

/--
Reference-scale collapse: at `μ = μ₀`, each multiplicative factor is
`1`, provided the reference inverse coupling is nonzero.
-/
theorem multiplicativeRunningFactor_at_reference
    (γ : ℝ) (α0 : AlphaInvAt) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (i : GaugeIndex) (hα0 : α0 i ≠ 0) :
    multiplicativeRunningFactor γ α0 μ₀ μ₀ i = 1 := by
  unfold multiplicativeRunningFactor alphaRunning
  have hcoll :
      GaugeGeometry.QFT.Analytic.alphaInvRunning
        mssmBetaCoefficients α0 μ₀ μ₀ = α0 :=
    GaugeGeometry.QFT.Analytic.alphaInvRunning_at_reference
      mssmBetaCoefficients α0 hμ₀
  rw [hcoll]
  have hne : (1 : ℝ) / α0 i ≠ 0 := by
    exact one_div_ne_zero hα0
  rw [div_self hne]
  exact Real.one_rpow γ

/--
Reference-scale collapse for the full multiplicative mass ratio.
At `μ = μ₀`, the mass ratio equals `1` (no running), provided the
reference inverse couplings are all nonzero.
-/
theorem multiplicativeRunningMassRatio_at_reference
    (w : SectorWeights) (α0 : AlphaInvAt) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hα0_u1 : α0 u1Index ≠ 0)
    (hα0_su2 : α0 su2Index ≠ 0)
    (hα0_su3 : α0 su3Index ≠ 0) :
    multiplicativeRunningMassRatio w α0 μ₀ μ₀ = 1 := by
  unfold multiplicativeRunningMassRatio
  rw [multiplicativeRunningFactor_at_reference (w.hypercharge : ℝ) α0 hμ₀ u1Index hα0_u1,
      multiplicativeRunningFactor_at_reference (w.weak : ℝ) α0 hμ₀ su2Index hα0_su2,
      multiplicativeRunningFactor_at_reference (w.color : ℝ) α0 hμ₀ su3Index hα0_su3]
  ring

/--
Explicit one-loop form of the sector coupling ratio.
Under `α⁻¹(μ₀) ≠ 0`, the ratio `α_i(μ) / α_i(μ₀)` equals
`α⁻¹_i(μ₀) / α⁻¹_i(μ)`.
-/
theorem alpha_ratio_eq_inv_ratio
    (α0 : AlphaInvAt) (μ μ₀ : ℝ) (i : GaugeIndex)
    (hα0 : GaugeGeometry.QFT.Analytic.alphaInvRunning
             mssmBetaCoefficients α0 μ₀ μ₀ i ≠ 0)
    (hαμ : GaugeGeometry.QFT.Analytic.alphaInvRunning
             mssmBetaCoefficients α0 μ μ₀ i ≠ 0) :
    alphaRunning α0 μ μ₀ i / alphaRunning α0 μ₀ μ₀ i =
      GaugeGeometry.QFT.Analytic.alphaInvRunning
          mssmBetaCoefficients α0 μ₀ μ₀ i /
        GaugeGeometry.QFT.Analytic.alphaInvRunning
          mssmBetaCoefficients α0 μ μ₀ i := by
  unfold alphaRunning
  field_simp

#print axioms generationFactorFromSectorWeights_shape
#print axioms generationFactorFromSectorWeights_second_nonzero
#print axioms canonicalWeakUniformColorScaled_pattern
#print axioms exists_weakUniformColorScaled
#print axioms multiplicativeRunningFactor_at_reference
#print axioms multiplicativeRunningMassRatio_at_reference
#print axioms alpha_ratio_eq_inv_ratio

end GaugeGeometry.Applications
