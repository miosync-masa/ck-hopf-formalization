/-
  Applications/QuarkMassRatios.lean

  Quark mass-ratio organization via the *ratio of ratios* construction.

  The central observation from the companion paper (Sec. 6) is that the
  generation-level quantities

    f̂₂ := (m_c / m_u) / (m_s / m_d)
    f̂₃ := (m_t / m_u) / (m_b / m_d)
    N̂_c := f̂₃ / f̂₂

  are empirically close to

    f̂₂ ≈ 30,   f̂₃ ≈ 90,   N̂_c ≈ 3,

  matching the color multiplicity `N_c = 3`. This module isolates the
  abstract `ℚ`-valued skeleton of this construction. All empirical
  numeric content remains in `Axioms/PDGInputs.lean`.
-/
import GaugeGeometry.Axioms.PDGInputs
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace GaugeGeometry.Applications

open GaugeGeometry.Core GaugeGeometry.Axioms

/-!
### Generation-factor abstraction

`GenerationFactor` is the abstract type of "per-generation mass-ratio
factors" as used in the `ratio of ratios` construction. The first
generation is the baseline `f_gen 0`; subsequent entries encode the
mass hierarchy relative to it.
-/

/-- Per-generation abstract mass-ratio factor, indexed by `Fin 3`. -/
abbrev GenerationFactor := Fin 3 → ℚ

/-- The second-generation factor `f_gen 1`. -/
def f2 (f_gen : GenerationFactor) : ℚ := f_gen 1

/-- The third-generation factor `f_gen 2`. -/
def f3 (f_gen : GenerationFactor) : ℚ := f_gen 2

/--
The `ratio of ratios` `f_gen 2 / f_gen 1`, which in the paper plays
the role of an abstract recovery of the color multiplicity `N_c`.
-/
def ratioOfRatios (f_gen : GenerationFactor) : ℚ := f3 f_gen / f2 f_gen

@[simp] theorem ratioOfRatios_def (f_gen : GenerationFactor) :
    ratioOfRatios f_gen = f_gen 2 / f_gen 1 := by
  rfl

/-!
### PDG-level concrete ratios

The following definitions instantiate `GenerationFactor` at observed
PDG values. They are intentionally `noncomputable` — they depend on
axiomatic PDG inputs and return real values through `MeasuredValue`.

For the purely structural `ℚ`-level theorems in `QuarkConsistency`,
this section is not required; it is provided for future concrete
consistency theorems.
-/

/--
PDG-valued up-type to down-type mass ratio in generation `g`:
`m_up(g) / m_down(g)`. The indexing uses the paper's convention:
gen 0 = (u, d), gen 1 = (c, s), gen 2 = (t, b).
-/
noncomputable def pdgUpDownRatio : Fin 3 → ℝ
  | ⟨0, _⟩ =>
      (pdgQuarkMass .up).centralValue / (pdgQuarkMass .down).centralValue
  | ⟨1, _⟩ =>
      (pdgQuarkMass .charm).centralValue / (pdgQuarkMass .strange).centralValue
  | ⟨2, _⟩ =>
      (pdgQuarkMass .top).centralValue / (pdgQuarkMass .bottom).centralValue

/--
PDG-valued `f̂_g = (m_up(g) / m_down(g)) / (m_up(0) / m_down(0))`,
i.e. the up/down ratio of generation `g` normalized to the first
generation.

This is the paper's Sec. 6 quantity. Concretely:
  f̂₁ = 1,  f̂₂ ≈ 30,  f̂₃ ≈ 90.
-/
noncomputable def pdgGenerationFactor (g : Fin 3) : ℝ :=
  pdgUpDownRatio g / pdgUpDownRatio 0

@[simp] theorem pdgGenerationFactor_zero :
    pdgGenerationFactor 0 = 1 := by
  unfold pdgGenerationFactor
  have h : pdgUpDownRatio 0 ≠ 0 := by
    unfold pdgUpDownRatio
    have hu := pdg_quarkMass_centralValue_positive .up
    have hd := pdg_quarkMass_centralValue_positive .down
    intro habs
    have huv : (pdgQuarkMass .up).centralValue ≠ 0 := ne_of_gt hu
    have hdv : (pdgQuarkMass .down).centralValue ≠ 0 := ne_of_gt hd
    rw [div_eq_zero_iff] at habs
    rcases habs with h1 | h2
    · exact huv h1
    · exact hdv h2
  field_simp

end GaugeGeometry.Applications
