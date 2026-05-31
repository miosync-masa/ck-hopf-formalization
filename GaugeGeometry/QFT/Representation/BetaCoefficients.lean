import GaugeGeometry.QFT.Representation.GaugeProduct
import GaugeGeometry.QFT.Representation.CasimirData
import GaugeGeometry.QFT.Representation.DynkinIndex
import GaugeGeometry.Axioms.MSSMChoice
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace GaugeGeometry.QFT.Representation

abbrev BetaCoefficients := GaugeIndex → ℚ

def mssmBetaCoefficients : BetaCoefficients
  | ⟨0, _⟩ => (33 : ℚ) / 5
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => -3

def betaTriple : BetaCoefficients :=
  mssmBetaCoefficients

theorem betaTriple_b1 :
    betaTriple u1Index = (33 : ℚ) / 5 := by
  rfl

theorem betaTriple_b2 :
    betaTriple su2Index = 1 := by
  rfl

theorem betaTriple_b3 :
    betaTriple su3Index = -3 := by
  rfl

theorem b1_positive :
    0 < betaTriple u1Index := by
  rw [betaTriple_b1]
  norm_num

theorem b2_positive :
    0 < betaTriple su2Index := by
  rw [betaTriple_b2]
  norm_num

theorem b3_negative :
    betaTriple su3Index < 0 := by
  rw [betaTriple_b3]
  norm_num

theorem mssm_beta_sign_pattern :
    0 < betaTriple u1Index ∧
    0 < betaTriple su2Index ∧
    betaTriple su3Index < 0 := by
  exact ⟨b1_positive, b2_positive, b3_negative⟩

/-!
## Theorem 1 — Stage 2 assembly

This section assembles the MSSM 1-loop β coefficients from the
representation-theoretic data declared in `Axioms/MSSMChoice.lean`
(adjoint Casimir `C₂(G_i)` and matter Dynkin index `T_i(matter)`)
via the SUSY 1-loop β formula

  b_i = - 3 · C₂(G_i) + T_i(matter).

The main theorem `mssmBetaCoefficients_eq_assembly` then shows that
the directly stated tuple `mssmBetaCoefficients = (33/5, 1, -3)`
coincides with the assembled expression. This promotes Stage 1 (values
as definitions) to Stage 2 (values as the unique output of a Lean-level
formula fed by explicit MSSM inputs), isolating the residual empirical
content to the MSSM Casimir/Dynkin axioms.
-/

/--
The SUSY 1-loop β assembly formula:
`b_i = -3 · C₂(G_i) + T_i(matter)`, evaluated through the canonical
gauge-index lookup.
-/
def assembledBeta
    (adj : AdjointCasimirData) (mat : DynkinIndexData) :
    BetaCoefficients :=
  fun i => (-3 : ℚ) * adj.atIndex i + mat.atIndex i

@[simp] theorem assembledBeta_u1
    (adj : AdjointCasimirData) (mat : DynkinIndexData) :
    assembledBeta adj mat u1Index
      = (-3 : ℚ) * adj.data.u1 + mat.u1 := by
  simp [assembledBeta]

@[simp] theorem assembledBeta_su2
    (adj : AdjointCasimirData) (mat : DynkinIndexData) :
    assembledBeta adj mat su2Index
      = (-3 : ℚ) * adj.data.su2 + mat.su2 := by
  simp [assembledBeta]

@[simp] theorem assembledBeta_su3
    (adj : AdjointCasimirData) (mat : DynkinIndexData) :
    assembledBeta adj mat su3Index
      = (-3 : ℚ) * adj.data.su3 + mat.su3 := by
  simp [assembledBeta]

/--
The MSSM 1-loop β coefficients arise from the SUSY assembly formula
fed by the MSSM Casimir/Dynkin axioms. This is the Stage 2 provenance
of Theorem 1 at the representation layer.
-/
theorem mssmBetaCoefficients_eq_assembly :
    mssmBetaCoefficients =
      assembledBeta
        GaugeGeometry.Axioms.mssmAdjointCasimir
        GaugeGeometry.Axioms.mssmMatterDynkin := by
  funext i
  fin_cases i
  · -- i = u1Index: (-3) * 0 + 33/5 = 33/5
    have hC := GaugeGeometry.Axioms.mssmAdjointCasimir_u1
    have hT := GaugeGeometry.Axioms.mssmMatterDynkin_u1
    show mssmBetaCoefficients u1Index = assembledBeta _ _ u1Index
    rw [assembledBeta_u1, hC, hT]
    show (33 : ℚ) / 5 = (-3 : ℚ) * 0 + 33 / 5
    ring
  · -- i = su2Index: (-3) * 2 + 7 = 1
    have hC := GaugeGeometry.Axioms.mssmAdjointCasimir_su2
    have hT := GaugeGeometry.Axioms.mssmMatterDynkin_su2
    show mssmBetaCoefficients su2Index = assembledBeta _ _ su2Index
    rw [assembledBeta_su2, hC, hT]
    show (1 : ℚ) = (-3 : ℚ) * 2 + 7
    ring
  · -- i = su3Index: (-3) * 3 + 6 = -3
    have hC := GaugeGeometry.Axioms.mssmAdjointCasimir_su3
    have hT := GaugeGeometry.Axioms.mssmMatterDynkin_su3
    show mssmBetaCoefficients su3Index = assembledBeta _ _ su3Index
    rw [assembledBeta_su3, hC, hT]
    show (-3 : ℚ) = (-3 : ℚ) * 3 + 6
    ring

/--
Theorem 1 (statement form): the MSSM 1-loop β tuple is exactly
`(33/5, 1, -3)`, obtained by assembling SUSY Casimir/Dynkin data.
-/
theorem mssm_one_loop_beta_coefficients :
    betaTriple u1Index = (33 : ℚ) / 5 ∧
    betaTriple su2Index = 1 ∧
    betaTriple su3Index = -3 :=
  ⟨betaTriple_b1, betaTriple_b2, betaTriple_b3⟩

end GaugeGeometry.QFT.Representation
