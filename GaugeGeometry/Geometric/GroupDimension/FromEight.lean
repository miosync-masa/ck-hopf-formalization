/-
  Geometric/GroupDimension/FromEight.lean
  Keystone theorem: N² - 1 = 8 ⟺ N = 3 (for N ≥ 2).
-/
import GaugeGeometry.Geometric.GroupDimension.AdjointFormula
import Mathlib.Tactic

namespace GaugeGeometry.Geometric.GroupDimension

theorem adjoint_dim_eight_iff_three {N : ℕ} (hN : 2 ≤ N) :
    adjointDim N = 8 ↔ N = 3 := by
  constructor
  · intro h
    have hsq : N ^ 2 = 9 := by
      simpa [adjointDim] using h
    have hlt4 : N < 4 := by
      by_contra hge
      have h4 : 4 ≤ N := Nat.not_lt.mp hge
      have h16 : 16 ≤ N ^ 2 := by
        calc
          16 = 4 ^ 2 := by norm_num
          _ ≤ N ^ 2 := Nat.pow_le_pow_left h4 2
      simp [hsq] at h16
    interval_cases N <;> simp_all
  · intro h
    subst h
    exact adjointDim_three

#print axioms adjoint_dim_eight_iff_three

end GaugeGeometry.Geometric.GroupDimension
