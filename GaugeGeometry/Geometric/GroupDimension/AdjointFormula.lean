/-
  Geometric/GroupDimension/AdjointFormula.lean
  Number-theoretic function adjointDim N = N² - 1.
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace GaugeGeometry.Geometric.GroupDimension

def adjointDim (N : ℕ) : ℕ := N ^ 2 - 1

theorem adjointDim_three : adjointDim 3 = 8 := by
  norm_num [adjointDim]

#print axioms adjointDim_three

end GaugeGeometry.Geometric.GroupDimension
