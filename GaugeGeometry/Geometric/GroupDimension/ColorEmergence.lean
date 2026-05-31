/-
  Geometric/GroupDimension/ColorEmergence.lean
  Triangle: Platonic 3 = solution to N²-1=8 = quark ratio.
-/
import GaugeGeometry.Geometric.Platonic.IntegerSet
import GaugeGeometry.Geometric.GroupDimension.FromEight
import Mathlib.Tactic

namespace GaugeGeometry.Geometric.GroupDimension

theorem three_is_consistent :
    3 ∈ GaugeGeometry.Geometric.Platonic.platonicIntegers ∧
      adjointDim 3 = 8 ∧
      ∀ {N : ℕ}, 2 ≤ N → adjointDim N = 8 → N = 3 := by
  refine ⟨?_, adjointDim_three, ?_⟩
  · simp [GaugeGeometry.Geometric.Platonic.platonicIntegers]
  · intro N hN hEight
    exact (adjoint_dim_eight_iff_three hN).mp hEight

#print axioms three_is_consistent

end GaugeGeometry.Geometric.GroupDimension
