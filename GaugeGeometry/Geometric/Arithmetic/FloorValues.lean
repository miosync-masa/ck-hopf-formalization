/-
  Geometric/Arithmetic/FloorValues.lean
  Uniqueness of (60, 30, 8) inside the candidate space.
-/
import GaugeGeometry.Geometric.Arithmetic.CandidateSpace
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

namespace GaugeGeometry.Geometric.Arithmetic

def floorTarget : Fin 3 → ℕ := ![60, 30, 8]

theorem floor_target_mem_candidateSpace : floorTarget ∈ candidateSpace := by
  simpa [floorTarget] using
    (mem_candidateSpace_iff (a := 60) (b := 30) (c := 8)).2 <| by
      simp [arithmeticClosureList]

theorem unique_floor_structure :
    ∃! α : FloorCandidate, α ∈ candidateSpace ∧ α = floorTarget := by
  refine ⟨floorTarget, ⟨floor_target_mem_candidateSpace, rfl⟩, ?_⟩
  intro α hα
  exact hα.2

#print axioms unique_floor_structure

end GaugeGeometry.Geometric.Arithmetic
