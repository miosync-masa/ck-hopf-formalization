/-
  Applications/UnificationRatio.lean

  Algebraic one-point unification condition as a physical auxiliary,
  *not* as a geometric theorem.

  The "unification ratio" here is the denominator-cleared form of the
  MSSM one-loop beta-gap condition. For slope gaps
  `(b₀ - b₁, b₁ - b₂) = (28/5, 4)`, the rational identity
  `(α₀ - α₁) / (α₁ - α₂) = 7/5` is equivalent to the integer identity
  `5 * Δ₀₁ = 7 * Δ₁₂`.

  This module now lives under `Applications/` because its content is a
  *physical* auxiliary condition (how idealized exact unification looks at
  the level of the inverse couplings), not a geometric theorem. The
  geometric uniqueness of the floor `(60, 30, 8)` does not rely on it;
  see `Geometric.Arithmetic.FloorValues`.

  Key point separating geometry from physics:

  * `(60, 30, 8)` is the empirically good floor but does *not* satisfy
    the idealized algebraic unification identity. Observed consistency
    is evaluated via MSSM RG running, not via this identity.
  * `(15, 8, 3)` does satisfy the algebraic identity but is physically
    rejected. Algebraic unification and observational consistency are
    therefore two different notions, and this file belongs to the
    application layer.
-/
import GaugeGeometry.Geometric.Arithmetic.CandidateSpace
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

namespace GaugeGeometry.Applications

/--
  Denominator-cleared form of the MSSM one-loop gap condition.
  For slope gaps `(b₀ - b₁, b₁ - b₂) = (28/5, 4)`, the rational identity
  is equivalent to `5 * Δ₀₁ = 7 * Δ₁₂`.
-/
def unificationConsistency (α : Fin 3 → ℤ) : Prop :=
  5 * (α 0 - α 1) = 7 * (α 1 - α 2)

def commonIntersection (α : Fin 3 → ℤ) : Prop :=
  ∃ t : ℤ, 5 * (α 0 - α 1) = t ∧ 7 * (α 1 - α 2) = t

theorem unification_equivalence (α : Fin 3 → ℤ) :
    unificationConsistency α ↔ commonIntersection α := by
  constructor
  · intro h
    refine ⟨5 * (α 0 - α 1), rfl, ?_⟩
    calc
      7 * (α 1 - α 2) = 5 * (α 0 - α 1) := by
        simpa [unificationConsistency] using h.symm
      _ = 5 * (α 0 - α 1) := rfl
  · rintro ⟨t, hLeft, hRight⟩
    calc
      5 * (α 0 - α 1) = t := hLeft
      _ = 7 * (α 1 - α 2) := hRight.symm

/-!
### Concrete floor evaluations

The two evaluations below articulate the split between algebraic
unification and empirical consistency:

* `floorTargetZ = (60, 30, 8)` — the empirical floor, *fails* the
  idealized identity.
* `nontrivialSolutionZ = (15, 8, 3)` — an integer solution of the
  identity that is physically rejected.
-/

/-- `ℤ`-valued version of the empirical floor tuple `(60, 30, 8)`. -/
def floorTargetZ : Fin 3 → ℤ := ![60, 30, 8]

/-- The empirical floor `(60, 30, 8)` does *not* satisfy the idealized
algebraic unification identity. -/
theorem target_not_unification_consistent :
    ¬ unificationConsistency floorTargetZ := by
  change ¬(5 * ((60 : ℤ) - 30) = 7 * (30 - 8))
  norm_num

/-- `ℕ`-valued version of the nontrivial algebraic solution `(15, 8, 3)`. -/
def nontrivialSolution :
    GaugeGeometry.Geometric.Arithmetic.FloorCandidate :=
  ![15, 8, 3]

/-- `ℤ`-valued version of the nontrivial algebraic solution `(15, 8, 3)`. -/
def nontrivialSolutionZ : Fin 3 → ℤ := ![15, 8, 3]

/-- `(15, 8, 3)` satisfies the idealized algebraic unification identity. -/
theorem nontrivial_unification_solution :
    ∃ α ∈ GaugeGeometry.Geometric.Arithmetic.candidateSpace,
      unificationConsistency (fun i => (α i : ℤ)) ∧ α = nontrivialSolution := by
  refine ⟨nontrivialSolution, ?_, ?_⟩
  · simpa [nontrivialSolution] using
      (GaugeGeometry.Geometric.Arithmetic.mem_candidateSpace_iff
        (a := 15) (b := 8) (c := 3)).2 <| by
        simp [GaugeGeometry.Geometric.Arithmetic.arithmeticClosureList]
  · refine ⟨?_, rfl⟩
    change 5 * ((15 : ℤ) - 8) = 7 * (8 - 3)
    norm_num

#print axioms unification_equivalence
#print axioms target_not_unification_consistent
#print axioms nontrivial_unification_solution

end GaugeGeometry.Applications
