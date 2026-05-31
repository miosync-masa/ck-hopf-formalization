/-
  Geometric/Arithmetic/CandidateSpace.lean
  The finite candidate space for the gauge coupling floor.
-/
import GaugeGeometry.Geometric.Platonic.IntegerSet
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

namespace GaugeGeometry.Geometric.Arithmetic

-- The candidate space is restricted to values built from {2, 3, 5}
-- using only the basic operations listed in Task_v2.
/--
  Explicit finite arithmetic closure used for the geometric floor search.
  It contains the singleton values, the needed sum values, and the products
  generated from `{2, 3, 5}` together with `4 = 2^2`.
-/
def arithmeticClosure : Finset ℕ :=
  ({2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 24, 25, 27, 30, 40, 45, 50, 60, 75, 100, 125} :
    Finset ℕ)

abbrev FloorCandidate := Fin 3 → ℕ

def arithmeticClosureList : List ℕ :=
  [2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 24, 25, 27, 30, 40, 45, 50, 60, 75, 100, 125]

def candidateSpace : List FloorCandidate :=
  arithmeticClosureList.flatMap fun a =>
    arithmeticClosureList.flatMap fun b =>
      arithmeticClosureList.map fun c => ![a, b, c]

theorem mem_candidateSpace_iff {a b c : ℕ} :
    (![a, b, c] : FloorCandidate) ∈ candidateSpace ↔
      a ∈ arithmeticClosureList ∧ b ∈ arithmeticClosureList ∧ c ∈ arithmeticClosureList := by
  simp [candidateSpace]

theorem candidate_space_finite : candidateSpace.length = arithmeticClosureList.length ^ 3 := by
  calc
    candidateSpace.length =
        arithmeticClosureList.length * (arithmeticClosureList.length * arithmeticClosureList.length) := by
          simp [candidateSpace]
    _ = arithmeticClosureList.length ^ 3 := by
          simp [pow_succ, Nat.mul_assoc]

#print axioms candidate_space_finite

end GaugeGeometry.Geometric.Arithmetic
