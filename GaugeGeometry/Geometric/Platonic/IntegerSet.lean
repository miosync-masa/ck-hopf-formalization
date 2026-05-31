/-
  Geometric/Platonic/IntegerSet.lean
  Extraction of {3, 4, 5} and primes {3, 5}.
-/
import GaugeGeometry.Geometric.Platonic.Classification
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic

namespace GaugeGeometry.Geometric.Platonic

def platonicIntegers : Finset ℕ := {3, 4, 5}

def platonicPrimes : Finset ℕ := {3, 5}

def platonicGenerators : Finset ℕ := {2, 3, 5}

def schlafliCoordinateSet : Finset ℕ :=
  {(PlatonicSolid.schlafli .tetrahedron).p,
   (PlatonicSolid.schlafli .tetrahedron).q,
   (PlatonicSolid.schlafli .cube).p,
   (PlatonicSolid.schlafli .cube).q,
   (PlatonicSolid.schlafli .octahedron).p,
   (PlatonicSolid.schlafli .octahedron).q,
   (PlatonicSolid.schlafli .dodecahedron).p,
   (PlatonicSolid.schlafli .dodecahedron).q,
   (PlatonicSolid.schlafli .icosahedron).p,
   (PlatonicSolid.schlafli .icosahedron).q}

theorem platonic_integers_from_classification :
    schlafliCoordinateSet = platonicIntegers := by
  ext n
  simp [schlafliCoordinateSet, platonicIntegers, PlatonicSolid.schlafli,
    schlafli33, schlafli34, schlafli35, schlafli43, schlafli53]
  constructor <;> intro h
  · rcases h with h4 | h3 | h5
    · exact Or.inr (Or.inl h4)
    · exact Or.inl h3
    · exact Or.inr (Or.inr h5)
  · rcases h with h3 | h4 | h5
    · exact Or.inr (Or.inl h3)
    · exact Or.inl h4
    · exact Or.inr (Or.inr h5)

theorem prime_three_manual : Nat.Prime 3 := by
  rw [Nat.prime_def]
  constructor
  · decide
  · intro m hm
    have hm_le : m ≤ 3 := Nat.le_of_dvd (by decide) hm
    interval_cases m <;> simp_all

theorem prime_five_manual : Nat.Prime 5 := by
  rw [Nat.prime_def]
  constructor
  · decide
  · intro m hm
    have hm_le : m ≤ 5 := Nat.le_of_dvd (by decide) hm
    interval_cases m <;> simp_all

theorem not_prime_four_manual : ¬ Nat.Prime 4 := by
  rw [Nat.prime_def]
  intro h
  rcases h with ⟨_, hforall⟩
  have hcase := hforall 2 (by decide : 2 ∣ 4)
  omega

theorem platonic_primes_are_3_and_5 :
    (∀ n, n ∈ platonicPrimes → Nat.Prime n) ∧
      (∀ n, n ∈ platonicIntegers → Nat.Prime n → n ∈ platonicPrimes) := by
  constructor
  · intro n hn
    simp [platonicPrimes] at hn
    rcases hn with h3 | h5
    · simpa [h3] using prime_three_manual
    · simpa [h5] using prime_five_manual
  · intro n hn hprime
    simp [platonicIntegers] at hn
    simp [platonicPrimes]
    rcases hn with h3 | h4 | h5
    · exact Or.inl h3
    · exact False.elim (not_prime_four_manual (h4 ▸ hprime))
    · exact Or.inr h5

theorem four_is_two_squared : 4 = 2 ^ 2 := by
  norm_num

#print axioms platonic_integers_from_classification
#print axioms platonic_primes_are_3_and_5
#print axioms four_is_two_squared

end GaugeGeometry.Geometric.Platonic
