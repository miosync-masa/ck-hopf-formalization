/-
  Geometric/Platonic/Schlafli.lean
  The Schläfli condition and enumeration of integer solutions.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

namespace GaugeGeometry.Geometric.Platonic

structure SchlafliPair where
  p : ℕ
  q : ℕ
  p_ge : 3 ≤ p
  q_ge : 3 ≤ q
  condition : p * q < 2 * (p + q)

def schlafli33 : SchlafliPair where
  p := 3
  q := 3
  p_ge := by decide
  q_ge := by decide
  condition := by decide

def schlafli34 : SchlafliPair where
  p := 3
  q := 4
  p_ge := by decide
  q_ge := by decide
  condition := by decide

def schlafli35 : SchlafliPair where
  p := 3
  q := 5
  p_ge := by decide
  q_ge := by decide
  condition := by decide

def schlafli43 : SchlafliPair where
  p := 4
  q := 3
  p_ge := by decide
  q_ge := by decide
  condition := by decide

def schlafli53 : SchlafliPair where
  p := 5
  q := 3
  p_ge := by decide
  q_ge := by decide
  condition := by decide

theorem SchlafliPair.ext {s t : SchlafliPair} (hp : s.p = t.p) (hq : s.q = t.q) : s = t := by
  cases s
  cases t
  cases hp
  cases hq
  simp

theorem schlafli_small_product {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (h : p * q < 2 * (p + q)) : (p - 2) * (q - 2) < 4 := by
  have hp' : p = (p - 2) + 2 := by omega
  have hq' : q = (q - 2) + 2 := by omega
  rw [hp', hq'] at h
  ring_nf at h
  omega

theorem schlafli_p_le_five {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q)
    (h : p * q < 2 * (p + q)) : p ≤ 5 := by
  have hp2 : 2 ≤ p := le_trans (by decide) hp
  have hq2 : 2 ≤ q := le_trans (by decide) hq
  have hsmall : (p - 2) * (q - 2) < 4 := schlafli_small_product hp2 hq2 h
  have hp_split : p ≤ 5 ∨ 6 ≤ p := by omega
  rcases hp_split with hp_le | hp6
  · exact hp_le
  · have hp4 : 4 ≤ p - 2 := by omega
    have hq1 : 1 ≤ q - 2 := by omega
    have hlarge : 4 ≤ (p - 2) * (q - 2) := by
      calc
        4 = 4 * 1 := by decide
        _ ≤ (p - 2) * (q - 2) := Nat.mul_le_mul hp4 hq1
    omega

theorem schlafli_enumeration (s : SchlafliPair) :
    (s.p, s.q) = (3, 3) ∨
    (s.p, s.q) = (3, 4) ∨
    (s.p, s.q) = (3, 5) ∨
    (s.p, s.q) = (4, 3) ∨
    (s.p, s.q) = (5, 3) := by
  rcases s with ⟨p, q, hp_ge, hq_ge, hcond⟩
  have hp_le : p ≤ 5 := schlafli_p_le_five hp_ge hq_ge hcond
  have hp_cases : p = 3 ∨ p = 4 ∨ p = 5 := by
    clear hcond
    omega
  rcases hp_cases with hp3 | hp4 | hp5
  · have hq_cases : q = 3 ∨ q = 4 ∨ q = 5 := by
      have hcond3 := hcond
      rw [hp3] at hcond3
      omega
    rcases hq_cases with hq3 | hq4 | hq5
    · left
      simp [hp3, hq3]
    · right
      left
      simp [hp3, hq4]
    · right
      right
      left
      simp [hp3, hq5]
  · have hq_eq : q = 3 := by
      have hcond4 := hcond
      rw [hp4] at hcond4
      omega
    right
    right
    right
    left
    simp [hp4, hq_eq]
  · have hq_eq : q = 3 := by
      have hcond5 := hcond
      rw [hp5] at hcond5
      omega
    right
    right
    right
    right
    simp [hp5, hq_eq]

theorem schlafli_finite :
    Set.range (fun s : SchlafliPair => (s.p, s.q)) =
      ({(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)} : Set (ℕ × ℕ)) := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    rcases schlafli_enumeration s with h | h | h | h | h <;> simp [h]
  · intro hx
    simp at hx
    rcases hx with h | h | h | h | h
    · exact ⟨schlafli33, by simpa [schlafli33] using h.symm⟩
    · exact ⟨schlafli34, by simpa [schlafli34] using h.symm⟩
    · exact ⟨schlafli35, by simpa [schlafli35] using h.symm⟩
    · exact ⟨schlafli43, by simpa [schlafli43] using h.symm⟩
    · exact ⟨schlafli53, by simpa [schlafli53] using h.symm⟩

#print axioms schlafli_enumeration
#print axioms schlafli_finite

end GaugeGeometry.Geometric.Platonic
