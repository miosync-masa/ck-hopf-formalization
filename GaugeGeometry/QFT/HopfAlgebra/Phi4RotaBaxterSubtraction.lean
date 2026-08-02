import GaugeGeometry.QFT.HopfAlgebra.Phi4StableConvolutionUnit

/-!
# QFT-R2-body-660 — the weight −1 Rota–Baxter SUBTRACTION VESSEL

Body-659b completed the character algebra (associative unital convolution on the SOURCE side).
**660 moves to the target algebra**: the weight −1 Rota–Baxter **SUBTRACTION VESSEL** — one explicit
owner `Phi4RotaBaxterSubtractionScheme` of the pole part `R` (`R² = R`, `R 1 = 0`, weight −1 RB), its
finite part `1 − R` (also weight −1 RB), and the prepared-value counterterm/renormalized split `−R b`
/ `(1 − R) b`.  This is the vessel; the Bogoliubov recursion is 661+.  `R` is ℚ-LINEAR only — **NOT a
character / AlgHom**; no real Laurent / dimensional-regularization scheme is built; the zero scheme is a
bare inhabitant (structure inhabitedness only, NOT physical minimal subtraction).

## Construction

* **Step 1 — the subtraction owner.**  `Phi4RotaBaxterSubtractionScheme A` — the ONE sanctioned new
  `structure` (Mathlib / repo have no suitable Rota–Baxter owner): a ℚ-linear `polePart : A →ₗ[ℚ] A`
  with `polePart_idempotent` (`R² = R`), `polePart_one` (`R 1 = 0`, an EXPLICIT field), and the weight −1
  Rota–Baxter identity `R x · R y = R (R x · y + x · R y − x · y)`.  Weight is FIXED at −1.
* **Step 2 — the finite part.**  `finitePart := LinearMap.id − polePart` (`= 1 − R`), with the basic
  decomposition lemmas: `R + (1−R) = id`, `(1−R) x = x − R x`, `R ((1−R) x) = 0`, `(1−R)(R x) = 0`,
  idempotence of `1 − R`, and `(1−R) 1 = 1`.
* **Step 3 — multiplicative closure (the RB identity's real content).**  `polePart_mul_fixed`: `R`-fixed
  points are closed under `·`; `finitePart_rotaBaxter_weight_neg_one`: `1 − R` is ALSO a weight −1
  Rota–Baxter operator; `finitePart_mul_fixed`: `(1−R)`-fixed points are closed under `·`.
* **Step 4 — prepared-value operations (NO recursion yet).**  `phi4CountertermValue S b := −R b`,
  `phi4RenormalizedValue S b := b + (−R b)`, with `phi4RenormalizedValue = finitePart` and the
  `0 ↦ 0`, `1 ↦ 0/1` normalizations.  `b` is a PREPARED-VALUE SOCKET — NOT a character's Bogoliubov
  preparation (that is 661).
* **Step 5 — consistency witness.**  `phi4ZeroSubtractionScheme` (`polePart := 0`) — a bare inhabitant,
  NOT claimed physical minimal subtraction.

## HEADLINE VERDICT

`phi4SubtractionScheme_decomposition` (`R b + renorm b = b`), `phi4CountertermValue_lands_in_pole` (the
counterterm `−R b` sits in the pole sector: `R (R b) = R b`), `phi4RenormalizedValue_lands_in_finite`
(the renormalized value sits in the finite sector: `R (renorm b) = 0`).

## HALT / red lines

`R` is ℚ-LINEAR only — NOT disguised as an `AlgHom` (`polePart` is NOT multiplicative).  NO real Laurent /
dimensional-regularization scheme; the zero scheme is a trivial inhabitant.  NO counterterm CHARACTER, NO
Bogoliubov recursion, NO antipode.  `polePart_one` (`R 1 = 0`) is an EXPLICIT field — NOT derived from the
RB identity.  Weight / sign are NOT parametrized (fixed at −1).  EXACTLY ONE new `structure`
(`Phi4RotaBaxterSubtractionScheme`); ZERO new `class` / `instance`.  NO `native_decide` /
`Lean.ofReduceBool`; NO `HEq` / `cast` / data-`▸`; NO forbidden divergence class in any declaration TYPE;
NO `sorry` / `admit`.  Bodies ≤659b UNEDITED; axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).

## Roadmap / 661 preview

661 supplies the Bogoliubov recursion `B_φ(Γ) = φ(Γ) + ∑_{γ ∈ W‴} φ₋(γ) · φ(Γ/γ)` with the counterterm
character `φ₋ = −R(B_φ)` and the renormalized character `φ₊ = (1 − R)(B_φ)` — feeding the PREPARED value
`B_φ(Γ)` of this body's socket `b` into `phi4CountertermValue` / `phi4RenormalizedValue`.  **HALT** at the
vessel; the recursion is 661+.
-/

namespace GaugeGeometry.QFT.Combinatorial

set_option linter.unusedVariables false

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- **Step 1 — the subtraction owner** (the ONE sanctioned new `structure`).  A weight −1 Rota–Baxter
operator on the target algebra `A`: an explicit owner of "which part is the pole part discarded in
renormalization".  `polePart` (`R`) is ℚ-LINEAR only — NOT a character / `AlgHom`.  The weight is FIXED
at −1 (not parametrized), and `polePart_one` (`R 1 = 0`) is an EXPLICIT field (NOT derived from the RB
identity). -/
structure Phi4RotaBaxterSubtractionScheme (A : Type*) [CommRing A] [Algebra ℚ A] where
  /-- The pole part `R` — the ℚ-linear projector onto the sector discarded in renormalization. -/
  polePart : A →ₗ[ℚ] A
  /-- `R` is idempotent (`R² = R`): re-subtracting the pole part changes nothing. -/
  polePart_idempotent : ∀ x, polePart (polePart x) = polePart x
  /-- `R 1 = 0`: the unit carries no pole part (EXPLICIT field, not derived). -/
  polePart_one : polePart 1 = 0
  /-- The weight −1 Rota–Baxter identity (weight fixed at −1). -/
  rotaBaxter_weight_neg_one : ∀ x y,
    polePart x * polePart y
      = polePart (polePart x * y + x * polePart y - x * y)

/-- **Step 2 — the finite part** `1 − R`.  The complementary projector onto the sector KEPT after
renormalization. -/
def Phi4RotaBaxterSubtractionScheme.finitePart (S : Phi4RotaBaxterSubtractionScheme A) : A →ₗ[ℚ] A :=
  LinearMap.id - S.polePart

/-- `R x + (1 − R) x = x`: the pole part and the finite part reconstruct the whole value. -/
theorem Phi4RotaBaxterSubtractionScheme.polePart_add_finitePart
    (S : Phi4RotaBaxterSubtractionScheme A) (x : A) :
    S.polePart x + S.finitePart x = x := by
  simp [finitePart, LinearMap.sub_apply, LinearMap.id_apply]

/-- `(1 − R) x = x − R x`. -/
theorem Phi4RotaBaxterSubtractionScheme.finitePart_apply
    (S : Phi4RotaBaxterSubtractionScheme A) (x : A) :
    S.finitePart x = x - S.polePart x := by
  simp [finitePart, LinearMap.sub_apply, LinearMap.id_apply]

/-- `R ((1 − R) x) = 0`: the finite part has no pole part. -/
theorem Phi4RotaBaxterSubtractionScheme.polePart_finitePart
    (S : Phi4RotaBaxterSubtractionScheme A) (x : A) :
    S.polePart (S.finitePart x) = 0 := by
  rw [finitePart_apply, map_sub, S.polePart_idempotent, sub_self]

/-- `(1 − R)(R x) = 0`: the pole part is annihilated by the finite projector. -/
theorem Phi4RotaBaxterSubtractionScheme.finitePart_polePart
    (S : Phi4RotaBaxterSubtractionScheme A) (x : A) :
    S.finitePart (S.polePart x) = 0 := by
  rw [finitePart_apply, S.polePart_idempotent, sub_self]

/-- `(1 − R)` is idempotent. -/
theorem Phi4RotaBaxterSubtractionScheme.finitePart_idempotent
    (S : Phi4RotaBaxterSubtractionScheme A) (x : A) :
    S.finitePart (S.finitePart x) = S.finitePart x := by
  rw [finitePart_apply (x := S.finitePart x), polePart_finitePart, sub_zero]

/-- `(1 − R) 1 = 1`: the unit is entirely finite. -/
theorem Phi4RotaBaxterSubtractionScheme.finitePart_one
    (S : Phi4RotaBaxterSubtractionScheme A) :
    S.finitePart 1 = 1 := by
  rw [finitePart_apply, S.polePart_one, sub_zero]

/-- **Step 3 — multiplicative closure.**  The set of `R`-fixed points is closed under multiplication:
if `R x = x` and `R y = y` then `R (x · y) = x · y`.  This is the RB identity's real content. -/
theorem Phi4RotaBaxterSubtractionScheme.polePart_mul_fixed
    (S : Phi4RotaBaxterSubtractionScheme A) {x y : A}
    (hx : S.polePart x = x) (hy : S.polePart y = y) :
    S.polePart (x * y) = x * y := by
  have hRB := S.rotaBaxter_weight_neg_one x y
  rw [hx, hy] at hRB
  -- hRB : x * y = polePart (x * y + x * y - x * y)
  have harg : x * y + x * y - x * y = x * y := by ring
  rw [harg] at hRB
  exact hRB.symm

/-- **Step 3 crux — `1 − R` is ALSO a weight −1 Rota–Baxter operator.**  The finite part satisfies the
same weight −1 RB identity as the pole part. -/
theorem Phi4RotaBaxterSubtractionScheme.finitePart_rotaBaxter_weight_neg_one
    (S : Phi4RotaBaxterSubtractionScheme A) (x y : A) :
    S.finitePart x * S.finitePart y
      = S.finitePart (S.finitePart x * y + x * S.finitePart y - x * y) := by
  have hRB : S.polePart x * S.polePart y
      = S.polePart (S.polePart x * y) + S.polePart (x * S.polePart y) - S.polePart (x * y) := by
    rw [S.rotaBaxter_weight_neg_one x y, map_sub, map_add]
  simp only [finitePart_apply, sub_mul, mul_sub, map_sub, map_add]
  rw [hRB]
  ring

/-- The set of `(1 − R)`-fixed points is closed under multiplication (mirror of `polePart_mul_fixed`). -/
theorem Phi4RotaBaxterSubtractionScheme.finitePart_mul_fixed
    (S : Phi4RotaBaxterSubtractionScheme A) {x y : A}
    (hx : S.finitePart x = x) (hy : S.finitePart y = y) :
    S.finitePart (x * y) = x * y := by
  have hRB := S.finitePart_rotaBaxter_weight_neg_one x y
  rw [hx, hy] at hRB
  have harg : x * y + x * y - x * y = x * y := by ring
  rw [harg] at hRB
  exact hRB.symm

/-- **Step 4 — the prepared-value counterterm** `−R b` (NO recursion yet; `b` is a prepared-value
SOCKET, NOT a character's Bogoliubov preparation — that is 661). -/
def phi4CountertermValue (S : Phi4RotaBaxterSubtractionScheme A) (b : A) : A := -S.polePart b

/-- **Step 4 — the prepared-value renormalized value** `b + (−R b)`. -/
def phi4RenormalizedValue (S : Phi4RotaBaxterSubtractionScheme A) (b : A) : A :=
  b + phi4CountertermValue S b

/-- The renormalized value is exactly the finite part `(1 − R) b`. -/
theorem phi4RenormalizedValue_eq_finitePart
    (S : Phi4RotaBaxterSubtractionScheme A) (b : A) :
    phi4RenormalizedValue S b = S.finitePart b := by
  unfold phi4RenormalizedValue phi4CountertermValue
  rw [S.finitePart_apply]
  ring

/-- The counterterm of `0` is `0`. -/
theorem phi4CountertermValue_zero (S : Phi4RotaBaxterSubtractionScheme A) :
    phi4CountertermValue S (0 : A) = 0 := by
  unfold phi4CountertermValue
  rw [map_zero, neg_zero]

/-- The counterterm of `1` is `0` (`R 1 = 0`). -/
theorem phi4CountertermValue_one (S : Phi4RotaBaxterSubtractionScheme A) :
    phi4CountertermValue S (1 : A) = 0 := by
  unfold phi4CountertermValue
  rw [S.polePart_one, neg_zero]

/-- The renormalized value of `0` is `0`. -/
theorem phi4RenormalizedValue_zero (S : Phi4RotaBaxterSubtractionScheme A) :
    phi4RenormalizedValue S (0 : A) = 0 := by
  rw [phi4RenormalizedValue_eq_finitePart, S.finitePart_apply, map_zero, sub_zero]

/-- The renormalized value of `1` is `1`. -/
theorem phi4RenormalizedValue_one (S : Phi4RotaBaxterSubtractionScheme A) :
    phi4RenormalizedValue S (1 : A) = 1 := by
  rw [phi4RenormalizedValue_eq_finitePart, S.finitePart_one]

/-- **Step 5 — consistency witness (inhabitedness).**  The zero scheme (`polePart := 0`).  This is a
BARE inhabitant establishing that the structure is non-vacuous — it is NOT physical minimal subtraction. -/
def phi4ZeroSubtractionScheme : Phi4RotaBaxterSubtractionScheme A where
  polePart := 0
  polePart_idempotent := by intro x; simp
  polePart_one := by simp
  rotaBaxter_weight_neg_one := by intro x y; simp

/-- **HEADLINE VERDICT — decomposition.**  `R b + renorm b = b`: the pole part and the renormalized
value reconstruct the prepared value. -/
theorem phi4SubtractionScheme_decomposition
    (S : Phi4RotaBaxterSubtractionScheme A) (b : A) :
    S.polePart b + phi4RenormalizedValue S b = b := by
  rw [phi4RenormalizedValue_eq_finitePart, S.finitePart_apply]
  ring

/-- **HEADLINE VERDICT — the counterterm lands in the pole sector.**  `−(counterterm) = R b`, and
`R (R b) = R b` by idempotence. -/
theorem phi4CountertermValue_lands_in_pole
    (S : Phi4RotaBaxterSubtractionScheme A) (b : A) :
    S.polePart (-phi4CountertermValue S b) = -phi4CountertermValue S b := by
  unfold phi4CountertermValue
  rw [neg_neg, S.polePart_idempotent]

/-- **HEADLINE VERDICT — the renormalized value lands in the finite sector.**  `renorm b = (1 − R) b`,
and `R ((1 − R) b) = 0`. -/
theorem phi4RenormalizedValue_lands_in_finite
    (S : Phi4RotaBaxterSubtractionScheme A) (b : A) :
    S.polePart (phi4RenormalizedValue S b) = 0 := by
  rw [phi4RenormalizedValue_eq_finitePart, S.polePart_finitePart]

end GaugeGeometry.QFT.Combinatorial
