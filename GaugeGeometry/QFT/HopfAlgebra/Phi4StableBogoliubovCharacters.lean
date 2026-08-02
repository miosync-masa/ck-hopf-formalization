import GaugeGeometry.QFT.HopfAlgebra.Phi4StableBogoliubovRecursion

/-!
# QFT-R2-body-662 — the genuine unital ℚ-algebra Bogoliubov CHARACTERS φ₋, φ₊

**662 uses the free-commutative-algebra universal property (`MvPolynomial.aeval`) to promote 661b's
generator-valued φ₋/φ₊ to genuine unital ℚ-algebra CHARACTERS**
`φ₋, φ₊ : StableResolvedPhi4HopfH →ₐ[ℚ] B` — with generator anchors, uniqueness (the recursion values
pin the character), the load-bearing left-aggregate `map_prod` bridge (input to 663), and the
sign-honest character-level generator laws.

`φ₋ 1 = 1` (the character's UNIT, `map_one`) does NOT contradict 660's `phi4CountertermValue S 1 = 0`
(the RB counterterm VALUE at the algebra unit, a prepared-value socket computation) — they are DIFFERENT
maps.  φ₋ is multiplicative, NOT `-R ∘ (preparation character)`; the `-R` relation holds ONLY on
generators (via the `_X` anchors).  The character does NOT land in the pole sector (`φ₋ 1 = 1 ≠ 0`
refutes it).

## Contents
* `phi4BogoliubovCountertermCharacter` / `phi4BogoliubovRenormalizedCharacter` — the two genuine
  `H →ₐ[ℚ] B` characters via `MvPolynomial.aeval` of 661b's generator functions.
* generator (`_X`), unit (`_one`), and multiplicativity (`_mul`) anchors.
* uniqueness (`algHom_ext`: the recursion values on generators pin the character).
* the load-bearing left-aggregate `map_prod` bridge (input to 663).
* the sign-honest character-level generator laws (reading 661b through the `_X` anchors).

## HALT compliance
661b generators + `_eq` theorems + decomposition, 660 Rota–Baxter, 629 left aggregate are consumed as
BLACK BOXES.  NO preparation CHARACTER; NO `φ₋ ⋆ φ = φ₊` (that is 663); the `-R` relation is NOT extended
to arbitrary polynomials (only generators, via `_X`); `polePart` is NOT treated as an `AlgHom`; the
661b recursion / 661a rank descent are NOT re-expanded.  NO antipode, NO Laurent / real integral, NO
Figure-1 evaluation.  NO `native_decide` / `Lean.ofReduceBool`; NO `HEq` / `cast` / graph-data `▸`.  NO
forbidden divergence class in any declaration TYPE.  NO `sorry` / `admit`.  ZERO new `structure` /
`class` / permanent `instance` (only a file-scoped `local instance` re-exposing the existing divergence
family).  Bodies ≤661b UNEDITED; axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).

## Roadmap
662 characters (THIS FILE) → 663 `φ₋ ⋆ φ = φ₊` via `convolution_of_graph` + the left-aggregate bridge +
`algHom_ext` → 664 Figure-1 dropped-term → renormalization weight + HALT.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped BigOperators

set_option linter.unusedVariables false

/-- File-scoped re-exposure of the φ⁴ divergence-measure family instance (NOT a permanent/global
instance — scoped to this file exactly as in `Phi4StableBogoliubovRecursion`), so the W‴ / left-aggregate
carrier types elaborate. -/
local instance instPhi4DivergenceMeasureFamily662 : ∀ H : FeynmanGraph, DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

variable {B : Type*} [CommRing B] [Algebra ℚ B]

/-! ## Step 1 — the two genuine characters -/

/-- **body-662 (Step 1) — the genuine counterterm character** `φ₋ : H →ₐ[ℚ] B`.  The
`MvPolynomial.aeval` extension of 661b's generator-valued counterterm along the
free-commutative-algebra universal property. -/
noncomputable def phi4BogoliubovCountertermCharacter
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B) :
    StableResolvedPhi4HopfH →ₐ[ℚ] B :=
  MvPolynomial.aeval (phi4BogoliubovCountertermGen S φ)

/-- **body-662 (Step 1) — the genuine renormalized character** `φ₊ : H →ₐ[ℚ] B`.  The
`MvPolynomial.aeval` extension of 661b's generator-valued renormalized generator. -/
noncomputable def phi4BogoliubovRenormalizedCharacter
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B) :
    StableResolvedPhi4HopfH →ₐ[ℚ] B :=
  MvPolynomial.aeval (phi4BogoliubovRenormalizedGen S φ)

/-! ## Step 2 — generator + unit + mul anchors -/

/-- **body-662 (Step 2) — the counterterm character on a generator** is 661b's counterterm value. -/
@[simp] theorem phi4BogoliubovCountertermCharacter_X
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (x : StableResolvedPhi4HopfGen) :
    phi4BogoliubovCountertermCharacter S φ (MvPolynomial.X x)
      = phi4BogoliubovCountertermGen S φ x := by
  rw [phi4BogoliubovCountertermCharacter, MvPolynomial.aeval_X]

/-- **body-662 (Step 2) — the renormalized character on a generator** is 661b's renormalized value. -/
@[simp] theorem phi4BogoliubovRenormalizedCharacter_X
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (x : StableResolvedPhi4HopfGen) :
    phi4BogoliubovRenormalizedCharacter S φ (MvPolynomial.X x)
      = phi4BogoliubovRenormalizedGen S φ x := by
  rw [phi4BogoliubovRenormalizedCharacter, MvPolynomial.aeval_X]

/-- **body-662 (Step 2) — the counterterm character is unital** (`map_one`).  `φ₋ 1 = 1` — the
character's UNIT.  This does NOT contradict 660's `phi4CountertermValue S 1 = 0`, which is the RB
counterterm VALUE at the algebra unit (a prepared-value socket), a DIFFERENT map. -/
@[simp] theorem phi4BogoliubovCountertermCharacter_one
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B) :
    phi4BogoliubovCountertermCharacter S φ 1 = 1 :=
  map_one _

/-- **body-662 (Step 2) — the renormalized character is unital** (`map_one`).  `φ₊ 1 = 1`. -/
@[simp] theorem phi4BogoliubovRenormalizedCharacter_one
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B) :
    phi4BogoliubovRenormalizedCharacter S φ 1 = 1 :=
  map_one _

/-- **body-662 (Step 2) — the counterterm character is multiplicative** (`map_mul`). -/
theorem phi4BogoliubovCountertermCharacter_mul
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (p q : StableResolvedPhi4HopfH) :
    phi4BogoliubovCountertermCharacter S φ (p * q)
      = phi4BogoliubovCountertermCharacter S φ p * phi4BogoliubovCountertermCharacter S φ q :=
  map_mul _ _ _

/-- **body-662 (Step 2) — the renormalized character is multiplicative** (`map_mul`). -/
theorem phi4BogoliubovRenormalizedCharacter_mul
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (p q : StableResolvedPhi4HopfH) :
    phi4BogoliubovRenormalizedCharacter S φ (p * q)
      = phi4BogoliubovRenormalizedCharacter S φ p * phi4BogoliubovRenormalizedCharacter S φ q :=
  map_mul _ _ _

/-! ## Step 3 — uniqueness (the recursion values pin the character) -/

/-- **body-662 (Step 3) — uniqueness of the counterterm character.**  Any algebra homomorphism agreeing
with 661b's counterterm generator on the free generators IS `φ₋` (`MvPolynomial.algHom_ext`). -/
theorem phi4BogoliubovCountertermCharacter_unique
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (ψ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (h : ∀ x, ψ (MvPolynomial.X x) = phi4BogoliubovCountertermGen S φ x) :
    ψ = phi4BogoliubovCountertermCharacter S φ := by
  apply MvPolynomial.algHom_ext
  intro x
  rw [h, phi4BogoliubovCountertermCharacter_X]

/-- **body-662 (Step 3) — uniqueness of the renormalized character.**  Any algebra homomorphism agreeing
with 661b's renormalized generator on the free generators IS `φ₊` (`MvPolynomial.algHom_ext`). -/
theorem phi4BogoliubovRenormalizedCharacter_unique
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (ψ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (h : ∀ x, ψ (MvPolynomial.X x) = phi4BogoliubovRenormalizedGen S φ x) :
    ψ = phi4BogoliubovRenormalizedCharacter S φ := by
  apply MvPolynomial.algHom_ext
  intro x
  rw [h, phi4BogoliubovRenormalizedCharacter_X]

/-! ## Step 4 — the load-bearing left-aggregate `map_prod` bridge (input to 663) -/

/-- **body-662 (Step 4, LOAD-BEARING) — the counterterm character on a stable left aggregate.**  Since
`φ₋` is an algebra homomorphism and `stableLeftAggregate` is the `∏` of the per-component generators
over `.attach`, `map_prod` distributes `φ₋` across the product, and each factor collapses to 661b's
counterterm value via the `_X` anchor — multiplicity exact, `.attach` preserved.  This is the load-
bearing input to 663's `φ₋ ⋆ φ = φ₊`. -/
theorem phi4BogoliubovCountertermCharacter_stableLeftAggregate
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    {G : ResolvedFeynmanGraph} (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G)
    (hSt : StableResolvedBoundaryIds G) :
    phi4BogoliubovCountertermCharacter S φ (stableLeftAggregate A hSt)
      = ∏ γ ∈ A.elements.attach,
          phi4BogoliubovCountertermGen S φ
            ((stableLocalBoundaryCompletedGraph γ.1).toStableResolvedPhi4HopfGen
              (stableLocalBoundaryCompletedGraph_exists_self_isConnectedDivergent γ.1
                (A.isConnectedDivergent γ.1 γ.2))
              (stableResolvedBoundaryIds_stableLocalBoundaryCompletedGraph γ.1 hSt)) := by
  rw [stableLeftAggregate, map_prod]
  refine Finset.prod_congr rfl (fun γ _ => ?_)
  rw [phi4BogoliubovCountertermCharacter_X]

/-! ## Step 5 — the sign-honest character-level generator laws -/

/-- **body-662 (Step 5) — the sign-honest generator decomposition, character level.**
`B_φ(x) + φ₋(X x) = φ₊(X x)` — 661b's `preparation + counterterm = renormalized` read through the `_X`
anchors.  NO recursion / RB re-proof. -/
theorem phi4BogoliubovCharacters_generator_decomposition
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (x : StableResolvedPhi4HopfGen) :
    phi4BogoliubovPreparationGen S φ x + phi4BogoliubovCountertermCharacter S φ (MvPolynomial.X x)
      = phi4BogoliubovRenormalizedCharacter S φ (MvPolynomial.X x) := by
  rw [phi4BogoliubovCountertermCharacter_X, phi4BogoliubovRenormalizedCharacter_X]
  exact phi4Bogoliubov_decomposition S φ x

/-- **body-662 (Step 5) — the counterterm character on a generator is `-R` of the prepared value.**  The
`-R` (pole-subtraction) relation holds ONLY on generators (via `_X`); the character itself is
multiplicative, NOT `-R ∘ (preparation character)`. -/
theorem phi4BogoliubovCountertermCharacter_X_eq_polePart
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (x : StableResolvedPhi4HopfGen) :
    phi4BogoliubovCountertermCharacter S φ (MvPolynomial.X x)
      = -S.polePart (phi4BogoliubovPreparationGen S φ x) := by
  rw [phi4BogoliubovCountertermCharacter_X, phi4BogoliubovCountertermGen_eq]

/-- **body-662 (Step 5) — the renormalized character on a generator is the finite part of the prepared
value.** -/
theorem phi4BogoliubovRenormalizedCharacter_X_eq_finitePart
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (x : StableResolvedPhi4HopfGen) :
    phi4BogoliubovRenormalizedCharacter S φ (MvPolynomial.X x)
      = S.finitePart (phi4BogoliubovPreparationGen S φ x) := by
  rw [phi4BogoliubovRenormalizedCharacter_X, phi4BogoliubovRenormalizedGen_eq]

/-- **body-662 (Step 5) — the renormalized character has no pole part on a generator.**  `R(φ₊(X x)) = 0`
(660's `polePart_finitePart` at the prepared value).  This is a GENERATOR-level statement — it does NOT
extend to the whole character (`φ₊ 1 = 1`, whose pole part need not vanish). -/
theorem phi4BogoliubovRenormalizedCharacter_X_polePart_zero
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (x : StableResolvedPhi4HopfGen) :
    S.polePart (phi4BogoliubovRenormalizedCharacter S φ (MvPolynomial.X x)) = 0 := by
  rw [phi4BogoliubovRenormalizedCharacter_X_eq_finitePart]
  exact S.polePart_finitePart _

end GaugeGeometry.QFT.Combinatorial
